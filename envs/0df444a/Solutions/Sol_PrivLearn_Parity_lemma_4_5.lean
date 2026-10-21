-- Prove2me | solution 1 for PrivLearn.Parity.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:25:55.244832+00:00
-- url     : https://prove2.me/submissions/17c8a7fd-0f52-4c21-a0a4-a1bb241109c5

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Parity_Amplified

set_option autoImplicit false
open MeasureTheory PrivLearn.Parity

namespace PLP


lemma zmod2_aux1 : ∀ a b c : ZMod 2, a = c → b = c → a + b + c = c := by decide
lemma zmod2_aux2 : ∀ a b c : ZMod 2, a ≠ c → b ≠ c → a + b + c = c := by decide

lemma mem_solSpace {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) (r : Fin d → ZMod 2) :
    r ∈ solSpace z S ↔ ∀ j ∈ S, parity (z j).1 r = (z j).2 := by
  simp [solSpace]

lemma halving_aux {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n)
    (h : (solSpace z (insert i T)).Nonempty) :
    (solSpace z T).card ≤ 2 * (solSpace z (insert i T)).card := by
  obtain ⟨r0, hr0⟩ := h
  have hsplit := Finset.card_filter_add_card_filter_not (s := solSpace z T)
    (fun r => parity (z i).1 r = (z i).2)
  have hgood : (solSpace z T).filter (fun r => parity (z i).1 r = (z i).2) = solSpace z (insert i T) := by
    ext r
    simp only [Finset.mem_filter, mem_solSpace, Finset.mem_insert, forall_eq_or_imp]
    tauto
  rw [hgood] at hsplit
  by_cases hex : ∃ r1 ∈ solSpace z T, ¬ parity (z i).1 r1 = (z i).2
  · obtain ⟨r1, hr1, hr1'⟩ := hex
    have hle : ((solSpace z T).filter (fun r => ¬ parity (z i).1 r = (z i).2)).card ≤
        (solSpace z (insert i T)).card := by
      apply Finset.card_le_card_of_injOn (fun r => r + r1 + r0)
      · intro r hr
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr
        simp only [Finset.mem_coe, mem_solSpace, Finset.mem_insert, forall_eq_or_imp]
        have hrT := (mem_solSpace z T r).mp hr.1
        have hr1T := (mem_solSpace z T r1).mp hr1
        have hr0' := (mem_solSpace z (insert i T) r0).mp hr0
        have key : ∀ j, parity (z j).1 (r + r1 + r0) = parity (z j).1 r + parity (z j).1 r1 +
            parity (z j).1 r0 := by
          intro j; simp [parity, dotProduct_add]
        constructor
        · rw [key, hr0' i (Finset.mem_insert_self _ _)]
          exact zmod2_aux2 _ _ _ hr.2 hr1'
        · intro j hj
          rw [key, hrT j hj, hr1T j hj, hr0' j (Finset.mem_insert_of_mem hj)]
          exact zmod2_aux1 _ _ _ rfl rfl
      · intro a _ b _ hab
        simpa using hab
    omega
  · push Not at hex
    have : ((solSpace z T).filter (fun r => ¬ parity (z i).1 r = (z i).2)) = ∅ := by
      ext r; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact fun hr => by simpa using hex r hr
    rw [this] at hsplit
    simp at hsplit
    omega


lemma outProb_nonneg {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) (r : Fin d → ZMod 2) :
    0 ≤ outProb z S r := by
  unfold outProb
  split_ifs
  · positivity
  · exact le_rfl

lemma outProb_le {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n)
    (r : Fin d → ZMod 2) : outProb z (insert i T) r ≤ 2 * outProb z T r := by
  by_cases hr : r ∈ solSpace z (insert i T)
  · have hrT : r ∈ solSpace z T := by
      rw [mem_solSpace] at hr ⊢
      exact fun j hj => hr j (Finset.mem_insert_of_mem hj)
    have hne : (solSpace z (insert i T)).Nonempty := ⟨r, hr⟩
    have hh := halving_aux z T i hne
    have hc1 : (0 : ℝ) < ((solSpace z (insert i T)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have hc2 : (0 : ℝ) < ((solSpace z T).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨r, hrT⟩
    have hh' : ((solSpace z T).card : ℝ) ≤ 2 * ((solSpace z (insert i T)).card : ℝ) := by
      exact_mod_cast hh
    unfold outProb
    rw [if_pos hr, if_pos hrT, mul_one_div, div_le_div_iff₀ hc1 hc2]
    linarith
  · unfold outProb
    rw [if_neg hr]
    have := outProb_nonneg z T r
    unfold outProb at this
    linarith

lemma claim43_main {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) (z : Fin n → Example d)
    (i : Fin n) (r : Fin d → ZMod 2) :
    ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z (insert i T) r ≤
      2 * ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z T r := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  have hw : 0 ≤ (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) := by
    have h1 : 0 ≤ ε / 4 := by positivity
    have h2 : 0 ≤ 1 - ε / 4 := by linarith
    positivity
  have := outProb_le z T i r
  calc _ ≤ ((ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card)) * (2 * outProb z T r) :=
        mul_le_mul_of_nonneg_left this hw
    _ = _ := by ring


instance instMSC (d : ℕ) : MeasurableSingletonClass (Option (Fin d → ZMod 2)) :=
  ⟨fun _ => by
    show MeasurableSet[⊤] _
    exact MeasurableSpace.measurableSet_top⟩

noncomputable def eS {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) : ℝ :=
  if (solSpace z S).Nonempty then 0 else 1

noncomputable def muS {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) :
    Measure (Option (Fin d → ZMod 2)) :=
  if (solSpace z S).Nonempty then
    ∑ r ∈ solSpace z S, ((solSpace z S).card : ENNReal)⁻¹ • Measure.dirac (some r)
  else Measure.dirac none

lemma selWeight_nonneg (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    0 ≤ selWeight p n S := by
  unfold selWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma muS_some {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) (r : Fin d → ZMod 2) :
    muS z S {some r} = ENNReal.ofReal (outProb z S r) := by
  unfold muS outProb
  by_cases hne : (solSpace z S).Nonempty
  · rw [if_pos hne]
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Option.some.injEq,
      Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases hr : r ∈ solSpace z S
    · have hc : (0 : ℝ) < ((solSpace z S).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
      rw [if_pos hr, if_pos hr, one_div, ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast]
    · rw [if_neg hr, if_neg hr]; simp
  · rw [if_neg hne]
    have : r ∉ solSpace z S := fun h => hne ⟨r, h⟩
    rw [if_neg this]
    simp

lemma muS_none {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) :
    muS z S {none} = ENNReal.ofReal (eS z S) := by
  unfold muS eS
  by_cases hne : (solSpace z S).Nonempty
  · rw [if_pos hne, if_pos hne]
    simp
  · rw [if_neg hne, if_neg hne]
    simp

lemma algA_eq {d n : ℕ} (ε : ℝ) (z : Fin n → Example d) :
    algA ε z = (1 / 2 : ENNReal) • Measure.dirac none +
      (1 / 2 : ENNReal) • ∑ S : Finset (Fin n), ENNReal.ofReal (selWeight (ε / 4) n S) • muS z S := rfl

lemma outProb_nn {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) (r : Fin d → ZMod 2) :
    0 ≤ outProb z S r := outProb_nonneg z S r

lemma eS_nn {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) : 0 ≤ eS z S := by
  unfold eS; split_ifs <;> norm_num

lemma algA_some {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) (z : Fin n → Example d)
    (r : Fin d → ZMod 2) :
    algA ε z {some r} =
      ENNReal.ofReal (1 / 2 * ∑ S : Finset (Fin n), selWeight (ε / 4) n S * outProb z S r) := by
  have hp0 : 0 ≤ ε / 4 := by positivity
  have hp1 : ε / 4 ≤ 1 := by linarith
  rw [algA_eq]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    smul_eq_mul, muS_some]
  have h1 : (Measure.dirac (none : Option (Fin d → ZMod 2))) {some r} = 0 := by simp
  rw [h1, mul_zero, zero_add]
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg
    (fun S _ => mul_nonneg (selWeight_nonneg _ _ hp0 hp1 S) (outProb_nn z S r))]
  congr 1
  · rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  · apply Finset.sum_congr rfl
    intro S _
    rw [ENNReal.ofReal_mul (selWeight_nonneg _ _ hp0 hp1 S)]

lemma algA_none {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) (z : Fin n → Example d) :
    algA ε z {none} =
      ENNReal.ofReal (1 / 2 + 1 / 2 * ∑ S : Finset (Fin n), selWeight (ε / 4) n S * eS z S) := by
  have hp0 : 0 ≤ ε / 4 := by positivity
  have hp1 : ε / 4 ≤ 1 := by linarith
  rw [algA_eq]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    smul_eq_mul, muS_none]
  have h1 : (Measure.dirac (none : Option (Fin d → ZMod 2))) {none} = 1 := by simp
  rw [h1, mul_one]
  have hs : 0 ≤ ∑ S : Finset (Fin n), selWeight (ε / 4) n S * eS z S :=
    Finset.sum_nonneg (fun S _ => mul_nonneg (selWeight_nonneg _ _ hp0 hp1 S) (eS_nn z S))
  rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_sum_of_nonneg
    (fun S _ => mul_nonneg (selWeight_nonneg _ _ hp0 hp1 S) (eS_nn z S))]
  congr 1
  · rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  · congr 1
    · rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    · apply Finset.sum_congr rfl
      intro S _
      rw [ENNReal.ofReal_mul (selWeight_nonneg _ _ hp0 hp1 S)]




lemma split_sum {n : ℕ} (i : Fin n) (p : ℝ) (g : Finset (Fin n) → ℝ) :
    ∑ S : Finset (Fin n), selWeight p n S * g S =
      ∑ T ∈ (Finset.univ.erase i).powerset, (p ^ T.card * (1 - p) ^ (n - 1 - T.card)) *
        ((1 - p) * g T + p * g (insert i T)) := by
  have h1 : (Finset.univ : Finset (Finset (Fin n))) = (insert i (Finset.univ.erase i)).powerset := by
    rw [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ]
  rw [h1, Finset.sum_powerset_insert (Finset.notMem_erase i _), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hi : i ∉ T := fun h => (Finset.notMem_erase i _) (hT h)
  have hcard : T.card ≤ n - 1 := by
    have := Finset.card_le_card hT
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)] at this
    simpa using this
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
  unfold selWeight
  rw [Finset.card_insert_of_notMem hi]
  have e1 : n - T.card = (n - 1 - T.card) + 1 := by omega
  have e2 : n - (T.card + 1) = n - 1 - T.card := by omega
  rw [e1, e2, pow_succ, pow_succ]
  ring

lemma sum_weights {n : ℕ} (i : Fin n) (p : ℝ) :
    ∑ T ∈ (Finset.univ.erase i).powerset, (p ^ T.card * (1 - p) ^ (n - 1 - T.card)) = 1 := by
  have := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ.erase i)
  have hc : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  rw [hc] at this
  simpa using this

lemma neighbors_solSpace {d n : ℕ} {z z' : Fin n → Example d} {i : Fin n}
    (h : ∀ j : Fin n, j ≠ i → z j = z' j) (T : Finset (Fin n)) (hi : i ∉ T) :
    solSpace z T = solSpace z' T := by
  ext r
  simp only [mem_solSpace]
  constructor
  · intro hr j hj
    have : j ≠ i := fun hh => hi (hh ▸ hj)
    rw [← h j this]; exact hr j hj
  · intro hr j hj
    have : j ≠ i := fun hh => hi (hh ▸ hj)
    rw [h j this]; exact hr j hj

lemma e_ineq (p x : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) : 1 + p + (1 - p) * x ≤ (1 + p) * (1 + x) := by
  nlinarith

lemma exp_ineq (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) : 1 + ε / 4 ≤ Real.exp ε * (1 - ε / 4) := by
  have h1 := Real.add_one_le_exp ε
  nlinarith

lemma dp_some {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {z z' : Fin n → Example d} (i : Fin n)
    (h : ∀ j : Fin n, j ≠ i → z j = z' j) (r : Fin d → ZMod 2) :
    1 / 2 * ∑ S : Finset (Fin n), selWeight (ε / 4) n S * outProb z S r ≤
      Real.exp ε * (1 / 2 * ∑ S : Finset (Fin n), selWeight (ε / 4) n S * outProb z' S r) := by
  have hp0 : 0 ≤ ε / 4 := by positivity
  have hp1 : ε / 4 ≤ 1 / 8 := by linarith
  rw [split_sum i, split_sum i]
  set p := ε / 4 with hp
  set W : Finset (Fin n) → ℝ := fun T => p ^ T.card * (1 - p) ^ (n - 1 - T.card) with hW
  have hW0 : ∀ T, 0 ≤ W T := fun T => by
    have : 0 ≤ 1 - p := by linarith
    simp only [hW]; positivity
  have hq : ∀ T ∈ (Finset.univ.erase i).powerset, outProb z T r = outProb z' T r := by
    intro T hT
    have hi : i ∉ T := fun hh => (Finset.notMem_erase i _) (Finset.mem_powerset.mp hT hh)
    unfold outProb
    rw [neighbors_solSpace h T hi]
  have hA : ∑ T ∈ (Finset.univ.erase i).powerset, W T * ((1 - p) * outProb z T r + p * outProb z (insert i T) r) ≤
      (1 + p) * ∑ T ∈ (Finset.univ.erase i).powerset, W T * outProb z T r := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T _
    have := outProb_le z T i r
    have h0 := hW0 T
    nlinarith [mul_nonneg h0 hp0]
  have hB : (1 - p) * ∑ T ∈ (Finset.univ.erase i).powerset, W T * outProb z T r ≤
      ∑ T ∈ (Finset.univ.erase i).powerset, W T * ((1 - p) * outProb z' T r + p * outProb z' (insert i T) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T hT
    rw [hq T hT]
    have h0 := hW0 T
    have := outProb_nn z' (insert i T) r
    have : 0 ≤ W T * (p * outProb z' (insert i T) r) := mul_nonneg h0 (mul_nonneg hp0 this)
    nlinarith
  have hex := exp_ineq ε hε hε2
  have hS : 0 ≤ ∑ T ∈ (Finset.univ.erase i).powerset, W T * outProb z T r :=
    Finset.sum_nonneg (fun T _ => mul_nonneg (hW0 T) (outProb_nn z T r))
  have hp' : 0 < 1 - p := by linarith
  calc _ ≤ 1 / 2 * ((1 + p) * ∑ T ∈ (Finset.univ.erase i).powerset, W T * outProb z T r) := by linarith
    _ ≤ 1 / 2 * (Real.exp ε * ((1 - p) * ∑ T ∈ (Finset.univ.erase i).powerset, W T * outProb z T r)) := by
        have : (1 + p) * ∑ T ∈ (Finset.univ.erase i).powerset, W T * outProb z T r ≤
            Real.exp ε * ((1 - p) * ∑ T ∈ (Finset.univ.erase i).powerset, W T * outProb z T r) := by
          rw [← mul_assoc]
          have := mul_le_mul_of_nonneg_right hex hS
          nlinarith
        linarith
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hB (Real.exp_pos ε).le
        linarith


lemma eS_le_one {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) : eS z S ≤ 1 := by
  unfold eS; split_ifs <;> norm_num

lemma eS_mono {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n) :
    eS z T ≤ eS z (insert i T) := by
  unfold eS
  by_cases hne : (solSpace z (insert i T)).Nonempty
  · have : (solSpace z T).Nonempty := by
      obtain ⟨r, hr⟩ := hne
      refine ⟨r, ?_⟩
      rw [mem_solSpace] at hr ⊢
      exact fun j hj => hr j (Finset.mem_insert_of_mem hj)
    rw [if_pos this, if_pos hne]
  · rw [if_neg hne]
    split_ifs <;> norm_num

lemma dp_none {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {z z' : Fin n → Example d} (i : Fin n)
    (h : ∀ j : Fin n, j ≠ i → z j = z' j) :
    1 / 2 + 1 / 2 * ∑ S : Finset (Fin n), selWeight (ε / 4) n S * eS z S ≤
      Real.exp ε * (1 / 2 + 1 / 2 * ∑ S : Finset (Fin n), selWeight (ε / 4) n S * eS z' S) := by
  have hp0 : 0 ≤ ε / 4 := by positivity
  have hp1 : ε / 4 ≤ 1 / 8 := by linarith
  rw [split_sum i, split_sum i]
  set p := ε / 4 with hp
  set W : Finset (Fin n) → ℝ := fun T => p ^ T.card * (1 - p) ^ (n - 1 - T.card) with hW
  have hW0 : ∀ T, 0 ≤ W T := fun T => by
    have : 0 ≤ 1 - p := by linarith
    simp only [hW]; positivity
  have hW1 : ∑ T ∈ (Finset.univ.erase i).powerset, W T = 1 := sum_weights i p
  have hq : ∀ T ∈ (Finset.univ.erase i).powerset, eS z T = eS z' T := by
    intro T hT
    have hi : i ∉ T := fun hh => (Finset.notMem_erase i _) (Finset.mem_powerset.mp hT hh)
    unfold eS
    rw [neighbors_solSpace h T hi]
  set X := ∑ T ∈ (Finset.univ.erase i).powerset, W T * eS z T with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun T _ => mul_nonneg (hW0 T) (eS_nn z T))
  have hA : ∑ T ∈ (Finset.univ.erase i).powerset, W T * ((1 - p) * eS z T + p * eS z (insert i T)) ≤
      (1 - p) * X + p := by
    have : ∑ T ∈ (Finset.univ.erase i).powerset, W T * ((1 - p) * eS z T + p * eS z (insert i T)) ≤
        ∑ T ∈ (Finset.univ.erase i).powerset, ((1 - p) * (W T * eS z T) + p * W T) := by
      apply Finset.sum_le_sum
      intro T _
      have := eS_le_one z (insert i T)
      have h0 := hW0 T
      nlinarith [mul_nonneg h0 hp0]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hW1] at this
    linarith
  have hB : X ≤ ∑ T ∈ (Finset.univ.erase i).powerset, W T * ((1 - p) * eS z' T + p * eS z' (insert i T)) := by
    have : ∑ T ∈ (Finset.univ.erase i).powerset, W T * eS z T ≤
        ∑ T ∈ (Finset.univ.erase i).powerset, W T * ((1 - p) * eS z' T + p * eS z' (insert i T)) := by
      apply Finset.sum_le_sum
      intro T hT
      rw [hq T hT]
      have h0 := hW0 T
      have := eS_mono z' T i
      apply mul_le_mul_of_nonneg_left _ h0
      nlinarith
    exact this
  have hex := exp_ineq ε hε hε2
  have hep : 1 + p ≤ Real.exp ε := by
    have : 0 ≤ p * Real.exp ε := mul_nonneg hp0 (Real.exp_pos ε).le
    nlinarith
  have he := e_ineq p X hp0 hX0
  have h1 : (1 + p) * (1 + X) ≤ Real.exp ε * (1 + X) :=
    mul_le_mul_of_nonneg_right hep (by linarith)
  have h2 : Real.exp ε * (1 + X) ≤ Real.exp ε * (1 + 2 * ∑ T ∈ (Finset.univ.erase i).powerset, W T * ((1 - p) * eS z' T + p * eS z' (insert i T))) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos ε).le
    linarith
  nlinarith



lemma algA_dp (d n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algA ε z) ε := by
  classical
  intro z z' hz E _
  obtain ⟨i, _, hj⟩ := hz
  have hε4 : ε ≤ 4 := by linarith
  have hpt : ∀ o : Option (Fin d → ZMod 2),
      algA ε z {o} ≤ ENNReal.ofReal (Real.exp ε) * algA ε z' {o} := by
    intro o
    cases o with
    | none =>
      rw [algA_none ε hε hε4, algA_none ε hε hε4, ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      exact ENNReal.ofReal_le_ofReal (dp_none ε hε hε2 i hj)
    | some r =>
      rw [algA_some ε hε hε4, algA_some ε hε hε4, ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      exact ENNReal.ofReal_le_ofReal (dp_some ε hε hε2 i hj r)
  have hE : (↑(Finset.univ.filter (fun o => o ∈ E)) : Set (Option (Fin d → ZMod 2))) = E := by
    ext o; simp
  rw [← hE, ← sum_measure_singleton, ← sum_measure_singleton, Finset.mul_sum]
  exact Finset.sum_le_sum (fun o _ => hpt o)



lemma prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ ν : Measure α}
    {μ' ν' : Measure β} [SFinite μ'] [SFinite ν'] (c c' : ENNReal)
    (h : μ ≤ c • ν) (h' : μ' ≤ c' • ν') : μ.prod μ' ≤ (c * c') • ν.prod ν' := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.prod_apply hs, Measure.smul_apply, Measure.prod_apply hs, smul_eq_mul]
  have hm : Measurable (fun x => ν' (Prod.mk x ⁻¹' s)) := measurable_measure_prodMk_left hs
  calc ∫⁻ x, μ' (Prod.mk x ⁻¹' s) ∂μ ≤ ∫⁻ x, c' * ν' (Prod.mk x ⁻¹' s) ∂μ := by
        apply lintegral_mono
        intro x
        have := Measure.le_iff'.mp h' (Prod.mk x ⁻¹' s)
        simpa using this
    _ = c' * ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ := lintegral_const_mul _ hm
    _ ≤ c' * ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂(c • ν) := by
        gcongr
    _ = (c * c') * ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂ν := by
        rw [lintegral_smul_measure]; ring

lemma pi_le : ∀ (k : ℕ) {O : Fin k → Type*} [∀ i, MeasurableSpace (O i)] (μ ν : ∀ i, Measure (O i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (c : Fin k → ENNReal),
    (∀ i, μ i ≤ c i • ν i) → Measure.pi μ ≤ (∏ i, c i) • Measure.pi ν := by
  intro k
  induction k with
  | zero =>
    intro O _ μ ν _ _ c h
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ k ih =>
    intro O _ μ ν _ _ c h
    rw [Measure.le_iff]
    intro E hE
    let e := MeasurableEquiv.piFinSuccAbove O 0
    have hμ := measurePreserving_piFinSuccAbove μ 0
    have hν := measurePreserving_piFinSuccAbove ν 0
    have hE' : MeasurableSet (e.symm ⁻¹' E) := e.symm.measurable hE
    have hEE : E = e ⁻¹' (e.symm ⁻¹' E) := by
      ext x
      show x ∈ E ↔ e.symm (e x) ∈ E
      rw [e.symm_apply_apply]
    have h1 : Measure.pi μ E = ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) (e.symm ⁻¹' E) := by
      conv_lhs => rw [hEE]
      exact hμ.measure_preimage_equiv _
    have h2 : Measure.pi ν E = ((ν 0).prod (Measure.pi fun j => ν (Fin.succAbove 0 j))) (e.symm ⁻¹' E) := by
      conv_lhs => rw [hEE]
      exact hν.measure_preimage_equiv _
    have h3 := prod_le (c 0) (∏ j : Fin k, c (Fin.succAbove 0 j)) (h 0)
      (ih (fun j => μ (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
        (fun j => c (Fin.succAbove 0 j)) (fun j => h _))
    rw [Measure.le_iff] at h3
    have h4 := h3 _ hE'
    rw [h1, Measure.smul_apply, h2, smul_eq_mul, Fin.prod_univ_succAbove _ 0]
    rw [Measure.smul_apply, smul_eq_mul] at h4
    exact h4

lemma lap_sf (σ : ℝ) : SigmaFinite (PrivLearn.Generic.laplace σ) := by
  unfold PrivLearn.Generic.laplace
  exact SigmaFinite.withDensity_of_ne_top' (fun x => ENNReal.ofReal_ne_top)

lemma map_laplace_apply (s c : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    ((PrivLearn.Generic.laplace s).map (fun η => c + η)) S =
      ∫⁻ y in S, ENNReal.ofReal (Real.exp (-|y - c| / s) / (2 * s)) := by
  have hm : Measurable (fun η : ℝ => c + η) := measurable_const_add c
  rw [Measure.map_apply hm hS, PrivLearn.Generic.laplace,
    withDensity_apply _ (hm hS)]
  have hmp : MeasurePreserving (fun η : ℝ => c + η) volume volume := measurePreserving_add_left volume c
  have := hmp.setLIntegral_comp_preimage hS
    (f := fun y => ENNReal.ofReal (Real.exp (-|y - c| / s) / (2 * s)))
    (by fun_prop)
  simpa using this

lemma lap_shift_le {σ : ℝ} (hσ : 0 < σ) (c c' : ℝ) :
    (PrivLearn.Generic.laplace σ).map (fun η => c + η) ≤
      ENNReal.ofReal (Real.exp (|c - c'| / σ)) • (PrivLearn.Generic.laplace σ).map (fun η => c' + η) := by
  rw [Measure.le_iff]
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, map_laplace_apply _ _ _ hS, map_laplace_apply _ _ _ hS]
  rw [← lintegral_const_mul' (ENNReal.ofReal (Real.exp (|c - c'| / σ)))
    (fun y => ENNReal.ofReal (Real.exp (-|y - c'| / σ) / (2 * σ))) ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  beta_reduce
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have h1 : |y - c'| ≤ |y - c| + |c - c'| := by
    calc |y - c'| = |(y - c) + (c - c')| := by ring_nf
      _ ≤ |y - c| + |c - c'| := abs_add_le _ _
  have h2 : -|y - c| / σ ≤ -|y - c'| / σ + |c - c'| / σ := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hσ.le
  calc Real.exp (-|y - c| / σ) / (2 * σ) ≤ Real.exp (-|y - c'| / σ + |c - c'| / σ) / (2 * σ) :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h2) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

lemma vec_shift_le {k : ℕ} {σ : ℝ} (hσ : 0 < σ) (δ : Fin k → ℝ) :
    (Measure.pi fun _ : Fin k => PrivLearn.Generic.laplace σ).map (fun η j => δ j + η j) ≤
      ENNReal.ofReal (Real.exp (∑ j, |δ j| / σ)) • Measure.pi fun _ : Fin k => PrivLearn.Generic.laplace σ := by
  haveI := lap_sf σ
  haveI hsf : ∀ j : Fin k, SigmaFinite ((PrivLearn.Generic.laplace σ).map (fun η => δ j + η)) := fun j => by
    have := (MeasurableEquiv.addLeft (δ j)).sigmaFinite_map (μ := PrivLearn.Generic.laplace σ)
    simpa using this
  rw [Measure.pi_map_pi (μ := fun _ : Fin k => PrivLearn.Generic.laplace σ) (f := fun j η => δ j + η)
    (fun j => (measurable_const_add (δ j)).aemeasurable)]
  have h := pi_le k (μ := fun j => (PrivLearn.Generic.laplace σ).map (fun η => δ j + η))
    (ν := fun _ => PrivLearn.Generic.laplace σ) (fun j => ENNReal.ofReal (Real.exp (|δ j| / σ))) (fun j => by
      have := lap_shift_le hσ (δ j) 0
      simpa using this)
  have hprod : (∏ j : Fin k, ENNReal.ofReal (Real.exp (|δ j| / σ))) =
      ENNReal.ofReal (Real.exp (∑ j, |δ j| / σ)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), Real.exp_sum]
  rw [hprod] at h
  exact h


lemma N_le {k : ℕ} {σ : ℝ} (hσ : 0 < σ) (ε : ℝ) {O : Type*} [MeasurableSpace O]
    (G : (Fin k → ℝ) → O) (e e' : Fin k → ℝ) (hee : ∑ j, |e j - e' j| / σ ≤ ε)
    (S : Set O) (hS : MeasurableSet S) :
    ((Measure.pi fun _ : Fin k => PrivLearn.Generic.laplace σ).map (fun η => G (fun j => e j + η j))) S ≤
      ENNReal.ofReal (Real.exp ε) *
        ((Measure.pi fun _ : Fin k => PrivLearn.Generic.laplace σ).map (fun η => G (fun j => e' j + η j))) S := by
  set μ := Measure.pi fun _ : Fin k => PrivLearn.Generic.laplace σ with hμ
  set F : (Fin k → ℝ) → O := fun η => G (fun j => e j + η j) with hF
  set F' : (Fin k → ℝ) → O := fun η => G (fun j => e' j + η j) with hF'
  have hsh : ∀ δ : Fin k → ℝ, Measurable (fun η : Fin k → ℝ => fun j => δ j + η j) := fun δ =>
    measurable_pi_lambda _ (fun j => (measurable_const_add (δ j)).comp (measurable_pi_apply j))
  have key : ∀ δ : Fin k → ℝ, μ.map (fun η j => δ j + η j) ≤
      ENNReal.ofReal (Real.exp (∑ j, |δ j| / σ)) • μ := fun δ => vec_shift_le hσ δ
  have hqmp : ∀ δ : Fin k → ℝ, Measure.QuasiMeasurePreserving (fun η : Fin k → ℝ => fun j => δ j + η j) μ μ :=
    fun δ => ⟨hsh δ, Measure.absolutelyContinuous_of_le_smul (key δ)⟩
  have hFF' : F = F' ∘ (fun η j => (e j - e' j) + η j) := by
    funext η
    simp only [hF, hF', Function.comp]
    congr 1
    funext j
    ring
  have hF'F : F' = F ∘ (fun η j => (e' j - e j) + η j) := by
    funext η
    simp only [hF, hF', Function.comp]
    congr 1
    funext j
    ring
  have hc : ENNReal.ofReal (Real.exp (∑ j, |e j - e' j| / σ)) ≤ ENNReal.ofReal (Real.exp ε) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hee)
  by_cases hA : AEMeasurable F μ
  · have hA' : AEMeasurable F' μ := by
      rw [hF'F]
      exact hA.comp_quasiMeasurePreserving (hqmp _)
    rw [Measure.map_apply_of_aemeasurable hA hS]
    calc μ (F ⁻¹' S) = μ ((fun η j => (e j - e' j) + η j) ⁻¹' (F' ⁻¹' S)) := by
          rw [hFF', Set.preimage_comp]
      _ ≤ (μ.map (fun η j => (e j - e' j) + η j)) (F' ⁻¹' S) :=
          Measure.le_map_apply (hsh _).aemeasurable _
      _ ≤ (ENNReal.ofReal (Real.exp (∑ j, |e j - e' j| / σ)) • μ) (F' ⁻¹' S) :=
          Measure.le_iff'.mp (key _) _
      _ = ENNReal.ofReal (Real.exp (∑ j, |e j - e' j| / σ)) * μ (F' ⁻¹' S) := by
          rw [Measure.smul_apply, smul_eq_mul]
      _ ≤ ENNReal.ofReal (Real.exp ε) * (μ.map F') S := by
          gcongr
          exact Measure.le_map_apply hA' S
  · rw [Measure.map_of_not_aemeasurable hA]
    simp

lemma testErr_diff {d s : ℕ} (T T' : Fin s → Example d) (t0 : Fin s)
    (h : ∀ t, t ≠ t0 → T t = T' t) (o : Option (Fin d → ZMod 2)) :
    |testErr T o - testErr T' o| ≤ 1 / s := by
  cases o with
  | none => simp [testErr]
  | some r =>
    unfold testErr
    set A := Finset.univ.filter fun t => parity r (T t).1 ≠ (T t).2 with hA
    set A' := Finset.univ.filter fun t => parity r (T' t).1 ≠ (T' t).2 with hA'
    have h1 : A ⊆ insert t0 A' := by
      intro t ht
      by_cases htt : t = t0
      · simp [htt]
      · simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        simp only [Finset.mem_insert, hA', Finset.mem_filter, Finset.mem_univ, true_and]
        right
        rw [← h t htt]; exact ht
    have h2 : A' ⊆ insert t0 A := by
      intro t ht
      by_cases htt : t = t0
      · simp [htt]
      · simp only [hA', Finset.mem_filter, Finset.mem_univ, true_and] at ht
        simp only [Finset.mem_insert, hA, Finset.mem_filter, Finset.mem_univ, true_and]
        right
        rw [h t htt]; exact ht
    have c1 : A.card ≤ A'.card + 1 := (Finset.card_le_card h1).trans (Finset.card_insert_le _ _)
    have c2 : A'.card ≤ A.card + 1 := (Finset.card_le_card h2).trans (Finset.card_insert_le _ _)
    have c1' : (A.card : ℝ) ≤ A'.card + 1 := by exact_mod_cast c1
    have c2' : (A'.card : ℝ) ≤ A.card + 1 := by exact_mod_cast c2
    rw [← sub_div, abs_div]
    by_cases hs : s = 0
    · subst hs; simp
    · have : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
      rw [abs_of_pos this]
      apply div_le_div_of_nonneg_right _ this.le
      rw [abs_le]; constructor <;> linarith



lemma paramK_pos (β : ℝ) (hβ : 0 < β) (hβ2 : β < 1 / 2) : 0 < paramK β := by
  unfold paramK
  apply Nat.ceil_pos.mpr
  apply Real.logb_pos (by norm_num)
  rw [lt_div_iff₀ (by positivity)]
  linarith

lemma entry_eq {d n : ℕ} {z z' : Fin n → Example d} {i : Fin n} (h : ∀ j, j ≠ i → z j = z' j)
    (m : ℕ) (hm : m ≠ i.val) : entry z m = entry z' m := by
  unfold entry
  split_ifs with hlt
  · exact h _ (fun hh => hm (by rw [← hh]))
  · rfl

lemma entry_i {d n : ℕ} (z : Fin n → Example d) (i : Fin n) : entry z i.val = z i := by
  unfold entry
  simp [i.2]

lemma weights_eq {d n K N' : ℕ} (ε : ℝ) {z z' : Fin n → Example d} {i : Fin n}
    (hj : ∀ j, j ≠ i → z j = z' j) (hne : ∀ (j : Fin K) (t : Fin N'), j.val * N' + t.val ≠ i.val)
    (H : Fin K → Option (Fin d → ZMod 2)) :
    ∏ j : Fin K, algA ε (trainBlock z N' j) {H j} = ∏ j : Fin K, algA ε (trainBlock z' N' j) {H j} := by
  apply Finset.prod_congr rfl
  intro j _
  have : trainBlock z N' j = trainBlock z' N' j := by
    funext t
    exact entry_eq hj _ (hne j t)
  rw [this]

lemma weights_i {d n K N' : ℕ} (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {z z' : Fin n → Example d}
    {i : Fin n} (hj : ∀ j, j ≠ i → z j = z' j) (hi : z i ≠ z' i) (h1 : i.val < K * N')
    (H : Fin K → Option (Fin d → ZMod 2)) :
    ∏ j : Fin K, algA ε (trainBlock z N' j) {H j} ≤
      ENNReal.ofReal (Real.exp ε) * ∏ j : Fin K, algA ε (trainBlock z' N' j) {H j} := by
  have hN : 0 < N' := by
    rcases Nat.eq_zero_or_pos N' with h | h
    · subst h; simp at h1
    · exact h
  have hdiv : i.val / N' < K := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h1)
  set j0 : Fin K := ⟨i.val / N', hdiv⟩ with hj0
  have hdm : N' * (i.val / N') + i.val % N' = i.val := Nat.div_add_mod _ _
  have hmod : i.val % N' < N' := Nat.mod_lt _ hN
  set t0 : Fin N' := ⟨i.val % N', hmod⟩ with ht0
  -- positions
  have hpos : ∀ (j : Fin K) (t : Fin N'), j.val * N' + t.val = i.val → j = j0 ∧ t = t0 := by
    intro j t h
    have hq : i.val / N' = j.val := by
      rw [← h, add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt t.2, zero_add]
    have hr : i.val % N' = t.val := by
      rw [← h, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt t.2]
    exact ⟨Fin.ext hq.symm, Fin.ext hr.symm⟩
  have hblock : ∀ j : Fin K, j ≠ j0 → trainBlock z N' j = trainBlock z' N' j := by
    intro j hjj
    funext t
    apply entry_eq hj
    intro h
    exact hjj (hpos j t h).1
  have hnb : PrivLearn.Generic.Neighbors (trainBlock z N' j0) (trainBlock z' N' j0) := by
    refine ⟨t0, ?_, ?_⟩
    · show entry z (j0.val * N' + t0.val) ≠ entry z' (j0.val * N' + t0.val)
      have : j0.val * N' + t0.val = i.val := by
        simp only [hj0, ht0]; rw [mul_comm]; exact hdm
      rw [this, entry_i, entry_i]
      exact hi
    · intro t ht
      apply entry_eq hj
      intro h
      exact ht (hpos j0 t h).2
  have hdp := algA_dp d N' ε hε hε2 _ _ hnb {H j0} (measurableSet_singleton _)
  rw [← Finset.mul_prod_erase Finset.univ (fun j : Fin K => algA ε (trainBlock z N' j) {H j}) (Finset.mem_univ j0),
    ← Finset.mul_prod_erase Finset.univ (fun j : Fin K => algA ε (trainBlock z' N' j) {H j}) (Finset.mem_univ j0)]
  have hprod : ∏ j ∈ Finset.univ.erase j0, algA ε (trainBlock z N' j) {H j} =
      ∏ j ∈ Finset.univ.erase j0, algA ε (trainBlock z' N' j) {H j} := by
    apply Finset.prod_congr rfl
    intro j hjm
    rw [hblock j (Finset.ne_of_mem_erase hjm)]
  rw [hprod]
  calc _ ≤ (ENNReal.ofReal (Real.exp ε) * algA ε (trainBlock z' N' j0) {H j0}) *
        ∏ j ∈ Finset.univ.erase j0, algA ε (trainBlock z' N' j) {H j} := by gcongr
    _ = _ := by ring


lemma testErr_sum {d s K : ℕ} {σ ε : ℝ} (hσ : 0 < σ) (hK : 0 < K) (hs : 0 < s)
    (hσe : σ = K / (s * ε)) (hε : 0 < ε)
    (T T' : Fin s → Example d) (t0 : Fin s) (h : ∀ t, t ≠ t0 → T t = T' t)
    (H : Fin K → Option (Fin d → ZMod 2)) :
    ∑ j : Fin K, |testErr T (H j) - testErr T' (H j)| / σ ≤ ε := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : ∀ j : Fin K, |testErr T (H j) - testErr T' (H j)| / σ ≤ ε / K := by
    intro j
    have := testErr_diff T T' t0 h (H j)
    calc |testErr T (H j) - testErr T' (H j)| / σ ≤ (1 / s) / σ :=
          div_le_div_of_nonneg_right this hσ.le
      _ = ε / K := by rw [hσe]; field_simp
  calc ∑ j : Fin K, |testErr T (H j) - testErr T' (H j)| / σ ≤ ∑ _j : Fin K, ε / K :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = ε := by simp; field_simp

end PLP

theorem solution (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') (d : ℕ) (hd : 1 ≤ d) (ε α β : ℝ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ2 : β < 1 / 2)
    (n : ℕ) :
    PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algAstar c c' d ε α β z) ε := by
  intro z z' hz S hS
  obtain ⟨i, hi, hj⟩ := hz
  have hK := PLP.paramK_pos β hβ hβ2
  have hexp : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := ENNReal.one_le_ofReal.mpr (Real.one_le_exp hε.le)
  simp only
  by_cases hn : n ≤ paramK β * paramN c d ε α + paramS c' ε α β
  · simp only [algAstar, if_pos hn]
    exact le_mul_of_one_le_left (zero_le) hexp
  · simp only [algAstar, if_neg hn, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    generalize paramK β = K at hK hn ⊢
    generalize paramN c d ε α = N' at hn ⊢
    generalize paramS c' ε α β = Sz at hn ⊢
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro H _
    by_cases h1 : i.val < K * N'
    · -- the changed entry lies in a training block
      have hw := PLP.weights_i (K := K) (N' := N') ε hε hε2 hj hi h1 H
      have hts : testSet z K N' Sz = testSet z' K N' Sz := by
        funext t
        apply PLP.entry_eq hj
        intro h; omega
      rw [hts]
      calc _ ≤ (ENNReal.ofReal (Real.exp ε) * ∏ j : Fin K, algA ε (trainBlock z' N' j) {H j}) *
            ((Measure.pi fun _ : Fin K => PrivLearn.Generic.laplace ((K : ℝ) / (Sz * ε))).map
              (fun η => select H (fun j => testErr (testSet z' K N' Sz) (H j) + η j))) S := by gcongr
        _ = _ := by ring
    · have hne : ∀ (j : Fin K) (t : Fin N'), j.val * N' + t.val ≠ i.val := by
        intro j t h
        have : (j.val + 1) * N' ≤ K * N' := Nat.mul_le_mul_right N' j.2
        have h2 : (j.val + 1) * N' = j.val * N' + N' := by ring
        have := t.2
        omega
      rw [PLP.weights_eq ε hj hne H]
      by_cases h2 : i.val < K * N' + Sz
      · -- the changed entry lies in the test set
        have ht0 : i.val - K * N' < Sz := by omega
        have hts : ∀ t : Fin Sz, t ≠ ⟨i.val - K * N', ht0⟩ → testSet z K N' Sz t = testSet z' K N' Sz t := by
          intro t ht
          apply PLP.entry_eq hj
          intro h
          apply ht
          apply Fin.ext
          show t.val = i.val - K * N'
          omega
        have hSpos : 0 < Sz := by omega
        have hσ : (0 : ℝ) < (K : ℝ) / (Sz * ε) := by
          have : (0 : ℝ) < K := by exact_mod_cast hK
          have : (0 : ℝ) < Sz := by exact_mod_cast hSpos
          positivity
        have hN := PLP.N_le hσ ε (select H) (fun j => testErr (testSet z K N' Sz) (H j))
          (fun j => testErr (testSet z' K N' Sz) (H j))
          (PLP.testErr_sum hσ hK hSpos rfl hε _ _ _ hts H) S hS
        calc _ ≤ (∏ j : Fin K, algA ε (trainBlock z' N' j) {H j}) *
              (ENNReal.ofReal (Real.exp ε) *
              ((Measure.pi fun _ : Fin K => PrivLearn.Generic.laplace ((K : ℝ) / (Sz * ε))).map
              (fun η => select H (fun j => testErr (testSet z' K N' Sz) (H j) + η j))) S) := by
              gcongr
          _ = _ := by ring
      · have hts : testSet z K N' Sz = testSet z' K N' Sz := by
          funext t
          apply PLP.entry_eq hj
          intro h; omega
        rw [hts]
        exact le_mul_of_one_le_left (zero_le) hexp
