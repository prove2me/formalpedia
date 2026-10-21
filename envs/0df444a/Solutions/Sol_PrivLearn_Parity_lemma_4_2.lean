-- Prove2me | solution 1 for PrivLearn.Parity.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:16:46.244923+00:00
-- url     : https://prove2.me/submissions/3438da6d-6bdc-4333-b773-530f6b3f7439

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Parity_Learner

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


end PLP

theorem solution (d n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
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
      rw [PLP.algA_none ε hε hε4, PLP.algA_none ε hε hε4, ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      exact ENNReal.ofReal_le_ofReal (PLP.dp_none ε hε hε2 i hj)
    | some r =>
      rw [PLP.algA_some ε hε hε4, PLP.algA_some ε hε hε4, ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
      exact ENNReal.ofReal_le_ofReal (PLP.dp_some ε hε hε2 i hj r)
  have hE : (↑(Finset.univ.filter (fun o => o ∈ E)) : Set (Option (Fin d → ZMod 2))) = E := by
    ext o; simp
  rw [← hE, ← sum_measure_singleton, ← sum_measure_singleton, Finset.mul_sum]
  exact Finset.sum_le_sum (fun o _ => hpt o)
