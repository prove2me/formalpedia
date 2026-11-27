-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:37:00.39558+00:00
-- url     : https://prove2.me/submissions/1de3a566-5feb-4f16-a71f-c8e8bfa4e17b

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Nat
noncomputable section

namespace TFIMPhaseDiagram.Classical.P7Aux

def cnt {d M : ℕ} (β : Fin d → Fin M) (r : Fin M) : ℕ := (Finset.univ.filter (fun j => β j = r)).card
def Gq (q : Bool) (x : ℝ) : ℝ := if q then Real.sinh x else Real.cosh x
def sg (q : Bool) : ℝ := if q then -1 else 1
def Ngood (d M : ℕ) (q : Fin M → Bool) : ℕ :=
  (Finset.univ.filter (fun β : Fin d → Fin M => ∀ r, (cnt β r).bodd = q r)).card

lemma neg_one_pow_bodd (c : ℕ) : (-1 : ℝ) ^ c = if c.bodd then -1 else 1 := by
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, ih, Nat.bodd_succ]; cases c.bodd <;> simp

lemma ind_eq (c : ℕ) (q : Bool) :
    (if c.bodd = q then (1:ℝ) else 0) = 1 / 2 + sg q * (-1) ^ c / 2 := by
  rw [neg_one_pow_bodd]; cases q <;> cases c.bodd <;> simp [sg] <;> norm_num

lemma prod_eps {d M : ℕ} (β : Fin d → Fin M) (T : Finset (Fin M)) :
    ∏ r ∈ T, (-1 : ℝ) ^ cnt β r = ∏ j, (if β j ∈ T then (-1 : ℝ) else 1) := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := β) (t := T)]
  · apply Finset.sum_congr rfl; intro b hb
    unfold cnt; congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hb, h⟩
    · intro h; exact h.2
  · intro j hj; simpa using hj

lemma Ngood_eq (d M : ℕ) (q : Fin M → Bool) :
    (Ngood d M q : ℝ) = ∑ T : Finset (Fin M), (1/2 : ℝ) ^ M * (∏ r ∈ T, sg (q r)) *
      ((M : ℝ) - 2 * T.card) ^ d := by
  have h1 : (Ngood d M q : ℝ) = ∑ β : Fin d → Fin M, ∏ r, (if (cnt β r).bodd = q r then (1:ℝ) else 0) := by
    unfold Ngood
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl; intro β _
    by_cases h : ∀ r, (cnt β r).bodd = q r
    · rw [if_pos h]; symm; apply Finset.prod_eq_one; intro r _; rw [if_pos (h r)]
    · rw [if_neg h]; push Not at h; obtain ⟨r, hr⟩ := h
      symm; exact Finset.prod_eq_zero (Finset.mem_univ r) (if_neg hr)
  rw [h1]
  simp only [ind_eq]
  have h2 : ∀ β : Fin d → Fin M, ∏ r, (1 / 2 + sg (q r) * (-1 : ℝ) ^ cnt β r / 2) =
      ∑ T : Finset (Fin M), (1/2 : ℝ) ^ M * (∏ r ∈ T, sg (q r)) * ∏ r ∈ T, (-1 : ℝ) ^ cnt β r := by
    intro β
    rw [show (∏ r, (1 / 2 + sg (q r) * (-1 : ℝ) ^ cnt β r / 2)) =
        ∏ r, ((fun r => sg (q r) * (-1 : ℝ) ^ cnt β r / 2) r + (fun _ => (1/2 : ℝ)) r) from
        Finset.prod_congr rfl (fun r _ => by ring), Fintype.prod_add]
    · apply Finset.sum_congr rfl; intro T _
      rw [Finset.prod_const, Finset.card_compl, Fintype.card_fin]
      have : ∏ r ∈ T, (sg (q r) * (-1 : ℝ) ^ cnt β r / 2) =
          (1/2 : ℝ) ^ T.card * ((∏ r ∈ T, sg (q r)) * ∏ r ∈ T, (-1 : ℝ) ^ cnt β r) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_const, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl; intro r _; ring
      rw [this]
      have hc : T.card ≤ M := by simpa using Finset.card_le_univ T
      rw [show (1/2 : ℝ) ^ M = (1/2) ^ T.card * (1/2) ^ (M - T.card) by
        rw [← pow_add, Nat.add_sub_cancel' hc]]
      ring
  simp only [h2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro T _
  rw [← Finset.mul_sum]
  congr 1
  simp only [prod_eps]
  rw [← Fintype.sum_pow (fun r => if r ∈ T then (-1 : ℝ) else 1)]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  have : (Finset.univ.filter (fun r : Fin M => r ∉ T)).card = M - T.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff_of_subset
      (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin]
  rw [this]
  have hc : T.card ≤ M := by simpa using Finset.card_le_univ T
  rw [Nat.cast_sub hc]; ring

lemma Gq_exp (q : Bool) (x : ℝ) : Gq q x = (Real.exp x + sg q * Real.exp (-x)) / 2 := by
  cases q <;> simp [Gq, sg, Real.cosh_eq, Real.sinh_eq] <;> ring

theorem gf (M : ℕ) (q : Fin M → Bool) (x : ℝ) :
    HasSum (fun d : ℕ => x ^ d / (d ! : ℝ) * (Ngood d M q : ℝ)) (∏ r, Gq (q r) x) := by
  simp only [Ngood_eq, Finset.mul_sum]
  have hT : ∀ T : Finset (Fin M), HasSum (fun d : ℕ => x ^ d / (d ! : ℝ) *
      ((1/2 : ℝ) ^ M * (∏ r ∈ T, sg (q r)) * ((M : ℝ) - 2 * T.card) ^ d))
      ((1/2 : ℝ) ^ M * (∏ r ∈ T, sg (q r)) * Real.exp (x * ((M : ℝ) - 2 * T.card))) := by
    intro T
    have := (NormedSpace.expSeries_div_hasSum_exp (x * ((M : ℝ) - 2 * T.card))).mul_left
      ((1/2 : ℝ) ^ M * (∏ r ∈ T, sg (q r)))
    rw [← Real.exp_eq_exp_ℝ] at this
    have e : (fun d : ℕ => x ^ d / (d ! : ℝ) *
        ((1/2 : ℝ) ^ M * (∏ r ∈ T, sg (q r)) * ((M : ℝ) - 2 * T.card) ^ d)) =
        (fun i : ℕ => ((1/2 : ℝ) ^ M * ∏ r ∈ T, sg (q r)) *
          ((x * ((M : ℝ) - 2 * T.card)) ^ i / (i ! : ℝ))) := by
      funext d; rw [mul_pow]; ring
    rw [e]; exact this
  convert hasSum_sum (fun T _ => hT T) using 1
  simp only [Gq_exp]
  rw [show (∏ r, (Real.exp x + sg (q r) * Real.exp (-x)) / 2) =
      ∏ r, ((fun r => sg (q r) * Real.exp (-x) / 2) r + (fun _ => Real.exp x / 2) r) from
      Finset.prod_congr rfl (fun r _ => by ring), Fintype.prod_add]
  · apply Finset.sum_congr rfl; intro T _
    rw [Finset.prod_const, Finset.card_compl, Fintype.card_fin]
    have hc : T.card ≤ M := by simpa using Finset.card_le_univ T
    have : ∏ r ∈ T, (sg (q r) * Real.exp (-x) / 2) =
        (∏ r ∈ T, sg (q r)) * (Real.exp (-x) / 2) ^ T.card := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro r _; ring
    rw [this, div_pow, div_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have e : Real.exp (x * ((M : ℝ) - 2 * T.card)) =
        Real.exp (↑T.card * -x) * Real.exp (↑(M - T.card) * x) := by
      rw [← Real.exp_add]; congr 1; rw [Nat.cast_sub hc]; ring
    rw [e, show (1/2 : ℝ) ^ M = (1/2) ^ T.card * (1/2) ^ (M - T.card) by
        rw [← pow_add, Nat.add_sub_cancel' hc]]
    field_simp
    rw [one_div_pow, one_div_pow]
    field_simp

open TFIMPhaseDiagram.Classical

instance u01_prob : IsProbabilityMeasure TFIMPhaseDiagram.Classical.uniform01 :=
  ⟨by simp [TFIMPhaseDiagram.Classical.uniform01]⟩

def binOf (M : ℕ) (hM : 0 < M) (x : ℝ) : Fin M := ⟨min (⌈x * M⌉₊ - 1) (M - 1), by omega⟩

def box {ι : Type} (M : ℕ) (β : ι → Fin M) : Set (ι → ℝ) :=
  Set.univ.pi (fun j => Set.Ioc ((β j : ℝ) / M) (((β j : ℝ) + 1) / M))

lemma mem_bin (M : ℕ) (hM : 0 < M) (x : ℝ) (b : Fin M) :
    x ∈ Set.Ioc ((b : ℝ) / M) (((b : ℝ) + 1) / M) ↔ (0 < x ∧ x ≤ 1) ∧ binOf M hM x = b := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := b.isLt
  have hbM : (b : ℝ) + 1 ≤ M := by exact_mod_cast hb
  simp only [Set.mem_Ioc]
  rw [div_lt_iff₀ hMr, le_div_iff₀ hMr]
  constructor
  · rintro ⟨h1, h2⟩
    have hc : ⌈x * M⌉₊ = b.val + 1 := by
      rw [Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel]; push_cast
      constructor <;> linarith
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : (0:ℝ) ≤ b := by positivity
      nlinarith
    · nlinarith
    · ext; simp only [binOf, hc]; omega
  · rintro ⟨⟨h0, h1⟩, hb'⟩
    have hpos : 0 < ⌈x * M⌉₊ := Nat.ceil_pos.2 (by positivity)
    have hle : ⌈x * M⌉₊ ≤ M := Nat.ceil_le.2 (by nlinarith)
    have hval : ⌈x * M⌉₊ - 1 = b.val := by
      have := congrArg Fin.val hb'; simp only [binOf] at this; omega
    have hc : ⌈x * M⌉₊ = b.val + 1 := by omega
    rw [Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel] at hc
    push_cast at hc
    exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

lemma u01_Ioc (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    TFIMPhaseDiagram.Classical.uniform01 (Set.Ioc a b) = ENNReal.ofReal (b - a) := by
  rw [TFIMPhaseDiagram.Classical.uniform01, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (fun x hx => Set.mem_Icc.2 ⟨by linarith [hx.1], le_trans hx.2 hb⟩),
    Real.volume_Ioc]

lemma box_measure {ι : Type} [Fintype ι] (M : ℕ) (hM : 0 < M) (β : ι → Fin M) :
    (Measure.pi (fun _ : ι => TFIMPhaseDiagram.Classical.uniform01)) (box M β) =
      ENNReal.ofReal (1 / M) ^ Fintype.card ι := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [box, Measure.pi_pi, ← Finset.card_univ, ← Finset.prod_const]
  apply Finset.prod_congr rfl; intro j _
  have hb : ((β j : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast (β j).isLt
  rw [u01_Ioc _ _ (by positivity) (by gcongr; linarith) (by rw [div_le_one hMr]; exact hb)]
  congr 1; field_simp; ring

lemma pattern {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : 0 < M)
    (G : (ι → Fin M) → Prop) [DecidablePred G] (E : Set (ι → ℝ))
    (hE : ∀ u : ι → ℝ, (∀ j, 0 < u j ∧ u j ≤ 1) → (u ∈ E ↔ G (fun j => binOf M hM (u j)))) :
    (Measure.pi (fun _ : ι => TFIMPhaseDiagram.Classical.uniform01)) E =
      ((Finset.univ.filter G).card : ENNReal) * ENNReal.ofReal (1 / M) ^ Fintype.card ι := by
  set μ := Measure.pi (fun _ : ι => TFIMPhaseDiagram.Classical.uniform01)
  set Good0 : Set (ι → ℝ) := Set.univ.pi (fun _ => Set.Ioc (0:ℝ) 1)
  have hG0 : μ Good0ᶜ = 0 := by
    have hm : MeasurableSet Good0 := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
    rw [prob_compl_eq_zero_iff hm, Measure.pi_pi]
    apply Finset.prod_eq_one; intro j _
    rw [u01_Ioc 0 1 le_rfl zero_le_one le_rfl]; simp
  set U := ⋃ β ∈ Finset.univ.filter G, box M β
  have hboxmem : ∀ (β : ι → Fin M) (u : ι → ℝ), u ∈ box M β ↔ (∀ j, 0 < u j ∧ u j ≤ 1) ∧ (fun j => binOf M hM (u j)) = β := by
    intro β u
    simp only [box, Set.mem_pi, Set.mem_univ, true_implies, mem_bin M hM]
    constructor
    · intro h; exact ⟨fun j => (h j).1, funext fun j => (h j).2⟩
    · rintro ⟨h1, h2⟩ j; exact ⟨h1 j, congrFun h2 j⟩
  have hUE : U ⊆ E := by
    intro u hu
    simp only [U, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨β, hβ, hu⟩ := hu
    rw [hboxmem] at hu
    rw [hE u hu.1, hu.2]; exact hβ
  have hEU : E ⊆ U ∪ Good0ᶜ := by
    intro u hu
    by_cases hg : ∀ j, 0 < u j ∧ u j ≤ 1
    · left
      simp only [U, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨_, (hE u hg).1 hu, (hboxmem _ u).2 ⟨hg, rfl⟩⟩
    · right
      simp only [Good0, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc]
      exact hg
  have hμU : μ U = ((Finset.univ.filter G).card : ENNReal) * ENNReal.ofReal (1 / M) ^ Fintype.card ι := by
    rw [measure_biUnion_finset]
    · rw [Finset.sum_congr rfl (fun β _ => box_measure M hM β), Finset.sum_const, nsmul_eq_mul]
    · intro β _ β' _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro u h1 h2
      rw [hboxmem] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    · intro β _; exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  apply le_antisymm
  · calc μ E ≤ μ (U ∪ Good0ᶜ) := measure_mono hEU
      _ ≤ μ U + μ Good0ᶜ := measure_union_le _ _
      _ = _ := by rw [hG0, add_zero, hμU]
  · rw [← hμU]; exact measure_mono hUE


def cntι {ι : Type} [Fintype ι] {M : ℕ} (β : ι → Fin M) (r : Fin M) : ℕ :=
  (Finset.univ.filter (fun j => β j = r)).card
def ltc {ι : Type} [Fintype ι] {M : ℕ} (β : ι → Fin M) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => (β j).val < k)).card

lemma ltc_succ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} (β : ι → Fin M) (k : ℕ) (hk : k < M) :
    ltc β (k+1) = ltc β k + cntι β ⟨k, hk⟩ := by
  unfold ltc cntι
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Fin.ext_iff]; omega
  · rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff] at h1 h2; omega

lemma ltc_zero {ι : Type} [Fintype ι] {M : ℕ} (β : ι → Fin M) : ltc β 0 = 0 := by
  simp [ltc]

lemma ltc_M {ι : Type} [Fintype ι] {M : ℕ} (β : ι → Fin M) : ltc β M = Fintype.card ι := by
  unfold ltc; rw [Finset.filter_true_of_mem (fun j _ => (β j).isLt), Finset.card_univ]

def qv {M : ℕ} (hM : 0 < M) (s : Fin M → Bool) (p : Bool) : Fin M → Bool := fun r =>
  if h : r.val + 1 < M then xor (s r) (s ⟨r.val + 1, h⟩) else xor (xor (s r) (s ⟨0, hM⟩)) p

lemma pattern_iff {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} (hM : 0 < M) (s : Fin M → Bool) (p : Bool)
    (β : ι → Fin M) (hcard : (Fintype.card ι).bodd = p) :
    (∀ k : Fin M, xor (s ⟨0, hM⟩) (ltc β k.val).bodd = s k) ↔ ∀ r, (cntι β r).bodd = qv hM s p r := by
  constructor
  · intro h r
    unfold qv
    by_cases hr : r.val + 1 < M
    · rw [dif_pos hr]
      have h1 := h r
      have h2 := h ⟨r.val + 1, hr⟩
      simp only at h2
      rw [ltc_succ β r.val r.isLt, Nat.bodd_add] at h2
      have : (⟨r.val, r.isLt⟩ : Fin M) = r := rfl
      rw [this] at h2
      revert h1 h2
      cases s ⟨0, hM⟩ <;> cases (ltc β r.val).bodd <;> cases (cntι β r).bodd <;>
        cases s r <;> cases s ⟨r.val + 1, hr⟩ <;> simp
    · rw [dif_neg hr]
      have hrM : r.val + 1 = M := by have := r.isLt; omega
      have h1 := h r
      have hM' : ltc β (r.val + 1) = Fintype.card ι := (congrArg (ltc β) hrM).trans (ltc_M β)
      rw [ltc_succ β r.val r.isLt] at hM'
      have : (⟨r.val, r.isLt⟩ : Fin M) = r := rfl
      rw [this] at hM'
      have h3 : xor (ltc β r.val).bodd (cntι β r).bodd = p := by
        rw [← Nat.bodd_add, hM', hcard]
      revert h1 h3
      cases s ⟨0, hM⟩ <;> cases (ltc β r.val).bodd <;> cases (cntι β r).bodd <;>
        cases s r <;> cases p <;> simp
  · intro h
    have key : ∀ k (hk : k < M), xor (s ⟨0, hM⟩) (ltc β k).bodd = s ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro hk; rw [ltc_zero]; simp
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        rw [ltc_succ β k (by omega), Nat.bodd_add]
        have hq := h ⟨k, by omega⟩
        unfold qv at hq
        rw [dif_pos hk] at hq
        rw [hq]
        revert ih'
        cases s ⟨0, hM⟩ <;> cases (ltc β k).bodd <;> cases s ⟨k, by omega⟩ <;>
          cases s ⟨k + 1, hk⟩ <;> simp
    intro k; exact key k.val k.isLt

lemma pattern_false {ι : Type} [Fintype ι] {M : ℕ} (hM : 0 < M) (s : Fin M → Bool) (b : Bool)
    (hb : b ≠ s ⟨0, hM⟩) (β : ι → Fin M) :
    ¬ ∀ k : Fin M, xor b (ltc β k.val).bodd = s k := by
  intro h; have := h ⟨0, hM⟩; rw [ltc_zero] at this; simp at this; exact hb this

lemma cnt_transport {ι : Type} [Fintype ι] {M : ℕ} (e : ι ≃ Fin (Fintype.card ι))
    (β : ι → Fin M) (r : Fin M) : cnt (β ∘ e.symm) r = cntι β r := by
  unfold cnt cntι
  apply Finset.card_equiv e.symm; intro j; simp

lemma Ngood_transport {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} (q : Fin M → Bool) :
    (Finset.univ.filter (fun β : ι → Fin M => ∀ r, (cntι β r).bodd = q r)).card =
      Ngood (Fintype.card ι) M q := by
  set e := Fintype.equivFin ι
  unfold Ngood
  apply Finset.card_equiv (Equiv.arrowCongr e (Equiv.refl _))
  intro β
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have : (e.arrowCongr (Equiv.refl (Fin M))) β = β ∘ e.symm := by
    funext j; simp [Equiv.arrowCongr_apply]
  rw [this]
  simp only [cnt_transport]


lemma meas_card {ι : Type} (s : Finset ι) (t : ℝ) :
    Measurable (fun u : ι → ℝ => (s.filter (fun j => u j ≤ t)).card) := by
  have : (fun u : ι → ℝ => (s.filter (fun j => u j ≤ t)).card) =
      fun u => ∑ j ∈ s, (if u j ≤ t then 1 else 0) := by
    funext u; rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ (fun j _ => Measurable.ite
    (measurableSet_le (measurable_pi_apply j) measurable_const) measurable_const measurable_const)

lemma spin_neg_iff (b : Bool) (c : ℕ) :
    (spin b * (-1 : ℝ) ^ c < 0) ↔ xor b c.bodd = true := by
  rw [neg_one_pow_bodd]; cases b <;> cases c.bodd <;> simp [spin]

lemma dec_spin (b : Bool) (c : ℕ) : decide (spin b * (-1 : ℝ) ^ c < 0) = xor b c.bodd := by
  rw [neg_one_pow_bodd]; cases b <;> cases c.bodd <;> simp [spin]

lemma pathValue_meas (t : ℝ) : Measurable (fun σ : PathData => pathValue σ t) := by
  apply measurable_from_prod_countable_right
  intro d
  unfold pathValue
  simp only
  apply Measurable.mul
  · exact (measurable_of_countable (fun b : Bool => spin b)).comp measurable_fst
  · exact (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n)).comp
      ((meas_card (Finset.range d) t).comp measurable_snd)

lemma discretize_meas (M : ℕ) : Measurable (discretize M) := by
  apply measurable_pi_lambda
  intro k
  apply measurable_to_bool
  have : (fun σ : PathData => discretize M σ k) ⁻¹' {true} = {σ | pathValue σ (k.val / (M:ℝ)) < 0} := by
    ext σ; simp [discretize, pathBits]
  rw [this]
  exact measurableSet_lt (pathValue_meas _) measurable_const


abbrev Uinf : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => TFIMPhaseDiagram.Classical.uniform01)

lemma pathLaw_apply (η : ℝ) (p : Bool) (A : Set PathData) (hA : MeasurableSet A) :
    pathLaw η p A = ∑' d, ENNReal.ofReal (parityMass η p d) *
      ∑ b : Bool, ENNReal.ofReal (1/2) * Uinf {U | (d, b, U) ∈ A} := by
  unfold pathLaw
  rw [Measure.prod_apply hA]
  unfold parityLaw
  rw [lintegral_sum_measure]
  congr 1; funext d
  rw [lintegral_smul_measure, lintegral_dirac]
  congr 1
  rw [Measure.prod_apply (measurable_prodMk_left hA)]
  unfold finiteLaw
  rw [lintegral_finset_sum_measure]
  apply Finset.sum_congr rfl; intro b _
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

lemma card_coe_filter (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (s.filter p).card = (Finset.univ.filter (fun j : ↥s => p j.val)).card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_coe_sort s]

lemma slice_prob (M : ℕ) (hM : 0 < M) (d : ℕ) (b : Bool) (s : Spins M) :
    Uinf {U | discretize M (d, b, U) = s} =
      ((Finset.univ.filter (fun β : ↥(Finset.range d) → Fin M =>
        ∀ k : Fin M, xor b (ltc β k.val).bodd = s k)).card : ENNReal) *
        ENNReal.ofReal (1 / M) ^ d := by
  set E' : Set (↥(Finset.range d) → ℝ) := {u | ∀ k : Fin M,
    xor b ((Finset.univ.filter (fun j => u j ≤ (k.val : ℝ) / M)).card).bodd = s k}
  have hset : {U | discretize M (d, b, U) = s} = MeasureTheory.cylinder (Finset.range d) E' := by
    ext U
    simp only [Set.mem_setOf_eq, MeasureTheory.mem_cylinder, E', funext_iff, discretize, pathBits,
      pathValue]
    apply forall_congr'; intro k
    rw [card_coe_filter (Finset.range d) (fun j => U j ≤ (k.val : ℝ) / M), dec_spin]
    simp only [Finset.restrict]
    exact Iff.rfl
  have hE'm : MeasurableSet E' := by
    have : E' = ⋂ k : Fin M, (fun u : ↥(Finset.range d) → ℝ =>
        (Finset.univ.filter (fun j => u j ≤ (k.val : ℝ) / M)).card) ⁻¹'
          {n | xor b n.bodd = s k} := by
      ext u; simp [E']
    rw [this]
    exact MeasurableSet.iInter (fun k => (meas_card _ _) (MeasurableSet.of_discrete))
  rw [hset, Measure.infinitePi_cylinder _ hE'm]
  have hcard : Fintype.card ↥(Finset.range d) = d := by simp
  rw [show ENNReal.ofReal (1 / M) ^ d = ENNReal.ofReal (1 / M) ^ Fintype.card ↥(Finset.range d) by
    rw [hcard]]
  apply pattern M hM
  intro u hu
  simp only [E', Set.mem_setOf_eq]
  apply forall_congr'; intro k
  have : (Finset.univ.filter (fun j => u j ≤ (k.val : ℝ) / M)).card =
      ltc (fun j => binOf M hM (u j)) k.val := by
    unfold ltc
    congr 1
    apply Finset.filter_congr; intro j _
    have hb := (mem_bin M hM (u j) (binOf M hM (u j))).2 ⟨hu j, rfl⟩
    have hMr : (0:ℝ) < M := by exact_mod_cast hM
    simp only [Set.mem_Ioc] at hb
    constructor
    · intro h
      by_contra hc; push Not at hc
      have : ((k.val : ℕ) : ℝ) ≤ ((binOf M hM (u j)).val : ℝ) := by exact_mod_cast hc
      have : (k.val : ℝ) / M ≤ ((binOf M hM (u j)).val : ℝ) / M := by gcongr
      linarith [hb.1]
    · intro h
      have : ((binOf M hM (u j)).val : ℝ) + 1 ≤ (k.val : ℝ) := by exact_mod_cast h
      have : (((binOf M hM (u j)).val : ℝ) + 1) / M ≤ (k.val : ℝ) / M := by gcongr
      linarith [hb.2]
  rw [this]


lemma mass_parity (η : ℝ) (p : Bool) (d : ℕ) (h : parityMass η p d ≠ 0) : d.bodd = p := by
  unfold parityMass at h
  by_contra hc
  by_cases h0 : η = 0
  · rw [if_pos h0, if_neg] at h
    · exact h rfl
    · intro hd; apply hc; rw [hd]; cases p <;> rfl
  · rw [if_neg h0, if_neg] at h
    · exact h rfl
    · intro hd; apply hc; have := Nat.mod_two_of_bodd d
      cases p <;> cases hb : d.bodd <;> simp_all

lemma mass_nonneg (η : ℝ) (hη : 0 ≤ η) (p : Bool) (d : ℕ) : 0 ≤ parityMass η p d := by
  unfold parityMass
  split_ifs <;> try positivity

lemma mass_hasSum (η : ℝ) (hη : 0 ≤ η) (p : Bool) : HasSum (fun d => parityMass η p d) 1 := by
  by_cases h0 : η = 0
  · subst h0
    have : (fun d => parityMass 0 p d) = fun d => if d = (if p then 1 else 0) then 1 else 0 := by
      funext d; simp [parityMass]
    rw [this]
    convert hasSum_ite_eq (if p then 1 else 0) (1:ℝ)
  have hpos : 0 < η := lt_of_le_of_ne hη (Ne.symm h0)
  cases p
  · have hc := (Real.hasSum_cosh η).div_const (Real.cosh η)
    rw [div_self (Real.cosh_pos η).ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η false d) ∘ (fun n : ℕ => 2 * n) =
          fun i => η ^ (2 * i) / ↑(2 * i)! / Real.cosh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, Bool.false_eq_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, Bool.false_eq_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) = x; omega⟩
  · have hs : 0 < Real.sinh η := Real.sinh_pos_iff.2 hpos
    have hc := (Real.hasSum_sinh η).div_const (Real.sinh η)
    rw [div_self hs.ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n + 1) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η true d) ∘ (fun n : ℕ => 2 * n + 1) =
          fun i => η ^ (2 * i + 1) / ↑(2 * i + 1)! / Real.sinh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, if_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, if_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) + 1 = x; omega⟩

lemma parityLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (parityLaw η p) := by
  constructor
  unfold parityLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (mass_nonneg η hη p) (mass_hasSum η hη p).summable,
    (mass_hasSum η hη p).tsum_eq, ENNReal.ofReal_one]

instance bern_prob : IsProbabilityMeasure (finiteLaw (fun _ : Bool => (1/2 : ℝ))) := by
  constructor
  unfold finiteLaw
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]; norm_num

lemma pathLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (pathLaw η p) := by
  haveI := parityLaw_prob η hη p
  unfold pathLaw; infer_instance


lemma pattern_back {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} (hM : 0 < M) (s : Fin M → Bool)
    (p : Bool) (β : ι → Fin M) (h : ∀ r, (cntι β r).bodd = qv hM s p r) :
    ∀ k (hk : k < M), xor (s ⟨0, hM⟩) (ltc β k).bodd = s ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero => intro hk; rw [ltc_zero]; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [ltc_succ β k (by omega), Nat.bodd_add]
    have hq := h ⟨k, by omega⟩
    unfold qv at hq
    rw [dif_pos hk] at hq
    rw [hq]
    revert ih'
    cases s ⟨0, hM⟩ <;> cases (ltc β k).bodd <;> cases s ⟨k, by omega⟩ <;>
      cases s ⟨k + 1, hk⟩ <;> simp

lemma Ngood_parity {M : ℕ} (hM : 0 < M) (s : Fin M → Bool) (p : Bool) (d : ℕ)
    (h : Ngood d M (qv hM s p) ≠ 0) : d.bodd = p := by
  unfold Ngood at h
  obtain ⟨β, hβ⟩ := Finset.card_ne_zero.1 h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
  have hb := pattern_back hM s p β hβ (M - 1) (by omega)
  have hlt : ltc β M = d := by rw [ltc_M]; simp
  have e : ltc β M = ltc β (M - 1 + 1) := by congr 1; omega
  rw [e, ltc_succ β (M - 1) (by omega)] at hlt
  have hlt2 := congrArg Nat.bodd hlt
  rw [Nat.bodd_add] at hlt2
  have hq := hβ ⟨M - 1, by omega⟩
  unfold qv at hq
  rw [dif_neg (by simp; omega)] at hq
  change (cntι β ⟨M - 1, _⟩).bodd = _ at hq
  rw [← hlt2, hq]
  revert hb
  cases s ⟨0, hM⟩ <;> cases (ltc β (M - 1)).bodd <;> cases s ⟨M - 1, by omega⟩ <;> cases p <;> simp

lemma pre_prob {M : ℕ} (hM : 0 < M) (η : ℝ) (p : Bool) (s : Spins M) :
    pathLaw η p (discretize M ⁻¹' {s}) = ∑' d, ENNReal.ofReal (parityMass η p d) *
      (ENNReal.ofReal (1/2) * ((Ngood d M (qv hM s p) : ENNReal) * ENNReal.ofReal (1 / M) ^ d)) := by
  rw [pathLaw_apply η p _ (discretize_meas M (measurableSet_singleton s))]
  congr 1; funext d
  by_cases hm : parityMass η p d = 0
  · simp [hm]
  have hp := mass_parity η p d hm
  congr 1
  have hcard : Fintype.card ↥(Finset.range d) = d := by simp
  have hslice : ∀ b : Bool, Uinf {U | (d, b, U) ∈ discretize M ⁻¹' {s}} =
      if b = s ⟨0, hM⟩ then (Ngood d M (qv hM s p) : ENNReal) * ENNReal.ofReal (1 / M) ^ d else 0 := by
    intro b
    have : {U | (d, b, U) ∈ discretize M ⁻¹' {s}} = {U | discretize M (d, b, U) = s} := rfl
    rw [this, slice_prob M hM d b s]
    split_ifs with hb
    · subst hb
      congr 2
      rw [show Ngood d M (qv hM s p) = Ngood (Fintype.card ↥(Finset.range d)) M (qv hM s p) by
        rw [hcard], ← Ngood_transport]
      apply congrArg
      apply Finset.filter_congr; intro β _
      exact pattern_iff hM s p β (by rw [hcard]; exact hp)
    · rw [Finset.filter_false_of_mem (fun β _ => pattern_false hM s b hb β)]
      simp
  rw [Fintype.sum_bool, hslice, hslice]
  cases h0 : s ⟨0, hM⟩ <;> simp


lemma prob_pos {M : ℕ} (hM : 0 < M) (η : ℝ) (hη : 0 < η) (p : Bool) (s : Spins M) :
    pathLaw η p (discretize M ⁻¹' {s}) = ENNReal.ofReal
      ((∏ r, Gq (qv hM s p r) (η / M)) / (2 * (if p then Real.sinh η else Real.cosh η))) := by
  rw [pre_prob hM η p s]
  set Z := if p then Real.sinh η else Real.cosh η
  have hZ : 0 < Z := by
    simp only [Z]; split_ifs
    · exact Real.sinh_pos_iff.2 hη
    · exact Real.cosh_pos η
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  set a : ℕ → ℝ := fun d => parityMass η p d * (1/2 * (Ngood d M (qv hM s p) * (1 / M) ^ d))
  have hterm : ∀ d, ENNReal.ofReal (parityMass η p d) * (ENNReal.ofReal (1/2) *
      ((Ngood d M (qv hM s p) : ENNReal) * ENNReal.ofReal (1 / M) ^ d)) = ENNReal.ofReal (a d) := by
    intro d
    simp only [a]
    rw [ENNReal.ofReal_mul (mass_nonneg η hη.le p d), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  simp only [hterm]
  have ha : ∀ d, a d = 1 / (2 * Z) * ((η / M) ^ d / (d.factorial : ℝ) * Ngood d M (qv hM s p)) := by
    intro d
    simp only [a]
    by_cases hN : Ngood d M (qv hM s p) = 0
    · simp [hN]
    have hp := Ngood_parity hM s p d hN
    have hmass : parityMass η p d = η ^ d / ((d.factorial : ℝ) * Z) := by
      unfold parityMass
      rw [if_neg hη.ne', if_pos]
      rw [Nat.mod_two_of_bodd, hp]; cases p <;> rfl
    rw [hmass, div_pow, one_pow, div_pow η]
    field_simp
  have hsum : HasSum a ((∏ r, Gq (qv hM s p r) (η / M)) / (2 * Z)) := by
    have := (gf M (qv hM s p) (η / M)).mul_left (1 / (2 * Z))
    rw [show a = fun d => 1 / (2 * Z) * ((η / M) ^ d / (d.factorial : ℝ) *
        Ngood d M (qv hM s p)) from funext ha]
    rw [show (∏ r, Gq (qv hM s p r) (η / M)) / (2 * Z) = 1 / (2 * Z) * ∏ r, Gq (qv hM s p r) (η / M)
      by ring]
    exact this
  have hnn : ∀ d, 0 ≤ a d := fun d => by
    simp only [a]; exact mul_nonneg (mass_nonneg η hη.le p d) (by positivity)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]

lemma prob_zero {M : ℕ} (hM : 0 < M) (p : Bool) (s : Spins M) :
    pathLaw 0 p (discretize M ⁻¹' {s}) = ENNReal.ofReal
      (1/2 * (Ngood (if p then 1 else 0) M (qv hM s p) * (1 / M) ^ (if p then 1 else 0))) := by
  rw [pre_prob hM 0 p s, tsum_eq_single (if p then 1 else 0)]
  · have hm : parityMass 0 p (if p then 1 else 0) = 1 := by simp [parityMass]
    rw [hm, ENNReal.ofReal_one, one_mul, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  · intro d hd
    have : parityMass 0 p d = 0 := by simp [parityMass, hd]
    simp [this]


lemma spin_mul (a b : Bool) : spin a * spin b = if xor a b then -1 else 1 := by
  cases a <;> cases b <;> simp [spin]

lemma exp_half_log (y : ℝ) (hy : 0 < y) : Real.exp ((1/2) * Real.log y) = Real.sqrt y := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]
  rw [show 1 / 2 * Real.log y + 1 / 2 * Real.log y = Real.log y by ring, Real.exp_log hy]

lemma Gq_factor {M : ℕ} (hM : 0 < M) (η : ℝ) (hη : 0 < η) (p : Bool) (s : Spins M) (r : Fin M) :
    Gq (qv hM s p r) (η / M) = Real.sqrt (Real.cosh (η / M) * Real.sinh (η / M)) *
      Real.exp (signedCoupling η p r * spin (s r) * spin (s (next r))) := by
  have hx : 0 < η / M := by have : (0:ℝ) < M := by exact_mod_cast hM
                            positivity
  set c := Real.cosh (η / M); set sn := Real.sinh (η / M)
  have hc : 0 < c := Real.cosh_pos _
  have hs : 0 < sn := Real.sinh_pos_iff.2 hx
  have hK : Real.exp (coupling M η) = Real.sqrt (c / sn) := by
    unfold coupling; exact exp_half_log _ (div_pos hc hs)
  have hKn : Real.exp (-coupling M η) = Real.sqrt (sn / c) := by
    rw [Real.exp_neg, hK, ← Real.sqrt_inv, inv_div]
  have e1 : Real.sqrt (c * sn) * Real.sqrt (c / sn) = c := by
    rw [← Real.sqrt_mul (by positivity), show c * sn * (c / sn) = c ^ 2 by field_simp,
      Real.sqrt_sq hc.le]
  have e2 : Real.sqrt (c * sn) * Real.sqrt (sn / c) = sn := by
    rw [← Real.sqrt_mul (by positivity), show c * sn * (sn / c) = sn ^ 2 by field_simp,
      Real.sqrt_sq hs.le]
  rw [mul_assoc, spin_mul]
  unfold qv signedCoupling
  by_cases hr : r.val + 1 < M
  · have hn : next r = ⟨r.val + 1, hr⟩ := by ext; simp [next, Nat.mod_eq_of_lt hr]
    rw [dif_pos hr, hn, if_neg (by omega)]
    cases xor (s r) (s ⟨r.val + 1, hr⟩) <;> simp [Gq, hK, hKn, e1, e2, c, sn]
  · have hrM : r.val + 1 = M := by have := r.isLt; omega
    have hn : next r = ⟨0, hM⟩ := by ext; simp [next, hrM]
    rw [dif_neg hr, hn]
    cases p <;> simp only [hrM, true_and, Bool.false_eq_true, and_false, if_false, if_true] <;>
      cases xor (s r) (s ⟨0, hM⟩) <;> simp [Gq, hK, hKn, e1, e2, c, sn]

lemma norm_lemma {A : Type} [Fintype A] (f w : A → ℝ) (C : ℝ) (hf : ∀ x, f x = C * w x)
    (hsum : ∑ x, f x = 1) (x : A) : f x = normalize w x := by
  unfold normalize
  have h1 : C * ∑ y, w y = 1 := by rw [Finset.mul_sum, ← hsum]; simp [hf]
  have hW : ∑ y, w y ≠ 0 := by intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  rw [hf, eq_div_iff hW, mul_comm C, mul_assoc, h1, mul_one]

lemma N0_eq {M : ℕ} (hM : 0 < M) (s : Spins M) :
    (Ngood 0 M (qv hM s false) : ℝ) = ∑ u : Bool, if s = (fun _ => u) then (1:ℝ) else 0 := by
  have h := Ngood_transport (ι := Fin 0) (M := M) (qv hM s false)
  simp only [Fintype.card_fin] at h
  rw [← h]
  have hfilt : Finset.univ.filter (fun β : Fin 0 → Fin M => ∀ r, (cntι β r).bodd = qv hM s false r) =
      Finset.univ.filter (fun β : Fin 0 → Fin M => ∀ k : Fin M, xor (s ⟨0, hM⟩) (ltc β k.val).bodd = s k) :=
    Finset.filter_congr (fun β _ => (pattern_iff hM s false β (by simp)).symm)
  rw [hfilt]
  have hl : ∀ (β : Fin 0 → Fin M) k, ltc β k = 0 := fun β k => by simp [ltc]
  simp only [hl, Nat.bodd_zero, Bool.xor_false]
  have hconst : (∀ k : Fin M, s ⟨0, hM⟩ = s k) ↔ s = fun _ => s ⟨0, hM⟩ := by
    constructor
    · intro h; funext k; exact (h k).symm
    · intro h k; rw [h]
  by_cases hs : ∀ k : Fin M, s ⟨0, hM⟩ = s k
  · rw [Finset.filter_true_of_mem (fun β _ => hs)]
    simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_fin, Finset.prod_empty]
    rw [Fintype.sum_bool]
    have hs' := hconst.1 hs
    cases h0 : s ⟨0, hM⟩ <;> rw [h0] at hs' <;> subst hs' <;> simp <;>
      (intro h; exact absurd (congrFun h ⟨0, hM⟩) (by simp))
  · rw [Finset.filter_false_of_mem (fun β _ => hs)]
    simp only [Finset.card_empty, Nat.cast_zero]
    rw [Fintype.sum_bool]
    have h1 : s ≠ fun _ => true := by
      intro h; apply hs; intro k; rw [h]
    have h2 : s ≠ fun _ => false := by
      intro h; apply hs; intro k; rw [h]
    simp [h1, h2]

lemma N1_eq {M : ℕ} (hM : 0 < M) (s : Spins M) :
    (Ngood 1 M (qv hM s true) : ℝ) =
      ∑ u : Bool, ∑ r : Fin M, if s = oneJump u r then (1:ℝ) else 0 := by
  have h := Ngood_transport (ι := Fin 1) (M := M) (qv hM s true)
  simp only [Fintype.card_fin] at h
  rw [← h]
  have hfilt : Finset.univ.filter (fun β : Fin 1 → Fin M => ∀ r, (cntι β r).bodd = qv hM s true r) =
      Finset.univ.filter (fun β : Fin 1 → Fin M => ∀ k : Fin M, xor (s ⟨0, hM⟩) (ltc β k.val).bodd = s k) :=
    Finset.filter_congr (fun β _ => (pattern_iff hM s true β (by simp)).symm)
  rw [hfilt]
  have hl : ∀ (β : Fin 1 → Fin M) (k : ℕ), (ltc β k).bodd = decide ((β 0).val < k) := by
    intro β k
    unfold ltc
    by_cases hk : (β 0).val < k
    · rw [Finset.filter_true_of_mem (fun j _ => by rwa [Subsingleton.elim j 0])]; simp [hk]
    · rw [Finset.filter_false_of_mem (fun j _ => by rwa [Subsingleton.elim j 0])]; simp [hk]
  simp only [hl]
  -- reduce u
  have hu : ∀ r : Fin M, (if s = oneJump (!s ⟨0, hM⟩) r then (1:ℝ) else 0) = 0 := by
    intro r; rw [if_neg]; intro h
    have := congrFun h ⟨0, hM⟩; simp [oneJump] at this
  have hsum : ∑ u : Bool, ∑ r : Fin M, (if s = oneJump u r then (1:ℝ) else 0) =
      ∑ r : Fin M, (if s = oneJump (s ⟨0, hM⟩) r then (1:ℝ) else 0) := by
    rw [Fintype.sum_bool]
    cases h0 : s ⟨0, hM⟩
    · have := hu; rw [h0] at this; simp only [Bool.not_false] at this
      simp [this]
    · have := hu; rw [h0] at this; simp only [Bool.not_true] at this
      simp [this]
  rw [hsum, Finset.sum_boole, Nat.cast_inj]
  apply Finset.card_equiv (Equiv.funUnique (Fin 1) (Fin M))
  intro β
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.funUnique_apply]
  rw [show (default : Fin 1) = 0 from rfl, funext_iff]
  apply forall_congr'; intro k
  simp only [oneJump]
  by_cases hk : k.val < (β 0).val + 1
  · rw [if_pos hk, decide_eq_false (by omega), Bool.xor_false]; exact eq_comm
  · rw [if_neg hk, decide_eq_true (by omega), Bool.xor_true]; exact eq_comm


lemma finiteLaw_singleton {A : Type} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [DecidableEq A] (q : A → ℝ) (s : A) : finiteLaw q {s} = ENNReal.ofReal (q s) := by
  unfold finiteLaw
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton s),
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']; simp

lemma fieldEnergy_zero {M : ℕ} (s : Spins M) : fieldEnergy (fun _ : Fin M => Field.finite 0) s = 0 := by
  unfold fieldEnergy; simp

lemma compatible_zero {M : ℕ} (s : Spins M) : compatible (fun _ : Fin M => Field.finite 0) s := by
  intro k; trivial

theorem prop7 (M : ℕ) (hM3 : 3 ≤ M) (η : ℝ) (hη : 0 ≤ η) (p : Bool) :
    (pathLaw η p).map (discretize M) = pathCycleLaw (M := M) η p (fun _ => .finite 0) := by
  have hM : 0 < M := by omega
  haveI := pathLaw_prob η hη p
  set f : Spins M → ℝ := fun s => (pathLaw η p (discretize M ⁻¹' {s})).toReal
  have hfin : ∀ s, pathLaw η p (discretize M ⁻¹' {s}) = ENNReal.ofReal (f s) := fun s =>
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hsum : ∑ s, f s = 1 := by
    simp only [f]
    rw [← ENNReal.toReal_sum (fun s _ => measure_ne_top _ _),
      sum_measure_preimage_singleton Finset.univ (fun s _ => discretize_meas M (measurableSet_singleton s))]
    simp
  have hw : ∃ C, ∀ s, f s = C * pathCycleWeight η p (fun _ => .finite 0) s := by
    by_cases h0 : η = 0
    · subst h0
      refine ⟨1, fun s => ?_⟩
      simp only [f, prob_zero hM p s]
      unfold pathCycleWeight
      rw [if_pos rfl, if_pos (compatible_zero s), fieldEnergy_zero, Real.exp_zero, mul_one, one_mul]
      have hnn : 0 ≤ 1/2 * ((Ngood (if p then 1 else 0) M (qv hM s p) : ℝ) *
          (1 / (M:ℝ)) ^ (if p then 1 else 0)) := by positivity
      rw [ENNReal.toReal_ofReal hnn]
      unfold zeroCycleBase
      cases p
      · simp only [Bool.false_eq_true, if_false, pow_zero, mul_one]
        rw [N0_eq hM s]; ring
      · simp only [if_true, pow_one]
        rw [N1_eq hM s]; field_simp
    · have hpos : 0 < η := lt_of_le_of_ne hη (Ne.symm h0)
      set Z := if p then Real.sinh η else Real.cosh η
      refine ⟨Real.sqrt (Real.cosh (η / M) * Real.sinh (η / M)) ^ M / (2 * Z), fun s => ?_⟩
      have hZ : 0 < Z := by
        simp only [Z]; split_ifs
        · exact Real.sinh_pos_iff.2 hpos
        · exact Real.cosh_pos η
      simp only [f, prob_pos hM η hpos p s]
      rw [ENNReal.toReal_ofReal (by
        apply div_nonneg _ (by positivity)
        apply Finset.prod_nonneg; intro r _
        rw [Gq_factor hM η hpos p s r]; positivity)]
      unfold pathCycleWeight
      rw [if_neg h0]
      unfold cycleWeight cycleEnergy
      rw [if_pos (compatible_zero s), fieldEnergy_zero, add_zero]
      simp only [Gq_factor hM η hpos p s, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
      ring
  obtain ⟨C, hC⟩ := hw
  have hprob := norm_lemma f _ C hC hsum
  rw [Measure.ext_iff_singleton]
  intro s
  rw [Measure.map_apply (discretize_meas M) (measurableSet_singleton s), hfin, hprob s]
  unfold pathCycleLaw
  rw [finiteLaw_singleton]
  rfl

end TFIMPhaseDiagram.Classical.P7Aux

open TFIMPhaseDiagram.Classical in
theorem solution (M : ℕ) (hM : 3 ≤ M) (η : ℝ) (hη : 0 ≤ η) (p : Bool) :
  (pathLaw η p).map (discretize M) = pathCycleLaw (M := M) η p (fun _ => .finite 0) :=
  TFIMPhaseDiagram.Classical.P7Aux.prop7 M hM η hη p
