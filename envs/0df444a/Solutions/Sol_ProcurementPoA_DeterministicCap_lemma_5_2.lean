-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.lemma_5_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:39:01.97941+00:00
-- url     : https://prove2.me/submissions/4069f089-fb36-4f3f-a56b-baf3d83aa07c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula
import Theorems.Thm_ProcurementPoA_DeterministicCap_capped_margin_efficiency

section
set_option autoImplicit false

open Filter Topology

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

variable {n : ℕ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

variable {n : ℕ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31A
end

section
set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31B

variable {n : ℕ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31B
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31A
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31B
open ProcurementPoA.DeterministicCap

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31C

variable {n : ℕ}

lemma sel_one (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
    (h : ∀ j, j ≠ i → v i < v j) : τ.select v {i} = 1 := by
  have h1 := τ.lowest_only v
  have h2 : ∀ᵐ k ∂(τ.select v), k = i := by
    filter_upwards [h1] with k hk
    by_contra hki
    have := hk i
    exact absurd (h k hki) (not_lt.2 this)
  have h3 : ({i} : Set (Suppliers n)) =ᵐ[τ.select v] (univ : Set (Suppliers n)) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [h2] with k hk
    simp [hk]
  rw [measure_congr h3, measure_univ]

lemma sel_zero (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
    (h : ∃ j, v j < v i) : τ.select v {i} = 0 := by
  obtain ⟨j, hj⟩ := h
  have h1 := τ.lowest_only v
  have h2 : ∀ᵐ k ∂(τ.select v), k ≠ i := by
    filter_upwards [h1] with k hk hki
    subst hki
    exact absurd (hk j) (not_le.2 hj)
  exact measure_mono_null (fun k hk => not_not.2 (mem_singleton_iff.1 hk)) (ae_iff.1 h2)

lemma sum_select {n : ℕ} (τ : TieRule n) (b : Suppliers n → ℝ) : ∑ i, τ.select b {i} = 1 := by
  rw [sum_measure_singleton]; simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31C
end

section
/-!
# Lemma 5.2 from the capped-margin efficiency leaf

Paper App. A.1.1. (i) Almost surely, if some cost is below `T` then some bid is accepted
(a supplier with cost `c < T` facing a positive chance that all rivals bid above `T`
strictly prefers bidding `T`). (ii) On acceptance, selected suppliers have cost at most `T`
(no underbidding, lowest bidders selected), so outcome cost plus margin equals `T`.
(iii) Pointwise, outcome + margin ≤ gCap + (1 - ε)(T - C*)⁺; integrate and cancel.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProcurementPoA.DeterministicCap.Dev.L52
open ProcurementPoA.DeterministicCap

variable {n : ℕ}

lemma lowest_cont : Continuous (fun c : Suppliers n → ℝ => lowest c) :=
  Continuous.finset_inf'_apply _ (fun i _ => continuous_apply i)

lemma lowest_meas : Measurable (fun c : Suppliers n → ℝ => lowest c) := lowest_cont.measurable

lemma lowest_le (c : Suppliers n → ℝ) (i : Suppliers n) : lowest c ≤ c i :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma le_lowest {c : Suppliers n → ℝ} {a : ℝ} (h : ∀ i, a ≤ c i) : a ≤ lowest c :=
  Finset.le_inf' _ _ (fun i _ => h i)

lemma exists_lt_of_lowest_lt {c : Suppliers n → ℝ} {a : ℝ} (h : lowest c < a) :
    ∃ i, c i < a := by
  obtain ⟨i, -, hi⟩ := (Finset.inf'_lt_iff _).1 h
  exact ⟨i, hi⟩

lemma gCap_meas (R T : ℝ) : Measurable (gCap R T) := by
  unfold gCap
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

lemma proj_meas : Measurable (fun (x : Suppliers n → ℝ × ℝ) (i : Suppliers n) => (x i).1) :=
  measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))

lemma typeLaw_map (D : IndependentTypes n) (σ : MixedProfile n) :
    (playLaw D σ).map (fun (x : Suppliers n → ℝ × ℝ) i => (x i).1) = typeLaw D := by
  unfold playLaw typeLaw
  rw [Measure.pi_map_pi (f := fun _ => (Prod.fst : ℝ × ℝ → ℝ))
    (fun j => measurable_fst.aemeasurable)]
  congr 1
  ext1 j
  show (D.law j ⊗ₘ σ.bid j).fst = _
  exact Measure.fst_compProd _ _

instance playLaw_isProb (D : IndependentTypes n) (σ : MixedProfile n) :
    IsProbabilityMeasure (playLaw D σ) := by
  unfold playLaw; infer_instance

lemma box_measure' (ν : Suppliers n → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (i : Suppliers n) (A : Set ℝ) :
    Measure.pi ν (Set.pi univ (fun k => if k = i then univ else A))
      = ∏ j : Fin n, ν (i.succAbove j) A := by
  rw [Measure.pi_pi, Fin.prod_univ_succAbove _ i]
  simp [Fin.succAbove_ne]

lemma interimWin_ge (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (b : ℝ) :
    ∏ k : Fin n, marginalBidLaw D σ (i.succAbove k) (Ioi b) ≤ interimWin D τ σ i b := by
  unfold interimWin
  rw [← box_measure' (marginalBidLaw D σ) i (Ioi b)]
  have hmeas : MeasurableSet
      (Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ioi b)) :=
    MeasurableSet.univ_pi fun k => by by_cases hk : k = i <;> simp [hk, measurableSet_Ioi]
  rw [← lintegral_indicator_one hmeas]
  apply lintegral_mono
  intro bs
  by_cases hbs : bs ∈ Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ioi b)
  · rw [Set.indicator_of_mem hbs]
    simp only [Pi.one_apply]
    rw [Supplement.Dev.L31C.sel_one τ _ i]
    intro j hj
    have := hbs j (mem_univ j)
    simp only [hj, if_false, mem_Ioi] at this
    simp [Function.update_self, Function.update_of_ne hj, this]
  · rw [Set.indicator_of_notMem hbs]; exact zero_le

lemma interimWin_le_one (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (b : ℝ) : interimWin D τ σ i b ≤ 1 := by
  unfold interimWin
  calc _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(Measure.pi (marginalBidLaw D σ)) :=
        lintegral_mono fun _ => prob_le_one
    _ = 1 := by simp

/-- Almost surely every cost lies in `[1, R]` and no bid is below its cost. -/
lemma ae_facts (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n) (R T : ℝ)
    (hcost : InCostInterval D 1 R) (heq : IsBNE D τ σ T) :
    ∀ᵐ x ∂(playLaw D σ), ∀ i, (x i).1 ∈ Icc 1 R ∧ (x i).1 ≤ (x i).2 := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval (fun i => D.law i ⊗ₘ σ.bid i) i).quasiMeasurePreserving
  have h1 : ∀ᵐ y ∂(D.law i ⊗ₘ σ.bid i), y.1 ∈ Icc 1 R ∧ y.1 ≤ y.2 := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (measurable_fst measurableSet_Icc).inter
        (measurableSet_le measurable_fst measurable_snd)
    · have hc : D.types i ∈ ae (D.law i) := mem_ae_iff.2 (D.concentrated i)
      filter_upwards [hc] with c hc
      filter_upwards [heq.1 i c hc] with b hb
      exact ⟨hcost i hc, hb⟩
  exact hq.ae h1

/-- A type below `T` facing a positive chance that all rivals bid above `T` never bids above `T`. -/
lemma no_high (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n) (T : ℝ)
    (heq : IsBNE D τ σ T) (i : Suppliers n)
    (hq : ∏ k : Fin n, marginalBidLaw D σ (i.succAbove k) (Ioi T) ≠ 0)
    (c : ℝ) (hc : c ∈ D.types i) (hcT : c < T) : σ.bid i c (Ioi T) = 0 := by
  have hW0 : interimWin D τ σ i T ≠ 0 := by
    intro h0
    exact hq (le_antisymm ((interimWin_ge D τ σ i T).trans h0.le) zero_le)
  have hW1 : interimWin D τ σ i T ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (interimWin_le_one D τ σ i T)
  have hpos : 0 < interimUtility D τ σ T i c T := by
    unfold interimUtility
    rw [if_pos le_rfl]
    exact mul_pos (sub_pos.2 hcT) (ENNReal.toReal_pos hW0 hW1)
  have h2 : ∀ᵐ b ∂(σ.bid i c), b ≤ T := by
    filter_upwards [heq.2 i c hc] with b hb
    by_contra hbT
    have h0 : interimUtility D τ σ T i c b = 0 := by
      unfold interimUtility
      rw [if_neg hbT]
    linarith [hb T]
  exact measure_mono_null (fun b hb => not_le.2 hb) (ae_iff.1 h2)

/-- Part (i): almost surely, a cost below `T` forces some bid at most `T`. -/
lemma ae_accept (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n) (T : ℝ)
    (heq : IsBNE D τ σ T) :
    ∀ᵐ x ∂(playLaw D σ), ∀ i, (x i).1 < T → ∃ j, (x j).2 ≤ T := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  let S : Suppliers n → Set (ℝ × ℝ) := fun j =>
    if j = i then Iio T ×ˢ Ioi T else univ ×ˢ Ioi T
  have hsub : {x : Suppliers n → ℝ × ℝ | ¬ ((x i).1 < T → ∃ j, (x j).2 ≤ T)}
      ⊆ Set.pi univ S := by
    intro x hx j _
    rw [Set.mem_ofPred_eq] at hx
    push Not at hx
    by_cases hj : j = i
    · rw [hj]
      simp only [S, if_pos rfl]
      exact ⟨hx.1, hx.2 i⟩
    · simp only [S, if_neg hj]
      exact ⟨mem_univ _, hx.2 j⟩
  refine measure_mono_null hsub ?_
  unfold playLaw
  rw [Measure.pi_pi, Fin.prod_univ_succAbove _ i]
  have hm : ∀ j, (D.law j ⊗ₘ σ.bid j) (univ ×ˢ Ioi T) = marginalBidLaw D σ j (Ioi T) := by
    intro j
    rw [Set.univ_prod, ← Measure.snd_apply measurableSet_Ioi, Measure.snd_compProd]
    rfl
  have hS : ∀ k : Fin n, S (i.succAbove k) = univ ×ˢ Ioi T := fun k => by
    simp [S, Fin.succAbove_ne]
  simp only [hS, hm]
  by_cases hq : ∏ k : Fin n, marginalBidLaw D σ (i.succAbove k) (Ioi T) = 0
  · rw [hq, mul_zero]
  · have hSi : S i = Iio T ×ˢ Ioi T := by simp [S]
    rw [hSi, Measure.compProd_apply_prod measurableSet_Iio measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Iio]
    have h0 : (Iio T).indicator (fun a => σ.bid i a (Ioi T)) =ᵐ[D.law i] 0 := by
      have hc : D.types i ∈ ae (D.law i) := mem_ae_iff.2 (D.concentrated i)
      filter_upwards [hc] with c hc
      by_cases hcT : c ∈ Iio T
      · rw [indicator_of_mem hcT]
        exact no_high D τ σ T heq i hq c hc hcT
      · rw [indicator_of_notMem hcT]; rfl
    rw [lintegral_congr_ae h0]
    simp

lemma eps_nonneg : 0 ≤ epsilon := (Real.exp_pos _).le

lemma eps_le_one : epsilon ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)

/-- Part (ii)-(iii): the pointwise inequality. -/
lemma pointwise (τ : TieRule n) (R T : ℝ) (x : Suppliers n → ℝ × ℝ)
    (h1 : ∀ i, (x i).1 ∈ Icc 1 R ∧ (x i).1 ≤ (x i).2)
    (h2 : ∀ i, (x i).1 < T → ∃ j, (x j).2 ≤ T) :
    outcomeCost τ R T x +
      (if lowest (fun i => (x i).2) ≤ T then
          ∑ i, ENNReal.ofReal (T - (x i).1) * τ.select (fun j => (x j).2) {i} else 0)
      ≤ ENNReal.ofReal (gCap R T (lowest fun i => (x i).1)) +
        ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal (T - lowest fun i => (x i).1) := by
  set cm := lowest fun i => (x i).1 with hcm_def
  have hcm1 : 1 ≤ cm := le_lowest fun i => (h1 i).1.1
  have hcmR : cm ≤ R := (lowest_le _ 0).trans (h1 0).1.2
  unfold outcomeCost
  by_cases hb : lowest (fun i => (x i).2) ≤ T
  · rw [if_pos hb, if_pos hb, ← Finset.sum_add_distrib]
    have key : ∀ i, ENNReal.ofReal (x i).1 * τ.select (fun j => (x j).2) {i} +
        ENNReal.ofReal (T - (x i).1) * τ.select (fun j => (x j).2) {i}
        = ENNReal.ofReal T * τ.select (fun j => (x j).2) {i} := by
      intro i
      rw [← add_mul]
      by_cases hl : ∃ j, (x j).2 < (x i).2
      · rw [Supplement.Dev.L31C.sel_zero τ _ i hl]; simp
      · push Not at hl
        have hbi : (x i).2 ≤ T := (le_lowest (c := fun j => (x j).2) hl).trans hb
        have hc1 := (h1 i).1.1
        have hc2 := (h1 i).2
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 2
        ring
    rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum,
      Supplement.Dev.L31C.sum_select, mul_one]
    by_cases hc : cm < T
    · unfold gCap
      rw [if_pos hc, ← ENNReal.ofReal_mul (by linarith [eps_le_one]),
        ← ENNReal.ofReal_add (by nlinarith [eps_nonneg]) (by nlinarith [eps_le_one])]
      apply le_of_eq
      congr 1
      ring
    · unfold gCap
      rw [if_neg hc]
      push Not at hc
      exact le_add_right (ENNReal.ofReal_le_ofReal (hc.trans hcmR))
  · rw [if_neg hb, if_neg hb, add_zero]
    have hc : ¬ cm < T := by
      intro hc
      obtain ⟨i, hi⟩ := exists_lt_of_lowest_lt hc
      obtain ⟨j, hj⟩ := h2 i hi
      exact hb ((lowest_le (fun i => (x i).2) j).trans hj)
    unfold gCap
    rw [if_neg hc]
    exact le_self_add

end ProcurementPoA.DeterministicCap.Dev.L52

namespace ProcurementPoA.DeterministicCap

open ProcurementPoA.DeterministicCap.Dev.L52 in
theorem chk_lemma_5_2 (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T)
    {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D 1 R) (heq : IsBNE D τ σ T) :
    socialCost D τ σ R T ≤ ∫⁻ c, ENNReal.ofReal (gCap R T (lowest c)) ∂(typeLaw D) := by
  have hcmMeas : Measurable (fun x : Suppliers n → ℝ × ℝ => lowest fun i => (x i).1) :=
    lowest_meas.comp proj_meas
  have hKmeas : Measurable (fun x : Suppliers n → ℝ × ℝ =>
      ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal (T - lowest fun i => (x i).1)) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_const.sub hcmMeas))
  have hG : ∫⁻ c, ENNReal.ofReal (gCap R T (lowest c)) ∂(typeLaw D) =
      ∫⁻ x, ENNReal.ofReal (gCap R T (lowest fun i => (x i).1)) ∂(playLaw D σ) := by
    rw [← typeLaw_map D σ, lintegral_map (f := fun c => ENNReal.ofReal (gCap R T (lowest c)))
      (by exact ENNReal.measurable_ofReal.comp ((gCap_meas R T).comp lowest_meas)) proj_meas]
  have hK : ∫⁻ x, ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal (T - lowest fun i => (x i).1)
        ∂(playLaw D σ) =
      ENNReal.ofReal (1 - epsilon) * ∫⁻ c, ENNReal.ofReal (T - lowest c) ∂(typeLaw D) := by
    rw [lintegral_const_mul (f := fun x : Suppliers n → ℝ × ℝ =>
        ENNReal.ofReal (T - lowest fun i => (x i).1)) _
        (by exact ENNReal.measurable_ofReal.comp (measurable_const.sub hcmMeas)),
      ← typeLaw_map D σ, lintegral_map (f := fun c => ENNReal.ofReal (T - lowest c))
        (by exact ENNReal.measurable_ofReal.comp (measurable_const.sub lowest_meas)) proj_meas]
  have leaf := capped_margin_efficiency R T hR hT D τ σ hcost heq
  have hfacts := ae_facts D τ σ R T hcost heq
  have hKfin : ∫⁻ x, ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal (T - lowest fun i => (x i).1)
        ∂(playLaw D σ) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal T)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ?_
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal T ∂(playLaw D σ) := by
          apply lintegral_mono_ae
          filter_upwards [hfacts] with x hx
          have hcm1 : (1 : ℝ) ≤ lowest fun i => (x i).1 := le_lowest fun i => (hx i).1.1
          gcongr
          linarith
      _ = _ := by simp
  apply ENNReal.le_of_add_le_add_right hKfin
  unfold socialCost
  calc _ ≤ ∫⁻ x, outcomeCost τ R T x ∂(playLaw D σ) +
        ∫⁻ x, (if lowest (fun i => (x i).2) ≤ T then
          ∑ i, ENNReal.ofReal (T - (x i).1) * τ.select (fun j => (x j).2) {i} else 0)
          ∂(playLaw D σ) := add_le_add le_rfl (by rw [hK]; exact leaf)
    _ ≤ _ := le_lintegral_add _ _
    _ ≤ ∫⁻ x, (ENNReal.ofReal (gCap R T (lowest fun i => (x i).1)) +
          ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal (T - lowest fun i => (x i).1))
          ∂(playLaw D σ) := by
        apply lintegral_mono_ae
        filter_upwards [hfacts, ae_accept D τ σ T heq] with x h1 h2
        exact pointwise τ R T x h1 h2
    _ = _ := by rw [lintegral_add_right _ hKmeas, hG]

end ProcurementPoA.DeterministicCap
end

theorem solution : type_of% @ProcurementPoA.DeterministicCap.chk_lemma_5_2 := @ProcurementPoA.DeterministicCap.chk_lemma_5_2
