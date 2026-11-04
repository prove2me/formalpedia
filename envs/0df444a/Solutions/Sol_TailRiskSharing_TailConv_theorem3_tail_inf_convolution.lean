-- Prove2me | solution 1 for TailRiskSharing.TailConv.theorem3_tail_inf_convolution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:04:14.754752+00:00
-- url     : https://prove2.me/submissions/fec8f4b9-488a-41c5-9dad-7277c3e4f0a8

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting
import Theorems.Thm_TailRiskSharing_TailConv_lemma1_tail_max
import Theorems.Thm_TailRiskSharing_TailConv_embrechts_cor1_varL_sum
import Theorems.Thm_TailRiskSharing_TailConv_infConv_monotone
import Theorems.Thm_TailRiskSharing_TailConv_infConv_lawInvariant

set_option autoImplicit false
open MeasureTheory TailRiskSharing.TailConv

namespace TCD21Help

open TailRiskSharing.VaRConv

variable {Ω : Type*} [MeasurableSpace Ω]

lemma distFn_mono (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) {x y : ℝ} (h : x ≤ y) :
    distFn P X x ≤ distFn P X y := by
  unfold distFn
  exact measureReal_mono (fun ω (hω : X ω ≤ x) => le_trans hω h)

lemma distFn_nonneg (P : Measure Ω) (X : Ω → ℝ) (x : ℝ) : 0 ≤ distFn P X x := by
  unfold distFn; exact measureReal_nonneg

lemma distFn_low (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) {x : ℝ} (hx : x < -C) : distFn P X x = 0 := by
  unfold distFn
  have hnull : P {ω | X ω ≤ x} = 0 := by
    refine measure_mono_null (t := {ω | ¬ |X ω| ≤ C}) ?_ (ae_iff.mp hC)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro habs
    have := (abs_le.mp habs).1
    linarith
  simp [Measure.real, hnull]

lemma distFn_high (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) : distFn P X C = 1 := by
  unfold distFn
  have : P {ω | X ω ≤ C} = 1 := by
    rw [← measure_univ (μ := P)]
    apply measure_congr
    filter_upwards [hC] with ω hω
    have : X ω ≤ C := (abs_le.mp hω).2
    exact propext ⟨fun _ => trivial, fun _ => this⟩
  simp [Measure.real, this]

lemma bdd_of (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) (t : ℝ) (ht : 0 < t) :
    BddBelow {x : ℝ | t ≤ distFn P X x} := by
  refine ⟨-C - 1, fun y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have h0 := distFn_low P X C hC (x := y) (by linarith)
  have hy' : t ≤ distFn P X y := hy
  linarith

lemma bddR_of (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) (t : ℝ) (ht : 0 ≤ t) :
    BddBelow {x : ℝ | t < distFn P X x} := by
  refine ⟨-C - 1, fun y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have h0 := distFn_low P X C hC (x := y) (by linarith)
  have hy' : t < distFn P X y := hy
  linarith

lemma VaRL_le_VaRR (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : X ∈ Linf P)
    (α : ℝ) (h0 : 0 < α) (h1 : α < 1) : VaRL P α X ≤ VaRR P α X := by
  obtain ⟨-, C, hC⟩ := hX
  unfold VaRL VaRR
  apply csInf_le_csInf (bdd_of P X C hC (1 - α) (by linarith))
  · exact ⟨C, by show 1 - α < distFn P X C; rw [distFn_high P X C hC]; linarith⟩
  · intro x (hx : 1 - α < distFn P X x); exact le_of_lt hx

/-- `VaR^R_α ≤ VaR^L_β` for `β < α`. -/
lemma VaRR_le_VaRL (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : X ∈ Linf P)
    (α β : ℝ) (hβ0 : 0 < β) (hβα : β < α) (hα : α < 1) : VaRR P α X ≤ VaRL P β X := by
  obtain ⟨-, C, hC⟩ := hX
  unfold VaRL VaRR
  apply csInf_le_csInf (bddR_of P X C hC (1 - α) (by linarith))
  · exact ⟨C, by show 1 - β ≤ distFn P X C; rw [distFn_high P X C hC]; linarith⟩
  · intro x (hx : 1 - β ≤ distFn P X x); show 1 - α < distFn P X x; linarith

/-- approximation of `VaR^R_α` from the left by `VaR^L_β`. -/
lemma exists_VaRL_close (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : X ∈ Linf P)
    (α : ℝ) (h0 : 0 < α) (h1 : α < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ β, 0 < β ∧ β < α ∧ VaRL P β X ≤ VaRR P α X + δ := by
  obtain ⟨-, C, hC⟩ := hX
  set r := VaRR P α X
  have hne : ({x : ℝ | 1 - α < distFn P X x}).Nonempty :=
    ⟨C, by show 1 - α < distFn P X C; rw [distFn_high P X C hC]; linarith⟩
  obtain ⟨y, hy, hyr⟩ := exists_lt_of_csInf_lt hne (show sInf _ < r + δ by
    show VaRR P α X < r + δ; linarith)
  have hy' : 1 - α < distFn P X y := hy
  have hF : 1 - α < distFn P X (r + δ) := lt_of_lt_of_le hy' (distFn_mono P X hyr.le)
  refine ⟨max (1 - distFn P X (r + δ)) (α / 2), lt_max_of_lt_right (by linarith),
    max_lt (by linarith) (by linarith), ?_⟩
  unfold VaRL
  apply csInf_le (bdd_of P X C hC _ ?_)
  · show 1 - max (1 - distFn P X (r + δ)) (α / 2) ≤ distFn P X (r + δ)
    have := le_max_left (1 - distFn P X (r + δ)) (α / 2)
    linarith
  · have := le_max_right (1 - distFn P X (r + δ)) (α / 2)
    have hF1 : distFn P X (r + δ) ≤ 1 := by
      unfold distFn; exact measureReal_le_one
    rw [sub_pos]
    exact max_lt (by linarith) (by linarith)

lemma max_mem_Linf (P : Measure Ω) (X : Ω → ℝ) (hX : X ∈ Linf P) (c : ℝ) :
    (fun ω => max (X ω) c) ∈ Linf P := by
  obtain ⟨hm, C, hC⟩ := hX
  refine ⟨hm.max measurable_const, max C |c|, ?_⟩
  filter_upwards [hC] with ω hω
  rw [abs_le] at hω ⊢
  constructor
  · have := neg_abs_le c
    have := le_max_left (X ω) c
    have := le_max_left C |c|
    linarith
  · apply max_le
    · exact le_trans hω.2 (le_max_left _ _)
    · exact le_trans (le_abs_self c) (le_max_right _ _)

lemma sum_mem_Linf (P : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) (hY : ∀ i, Y i ∈ Linf P) :
    (fun ω => ∑ i, Y i ω) ∈ Linf P := by
  choose hm C hC using hY
  refine ⟨Finset.measurable_sum _ (fun i _ => hm i), ∑ i, C i, ?_⟩
  have : ∀ᵐ ω ∂P, ∀ i, |Y i ω| ≤ C i := ae_all_iff.mpr hC
  filter_upwards [this] with ω hω
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => hω i))

/-- Subadditivity of right VaR derived from the left-VaR version (Embrechts et al. Cor. 1). -/
lemma VaRR_sum_le (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (n : ℕ) (hn : 1 ≤ n) (εs : Fin n → ℝ)
    (hε : ∀ i, 0 < εs i ∧ εs i < 1) (hsum : ∑ i, εs i < 1) (Xs : Fin n → Ω → ℝ)
    (hXs : ∀ i, Xs i ∈ Linf P) :
    VaRR P (∑ i, εs i) (fun ω => ∑ i, Xs i ω) ≤ ∑ i, VaRR P (εs i) (Xs i) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply le_of_forall_pos_lt_add
  intro η hη
  have hδ : 0 < η / (2 * n) := by positivity
  choose β hβ0 hβε hβle using fun i => exists_VaRL_close P (Xs i) (hXs i) (εs i) (hε i).1 (hε i).2
    (η / (2 * n)) hδ
  have hβlt : ∑ i, β i < ∑ i, εs i := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    · intro i _; exact hβε i
  have hβpos : 0 < ∑ i, β i :=
    Finset.sum_pos (fun i _ => hβ0 i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h1 := VaRR_le_VaRL P (fun ω => ∑ i, Xs i ω) (sum_mem_Linf P Xs hXs) (∑ i, εs i) (∑ i, β i)
    hβpos hβlt hsum
  have h2 := TailRiskSharing.TailConv.embrechts_cor1_varL_sum P hP n hn β
    (fun i => ⟨hβ0 i, lt_trans (hβε i) (hε i).2⟩) (lt_trans hβlt hsum) Xs hXs
  have h3 : ∑ i, VaRL P (β i) (Xs i) ≤ ∑ i, (VaRR P (εs i) (Xs i) + η / (2 * n)) :=
    Finset.sum_le_sum (fun i _ => hβle i)
  rw [Finset.sum_add_distrib] at h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  have h4 : (n : ℝ) * (η / (2 * n)) = η / 2 := by field_simp
  rw [h4] at h3
  linarith

/-- Display (21) with any level `m ≤ VaR^R_ε(X)`. -/
theorem infConv_eq_max (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ) (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P (Linf P) (εs i) (ρ i))
    (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j))
    (hsum : ∑ i, εs i < 1) (X : Ω → ℝ) (hX : X ∈ Linf P) (m : ℝ)
    (hm : m ≤ VaRR P (∑ i, εs i) X) :
    infConv (Linf P) ρ X = infConv (Linf P) ρ (fun ω => max (X ω) m) := by
  have hM := TailRiskSharing.TailConv.infConv_monotone P hP n hn ρ j hmono
  apply le_antisymm
  · exact hM X hX _ (max_mem_Linf P X hX m) (Filter.Eventually.of_forall fun ω => le_max_left _ _)
  · unfold infConv
    refine le_iInf₂ (fun Xs hXs => ?_)
    obtain ⟨hXsL, hXsum⟩ := hXs
    set ms : Fin n → ℝ := fun i => VaRR P (εs i) (Xs i)
    set Y : Fin n → Ω → ℝ := fun i ω => max (Xs i ω) (ms i)
    have hYL : ∀ i, Y i ∈ Linf P := fun i => max_mem_Linf P (Xs i) (hXsL i) (ms i)
    have hρ : ∀ i, ρ i (Y i) = ρ i (Xs i) := by
      intro i
      apply htail i (Y i) (hYL i) (Xs i) (hXsL i)
      exact TailRiskSharing.TailConv.lemma1_tail_max P hP (εs i) (hε i).1 (hε i).2 (Xs i) (hXsL i)
        (ms i) (VaRL_le_VaRR P (Xs i) (hXsL i) (εs i) (hε i).1 (hε i).2) le_rfl
    set Z : Ω → ℝ := fun ω => ∑ i, Y i ω
    have hZL : Z ∈ Linf P := sum_mem_Linf P Y hYL
    have hXeq : X = fun ω => ∑ i, Xs i ω := funext fun ω => (hXsum ω).symm
    have hsumm : VaRR P (∑ i, εs i) X ≤ ∑ i, ms i := by
      rw [hXeq]; exact VaRR_sum_le P hP n hn εs hε hsum Xs hXsL
    have hZge : ∀ ω, max (X ω) m ≤ Z ω := by
      intro ω
      apply max_le
      · rw [← hXsum ω]
        exact Finset.sum_le_sum (fun i _ => le_max_left _ _)
      · calc m ≤ ∑ i, ms i := le_trans hm hsumm
          _ ≤ Z ω := Finset.sum_le_sum (fun i _ => le_max_right _ _)
    have h1 := hM _ (max_mem_Linf P X hX m) Z hZL (Filter.Eventually.of_forall hZge)
    refine le_trans h1 ?_
    unfold infConv
    have hYA : Y ∈ Allocations (Linf P) n Z := ⟨hYL, fun ω => rfl⟩
    refine le_trans (iInf₂_le Y hYA) ?_
    rw [Finset.sum_congr rfl (fun i _ => hρ i)]


lemma distFn_eq_cdf (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (x : ℝ) : distFn P X x = ProbabilityTheory.cdf (P.map X) x := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, map_measureReal_apply hX measurableSet_Iic]
  rfl

/-- right-continuity: `F_X(VaR^R_α(X)) ≥ 1 - α`. -/
lemma distFn_VaRR_ge (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : X ∈ Linf P)
    (α : ℝ) (h0 : 0 < α) (h1 : α < 1) : 1 - α ≤ distFn P X (VaRR P α X) := by
  obtain ⟨hm, C, hC⟩ := hX
  set r := VaRR P α X
  have hne : ({x : ℝ | 1 - α < distFn P X x}).Nonempty :=
    ⟨C, by show 1 - α < distFn P X C; rw [distFn_high P X C hC]; linarith⟩
  have hgt : ∀ x, r < x → 1 - α < distFn P X x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne (show sInf _ < x from hx)
    exact lt_of_lt_of_le hy (distFn_mono P X hyx.le)
  have hc := (ProbabilityTheory.cdf (P.map X)).right_continuous r
  have ht : Filter.Tendsto (ProbabilityTheory.cdf (P.map X)) (nhdsWithin r (Set.Ioi r))
      (nhds (ProbabilityTheory.cdf (P.map X) r)) :=
    (hc.mono Set.Ioi_subset_Ici_self).tendsto
  rw [distFn_eq_cdf P X hm]
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [← distFn_eq_cdf P X hm]
  exact (hgt x hx).le

lemma VaRR_congr (P : Measure Ω) (X Y : Ω → ℝ) (α : ℝ)
    (h : TailRiskSharing.VaRTail.TailEquiv P α X Y) : VaRR P α X = VaRR P α Y := by
  unfold VaRR
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  have hx := h x
  constructor
  · intro hlt
    rw [max_eq_left (by linarith)] at hx
    by_contra hle; push Not at hle
    rw [max_eq_right (by linarith)] at hx; linarith
  · intro hlt
    rw [max_eq_left (a := distFn P Y x - (1 - α)) (by linarith)] at hx
    by_contra hle; push Not at hle
    rw [max_eq_right (by linarith)] at hx; linarith

lemma distFn_max_of_lt (P : Measure Ω) (X : Ω → ℝ) (b x : ℝ) (hx : x < b) :
    distFn P (fun ω => max (X ω) b) x = 0 := by
  unfold distFn
  have : {ω | max (X ω) b ≤ x} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx (le_max_right _ _)
  rw [this]; simp

lemma distFn_max_of_ge (P : Measure Ω) (X : Ω → ℝ) (b x : ℝ) (hx : b ≤ x) :
    distFn P (fun ω => max (X ω) b) x = distFn P X x := by
  unfold distFn
  congr 2
  ext ω
  simp [hx]

end TCD21Help

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ) (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P (Linf P) (εs i) (ρ i))
    (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j))
    (hcont : IsSupNormContinuousFromAbove P (Linf P) (ρ j)) :
    TailRiskSharing.VaRTail.IsMonotoneE P (Linf P) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) ∧
      TailRiskSharing.VaRTail.IsTailRiskMeasureE P (Linf P) (min (∑ i, εs i) 1) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) := by
  open TailRiskSharing.VaRConv TCD21Help in
  have hM := TailRiskSharing.TailConv.infConv_monotone P hP n hn ρ j hmono
  have hLI := TailRiskSharing.TailConv.infConv_lawInvariant P hP n hn ρ εs hε htail j hmono hcont
  refine ⟨hM, ?_⟩
  intro X hX Y hY hXY
  by_cases hs : 1 ≤ ∑ i, εs i
  · rw [min_eq_right hs] at hXY
    apply hLI X hX Y hY
    intro x
    have h := hXY x
    simp only [sub_self, sub_zero] at h
    rwa [max_eq_left (distFn_nonneg P X x), max_eq_left (distFn_nonneg P Y x)] at h
  · push Not at hs
    rw [min_eq_left hs.le] at hXY
    set ε := ∑ i, εs i with hεdef
    have hε0 : 0 < ε :=
      Finset.sum_pos (fun i _ => (hε i).1) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    set b := VaRR P ε X with hbdef
    have hbY : VaRR P ε Y = b := (VaRR_congr P X Y ε hXY).symm
    have h1 := infConv_eq_max P hP n hn ρ εs hε htail j hmono hs X hX b le_rfl
    have h2 := infConv_eq_max P hP n hn ρ εs hε htail j hmono hs Y hY b hbY.ge
    rw [h1, h2]
    apply hLI _ (max_mem_Linf P X hX b) _ (max_mem_Linf P Y hY b)
    intro x
    rcases lt_or_ge x b with hx | hx
    · rw [distFn_max_of_lt P X b x hx, distFn_max_of_lt P Y b x hx]
    · rw [distFn_max_of_ge P X b x hx, distFn_max_of_ge P Y b x hx]
      have hFX : 1 - ε ≤ distFn P X x :=
        le_trans (distFn_VaRR_ge P X hX ε hε0 hs) (distFn_mono P X hx)
      have hFY : 1 - ε ≤ distFn P Y x := by
        have := distFn_VaRR_ge P Y hY ε hε0 hs
        rw [hbY] at this
        exact le_trans this (distFn_mono P Y hx)
      have h := hXY x
      rw [max_eq_left (by linarith), max_eq_left (by linarith)] at h
      linarith
