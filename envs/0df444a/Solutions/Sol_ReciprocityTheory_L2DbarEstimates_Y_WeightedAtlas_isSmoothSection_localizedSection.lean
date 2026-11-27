-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.isSmoothSection_localizedSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:24.820983+00:00
-- url     : https://prove2.me/submissions/194ef2c9-473d-4154-ae86-5d85b60df694

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffOn_of_holo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (la' : La) (Sf : Finset Y) (idx : Y → ι) (χ : Y → Y → ℝ) (c : Y → ℂ)
    (K : Y → Set Y) (hχ : ∀ P ∈ Sf, A.SmoothFn (χ P)) (hχs : ∀ P ∈ Sf, ∀ y, χ P y ≠ 0 → y ∈ K P)
    (hKc : ∀ P ∈ Sf, IsCompact (K P)) (hKs : ∀ P ∈ Sf, K P ⊆ (A.chart (idx P)).source) :
    A.IsSSec la' (A.F0 la' Sf idx χ c) := by
  refine ⟨fun j => ?_, fun i j y hi hj => ?_⟩
  · have : (A.F0 la' Sf idx χ c j ∘ (A.chart j).symm) = fun v => ∑ P ∈ Sf,
        c P * (χ P ((A.chart j).symm v) : ℂ) * A.g la' j (idx P) ((A.chart j).symm v) := by
      funext v; rfl
    rw [this]
    refine ContDiffOn.sum fun P hP => contDiffOn_of_locally_contDiffOn fun v hv => ?_
    by_cases hx : (A.chart j).symm v ∈ (A.chart (idx P)).source
    · refine ⟨ovl A.chart j (idx P), A.isOpen_ovl j _, ⟨hv, hx⟩, ?_⟩
      have hg : ContDiffOn ℝ ∞ (A.g la' j (idx P) ∘ (A.chart j).symm) (ovl A.chart j (idx P)) :=
        contDiffOn_of_holo (A.isOpen_ovl j _) (A.holo_g la' j (idx P))
      have hc : ContDiffOn ℝ ∞ (fun v => (χ P ((A.chart j).symm v) : ℂ)) (A.chart j).target :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ P hP j)
      exact ((contDiffOn_const.mul hc).mono Set.inter_subset_left).mul
        (hg.mono Set.inter_subset_right)
    · have hKc' := (hKc P hP).isClosed
      have hxK : (A.chart j).symm v ∉ K P := fun h => hx (hKs P hP h)
      refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' (K P)ᶜ,
        (A.chart j).isOpen_inter_preimage_symm hKc'.isOpen_compl, ⟨hv, hxK⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v' hv' => ?_
      have h0 : χ P ((A.chart j).symm v') = 0 := by
        by_contra h; exact hv'.2.2 (hχs P hP _ h)
      simp [h0]
  · unfold F0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    by_cases hy : y ∈ (A.chart (idx P)).source
    · rw [A.g_cocycle la' i j (idx P) y hi hj hy]; ring
    · have h0 : χ P y = 0 := by by_contra h; exact hy (hKs P hP (hχs P hP y h))
      simp [h0]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
