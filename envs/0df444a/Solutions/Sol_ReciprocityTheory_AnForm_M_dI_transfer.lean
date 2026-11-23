-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:34.162113+00:00
-- url     : https://prove2.me/submissions/968d6664-26c4-4af5-b9f3-65443c46db34

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrableOn_image_iff_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D)
    (a b : Fin A.n) (f : X → ℝ) (hf : ∀ x, x ∉ (A.chart a).source → f x = 0)
    (hint : IntegrableOn (fun y => f ((A.chart a).symm y) * D a y) (A.chart a).target) :
    IntegrableOn (fun y => f ((A.chart b).symm y) * D b y) (A.chart b).target ∧
    ∫ y in (A.chart b).target, f ((A.chart b).symm y) * D b y =
      ∫ y in (A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source,
        f ((A.chart a).symm y) * D a y := by
  have hU : IsOpen ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) :=
    (A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
      (A.chart b).open_source
  have hτ : AnalyticOnNhd ℂ (A.chart b ∘ (A.chart a).symm)
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) := A.holo a b
  have hinj : Set.InjOn (A.chart b ∘ (A.chart a).symm)
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) := by
    intro u hu v hv huv
    exact (A.chart a).symm.injOn hu.1 hv.1 ((A.chart b).injOn hu.2 hv.2 huv)
  have himg : (A.chart b ∘ (A.chart a).symm) ''
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) ⊆ (A.chart b).target := by
    rintro _ ⟨z, hz, rfl⟩; exact (A.chart b).map_source hz.2
  have hin : ∀ w ∈ (A.chart b).target, (A.chart b).symm w ∈ (A.chart a).source →
      w ∈ (A.chart b ∘ (A.chart a).symm) ''
        ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) := by
    intro w hw h2
    refine ⟨A.chart a ((A.chart b).symm w), ⟨(A.chart a).map_source h2, ?_⟩, ?_⟩
    · show (A.chart a).symm (A.chart a ((A.chart b).symm w)) ∈ (A.chart b).source
      rw [(A.chart a).left_inv h2]; exact (A.chart b).map_target hw
    · show A.chart b ((A.chart a).symm (A.chart a ((A.chart b).symm w))) = w
      rw [(A.chart a).left_inv h2, (A.chart b).right_inv hw]
  have hzero : ∀ w ∈ (A.chart b).target \ (A.chart b ∘ (A.chart a).symm) ''
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source),
      f ((A.chart b).symm w) * D b w = 0 := by
    rintro w ⟨hw, hwU⟩
    have h1 : (A.chart b).symm w ∉ (A.chart a).source := fun h => hwU (hin w hw h)
    simp [hf _ h1]
  have heq : ∀ z ∈ (A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source,
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart b ∘ (A.chart a).symm) z).det *
        (f ((A.chart b).symm ((A.chart b ∘ (A.chart a).symm) z)) *
          D b ((A.chart b ∘ (A.chart a).symm) z)) = f ((A.chart a).symm z) * D a z := by
    intro z hz
    have hz2 : (A.chart a).symm z ∈ (A.chart b).source := hz.2
    simp only [Function.comp_apply, (A.chart b).left_inv hz2]
    rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hD a b z hz.1 hz2]
    ring
  have hIU : IntegrableOn (fun y => f ((A.chart a).symm y) * D a y)
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) :=
    hint.mono_set Set.inter_subset_left
  have hIimg : IntegrableOn (fun w => f ((A.chart b).symm w) * D b w)
      ((A.chart b ∘ (A.chart a).symm) ''
        ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source)) := by
    rw [ReciprocityTheory.AnForm.A.integrableOn_image_iff_analytic _ _ hU hτ hinj]
    refine hIU.congr_fun (fun z hz => ?_) hU.measurableSet
    simp only [smul_eq_mul]
    exact (heq z hz).symm
  refine ⟨hIimg.of_forall_sdiff_eq_zero (A.chart b).open_target.measurableSet hzero, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart b).open_target.measurableSet
      himg hzero,
    ReciprocityTheory.AnForm.A.integral_image_eq_integral_normSq_det_smul _ _ hU hτ hinj]
  refine setIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
  simp only [smul_eq_mul]
  exact heq z hz
end ReciprocityTheory.AnForm.M
