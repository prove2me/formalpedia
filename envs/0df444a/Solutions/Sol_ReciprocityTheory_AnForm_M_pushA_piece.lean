-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:08.077046+00:00
-- url     : https://prove2.me/submissions/1c0a60a3-c97c-4b40-ac29-627740a11db5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_detR
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_fib

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
theorem _root_.solution (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hD : MeasurableSet D) (hdiff : ∀ z ∈ D, DifferentiableAt ℂ (q ∘ s) z)
    (hinj : Set.InjOn (q ∘ s) D) (k : X → ℝ) :
    (Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x) ↔
      IntegrableOn (fun z => Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z)) D) ∧
    ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x =
      ∫ z in D, Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z) := by
  obtain ⟨h1, h2⟩ := pushA_fib q s hinj
  set G : (Fin e → ℂ) → ℝ := fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x with hG
  have hGτ : ∀ z ∈ D, G ((q ∘ s) z) = k (s z) := by
    intro z hz
    simp only [hG]
    rw [Function.comp_apply, h1 z hz, finsum_mem_singleton]
  have hG0 : ∀ y, y ∉ (q ∘ s) '' D → G y = 0 := by
    intro y hy
    simp only [hG]
    rw [h2 y hy, finsum_mem_empty]
  have hf' : ∀ z ∈ D, HasFDerivWithinAt (q ∘ s) ((fderiv ℂ (q ∘ s) z).restrictScalars ℝ) D z :=
    fun z hz => ((hdiff z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hEq : Set.EqOn (fun z => |((fderiv ℂ (q ∘ s) z).restrictScalars ℝ).det| • G ((q ∘ s) z))
      (fun z => Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z)) D := by
    intro z hz
    simp only [smul_eq_mul]
    rw [hGτ z hz, pushA_detR, abs_of_nonneg (Complex.normSq_nonneg _)]
  have hI := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hf' hinj G
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj G
  constructor
  · rw [← integrableOn_congr_fun hEq hD, ← hI]
    exact ⟨fun h => h.integrableOn, fun h => h.integrable_of_forall_notMem_eq_zero hG0⟩
  · rw [← setIntegral_congr_fun hD hEq, ← hJ, setIntegral_eq_integral_of_forall_compl_eq_zero hG0]
end ReciprocityTheory.AnForm.M
