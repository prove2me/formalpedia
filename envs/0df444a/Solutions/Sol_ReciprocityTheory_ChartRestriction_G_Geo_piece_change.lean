-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.piece_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:39.428164+00:00
-- url     : https://prove2.me/submissions/0634575f-0b54-4174-a927-e860ea86cf25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_abs_det_restrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {D : Set (Fin e → ℂ)} (hD : MeasurableSet D) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQd : ∀ u ∈ D, DifferentiableAt ℂ Q u)
    (hdet : ∀ u ∈ D, LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hinj : InjOn Q D) {h : (Fin e → ℂ) → ℝ} (hh : IntegrableOn h D) :
    Integrable (fibSum D Q h) ∧ ∫ y, fibSum D Q h y = ∫ u in D, h u ∧
      ∫ y, ‖fibSum D Q h y‖ = ∫ u in D, ‖h u‖ := by
  have hf' : ∀ u ∈ D, HasFDerivWithinAt Q ((fderiv ℂ Q u).restrictScalars ℝ) D u :=
    fun u hu => ((hQd u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hJpos : ∀ u ∈ D, 0 < jacN Q u := fun u hu =>
    pow_pos (norm_pos_iff.mpr (hdet u hu)) 2
  have hval : ∀ u ∈ D, fibSum D Q h (Q u) = h u / jacN Q u := by
    intro u hu
    have : D ∩ Q ⁻¹' {Q u} = {u} := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨hv, hq⟩ => hinj hv hu hq, fun hv => by subst hv; exact ⟨hu, rfl⟩⟩
    simp only [fibSum, this, finsum_mem_singleton]
  have hzero : ∀ y, y ∉ Q '' D → fibSum D Q h y = 0 := by
    intro y hy
    have : D ∩ Q ⁻¹' {y} = ∅ := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      exact fun hv hq => hy ⟨v, hv, hq⟩
    simp [fibSum, this]
  have hdetJ : ∀ u, |((fderiv ℂ Q u).restrictScalars ℝ).det| = jacN Q u := fun u =>
    abs_det_restrictScalars _
  have hkey : EqOn (fun u => |((fderiv ℂ Q u).restrictScalars ℝ).det| • fibSum D Q h (Q u)) h D := by
    intro u hu
    simp only [hval u hu, hdetJ, smul_eq_mul]
    field_simp [(hJpos u hu).ne']
  have hkeyn : EqOn (fun u => |((fderiv ℂ Q u).restrictScalars ℝ).det| • ‖fibSum D Q h (Q u)‖)
      (fun u => ‖h u‖) D := by
    intro u hu
    simp only [hval u hu, hdetJ, smul_eq_mul, norm_div, Real.norm_of_nonneg (hJpos u hu).le]
    field_simp [(hJpos u hu).ne']
  have hint_on : IntegrableOn (fibSum D Q h) (Q '' D) := by
    rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hf' hinj]
    exact hh.congr_fun (fun u hu => (hkey hu).symm) hD
  have hint : Integrable (fibSum D Q h) := hint_on.integrable_of_forall_notMem_eq_zero hzero
  refine ⟨hint, ?_, ?_⟩
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj]
    exact setIntegral_congr_fun hD hkey
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Q '' D)
      (fun y hy => by rw [hzero y hy, norm_zero]),
      integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj]
    exact setIntegral_congr_fun hD hkeyn
end ReciprocityTheory.ChartRestriction.G.Geo
