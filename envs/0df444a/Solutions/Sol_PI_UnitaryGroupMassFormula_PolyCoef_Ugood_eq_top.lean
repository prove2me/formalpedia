-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.Ugood_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:16.530786+00:00
-- url     : https://prove2.me/submissions/8167f917-7b33-493b-8531-3f3ed71f668a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_orb_cont
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_integrable_cont
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_isPositiveDefinite_matrix_coefficient_of_mem_algA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_algA_dense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution (hrep : IsURepOn (Kset (allPos N)) σ) (hfin : FiniteDimensional ℂ S)
    (hst : IsKStableOn (allPos N) σ S) : Ugood σ S = ⊤ := by
  haveI := hfin
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let φC : S →L[ℂ] ℂ := LinearMap.toContinuousLinearMap φ
  apply hφ0
  ext u
  let g : UG N → ℂ := fun x => φC (orb hst u x)
  have hg : Continuous g := φC.continuous.comp (orb_cont hrep hst u)
  have hA : ∀ f ∈ algA N, ∫ x, f x * g x ∂(muU N) = 0 := by
    intro f hf
    have hmem : T hst f u ∈ Ugood σ S := fun w => isPositiveDefinite_matrix_coefficient_of_mem_algA hrep hst hf u w
    have h0 : φ (T hst f u) = 0 := LinearMap.mem_ker.mp (hle hmem)
    have hint : Integrable (fun x => f x • orb hst u x) (muU N) :=
      integrable_cont (f.continuous.smul (orb_cont hrep hst u))
    have hc := φC.integral_comp_comm hint
    rw [← h0]
    refine Eq.trans ?_ hc
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [g, φC, map_smul, smul_eq_mul]
  have hall : ∀ F : C(UG N, ℂ), ∫ x, F x * g x ∂(muU N) = 0 := by
    intro F
    have hM0 : 0 ≤ ∫ x, ‖g x‖ ∂(muU N) := integral_nonneg fun x => norm_nonneg _
    have hbound : ∀ ε > 0, ‖∫ x, F x * g x ∂(muU N)‖ ≤ ε * ∫ x, ‖g x‖ ∂(muU N) := by
      intro ε hε
      obtain ⟨f, hf, hfF⟩ := algA_dense N F hε
      have hsplit : ∫ x, F x * g x ∂(muU N) = ∫ x, (F - f) x * g x ∂(muU N) := by
        have h1 : ∫ x, (F - f) x * g x ∂(muU N) =
            ∫ x, F x * g x ∂(muU N) - ∫ x, f x * g x ∂(muU N) := by
          have hi1 : Integrable (fun x => F x * g x) (muU N) := integrable_cont (F.continuous.mul hg)
          have hi2 : Integrable (fun x => f x * g x) (muU N) := integrable_cont (f.continuous.mul hg)
          rw [← integral_sub hi1 hi2]
          congr 1
          funext x
          simp [sub_mul]
        rw [h1, hA f hf, sub_zero]
      rw [hsplit]
      calc ‖∫ x, (F - f) x * g x ∂(muU N)‖ ≤ ∫ x, ‖(F - f) x * g x‖ ∂(muU N) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ε * ‖g x‖ ∂(muU N) := by
          refine integral_mono (integrable_cont (((F - f).continuous.mul hg).norm))
            (integrable_cont (continuous_const.mul hg.norm)) fun x => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right ((ContinuousMap.norm_coe_le_norm (F - f) x).trans hfF.le)
            (norm_nonneg _)
        _ = ε * ∫ x, ‖g x‖ ∂(muU N) := integral_const_mul _ _
    by_contra hne0
    have hpos : 0 < ‖∫ x, F x * g x ∂(muU N)‖ := norm_pos_iff.mpr hne0
    set I := ‖∫ x, F x * g x ∂(muU N)‖
    set M := ∫ x, ‖g x‖ ∂(muU N)
    have h3 := hbound (I / (M + 1)) (div_pos hpos (by linarith))
    have hlt : I / (M + 1) * M < I := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hF := hall ⟨fun x => star (g x), continuous_star.comp hg⟩
  have hcn : Continuous fun x => Complex.normSq (g x) := Complex.continuous_normSq.comp hg
  have hF' : ∫ x, Complex.normSq (g x) ∂(muU N) = 0 := by
    have h4 : ∫ x, ((Complex.normSq (g x) : ℝ) : ℂ) ∂(muU N) = 0 := by
      rw [← hF]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact Complex.normSq_eq_conj_mul_self
    rw [integral_complex_ofReal] at h4
    exact_mod_cast h4
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (g x))
    (integrable_cont hcn)).mp hF'
  have heq : (fun x => Complex.normSq (g x)) = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq (muU N) hcn continuous_const).mp hae
  have h1 : Complex.normSq (g 1) = 0 := congrFun heq 1
  rw [Complex.normSq_eq_zero] at h1
  have horb : orb hst u 1 = u := by
    apply Subtype.ext
    simp [orb, hrep.1.1]
  simp only [g, horb] at h1
  simpa [φC] using h1
end PI.UnitaryGroupMassFormula.PolyCoef
