-- Prove2me | solution 1 for PIW.HCFdeg.stOrthOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:22.5658+00:00
-- url     : https://prove2.me/submissions/883d110d-bda8-4ea3-9c4a-5f0c15bcf067

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf
import Theorems.Thm_PIW_HCFdeg_cfL_apply
import Theorems.Thm_PIW_HCFdeg_inner_pi
import Theorems.Thm_PIW_HCFdeg_pi_mul_inv
import Theorems.Thm_PIW_HCFdeg_pi_inv
import Theorems.Thm_PIW_HCFdeg_integrable_cf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace PIW.HCFdeg
theorem _root_.solution : StOrthOf := by
  intro hSchur hBdd G _ _ _ _ _ _ _ μ _ _ _ H _ _ _ _ π hiso hcont hirr hL2
  have hcv : ∀ (w : H) (g : G), Continuous fun v => cfL π w v g := fun w g => by
    show Continuous fun v => ⟪w, π g v⟫_ℂ
    exact continuous_const.inner (π g).continuous
  choose T hT using fun w : H => hBdd G H μ (cfL π w) (hcv w) (fun v => hL2 v w)
  let B : H → H → H → H → ℂ := fun v w v' w' => ∫ g, cf π v w g * star (cf π v' w' g) ∂μ
  have hBT : ∀ v w v' w', B v w v' w' = ⟪v', (T w').adjoint (T w v)⟫_ℂ := by
    intro v w v' w'
    rw [ContinuousLinearMap.adjoint_inner_right, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT w v, hT w' v'] with g h1 h2
    rw [h1, h2]
    simp [cfL_apply, RCLike.inner_apply, mul_comm]
  have hpiadj : ∀ (h : G) (x y : H), ⟪π h⁻¹ x, y⟫_ℂ = ⟪x, π h y⟫_ℂ := by
    intro h x y
    rw [← inner_pi π hiso h (π h⁻¹ x) y, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hshift : ∀ (h : G) v w v' w', B (π h v) w v' w' = B v w (π h⁻¹ v') w' := by
    intro h v w v' w'
    show ∫ g, cf π (π h v) w g * star (cf π v' w' g) ∂μ = ∫ g, cf π v w g * star (cf π (π h⁻¹ v') w' g) ∂μ
    conv_rhs => rw [← integral_mul_right_eq_self _ h]
    congr 1
    funext g
    simp only [cf]
    rw [pi_mul_inv, map_mul, ContinuousLinearMap.mul_apply]
  have hcomm : ∀ w w' (h : G), ((T w').adjoint ∘L T w) ∘L π h = π h ∘L ((T w').adjoint ∘L T w) := by
    intro w w' h
    refine ContinuousLinearMap.ext fun v => ?_
    apply ext_inner_left ℂ
    intro v'
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hBT, hshift, hBT, hpiadj]
  choose c hc using fun w w' : H => hSchur G H π hiso hirr _ (hcomm w w')
  have hBc : ∀ v w v' w', B v w v' w' = c w w' * ⟪v', v⟫_ℂ := by
    intro v w v' w'
    rw [hBT]
    have e := congrArg (fun A : H →L[ℂ] H => A v) (hc w w')
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at e
    rw [e, inner_smul_right]
  have hcfinv : ∀ v w g, cf π v w g = star (cf π w v g⁻¹) := by
    intro v w g
    have e := pi_inv π hiso g⁻¹ v w
    rw [inv_inv] at e
    exact e
  have hBsymm : ∀ v w v' w', B v w v' w' = conj (B w v w' v') := by
    intro v w v' w'
    show ∫ g, cf π v w g * star (cf π v' w' g) ∂μ = conj (∫ g, cf π w v g * star (cf π w' v' g) ∂μ)
    rw [← integral_conj]
    conv_rhs => rw [← integral_inv_eq_self _ μ]
    congr 1
    funext g
    rw [hcfinv v w g, hcfinv v' w' g]
    simp [RCLike.star_def, map_mul]
  have hrel : ∀ v w v' w', c w w' * ⟪v', v⟫_ℂ = conj (c v v') * ⟪w, w'⟫_ℂ := by
    intro v w v' w'
    rw [← hBc, hBsymm, hBc, map_mul, inner_conj_symm]
  obtain ⟨x0, hx0⟩ := exists_ne (0 : H)
  set e : H := ((‖x0‖ : ℂ))⁻¹ • x0 with he
  have hn : ‖e‖ = 1 := by
    rw [he]
    exact norm_smul_inv_norm hx0
  have hee : ⟪e, e⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hne : e ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  let φ : G → ℝ := fun g => Complex.normSq (cf π e e g)
  have hφc : Continuous φ := Complex.continuous_normSq.comp (continuous_const.inner (hcont e))
  have hBφ : B e e e e = ((∫ g, φ g ∂μ : ℝ) : ℂ) := by
    show ∫ g, cf π e e g * star (cf π e e g) ∂μ = _
    rw [← integral_complex_ofReal]
    congr 1
    funext g
    simp only [φ, RCLike.star_def, Complex.mul_conj]
  have hφi : Integrable φ μ := by
    have h2 := (memLp_two_iff_integrable_sq_norm (hL2 e e).1).mp (hL2 e e)
    refine h2.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [φ, cf, Complex.normSq_eq_norm_sq]
  have hφpos : 0 < ∫ g, φ g ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hφi]
    apply hφc.isOpen_support.measure_pos μ
    refine ⟨1, ?_⟩
    simp [φ, cf, hee, hne]
  refine ⟨(∫ g, φ g ∂μ)⁻¹, inv_pos.mpr hφpos, fun v w v' w' => ⟨integrable_cf π hL2 v w v' w', ?_⟩⟩
  have hκ : conj (c e e) = ((∫ g, φ g ∂μ : ℝ) : ℂ) := by
    have h1 := hBc e e e e
    rw [hee, mul_one] at h1
    have h2 := hrel e e e e
    rw [hee, mul_one, mul_one] at h2
    rw [← h2, ← h1, hBφ]
  have hcw : c w w' = conj (c e e) * ⟪w, w'⟫_ℂ := by
    have h3 := hrel e w e w'
    rwa [hee, mul_one] at h3
  show B v w v' w' = _
  rw [hBc, hcw, hκ, Complex.ofReal_inv, div_inv_eq_mul]
  ring
end PIW.HCFdeg
