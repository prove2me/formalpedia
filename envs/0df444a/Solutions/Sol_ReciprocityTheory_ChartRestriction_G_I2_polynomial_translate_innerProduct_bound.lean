-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.polynomial_translate_innerProduct_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:26:32.289729+00:00
-- url     : https://prove2.me/submissions/cd2a0430-e181-4200-bde7-ff0178634a29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paIsPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paTR_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paFock_cv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_eq_inner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fockU_coeff_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    ‖paIP q (paU q a F) G‖ ≤ 2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
      Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) * paN q F * paN q G := by
  set s : ℝ := Real.sqrt (q * Real.pi) with hs
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt (by positivity)
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  have hqpi : (q : ℂ) * (Real.pi : ℂ) = (s : ℂ) ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← hs2]
    push_cast
    ring

  set a' : EuclideanSpace ℂ (Fin (Fintype.card ι)) := s • (paT (ι := ι)).symm a with ha'
  have hna : ‖a'‖ = s * ‖a‖ := by
    rw [ha', norm_smul, Real.norm_eq_abs, abs_of_pos hs0, LinearIsometryEquiv.norm_map]
  have hT : paT (s • (paT (ι := ι)).symm a) = s • a := by
    rw [← paTR_apply, map_smul, paTR_apply, LinearIsometryEquiv.apply_symm_apply]
  have hU : (fun z => paU q a F (s⁻¹ • paT z)) = fockU a' (fun z => F (s⁻¹ • paT z)) := by
    ext z
    unfold paU fockU
    congr 1
    · congr 1
      rw [hna, show (∑ i, z i * (starRingEnd ℂ) (a' i)) = Hf z a' from rfl, Hf_eq_inner, Hf_eq_inner,
        Hf_eq_inner, ← Complex.coe_smul s⁻¹ (paT z), inner_smul_right, ha',
        ← Complex.coe_smul s, inner_smul_left, inner_self_eq_norm_sq_to_K,
        ← (paT (ι := ι)).inner_map_map, LinearIsometryEquiv.apply_symm_apply, hqpi]
      simp only [Complex.conj_ofReal]
      push_cast
      field_simp
      first
      | rfl
      | ring
    · congr 1
      rw [map_sub, hT, smul_sub, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
  have hF' := paIsPoly s⁻¹ hF
  have hG' := paIsPoly s⁻¹ hG
  have hB := fockU_coeff_le a' _ _ hF' hG'
  rw [← hU, paFock_cv hq, paFock_cv hq, paFock_cv hq] at hB
  have hqn : (0 : ℝ) < (q : ℝ) ^ Fintype.card ι := by positivity
  have hre : ∀ H : EuclideanSpace ℂ ι → ℂ,
      Real.sqrt ((q : ℂ) ^ Fintype.card ι * paIP q H H).re =
        Real.sqrt ((q : ℝ) ^ Fintype.card ι) * paN q H := by
    intro H
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Real.sqrt_mul hqn.le]
    rfl
  rw [hre, hre, norm_mul, norm_pow, Complex.norm_natCast, hna] at hB
  have hsq : Real.sqrt ((q : ℝ) ^ Fintype.card ι) * Real.sqrt ((q : ℝ) ^ Fintype.card ι) =
      (q : ℝ) ^ Fintype.card ι := Real.mul_self_sqrt hqn.le
  have hexp : Real.exp (-(s * ‖a‖) ^ 2 / 16) = Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) := by
    rw [mul_pow, hs2]
    ring_nf
  rw [hexp] at hB
  have hB' : (q : ℝ) ^ Fintype.card ι * ‖paIP q (paU q a F) G‖ ≤ (q : ℝ) ^ Fintype.card ι *
      (2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
        Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) * paN q F * paN q G) := by
    calc _ ≤ _ := hB
      _ = _ := by
        linear_combination (2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
          Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) * paN q F * paN q G) * hsq
  exact le_of_mul_le_mul_left hB' hqn
end ReciprocityTheory.ChartRestriction.G.I2
