-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_class_sum_3b7d7a5b3ec6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:53.590694+00:00
-- url     : https://prove2.me/submissions/7a013af4-c301-43b1-9827-949f584ea471

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_realEisenstein_eq_tsum_1d2f5bf29f0e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eisTerm_nonneg_e6d069c6df72
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_summable_eisTerm_c032e00307cd
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_psi_f565265bd92d
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_absNorm_psi_b9d8f94c9e99
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_rpow_identity_846bbc1944ac
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_pairToLattice_bijective_0c88b201f33f
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eltToLattice_bijective_a2eb0a9320c3
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_discr_neg_and_absNorm_mul_efde573e849a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) {s : ℝ}
    (hs : 1 < s) :
    (Units.torsionOrder K : ENNReal) * ∑' t : InvClassIdeals J,
        ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
      ENNReal.ofReal ((2 / Real.sqrt |(discr K : ℝ)|) ^ s * realEisenstein τ s) := by
  rw [← tsum_psi hK σ hσ J (fun t => ENNReal.ofReal
    ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)))]
  obtain ⟨hD, hcov⟩ := discr_neg_and_absNorm_mul hK σ hσ (↑ᶠ J) τ c hc himg
  set q := Real.sqrt |(discr K : ℝ)| with hqdef
  have hq : 0 < q := Real.sqrt_pos.mpr (abs_pos.mpr hD.ne)
  have hy := τ.im_pos
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set F : NzLattice τ → ENNReal :=
    fun z => ENNReal.ofReal ((2 / q) ^ s * (τ.im ^ s / ‖(z : ℂ)‖ ^ (2 * s))) with hF
  have hterm : ∀ x : Nz J, ENNReal.ofReal
      ((Ideal.absNorm ((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
        F (eltToLattice σ J τ c hc himg x) := by
    intro x
    rw [absNorm_psi hK σ hσ J x, hF]
    congr 1
    have hx0 : σ (x : K) ≠ 0 := (map_ne_zero σ).mpr x.2.2
    have hN : ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) = 2 * τ.im / (q * ‖c‖ ^ 2) := by
      rw [eq_div_iff (by positivity)]
      rw [eq_div_iff hq.ne'] at hcov
      linear_combination hcov
    have h3 : ‖σ (x : K)‖ ^ 2 / ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) =
        ‖c * σ (x : K)‖ ^ 2 * q / (2 * τ.im) := by
      rw [hN, norm_mul]
      field_simp
    rw [h3]
    exact rpow_identity (norm_pos_iff.mpr (mul_ne_zero hc hx0)) hq hy s
  rw [tsum_congr hterm]
  have e1 := (Equiv.ofBijective _ (eltToLattice_bijective σ J τ c hc himg)).tsum_eq F
  simp only [Equiv.ofBijective_apply] at e1
  rw [e1]
  have e2 := (Equiv.ofBijective _ (pairToLattice_bijective τ)).tsum_eq F
  simp only [Equiv.ofBijective_apply] at e2
  rw [← e2]
  have hG : ∀ p : NzPair, F (pairToLattice τ p) =
      ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p.1) := by
    intro p
    simp only [hF, pairToLattice, eisTerm, if_neg p.2]
  rw [tsum_congr hG]
  have hsupp : Function.support (fun p : ℤ × ℤ => ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p)) ⊆
      {p | p ≠ 0} := by
    intro p hp h0
    apply hp
    have h0' : p = 0 := by simpa using h0
    simp [h0', eisTerm]
  have e3 := tsum_subtype_eq_of_support_subset hsupp
  change ∑' p : {p : ℤ × ℤ // p ≠ 0}, _ = _
  rw [show (∑' p : {p : ℤ × ℤ // p ≠ 0}, ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p.1)) =
    ∑' p : ({p | p ≠ 0} : Set (ℤ × ℤ)), ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p) from rfl, e3,
    ← ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg (by positivity) (eisTerm_nonneg τ s p))
      ((summable_eisTerm τ hs).mul_left _), tsum_mul_left, realEisenstein_eq_tsum]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
