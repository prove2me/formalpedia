-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_dedekindZeta_eq_sum_realEisenstein_899175d53bfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:59.643962+00:00
-- url     : https://prove2.me/submissions/389dd55c-2ae2-433b-823a-529cc56ca3ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_ofReal_dedekindZetaReal_10d78e70b478
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_ideal_eq_sum_class_0199de70b461
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_class_sum_3b7d7a5b3ec6
import Theorems.Thm_GroundTheory_Global_dedekindZetaTerm_nonneg
import Theorems.Thm_GroundTheory_Global_dedekindZeta_ofReal
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_realEisenstein_nonneg_23a9db672901


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
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (τ : ClassGroup (𝓞 K) → ℍ)
    (hτ : ∀ A, ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = A ∧
      IsLatticeParam (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) (τ A))
    {s : ℝ} (hs : 1 < s) :
    NumberField.dedekindZeta K s =
      (((NumberField.Units.torsionOrder K : ℝ)⁻¹ * (2 / Real.sqrt |(NumberField.discr K : ℝ)|) ^ s *
        ∑ A : ClassGroup (𝓞 K), realEisenstein (τ A) s : ℝ) : ℂ) := by
  classical
  rw [GroundTheory.Global.dedekindZeta_ofReal K (by linarith : s ≠ 0)]
  congr 1
  set q := Real.sqrt |(discr K : ℝ)| with hqdef
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hcl : ∀ A : ClassGroup (𝓞 K),
      ∑' t : (ClassGroup.mk0 ⁻¹' {A⁻¹} : Set (Ideal (𝓞 K))⁰),
        ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
      ENNReal.ofReal ((Units.torsionOrder K : ℝ)⁻¹ * ((2 / q) ^ s * realEisenstein (τ A) s)) := by
    intro A
    obtain ⟨J, hJ, c, hc, himg⟩ := hτ A
    have h := class_sum hK σ hσ J (τ A) c hc himg hs
    subst hJ
    have hw0 : (Units.torsionOrder K : ENNReal) ≠ 0 := by
      exact_mod_cast (Units.torsionOrder_ne_zero K)
    have hwt : (Units.torsionOrder K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hw.le), ENNReal.ofReal_inv_of_pos hw,
      ENNReal.ofReal_natCast, ← ENNReal.div_eq_inv_mul, ENNReal.eq_div_iff hw0 hwt]
    exact h
  have hnn : ∀ A : ClassGroup (𝓞 K),
      0 ≤ (Units.torsionOrder K : ℝ)⁻¹ * ((2 / q) ^ s * realEisenstein (τ A) s) := fun A =>
    mul_nonneg (inv_nonneg.mpr hw.le) (mul_nonneg (by positivity) (realEisenstein_nonneg _ _))
  have hmain : ENNReal.ofReal (GroundTheory.Global.dedekindZetaReal K s) =
      ENNReal.ofReal ((Units.torsionOrder K : ℝ)⁻¹ * (2 / q) ^ s *
        ∑ A : ClassGroup (𝓞 K), realEisenstein (τ A) s) := by
    rw [ofReal_dedekindZetaReal K hs, tsum_ideal_eq_sum_class K (by linarith),
      (Fintype.sum_equiv (Equiv.inv (ClassGroup (𝓞 K)))
        (fun A => ∑' t : (ClassGroup.mk0 ⁻¹' {A⁻¹} : Set (Ideal (𝓞 K))⁰),
          ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)))
        (fun B => ∑' t : (ClassGroup.mk0 ⁻¹' {B} : Set (Ideal (𝓞 K))⁰),
          ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)))
        (fun A => rfl)).symm]
    rw [Finset.sum_congr rfl (fun A _ => hcl A), ← ENNReal.ofReal_sum_of_nonneg (fun A _ => hnn A),
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun A _ => ?_
    ring
  have h0 : 0 ≤ GroundTheory.Global.dedekindZetaReal K s :=
    tsum_nonneg (GroundTheory.Global.dedekindZetaTerm_nonneg K s)
  have h1 : 0 ≤ (Units.torsionOrder K : ℝ)⁻¹ * (2 / q) ^ s *
      ∑ A : ClassGroup (𝓞 K), realEisenstein (τ A) s :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hw.le) (by positivity))
      (Finset.sum_nonneg fun A _ => realEisenstein_nonneg _ _)
  exact (ENNReal.ofReal_eq_ofReal_iff h0 h1).mp hmain
end GroundTheory.Heights₂.Theta.projectiveLineClassData
