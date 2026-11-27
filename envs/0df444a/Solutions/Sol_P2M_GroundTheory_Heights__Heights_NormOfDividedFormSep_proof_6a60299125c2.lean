-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_proof_6a60299125c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:49.633622+00:00
-- url     : https://prove2.me/submissions/6a4f7560-5610-4670-91ff-5ed006832621

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PNormOfDividedFormSep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_algebraMap_sum_smul_e225fa246b95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_adjoin_range_eq_top_635c10f15b7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormOfDividedFormSep_algebraMap_det_mulLeft_6b74d38cd8fc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped nonZeroDivisors
noncomputable section
open NormOfDividedFormSep
namespace GroundTheory.Heights₂.Heights
namespace NormOfDividedFormSep
theorem _root_.solution (hEval : NormFormEval.Statement) (hDvd : NormFormDvd.Statement)
    (hPrime : PrimeMapFractionRing.Statement) : NormOfDividedFormSep.Statement := by
  intro O B _ _ _ _ _ _ _ _ n η t P hsep hgen ht hP hdvd u
  let K := FractionRing O
  let L := FractionRing B
  let _ : Algebra K L := FractionRing.liftAlgebra O L
  have : IsScalarTower O K L := FractionRing.isScalarTower_liftAlgebra O L
  have : FiniteDimensional K L := .of_isLocalization O B O⁰
  have : Algebra.IsSeparable K L := hsep
  have hOB : Function.Injective (algebraMap O B) := FaithfulSMul.algebraMap_injective O B
  have hOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have : Infinite K := Infinite.of_injective _ hOK
  let ηL : Fin n → L := fun m => algebraMap B L (η m)
  let tK : Fin n → K := fun m => algebraMap O K (t m)
  have htL : ∑ m, tK m • ηL m = 1 := by
    rw [← algebraMap_sum_smul, ht, map_one]

  have hdvdL : (∑ m, X m * C (ηL m)) ∣ map (algebraMap K L) (map (algebraMap O K) P) := by
    have h := _root_.map_dvd (MvPolynomial.map (algebraMap B L)) hdvd
    rw [map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq O K L, ← map_map, map_sum] at h
    simpa only [map_mul, map_X, map_C] using h

  have hnc : ∀ a : O, P ≠ C a := by
    rintro a rfl
    obtain ⟨g, hg⟩ := hdvd
    have h := congrArg (eval 0) hg
    simp only [map_C, eval_C, map_mul, map_sum, eval_X, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
    exact hP.ne_zero (by rw [(map_eq_zero_iff _ hOB).1 h, map_zero])

  obtain ⟨c, hc⟩ := hDvd K L n ηL tK _ (adjoin_range_eq_top η hgen) htL hdvdL
  have hNt : eval tK (normForm K L ηL) = 1 := by
    rw [hEval K L n ηL, htL, map_one]
  have hN0 : ¬ IsUnit (normForm K L ηL) := by
    intro h
    have h0 := h.map (eval (0 : Fin n → K))
    rw [hEval K L n ηL] at h0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, Algebra.norm_zero] at h0
    exact not_isUnit_zero h0
  have hcu : IsUnit c := ((hPrime O K n P hP hnc).irreducible.isUnit_or_isUnit hc).resolve_left hN0
  obtain ⟨c₀, -, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hcu
  have hev : ∀ v : Fin n → O, eval (fun m => algebraMap O K (v m)) (map (algebraMap O K) P) =
      algebraMap O K (eval v P) := fun v => by
    rw [eval_map]
    exact (eval₂_comp_left (algebraMap O K) (RingHom.id O) v P).symm
  have hct : c₀ = algebraMap O K (eval t P) := by
    have h := congrArg (eval tK) hc
    rw [map_mul, hNt, eval_C, one_mul] at h
    rw [← h, hev]
  apply hOK
  have h := congrArg (eval (fun m => algebraMap O K (u m))) hc
  rw [map_mul, eval_C, hct, hev] at h
  rw [map_mul, algebraMap_det_mulLeft (L := L) hEval η u, h, mul_comm]
end NormOfDividedFormSep
end GroundTheory.Heights₂.Heights
