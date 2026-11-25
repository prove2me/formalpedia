-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RecQOfRecursion_integral_eq_857bb0c640d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:50.343731+00:00
-- url     : https://prove2.me/submissions/6e11bf6b-df5a-462b-8dad-2f4b5dec9fd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivSuppHorizontalArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_HeightMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_map_genericIdeal_90ec9b2dcad1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_logFormNorm_eq_bab2e108a793
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_map_specFirst_60810c1809b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_specFirst_eq_27ac14c10d3e


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
noncomputable section
open GroundTheory.Heights₂.Heights.RecQOfRecursion
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RecQOfRecursion
theorem _root_.solution (hC : ComplexFibreCycle.Statement) (hI : ConeIntegralPts.Statement)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hsf : specFirst f (fun j => (u j : ℚ)) ≠ 0) :
    ∑ σ : ℚ →+* ℂ, cycleIntegral ((archData S hS hconj).normAt σ)
        (fundCycle ((ObjectsChow.genericIdeal P).map (MvPolynomial.map σ))) e
        (fsLog ((archData S hS hconj).normAt σ) fun j => σ (u j : ℚ)) =
      arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
        (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) := by
  have hu : (fun j => (Rat.castHom ℂ) (u j : ℚ)) = fun j => (u j : ℂ) := funext fun j => by simp
  rw [Fintype.sum_subsingleton _ (Rat.castHom ℂ), hu, map_genericIdeal]
  have hW : ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm (fun j => (u j : ℂ)) ∉ W := by
    refine ((hC n e δ P _ hP hf).2.2 _).mp ?_
    have h : IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℂ)) (map (Rat.castHom ℂ) f) =
        map (Rat.castHom ℂ) (specFirst f fun j => (u j : ℚ)) := by
      rw [ObjectsChow.specFirst_eq, ObjectsChow.map_specFirst, ← hu]
      rfl
    rw [h]
    exact fun h0 => hsf (map_injective _ (Rat.castHom ℂ).injective (by rw [h0, map_zero]))
  exact (hI n e S hS P _ hP hW).trans (by rw [logFormNorm_eq]; rfl)
end GroundTheory.Heights₂.Heights.RecQOfRecursion
