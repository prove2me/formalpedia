-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RecQOfRecursion_step_203b02825f9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:56:51.295418+00:00
-- url     : https://prove2.me/submissions/2945f3b2-bb94-4606-8bc9-124362715032

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_ne_zero_of_isChowFormCycle_98bd857a68c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_integral_eq_857bb0c640d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_of_isChowForm_129f76209172
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isChowForm_genericIdeal_bbb2eb08edc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isProjPrime_genericIdeal_2708c8f68489
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_linForm_not_mem_genericIdeal_6fe79e6359ca


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
theorem _root_.solution (hRec : ChowHeightRecursionRat.Statement) (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
                              chowHt (archData S hS hconj) e δ (specFirst f fun j => (u j : ℚ)) +
                                (IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u) -
                                  arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
                                    (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)) ∧
      IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) e
        (specFirst f fun j => (u j : ℚ)) := by
  have hprime := VerticalPartGauss.isProjPrime_genericIdeal hP
  have hfA := VerticalPartGauss.isChowForm_genericIdeal hP hf
  have huA := VerticalPartGauss.linForm_not_mem_genericIdeal hP hu
  have hcyc := hSec ℚ n e (ObjectsChow.genericIdeal P) f _ hprime hfA huA
  have hcast : ∀ j, (((u j : ℤ) : 𝓞 ℚ) : ℚ) = (u j : ℚ) := fun j => by simp
  have key := hRec n e δ (archData S hS hconj) (ObjectsChow.genericIdeal P) f
    (fun j => ((u j : ℤ) : 𝓞 ℚ)) hprime hfA (ObjectsChow.isMultiHomog_of_isChowForm hf)
    (by simp only [hcast]; exact huA)
  simp only [hcast] at key
  refine ⟨?_, hcyc⟩
  rw [← ObjectsHeight.chowHt_eq_chowHeight (archData S hS hconj) S hS
      (fun _ u => ObjectsHeight.ofPointMatrix_norm S hS u), key, hV n e P u hP hu,
    integral_eq hC hI S hS hconj hP hf (ne_zero_of_isChowFormCycle hcyc), Module.finrank_self]
  simp
end GroundTheory.Heights₂.Heights.RecQOfRecursion
