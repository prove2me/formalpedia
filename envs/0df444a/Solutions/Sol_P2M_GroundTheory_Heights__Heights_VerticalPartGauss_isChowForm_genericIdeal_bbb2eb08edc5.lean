-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isChowForm_genericIdeal_bbb2eb08edc5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:59.761694+00:00
-- url     : https://prove2.me/submissions/15499e94-0149-4c23-9632-00ae48aa06c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_proof_14040d77a0cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_proof_775875bd000c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowForm_C_mul_941588753c43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RadicalBaseChange_proof_fda9669ff964


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.VerticalPartGauss
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)
namespace GroundTheory.Heights₂.Heights.VerticalPartGauss
theorem _root_.solution {n e δ : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P (e + 1))
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) :
    IsChowForm (genericIdeal P) (e + 1) f := by
  obtain ⟨c, hc, g, hcg, hg⟩ := ObjectsChow.ComplexChowFormToChowForm.proof n e δ P _ hP hf
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hg.1
  have hcoef := congrArg (coeff m) hcg
  rw [coeff_map, coeff_C_mul, coeff_map] at hcoef
  have hm' : ((g.coeff m : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hcq : c = ((f.coeff m / g.coeff m : ℚ) : ℂ) := by
    rw [Rat.cast_div, eq_div_iff hm']
    simpa using hcoef.symm
  have hfq : f = C (f.coeff m / g.coeff m) * g := by
    apply map_injective (Rat.castHom ℂ) (Rat.castHom ℂ).injective
    rw [hcg, map_mul, map_C, hcq]
    rfl
  have hq : f.coeff m / g.coeff m ≠ 0 := by
    intro h
    apply hc
    rw [hcq, h, Rat.cast_zero]
  rw [hfq]
  exact ObjectsChow.isChowForm_C_mul hg hq
end GroundTheory.Heights₂.Heights.VerticalPartGauss
