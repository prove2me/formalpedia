-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isHomog_b53edbad69d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:26.054422+00:00
-- url     : https://prove2.me/submissions/7264ac33-fe49-4740-911f-cefb4f719cf6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isHomogeneous_of_isMultiHomog_bf28aa3e9343
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_eq_span_28202021c411

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
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.VerticalPartGauss
theorem _root_.solution {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hSh, hS⟩ := hP.2.1.2.1
  have hspan : genericIdeal P = Ideal.span ((fun s => map (Int.castRingHom ℚ)
      (rename (blkEquiv n).symm s)) '' S) := by
    rw [ObjectsChow.genericIdeal, finIdeal_eq_span hS, Ideal.map_span, ← Set.image_comp]
    rfl
  have hhom : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
    rw [hspan]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hSh s hs
    exact ⟨a (), (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_of_isMultiHomog ha)⟩
  intro f hf i
  have := hhom i hf
  rwa [← decomposition.decompose'_apply]
end GroundTheory.Heights₂.Heights.VerticalPartGauss
