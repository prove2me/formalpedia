-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogIdeal_genericIdeal_0eabf1506c24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:43.80789+00:00
-- url     : https://prove2.me/submissions/1f9cbe60-4328-4b09-864e-991c4a89256f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsHomogeneousOfIsMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogeneous_of_isMultiHomog_5953ec960bf0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_map_baf010c3c500


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
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hS, rfl⟩ := hP.2.1.2.1
  let E : MRing (PBlk n) ≃+* MvPolynomial (Fin n) ℤ :=
    (renameEquiv ℤ (Equiv.uniqueSigma (PBlk n))).toRingEquiv
  have hfin : IndefiniteRowSideFullHecke.ArithBezout.finIdeal (Ideal.span S) = (Ideal.span S).map E := by
    rw [← Ideal.comap_symm]
    rfl
  have hhom : IsHomogIdeal (IndefiniteRowSideFullHecke.ArithBezout.finIdeal (Ideal.span S)) := by
    rw [isHomogIdeal_iff, hfin, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hS s hs
    exact ⟨a (), (mem_homogeneousSubmodule _ _).mpr
      ((isHomogeneous_of_isMultiHomog ha).rename_isHomogeneous)⟩
  exact isHomogIdeal_map (Int.castRingHom ℚ) hhom
end GroundTheory.Heights₂.Heights.ObjectsChow
