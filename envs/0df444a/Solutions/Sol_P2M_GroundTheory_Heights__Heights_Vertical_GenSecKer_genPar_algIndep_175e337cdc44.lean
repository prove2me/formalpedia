-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_genPar_algIndep_175e337cdc44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:27.067044+00:00
-- url     : https://prove2.me/submissions/81af4da6-3038-48d4-aa71-449d6b529c87

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecKer
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecKer
theorem _root_.solution (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h
end GroundTheory.Heights₂.Heights.Vertical.GenSecKer
