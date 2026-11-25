-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecAlgField_genPar_algebraicIndependent_e5b691f6d8b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:07.634479+00:00
-- url     : https://prove2.me/submissions/d99a2b04-5d01-43ec-9d3e-fe890f345748

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgField

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgField
namespace GroundTheory.Heights₂.Heights.Vertical.SecAlgField
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
end GroundTheory.Heights₂.Heights.Vertical.SecAlgField
