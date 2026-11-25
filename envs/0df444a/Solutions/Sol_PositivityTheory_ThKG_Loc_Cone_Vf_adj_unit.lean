-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.adj_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:46.719118+00:00
-- url     : https://prove2.me/submissions/1e7904a0-1b89-4490-aabf-e8be7ad0d852

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}
namespace PositivityTheory.ThKG.Loc.Cone.Vf
theorem _root_.solution (k : UG c J) : Adj c J (k.1 : Matrix β β A) (k⁻¹).1 := by
  have h : (k.1 : Matrix β β A)ᵀ * J * (k.1 : Matrix β β A).map c = J := k.2
  have h1 : (k.1 : Matrix β β A) * ((k⁻¹).1 : Matrix β β A) = 1 := k.1.mul_inv
  unfold Adj
  calc (k.1 : Matrix β β A)ᵀ * J = (k.1 : Matrix β β A)ᵀ * J * ((k.1 : Matrix β β A).map c * ((k⁻¹).1 : Matrix β β A).map c) := by
        rw [← mapc_mul, h1, mapc_one, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h]
end PositivityTheory.ThKG.Loc.Cone.Vf
