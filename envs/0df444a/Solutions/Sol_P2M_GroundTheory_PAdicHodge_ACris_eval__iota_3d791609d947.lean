-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_ACris_eval__iota_3d791609d947
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:16.478556+00:00
-- url     : https://prove2.me/submissions/762d0551-764e-4610-9039-7c45ace68b22

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (m : ℕ) (y : ACris K p) :
    _root_.AdicCompletion.evalₐ (kerAway K p) m (iota K p y) = iotaQ K p m y :=
  _root_.AdicCompletion.evalₐ_liftRingHom _ _ _ m y
end GroundTheory.PAdicHodge.ACris
