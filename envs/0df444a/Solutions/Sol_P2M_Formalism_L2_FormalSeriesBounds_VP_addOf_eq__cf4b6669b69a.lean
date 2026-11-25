-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_VP_addOf_eq__cf4b6669b69a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:42.479842+00:00
-- url     : https://prove2.me/submissions/d4efa017-98ec-4468-b0a6-a3335e9c03d1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by
  unfold addAt
  unfold addOf
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; unfold P2; rfl)
  | (congr 1; funext q; unfold P2; obtain ⟨j, k⟩ := q; fin_cases j <;> simp)
end Formalism.L2.FormalSeriesBounds.VP
