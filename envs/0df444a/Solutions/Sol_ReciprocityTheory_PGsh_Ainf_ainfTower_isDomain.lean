-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.ainfTower_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:31:29.965432+00:00
-- url     : https://prove2.me/submissions/127315e7-67db-443e-8734-9cb80a3f14a6

import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution : IsDomain ((ainfTower p O hv ε hε).O : Type) := by
  show IsDomain O
  exact Function.Injective.isDomain (algebraMap O C) hv.hom_inj
end ReciprocityTheory.PGsh.Ainf
