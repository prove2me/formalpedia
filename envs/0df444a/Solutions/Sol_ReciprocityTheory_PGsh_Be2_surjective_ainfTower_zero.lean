-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Be2.surjective_ainfTower_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:14.678835+00:00
-- url     : https://prove2.me/submissions/34dbf39f-5ef9-4251-8ceb-685556fd0a14

import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
namespace ReciprocityTheory.PGsh.Be2
theorem _root_.solution : Function.Surjective ((ainfTowerL p O hv ε hε).q 0).1 :=
  fun y => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O) ^ (0 + 1)}) y
end ReciprocityTheory.PGsh.Be2
