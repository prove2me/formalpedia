-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.root_succ_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:45:23.576999+00:00
-- url     : https://prove2.me/submissions/29319f43-b401-423e-a112-56d602ed11e0

import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat

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
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (k : ℕ) : root p O ε (k + 1) ^ p = root p O ε k := by
  show ((frobeniusEquiv (PreTilt O p) p).symm^[k + 1] ε) ^ p = _
  rw [Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl
end ReciprocityTheory.PGsh.Ainf
