-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.zeta_succ_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:56:51.455287+00:00
-- url     : https://prove2.me/submissions/05271626-e661-4d5d-a0c1-a712b04d57e3

import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_root_succ_pow

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
theorem _root_.solution (n : ℕ) : zetaV p O ε (n + 1) ^ p = zetaV p O ε n := by
  rw [zetaV, zetaV, ← map_pow, ← map_pow, root_succ_pow]
end ReciprocityTheory.PGsh.Ainf
