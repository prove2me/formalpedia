-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.c_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:34:50.657847+00:00
-- url     : https://prove2.me/submissions/6e297fe9-96b3-4112-90b7-de225b6f1151

import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Theorems.Thm_ReciprocityTheory_PGsh_a0


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
include hv hε
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution : v (algebraMap O C (fontaineTheta O p (nu p O ε))) ^ (p - 1) = v (p : C) := by
  obtain ⟨-, -, -, hX, -, -⟩ := a0 p C v O hv
  exact (hX ε hv hε).2.2.1
end ReciprocityTheory.PGsh.Ainf
