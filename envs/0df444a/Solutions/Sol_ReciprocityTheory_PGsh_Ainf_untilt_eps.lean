-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.untilt_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:54.486635+00:00
-- url     : https://prove2.me/submissions/d3d6ee29-8864-4cd0-8e21-2a9ff88b43e9

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts

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
theorem _root_.solution : ε.untilt = 1 := by
  have he : ε = ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ p := by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  rw [he, map_pow, hε.pow_eq_one]
end ReciprocityTheory.PGsh.Ainf
