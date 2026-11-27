-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.thmA_ainf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:04.799333+00:00
-- url     : https://prove2.me/submissions/b9e34e53-3913-447f-85aa-3986497c3857

import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Theorems.Thm_ReciprocityTheory_PGsh_thmAFull


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
theorem _root_.solution (B : BX (R0 p O ε)) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) :
    ThmAFullStatement B (ainfTower p O hv ε hε) := by
  exact thmAFull B hB1 hB3 _
end ReciprocityTheory.PGsh.Ainf
