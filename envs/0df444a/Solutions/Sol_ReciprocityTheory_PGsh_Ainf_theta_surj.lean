-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.theta_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:04:22.809819+00:00
-- url     : https://prove2.me/submissions/982436a5-a4ff-402d-bba7-f6f71dc6833d

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_frob_surj

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
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (hv : v.Integers O) : Function.Surjective (fontaineTheta O p) :=
  surjective_fontaineTheta (frob_surj p O hv)
end ReciprocityTheory.PGsh.Ainf
