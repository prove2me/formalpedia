-- Prove2me | solution 1 for P2M_GlobalTheory_EisBL_NilAlg_blk_map__4db2ce721b87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:39.294464+00:00
-- url     : https://prove2.me/submissions/b0bf58e7-5478-4dd8-b85e-f11ad5a4026b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution {B' : Type} [CommRing B'] (f : B →+* B') (X : Matrix n n B) : (blk X).map f = blk (X.map f) := by
  have e : ∀ M : Matrix n n B, M.map f = f.mapMatrix M := fun _ => rfl
  simp only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]
end GlobalTheory.EisBL.NilAlg
