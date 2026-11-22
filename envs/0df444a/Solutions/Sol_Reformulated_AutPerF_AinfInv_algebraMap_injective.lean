-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:16:41.223067+00:00
-- url     : https://prove2.me/submissions/fac30593-5784-4347-81b8-3a5132b3eab5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution : Function.Injective (algebraMap (Ainf p R) (AinfInv p R)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors Ainf.p_ne_zero)
end Reformulated.AutPerF.AinfInv
