-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rows_rpow_pow_7d3f75c3e74b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:06.201797+00:00
-- url     : https://prove2.me/submissions/12eb422a-80f1-4139-a0b6-1bade58a371d

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open Formalism.HermitianLatticeCounting
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {b : ℝ} (hb : 0 < b) (x : ℝ) (n : ℕ) : (b ^ x) ^ n = b ^ (x * n) := by
  first
    | exact (Real.rpow_mul_natCast hb.le x n).symm
    | (rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le])
end Formalism.MainNotions.BridgeLemma₂
