-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_volU_succ__cd99a22eae0a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:46.486081+00:00
-- url     : https://prove2.me/submissions/2fdf954c-dac7-4db5-9728-325129f329ff

import Definitions.Def_Formalism_FlagUnipotentLattices_UnitSumBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ConstantProductFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (j : ℕ) : volU (j + 1) = volU j * ((2 * Real.pi) ^ (j + 1) / (j.factorial : ℝ)) := by
  unfold volU
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp
end Formalism.HermitianLatticeCounting.P
