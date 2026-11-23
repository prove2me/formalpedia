-- Prove2me | solution 1 for P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:29.749806+00:00
-- url     : https://prove2.me/submissions/46d9a0a7-66fe-42a2-b464-a6d2d33935e3

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (N : ℕ) (c : Fin N → K) : 0 ≤ e3μ K N c := by
  unfold e3μ
  exact sqWeight_nonneg _
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
