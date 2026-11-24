-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_mem_finsuppAntidiag_univ_iff_5c8a1f46e0c6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:46.171296+00:00
-- url     : https://prove2.me/submissions/3a6492f3-ae2b-4454-876d-4b19c4f2a0cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus
namespace GroundTheory.Heights₂.Heights.IncidenceZeroLocus
theorem _root_.solution {n N : ℕ} (f : Fin n →₀ ℕ) :
    f ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag N ↔ f.degree = N := by
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
end GroundTheory.Heights₂.Heights.IncidenceZeroLocus
