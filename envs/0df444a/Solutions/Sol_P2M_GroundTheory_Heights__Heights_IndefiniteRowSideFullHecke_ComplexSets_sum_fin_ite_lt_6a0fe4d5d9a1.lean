-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sum_fin_ite_lt_6a0fe4d5d9a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:31:02.437323+00:00
-- url     : https://prove2.me/submissions/11946ac5-bf17-496a-b12b-aab89c85f605

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Finset
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) (f : ℕ → ℂ) :
    ∑ j : Fin n, (if (j : ℕ) < m then f j else 0) = ∑ j ∈ range m, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then f j else 0) n, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
