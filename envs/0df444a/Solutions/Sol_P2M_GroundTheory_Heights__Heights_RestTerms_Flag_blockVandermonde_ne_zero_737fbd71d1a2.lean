-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockVandermonde_ne_zero_737fbd71d1a2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:05.448579+00:00
-- url     : https://prove2.me/submissions/963a7a9d-60dc-4bb0-9cdf-5e345c4d381f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f N : ℕ) : blockVandermonde f N ≠ 0 := by
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_ne_zero_iff.mpr (fun τ _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)))
  rw [sub_ne_zero]
  intro h
  have := X_injective h
  simp only [Prod.mk.injEq, true_and] at this
  rw [Finset.mem_Ioi] at hj
  exact (ne_of_lt hj) this
end GroundTheory.Heights₂.Heights.RestTerms.Flag
