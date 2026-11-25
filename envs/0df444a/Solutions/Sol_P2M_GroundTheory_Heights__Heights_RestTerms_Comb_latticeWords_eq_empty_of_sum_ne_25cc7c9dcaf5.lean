-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_latticeWords_eq_empty_of_sum_ne_25cc7c9dcaf5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:46.027137+00:00
-- url     : https://prove2.me/submissions/4faedafb-7e3f-4086-9169-2a5ab105b6fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sum_pcnt_3ec33b1f59f4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
open scoped Classical
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (n : ℕ) (lam : Fin m → ℕ) (h : ∑ i, lam i ≠ n) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  rw [← sum_pcnt w]
  exact Finset.sum_congr rfl fun i _ => (hw.2 i).symm
end GroundTheory.Heights₂.Heights.RestTerms.Comb
