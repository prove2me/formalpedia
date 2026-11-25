-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_one_9cea0c74fd23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:04.183149+00:00
-- url     : https://prove2.me/submissions/f56fdfd3-cdd4-40cb-903d-cee83ba69cec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLinearTermValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9


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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (r : ℕ) (hr : 1 ≤ r) : partitionsOf r 1 = {rowOne r} := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  ext lam
  rw [mem_partitionsOf_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, ha⟩
    rw [Fin.sum_univ_succ] at hs
    have hle : ∀ i : Fin r', lam i.succ ≤ lam 0 := fun i => ha (Fin.zero_le _)
    have h0 : lam 0 = 1 := by
      by_contra h
      have hz : lam 0 = 0 := by omega
      have : ∑ i : Fin r', lam i.succ = 0 :=
        Finset.sum_eq_zero fun i _ => by have := hle i; omega
      omega
    have hrest : ∑ i : Fin r', lam i.succ = 0 := by omega
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rowOne, h0]
    · have := Finset.sum_eq_zero_iff.mp hrest j (Finset.mem_univ j)
      simp [rowOne, this]
  · rintro rfl
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Fin.sum_univ_succ]
      simp [rowOne]
    · simp only [rowOne]
      split_ifs with h1 h2 <;> first | omega | (exfalso; have : (i : ℕ) ≤ j := hij; omega)
end GroundTheory.Heights₂.Heights.RestTerms.Top
