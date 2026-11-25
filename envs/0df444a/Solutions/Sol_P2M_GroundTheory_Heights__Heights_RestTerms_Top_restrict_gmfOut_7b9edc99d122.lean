-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrict_gmfOut_7b9edc99d122
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:27.204949+00:00
-- url     : https://prove2.me/submissions/0f6bc8a2-1ff9-4266-878e-6ef85996a2f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrictToBlock_blockEmb_d48514eb86a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_eq_mstar_of_205773e62c79
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_blockOut_1bbd3daf3e2a


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
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (hq : ∀ σ, σ ≠ τ → q σ ≤ r * a)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    restrictToBlock f (r + a) τ (gmfOut f r a c κ q e) =
      ((Nat.multinomial Finset.univ (mstar f r a q e τ) : ℚ) *
          ∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) •
        toN (r + a) (blockOut r a c κ (q τ) (mstar f r a q e τ τ)) := by
  rw [gmfOut, map_sum]
  rw [Finset.sum_eq_single (mstar f r a q e τ)]
  · rw [map_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    rw [restrictToBlock_blockEmb, if_pos rfl]
    have : ∏ x ∈ Finset.univ.erase τ, restrictToBlock f (r + a) τ
        (blockEmb f (r + a) x (blockOut r a c κ (q x) (mstar f r a q e τ x))) =
        C (∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun σ hσ => ?_
      have hne := Finset.ne_of_mem_erase hσ
      rw [restrictToBlock_blockEmb, if_neg hne, constantCoeff_blockOut]
      simp only [mstar, if_neg hne]
      rw [if_pos (by have := hq σ hne; omega)]
    rw [this, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_natCast]
    ring
  · intro m hm hne
    obtain ⟨σ, hστ, hσ⟩ : ∃ σ, σ ≠ τ ∧ m σ ≠ r * a - q σ := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_mstar_of f r a q e τ m hm hcon)
    rw [map_smul, map_prod, Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]
    rw [restrictToBlock_blockEmb, if_neg hστ, constantCoeff_blockOut, if_neg, map_zero]
    have := hq σ hστ
    omega
  · intro h
    exact absurd (mstar_mem f r a q e τ he) h
end GroundTheory.Heights₂.Heights.RestTerms.Top
