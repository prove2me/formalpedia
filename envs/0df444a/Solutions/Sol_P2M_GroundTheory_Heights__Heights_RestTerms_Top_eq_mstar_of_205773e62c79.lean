-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_eq_mstar_of_205773e62c79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:14.394204+00:00
-- url     : https://prove2.me/submissions/7912ea11-614c-45da-96bb-15e26666d467

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue

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
theorem _root_.solution (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) (m : Fin f → ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e)
    (h : ∀ σ, σ ≠ τ → m σ = r * a - q σ) : m = mstar f r a q e τ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    rw [Finset.mem_piAntidiag] at hm
    have hs := hm.1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ)] at hs
    have : ∑ x ∈ Finset.univ.erase σ, m x = ∑ σ' ∈ Finset.univ.erase σ, (r * a - q σ') :=
      Finset.sum_congr rfl fun x hx => h x (Finset.ne_of_mem_erase hx)
    simp only [mstar, if_true]
    omega
  · simp [mstar, hσ, h σ hσ]
end GroundTheory.Heights₂.Heights.RestTerms.Top
