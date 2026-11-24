-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:42.084966+00:00
-- url     : https://prove2.me/submissions/7703555d-8091-4a4d-9ebe-4ee2685d5793

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
theorem _root_.solution (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    mstar f r a q e τ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e := by
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, fun i _ => Finset.mem_univ i⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ)]
  have : ∑ x ∈ Finset.univ.erase τ, mstar f r a q e τ x =
      ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') :=
    Finset.sum_congr rfl fun x hx => by simp [mstar, Finset.ne_of_mem_erase hx]
  rw [this]
  simp only [mstar, if_true]
  omega
end GroundTheory.Heights₂.Heights.RestTerms.Top
