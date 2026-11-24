-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_mem_psumIdeal_6a4fee1897e0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:48.11688+00:00
-- url     : https://prove2.me/submissions/ff0cb2ef-328e-473f-afd4-431e59982174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
theorem _root_.solution {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    bps K f n m b ∈ psumIdeal K f n :=
  Ideal.subset_span ⟨m, b, h1, h2, rfl⟩
end GroundTheory.Heights₂.Heights.RestTerms.Coinv
