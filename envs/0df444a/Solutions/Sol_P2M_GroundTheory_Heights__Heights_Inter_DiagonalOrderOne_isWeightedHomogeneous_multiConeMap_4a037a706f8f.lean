-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_isWeightedHomogeneous_multiConeMap_4a037a706f8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:22.3338+00:00
-- url     : https://prove2.me/submissions/648daea2-6d69-40e1-8f20-70a604e4d6e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrdOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_multiConeMap_of_homog_3655d6d60990
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
theorem _root_.solution (c : (Σ k, ι k) → Φ) {p : MRing ι} {m : K → ℕ}
    (hp : IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) p m) :
    IsWeightedHomogeneous (fun k : K => (Pi.single k 1 : K → ℕ)) (T.multiConeMap c p) m := by
  rw [DiagRAux.multiConeMap_of_homog c p m ((isMultiHomog_iff_weighted p m).2 hp)]
  have := (isWeightedHomogeneous_C (fun k : K => (Pi.single k 1 : K → ℕ)) (aeval c p)).mul
    (IsWeightedHomogeneous.prod Finset.univ (fun k => (X k : MvPolynomial K Φ) ^ m k)
      (fun k => m k • (Pi.single k 1 : K → ℕ)) (fun k _ => (isWeightedHomogeneous_X Φ _ k).pow (m k)))
  convert this using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]
end GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
