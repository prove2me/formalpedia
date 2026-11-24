-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_succ_isEmpty_c7809aa49cfb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:00.419789+00:00
-- url     : https://prove2.me/submissions/ba4f5387-c2ae-4e44-86fa-9aab26871aac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (n : ℕ) : IsEmpty (KH.Cell K ι (n + 1)) := by
  refine ⟨fun I => ?_⟩
  have h : ∑ k, ((I.1 k).card - 1) = 0 :=
    Finset.sum_eq_zero fun k _ => Nat.sub_eq_zero_of_le (Finset.card_le_one_of_subsingleton _)
  have := I.2.2
  omega
end GroundTheory.Heights₂.Heights.HilbertSamuel
