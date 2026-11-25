-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_norm_le_of_monic_root_673655a91a77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:28.700843+00:00
-- url     : https://prove2.me/submissions/9b93eb53-e8cb-48d3-b73a-238f01c4cfac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen

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
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
theorem _root_.solution {G : Polynomial ℂ} (hG : G.Monic) {t : ℂ} (ht : G.eval t = 0) :
    ‖t‖ ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖ + 1 := by
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hG.ne_zero ht
  have h2 : Polynomial.cauchyBound G ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1 := by
    rw [Polynomial.cauchyBound, hG.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun k hk =>
      Finset.single_le_sum (f := fun k => ‖G.coeff k‖₊) (fun _ _ => zero_le) hk
  have h3 : ‖t‖₊ ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1 := (h1.trans_le h2).le
  have h4 := NNReal.coe_le_coe.2 h3
  simpa using h4
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
