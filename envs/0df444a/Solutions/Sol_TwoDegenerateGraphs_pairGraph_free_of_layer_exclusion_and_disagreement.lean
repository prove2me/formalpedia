-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraph_free_of_layer_exclusion_and_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/7b140836-b050-44c2-ba13-21b2672e89ad

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_entropy_layer_exclusion
import Theorems.Thm_TwoDegenerateGraphs_pairLayerPair_nonempty
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopyLayerPotential_mem_Icc
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_layer_entropy_upper_of_disagreement
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_entropy_lower_of_exclusion

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairParentSystem baseSize depth).graph.Free
      (retainedHammingHost dimension radius retained) := by
  classical
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  let potential : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth + 1 then
      pairGraphCopyLayerPotential retained copy ⟨layer, hlevel⟩
    else 0
  let conditionalEntropy : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy ⟨layer, hlevel⟩)
        (pairGraphCopyChildWords retained copy ⟨layer, hlevel⟩)
    else 0
  let error : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      empiricalEntropyError
        (Fintype.card (PairLayer baseSize layer))
    else 0
  apply entropy_layer_exclusion depth
    potential conditionalEntropy error
  · intro layer hlayer
    have hinrange : layer < depth + 1 := by omega
    have hle : layer ≤ depth := by omega
    simpa [potential, hinrange, hle] using
      pairGraphCopyLayerPotential_mem_Icc
        hbase hdimension retained copy ⟨layer, hinrange⟩
  · intro layer hlayer
    simpa [error, hlayer] using
      herror ⟨layer, hlayer⟩
  · intro layer hlayer
    have hsize :
        2 ≤ Fintype.card (PairLayer baseSize layer) := by
      have hcard := pairLayer_card_ge_base
        baseSize layer hbase
      omega
    let reference :
        PairLayer (Fintype.card (PairLayer baseSize layer)) 1 :=
      Classical.choice (pairLayerPair_nonempty hsize)
    have hlower := pairGraphCopy_entropy_lower_of_exclusion
      retained copy ⟨layer, hlayer⟩ reference
        (midpointBeta - entropySlack)
        (hexclusion
          (pairGraphCopyChildSide
            retained copy ⟨layer, hlayer⟩ reference)
          ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, hlayer] using hlower
  · intro layer hlayer
    have hnext : layer + 1 < depth + 1 := by omega
    have hcurrent : layer < depth + 1 := by omega
    have hnext_le : layer + 1 ≤ depth := by omega
    have hcurrent_le : layer ≤ depth := by omega
    have hupper := pairGraphCopy_layer_entropy_upper_of_disagreement
      hbase hdimension retained copy ⟨layer, hlayer⟩
      (hdisagreement copy ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, potential, error,
      hlayer, hnext, hcurrent, hnext_le, hcurrent_le] using hupper
  · exact hdepth
end TwoDegenerateGraphs
