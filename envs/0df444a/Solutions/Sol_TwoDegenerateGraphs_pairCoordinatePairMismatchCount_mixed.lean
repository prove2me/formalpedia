-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinatePairMismatchCount_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/9a0babf9-3e2c-41e0-8c83-5a8dee1b6d93

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (hgroup : pairCoordinateBitType parents coordinate pair = 2) :
    pairCoordinatePairMismatchCount parents children coordinate pair = 1 := by
  classical
  have hnotfalse :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = false := by
    intro hfalse
    have hzero :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair false).mpr hfalse
    rw [hgroup] at hzero
    simp at hzero
  have hnottrue :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = true := by
    intro htrue
    have hone :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair true).mpr htrue
    rw [hgroup] at hone
    simp at hone
  have hexfalse :
      ∃ parent ∈ pair.val, parents parent coordinate = false := by
    by_contra hnone
    push Not at hnone
    apply hnottrue
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  have hextrue :
      ∃ parent ∈ pair.val, parents parent coordinate = true := by
    by_contra hnone
    push Not at hnone
    apply hnotfalse
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  obtain ⟨falseParent, hfalseParent, hfalseBit⟩ := hexfalse
  obtain ⟨trueParent, htrueParent, htrueBit⟩ := hextrue
  let mismatches : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
  let agreements : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        ¬ parents parent coordinate ≠ children pair coordinate)
  have hmismatch : mismatches.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨trueParent, ?_⟩
      simp [mismatches, htrueParent, htrueBit, hchild]
    · refine ⟨falseParent, ?_⟩
      simp [mismatches, hfalseParent, hfalseBit, hchild]
  have hagreement : agreements.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨falseParent, ?_⟩
      simp [agreements, hfalseParent, hfalseBit, hchild]
    · refine ⟨trueParent, ?_⟩
      simp [agreements, htrueParent, htrueBit, hchild]
  have hpartition : mismatches.card + agreements.card = 2 := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pair.val)
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
    change mismatches.card + agreements.card = pair.val.card at hfilter
    simpa [pair.property] using hfilter
  have hmismatch_pos := Finset.card_pos.mpr hmismatch
  have hagreement_pos := Finset.card_pos.mpr hagreement
  change mismatches.card = 1
  omega
end TwoDegenerateGraphs
