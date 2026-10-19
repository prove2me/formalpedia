-- Prove2me | solution 1 for SoficGroups.SourceCompressionRetainedDiscard.witnessless_component_card_le_twice_rankChanging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/c059a05b-eeae-493e-bd21-df4c99e67492

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_maximumOverlapPart_overlap_of_not_mem_insufficient

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionRetainedDiscard
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ)
    (eta : ℝ) (heta : eta ≤ (1 : ℝ) / 2)
    (C : Finset V)
    (hC : C ∈ witnesslessComponents P Q T b eta) :
    C.card ≤
      2 * (C ∩ SoficGroups.RankArcCharging.rankChangingArc
        (Finset.univ : Finset V) b T.symm).card := by
  have hfilter := Finset.mem_filter.mp hC
  have hgood := Finset.mem_sdiff.mp hfilter.1
  have hpart : C ∈ P.parts := hgood.1
  have hnotbad : C ∉ SoficGroups.insufficientOverlapComponents P Q eta :=
    hgood.2
  have hoverlap :=
    SoficGroups.maximumOverlapPart_overlap_of_not_mem_insufficient
      P Q eta C hpart hnotbad
  have hsubset :
      C ∩ SoficGroups.maximumOverlapPart Q C ⊆
        C ∩ SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm := by
    intro y hy
    have hy' := Finset.mem_inter.mp hy
    refine Finset.mem_inter.mpr ⟨hy'.1, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ y, hfilter.2 y hy⟩
  have hcard :
      ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ) ≤
        ((C ∩ SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hhalf :
      (1 / 2 : ℝ) * (C.card : ℝ) ≤
        (1 - eta) * (C.card : ℝ) := by
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hreal :
      (C.card : ℝ) ≤
        2 * ((C ∩ SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm).card : ℝ) := by
    linarith
  exact_mod_cast hreal
end SoficGroups.SourceCompressionRetainedDiscard
