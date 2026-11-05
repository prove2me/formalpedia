-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun.setRestrict_of_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:20:21.706122+00:00
-- url     : https://prove2.me/submissions/97e76d62-bbf3-4e38-82e4-5e73ea191c17

import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Theorems.Thm_ProbabilityTheory_iIndepSets_piiUnionInter_of_pairwiseDisjoint
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Independence.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory MeasurableSpace Set

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace ProbabilityTheory

theorem iIndep.biSup_of_pairwiseDisjoint {m : κ → MeasurableSpace Ω}
    (h_le : ∀ k, m k ≤ mΩ) (h_indep : iIndep m μ) {S : ι → Set κ}
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndep (fun i => ⨆ k ∈ S i, m k) μ := by
  refine iIndepSets.iIndep (fun i => iSup₂_le fun k _ => h_le k)
    (fun i => piiUnionInter (fun k => {s | MeasurableSet[m k] s}) (S i)) ?_ ?_ ?_
  · exact fun i => isPiSystem_piiUnionInter _
      (fun k => @MeasurableSpace.isPiSystem_measurableSet Ω (m k)) (S i)
  · exact fun i => (generateFrom_piiUnionInter_measurableSet m (S i)).symm
  · exact h_indep.iIndepSets'.piiUnionInter_of_pairwiseDisjoint hS

end ProbabilityTheory

theorem solution {β : κ → Type*}
    {mβ : ∀ k, MeasurableSpace (β k)} {f : ∀ k, Ω → β k} (hf : ∀ k, Measurable (f k))
    (h_indep : iIndepFun f μ) {S : ι → Set κ}
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepFun (fun i ω => (S i).restrict fun k => f k ω) μ := by
  have hcomap : ∀ i, MeasurableSpace.comap (fun ω => (S i).restrict fun k => f k ω)
      MeasurableSpace.pi = ⨆ k ∈ S i, MeasurableSpace.comap (f k) (mβ k) := by
    intro i
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, Set.restrict_apply]
    exact iSup_subtype'' (S i) fun k => MeasurableSpace.comap (f k) (mβ k)
  show iIndep (fun i => MeasurableSpace.comap (fun ω => (S i).restrict fun k => f k ω)
      MeasurableSpace.pi) μ
  simp_rw [hcomap]
  exact iIndep.biSup_of_pairwiseDisjoint (fun k => (hf k).comap_le) h_indep hS
