-- Prove2me | solution 1 for SoficGroups.boundary_permutationGraph_eq_commutationDefect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/227f1307-e11c-4499-b6ce-290f124f255a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_mem_permutationGraph

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
namespace SoficGroups
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V) :
    boundary (fun i => (σ i).prodCongr (σ i)) (permutationGraph p) =
      permutationCommutationDefect σ p := by
  classical
  unfold boundary permutationCommutationDefect
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_bij (fun z _ => z.1)
  · intro z hz
    obtain ⟨hzgraph, hzbad⟩ := Finset.mem_filter.mp hz
    have hzsecond : z.2 = p z.1 :=
      (mem_permutationGraph p z.1 z.2).mp hzgraph
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcommute
    apply hzbad
    apply (mem_permutationGraph p (σ i z.1) (σ i z.2)).mpr
    simpa [hzsecond] using hcommute.symm
  · intro z hz w hw hfirst
    obtain ⟨hzgraph, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwgraph, _⟩ := Finset.mem_filter.mp hw
    have hzsecond := (mem_permutationGraph p z.1 z.2).mp hzgraph
    have hwsecond := (mem_permutationGraph p w.1 w.2).mp hwgraph
    apply Prod.ext hfirst
    simpa [hzsecond, hwsecond] using congrArg p hfirst
  · intro x hx
    obtain ⟨_, hbad⟩ := Finset.mem_filter.mp hx
    refine ⟨(x, p x), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_permutationGraph p x (p x)).mpr rfl, ?_⟩
    intro hgraph
    have hcommute :=
      (mem_permutationGraph p (σ i x) (σ i (p x))).mp hgraph
    exact hbad hcommute.symm
end SoficGroups
