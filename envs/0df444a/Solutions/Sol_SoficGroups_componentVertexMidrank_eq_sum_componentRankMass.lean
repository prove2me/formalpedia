-- Prove2me | solution 1 for SoficGroups.componentVertexMidrank_eq_sum_componentRankMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/8557edef-9089-499c-b948-3bac572963b5

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    componentVertexMidrank C b x =
      (∑ j ∈ (C.image b).filter (fun j => j < b x),
        componentRankMass C b j) + componentRankMass C b (b x) / 2 := by
  classical
  let J : Finset ℤ := (C.image b).filter fun j => j < b x
  have hfilter :
      C.filter (fun z => b z ∈ J) =
        C.filter (fun z => b z < b x) := by
    ext z
    simp only [Finset.mem_filter]
    dsimp [J]
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  have hcard :
      (∑ j ∈ J, (C.filter fun z => b z = j).card) =
        (C.filter fun z => b z < b x).card := by
    calc
      (∑ j ∈ J, (C.filter fun z => b z = j).card) =
          (C.filter fun z => b z ∈ J).card :=
        Finset.sum_card_fiberwise_eq_card_filter C J b
      _ = (C.filter fun z => b z < b x).card :=
        congrArg Finset.card hfilter
  have hcard' :
      (∑ j ∈ J, ((C.filter fun z => b z = j).card : ℝ)) =
        ((C.filter fun z => b z < b x).card : ℝ) := by
    exact_mod_cast hcard
  simp only [componentVertexMidrank, componentRankMass, ← Finset.sum_div]
  rw [show
    (∑ j ∈ (C.image b).filter (fun j => j < b x),
      ((C.filter fun z => b z = j).card : ℝ)) =
        ((C.filter fun z => b z < b x).card : ℝ) from by
      simpa only [J] using hcard']
  ring
end SoficGroups
