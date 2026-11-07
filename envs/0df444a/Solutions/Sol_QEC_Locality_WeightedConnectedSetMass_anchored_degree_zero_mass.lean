-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.anchored_degree_zero_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:42.771807+00:00
-- url     : https://prove2.me/submissions/1beb260b-6e66-4f6f-99b0-05133cc987c2

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_anchored_one_mass
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_anchored_eq_biUnion
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_rooted

section
noncomputable section
namespace QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
private theorem rooted_degree_zero_empty (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} = 0) (r : V) (m : ℕ) (hm : m ≠ 1) :
    rooted G r m = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro K hK
  obtain ⟨hr,hcard,hc⟩ := (mem_rooted G r m K).mp hK
  have hno : ∀ v w, ¬ G.Adj v w := by
    intro v w hvw
    have hcard0 : Fintype.card {w : V // G.Adj v w}=0 := by
      simpa only [Nat.card_eq_fintype_card] using hd v
    have hEmpty : IsEmpty {w : V // G.Adj v w} := Fintype.card_eq_zero_iff.mp hcard0
    exact hEmpty.false (⟨w,hvw⟩ : {w : V // G.Adj v w})
  have heq : G.induce (K : Set V) = ⊥ := by
    ext v w
    exact iff_false_intro (hno v.val w.val)
  have hsub : Subsingleton (K : Set V) :=
    SimpleGraph.preconnected_bot_iff_subsingleton.mp (heq ▸ hc.preconnected)
  have hsingle : K = {r} := by
    ext v
    constructor
    · intro hv
      have he := @Subsingleton.elim _ hsub (⟨v,hv⟩ : K) ⟨r,hr⟩
      exact Finset.mem_singleton.mpr (congrArg Subtype.val he)
    · intro hv
      simpa only [Finset.mem_singleton.mp hv] using hr
  apply hm
  simpa only [hsingle,Finset.card_singleton] using hcard.symm
end QEC.Locality.WeightedConnectedSetMass
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} = 0) (R : Finset V) (m : ℕ) (a : V → ℝ) :
    anchoredMass G R m a = if m=1 then ∑ r ∈ R, a r else 0 := by
  by_cases h : m=1
  · subst m; simp [anchored_one_mass]
  · have he : anchored G R m = ∅ := by
      rw [anchored_eq_biUnion]
      apply Finset.eq_empty_of_forall_notMem
      intro K hK
      obtain ⟨r,hr,hKr⟩ := Finset.mem_biUnion.mp hK
      rw [rooted_degree_zero_empty G hd r m h] at hKr
      exact Finset.notMem_empty K hKr
    simp [anchoredMass,he,h]
end QEC.Locality.WeightedConnectedSetMass
