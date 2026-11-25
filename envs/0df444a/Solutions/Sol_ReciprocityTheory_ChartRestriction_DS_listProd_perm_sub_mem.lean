-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.listProd_perm_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:34.257423+00:00
-- url     : https://prove2.me/submissions/af0e637e-f686-4617-a13a-bf55198eb998

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_listProd_mem_layer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_layer_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {l₁ l₂ : List (Fin n × Fin n)} (hp : l₁.Perm l₂) (hnc : ∀ p ∈ l₁, ε p.1 ≠ ε p.2)
    {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) (m : ℕ) (hm : l₁.length ≤ m + 1) :
    (l₁.map fun p => E p.1 p.2).prod v - (l₂.map fun p => E p.1 p.2).prod v ∈
      layer ε E V (j + m) := by
  induction hp generalizing m with
  | nil => simp
  | @cons x l₁ l₂ h ih =>
    rcases m with _ | m
    · have hl1 : l₁ = [] := by simpa using hm
      subst hl1
      have hl2 := List.Perm.nil_eq h
      subst hl2
      simp
    · have hD := ih (fun p hp' => hnc p (List.mem_cons_of_mem _ hp')) m (by simpa using hm)
      have := apply_mem_layer_succ hE hV x.1 x.2 hD
      rw [map_sub] at this
      simpa [List.map_cons, List.prod_cons, Module.End.mul_apply, add_assoc] using this
  | swap x y l =>
    have hw := listProd_mem_layer hE hV l hv
    have hlen : j + l.length + 1 ≤ j + m := by simp at hm; omega
    have h1 : ∀ a b, (E a b) ((l.map fun p => E p.1 p.2).prod v) ∈ layer ε E V (j + m) :=
      fun a b => layer_mono hlen (apply_mem_layer_succ hE hV a b hw)
    have key : ((y :: x :: l).map fun p => E p.1 p.2).prod v - ((x :: y :: l).map fun p => E p.1 p.2).prod v =
        (E y.1 y.2 * E x.1 x.2 - E x.1 x.2 * E y.1 y.2) ((l.map fun p => E p.1 p.2).prod v) := by
      simp only [List.map_cons, List.prod_cons, LinearMap.sub_apply, Module.End.mul_apply]
    rw [key, hE, LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact h1 _ _
      · simp
    · split_ifs
      · exact h1 _ _
      · simp
  | trans h₁ h₂ ih₁ ih₂ =>
    have hA := ih₁ hnc m hm
    have hB := ih₂ (fun p hp' => hnc p (h₁.symm.subset hp')) m (by rw [← h₁.length_eq]; exact hm)
    have := Submodule.add_mem _ hA hB
    rwa [sub_add_sub_cancel] at this
end ReciprocityTheory.ChartRestriction.DS
