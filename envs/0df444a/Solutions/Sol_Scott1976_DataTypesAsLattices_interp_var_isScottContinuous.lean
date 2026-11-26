-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.interp_var_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:25.025812+00:00
-- url     : https://prove2.me/submissions/2d62c700-edc8-4097-bf16-008e0afe3b86

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_succSet_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_predSet_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_id_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_const_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_const_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_envSet_comm
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_finite
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_or
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_or_of_subset
import Theorems.Thm_Scott1976_DataTypesAsLattices_exists_e_cover_finite
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) := by
  induction t generalizing ρ i with
  | var j =>
    intro x
    by_cases hj : j = i
    · subst hj
      simpa [interp, envSet, Function.update] using id_isScottContinuous x
    · simpa [interp, envSet, Function.update, hj] using const_isScottContinuous (ρ j) x
  | zero =>
    intro x
    simpa [interp] using const_isScottContinuous (ofNat 0) x
  | succ t ih =>
    exact theorem_1_3 succSet_isScottContinuous (ih ρ i)
  | pred t ih =>
    exact theorem_1_3 predSet_isScottContinuous (ih ρ i)
  | cond z x y iz ix iy =>
    intro w
    ext n
    simp only [interp]
    constructor
    · intro hn
      rcases hn with ⟨hnx, h0⟩ | ⟨hny, t, ht⟩
      · have : n ∈ scottUnion (fun v => interp x (envSet ρ i v)) w := by
          rw [← ix ρ i w]; exact hnx
        obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp this
        have : 0 ∈ scottUnion (fun v => interp z (envSet ρ i v)) w := by
          rw [← iz ρ i w]; exact h0
        obtain ⟨m', hm', h0m⟩ := mem_scottUnion.mp this
        refine mem_scottUnion.mpr ⟨m ||| m', e_or_of_subset hm hm', Or.inl ⟨?_, ?_⟩⟩
        · exact isScottContinuous_monotone (ix ρ i)
            (by rw [e_or]; exact Set.subset_union_left) hnm
        · exact isScottContinuous_monotone (iz ρ i)
            (by rw [e_or]; exact Set.subset_union_right) h0m
      · have : n ∈ scottUnion (fun v => interp y (envSet ρ i v)) w := by
          rw [← iy ρ i w]; exact hny
        obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp this
        have : t + 1 ∈ scottUnion (fun v => interp z (envSet ρ i v)) w := by
          rw [← iz ρ i w]; exact ht
        obtain ⟨m', hm', htm⟩ := mem_scottUnion.mp this
        refine mem_scottUnion.mpr ⟨m ||| m', e_or_of_subset hm hm', Or.inr ⟨?_, t, ?_⟩⟩
        · exact isScottContinuous_monotone (iy ρ i)
            (by rw [e_or]; exact Set.subset_union_left) hnm
        · exact isScottContinuous_monotone (iz ρ i)
            (by rw [e_or]; exact Set.subset_union_right) htm
    · intro hn
      obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
      rcases hnm with ⟨hnx, h0⟩ | ⟨hny, t, ht⟩
      · exact Or.inl ⟨isScottContinuous_monotone (ix ρ i) hm hnx,
          isScottContinuous_monotone (iz ρ i) hm h0⟩
      · exact Or.inr ⟨isScottContinuous_monotone (iy ρ i) hm hny, t,
          isScottContinuous_monotone (iz ρ i) hm ht⟩
  | app u x iu ix =>
    intro w
    ext n
    simp only [interp]
    constructor
    · intro ⟨p, hp, hpair⟩
      have : pair p n ∈ scottUnion (fun v => interp u (envSet ρ i v)) w := by
        rw [← iu ρ i w]; exact hpair
      obtain ⟨m, hm, hpm⟩ := mem_scottUnion.mp this
      obtain ⟨s, hs⟩ := (e_finite p).exists_finset_coe
      have hall : ∀ t ∈ s, ∃ q, e q ⊆ w ∧ t ∈ interp x (envSet ρ i (e q)) := by
        intro t ht
        have ht' : t ∈ e p := by
          have : t ∈ (s : Set ℕ) := ht
          rwa [hs] at this
        have : t ∈ interp x (envSet ρ i w) := hp ht'
        have : t ∈ scottUnion (fun v => interp x (envSet ρ i v)) w := by
          rwa [← ix ρ i w]
        exact mem_scottUnion.mp this
      obtain ⟨N, hN, hsN⟩ := exists_e_cover_finite (ix ρ i) s hall
      refine mem_scottUnion.mpr ⟨m ||| N, e_or_of_subset hm hN, p, ?_, ?_⟩
      · have : e p ⊆ interp x (envSet ρ i (e (m ||| N))) := by
          rw [← hs]
          intro t ht
          exact isScottContinuous_monotone (ix ρ i)
            (by rw [e_or]; exact Set.subset_union_right) (hsN ht)
        exact this
      · exact isScottContinuous_monotone (iu ρ i)
          (by rw [e_or]; exact Set.subset_union_left) hpm
    · intro hn
      obtain ⟨m, hm, p, hp, hpair⟩ := mem_scottUnion.mp hn
      exact ⟨p, subset_trans hp (isScottContinuous_monotone (ix ρ i) hm),
        isScottContinuous_monotone (iu ρ i) hm hpair⟩
  | lam j body ih =>
    by_cases hj : j = i
    · subst hj
      intro w
      simpa [interp, envSet, Function.update] using
        const_isScottContinuous (graph (fun v => interp body (envSet ρ j v))) w
    · have hmap : IsScottContinuous (fun w =>
          graph (fun v => interp body (envSet (envSet ρ i w) j v))) := by
        refine graph_const_isScottContinuous
          (fun w v => interp body (envSet (envSet ρ i w) j v)) ?_
        intro v
        have : (fun w => interp body (envSet (envSet ρ i w) j v)) =
            (fun w => interp body (envSet (envSet ρ j v) i w)) := by
          funext w; rw [envSet_comm hj]
        rw [this]
        exact ih (envSet ρ j v) i
      intro w
      simpa [interp] using hmap w
end Scott1976.DataTypesAsLattices
