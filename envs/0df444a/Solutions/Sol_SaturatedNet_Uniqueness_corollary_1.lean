-- Prove2me | solution 1 for SaturatedNet.Uniqueness.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:11:57.545386+00:00
-- url     : https://prove2.me/submissions/64c60d7e-e544-493d-a455-3c38dbb971dc

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_1_i
import Theorems.Thm_SaturatedNet_Uniqueness_theorem_1
open Matrix


open Matrix

namespace SaturatedNet.Uniqueness.DimensionProof

lemma node_partition {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (w : n → ℝ) (hw : 0 ≤ w) (c x : n → ℝ) :
    Disjoint (surplus P w c x) (exposed P w c x) ∧
    Disjoint (surplus P w c x) (deficit P c x) ∧
    Disjoint (exposed P w c x) (deficit P c x) ∧
    surplus P w c x ∪ exposed P w c x ∪ deficit P c x = Finset.univ := by
  refine ⟨?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [surplus,exposed,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
    linarith [hj.2]
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [surplus,deficit,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
    have hwi : 0 ≤ w i := hw i
    linarith
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [exposed,deficit,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
    linarith [hi.1]
  · ext i
    simp only [Finset.mem_union,surplus,exposed,deficit,Finset.mem_filter,
      Finset.mem_univ,true_and,iff_true]
    by_cases hn : inflow P c x i < 0
    · exact Or.inr hn
    · by_cases hp : w i < inflow P c x i
      · exact Or.inl (Or.inl hp)
      · exact Or.inl (Or.inr ⟨le_of_not_gt hn,le_of_not_gt hp⟩)

lemma equilibrium_regions {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (w : n → ℝ) (hw : 0 ≤ w) (c x : n → ℝ)
    (hx : x ∈ equilibria P w c) :
    (∀ i ∈ deficit P c x, x i=0) ∧
    (∀ i ∈ exposed P w c x, x i=inflow P c x i) ∧
    (∀ i ∈ surplus P w c x, x i=w i) := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    simp only [deficit,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    have hwi : 0 ≤ w i := hw i
    rw [hx i]
    unfold sat
    rw [max_eq_right hi.le,min_eq_left hwi]
  · intro i hi
    simp only [exposed,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    rw [hx i]
    simp [sat,max_eq_left hi.1,min_eq_left hi.2]
  · intro i hi
    simp only [surplus,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    have hwi : 0 ≤ w i := hw i
    rw [hx i]
    unfold sat
    rw [max_eq_left (hwi.trans hi.le),min_eq_right hi.le]

lemma corollary_of_partition {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ)
    (hpart : ∀ x ∈ equilibria P w c, ∀ y ∈ equilibria P w c,
      surplus P w c x = surplus P w c y ∧ exposed P w c x = exposed P w c y ∧
      deficit P c x = deficit P c y) :
    ∃ Vp V0 Vm : Finset n,
      Disjoint Vp V0 ∧ Disjoint Vp Vm ∧ Disjoint V0 Vm ∧ Vp ∪ V0 ∪ Vm = Finset.univ ∧
      (∀ x ∈ equilibria P w c,
        (∀ i ∈ Vm, x i = 0) ∧
        (∀ i ∈ V0, x i = ∑ k ∈ V0, P k i * x k + ∑ k ∈ Vp, P k i * x k + c i) ∧
        (∀ i ∈ Vp, x i = w i)) ∧
      (∀ x ∈ equilibria P w c, ∀ y ∈ equilibria P w c,
        (∀ i ∈ Vm, x i = y i) ∧ (∀ i ∈ Vp, x i = y i)) := by
  classical
  obtain ⟨z,hz,_⟩ := (proposition_1_i P hP w hw c).2.1
  let Vp := surplus P w c z
  let V0 := exposed P w c z
  let Vm := deficit P c z
  obtain ⟨hdp0,hdpm,hd0m,hcover⟩ := node_partition P w hw c z
  have hregions (x : n → ℝ) (hx : x ∈ equilibria P w c) :
      (∀ i ∈ Vm,x i=0) ∧ (∀ i ∈ V0,x i=inflow P c x i) ∧ (∀ i ∈ Vp,x i=w i) := by
    obtain ⟨hp,h0,hm⟩ := hpart z hz x hx
    simpa only [Vp,V0,Vm,hp,h0,hm] using equilibrium_regions P w hw c x hx
  refine ⟨Vp,V0,Vm,hdp0,hdpm,hd0m,hcover,?_,?_⟩
  · intro x hx
    obtain ⟨hm,h0,hp⟩ := hregions x hx
    refine ⟨hm,?_,hp⟩
    intro i hi
    have hsum : (∑ k,P k i*x k) = ∑ k ∈ V0,P k i*x k + ∑ k ∈ Vp,P k i*x k := by
      rw [← Finset.sum_union hdp0.symm]
      apply (Finset.sum_subset (Finset.subset_univ (V0 ∪ Vp)) ?_).symm
      intro k _ hk
      have hkm : k ∈ Vm := by
        have hku : k ∈ Vp ∪ V0 ∪ Vm := by rw [hcover]; exact Finset.mem_univ k
        simp only [Finset.mem_union] at hku hk
        tauto
      rw [hm k hkm,mul_zero]
    rw [h0 i hi]
    unfold inflow
    simp_rw [mul_comm (x _) (P _ i)]
    rw [hsum]
  · intro x hx y hy
    obtain ⟨hxm,_,hxp⟩ := hregions x hx
    obtain ⟨hym,_,hyp⟩ := hregions y hy
    exact ⟨fun i hi => (hxm i hi).trans (hym i hi).symm,
      fun i hi => (hxp i hi).trans (hyp i hi).symm⟩

end SaturatedNet.Uniqueness.DimensionProof


namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hne : IsNonExpansive P) :
    ∃ Vp V0 Vm : Finset n,
      Disjoint Vp V0 ∧ Disjoint Vp Vm ∧ Disjoint V0 Vm ∧ Vp ∪ V0 ∪ Vm = Finset.univ ∧
      (∀ x ∈ equilibria P w c,
        (∀ i ∈ Vm, x i = 0) ∧
        (∀ i ∈ V0, x i = ∑ k ∈ V0, P k i * x k + ∑ k ∈ Vp, P k i * x k + c i) ∧
        (∀ i ∈ Vp, x i = w i)) ∧
      (∀ x ∈ equilibria P w c, ∀ y ∈ equilibria P w c,
        (∀ i ∈ Vm, x i = y i) ∧ (∀ i ∈ Vp, x i = y i)) := by
  exact DimensionProof.corollary_of_partition P hP w hw c (theorem_1 P hP w hw c hne)

end SaturatedNet.Uniqueness
