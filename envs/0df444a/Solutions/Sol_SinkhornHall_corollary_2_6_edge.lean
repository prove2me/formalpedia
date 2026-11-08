-- Prove2me | solution 1 for SinkhornHall.corollary_2_6_edge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:41:57.434207+00:00
-- url     : https://prove2.me/submissions/f6360e11-b329-4763-a369-ad11d2326220

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

open SinkhornHall in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (h2 : 1 < numEdges A)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, 0 < x i)
    (hy : ∀ j, 0 < y j) (hκ : kappa A r c x y ≤ Amin A) :
    ∀ k l, 0 < A k l →
      x k * y l < (∏ i, x i ^ (r i / ∑ i', r i')) * ∏ j, y j ^ (c j / ∑ j', c j') := by
  classical
  intro k l hkl
  obtain ⟨G, hGdef⟩ : ∃ G, G = (∏ i, x i ^ (r i / ∑ i', r i')) * ∏ j, y j ^ (c j / ∑ j', c j') :=
    ⟨_, rfl⟩
  rw [← hGdef]
  have hG : 0 < G := by
    rw [hGdef]
    apply mul_pos
    · exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
    · exact Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy j) _
  set T : Set ℝ := {a : ℝ | ∃ i j, 0 < A i j ∧ A i j = a} with hT
  have hTfin : T.Finite := by
    apply (Set.finite_range (fun p : ι × κ => A p.1 p.2)).subset
    rintro a ⟨i, j, _, rfl⟩
    exact ⟨(i, j), rfl⟩
  have hTne : T.Nonempty := ⟨A k l, k, l, hkl, rfl⟩
  have hAmin_pos : 0 < Amin A := by
    obtain ⟨i, j, hij, e⟩ := hTne.csInf_mem hTfin
    unfold Amin
    rw [← hT, ← e]; exact hij
  have hAmin_le : Amin A ≤ A k l := by
    unfold Amin
    rw [← hT]
    exact csInf_le ⟨0, fun a ⟨i, j, h, e⟩ => e ▸ h.le⟩ ⟨k, l, hkl, rfl⟩
  set f : ι × κ → ℝ := fun p => A p.1 p.2 * x p.1 * y p.2 with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p =>
    mul_nonneg (mul_nonneg (hA _ _) (hx _).le) (hy _).le
  have hS : ∑ i, ∑ j, A i j * x i * y j = ∑ p, f p := by
    simp only [hf]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  -- another positive edge
  obtain ⟨p0, hp0, hne⟩ : ∃ p0 : ι × κ, 0 < A p0.1 p0.2 ∧ p0 ≠ (k, l) := by
    unfold numEdges at h2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_cases h : a = (k, l)
    · exact ⟨b, hb, fun hb' => hab (h.trans hb'.symm)⟩
    · exact ⟨a, ha, h⟩
  have hfp0 : 0 < f p0 := mul_pos (mul_pos hp0 (hx _)) (hy _)
  have hlt : f (k, l) < ∑ p, f p := by
    have hsub : ({(k, l), p0} : Finset (ι × κ)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf0 p)
    rw [Finset.sum_pair (Ne.symm hne)] at this
    linarith
  have hSle : ∑ i, ∑ j, A i j * x i * y j ≤ Amin A * G := by
    unfold kappa at hκ
    rw [← hGdef, div_le_iff₀ hG] at hκ
    exact hκ
  have hxy : 0 < x k * y l := mul_pos (hx k) (hy l)
  have h3 : Amin A * (x k * y l) ≤ f (k, l) := by
    simp only [hf]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hAmin_le hxy.le
  have h4 : Amin A * (x k * y l) < Amin A * G := by linarith
  exact lt_of_mul_lt_mul_left h4 hAmin_pos.le
