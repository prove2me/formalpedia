-- Prove2me | solution 1 for OceanicGames.Interior.pivotSet_ae_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:51:37.179543+00:00
-- url     : https://prove2.me/submissions/8ee128a0-cd70-4be5-aaaa-cd231f5f7bb6

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology


namespace OceanicGames.Interior

lemma og_hyper_null {m : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) (hL : L ≠ 0) (a : ℝ) :
    volume {x : Fin m → ℝ | L x = a} = 0 := by
  by_cases hne : ∃ p, L p = a
  · obtain ⟨p, hp⟩ := hne
    have hker : (LinearMap.ker L) ≠ ⊤ := by
      intro h; exact hL (LinearMap.ker_eq_top.mp h)
    have h0 := Measure.addHaar_submodule (volume : Measure (Fin m → ℝ)) (LinearMap.ker L) hker
    have hset : {x : Fin m → ℝ | L x = a} = (fun x => x + (-p)) ⁻¹' (LinearMap.ker L : Set _) := by
      ext x; simp [sub_eq_zero, hp, ← sub_eq_add_neg]
    rw [hset, measure_preimage_add_right]; exact h0
  · push_neg at hne
    have : {x : Fin m → ℝ | L x = a} = ∅ := by ext x; simp [hne x]
    rw [this]; simp

lemma og_diag_null {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    volume {x : Fin m → ℝ | x i = x j} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i - LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j
  have hL : L ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h (Pi.single i 1)
    simp [L, Pi.single_apply, hij.symm] at this
  have := og_hyper_null L hL 0
  have hset : {x : Fin m → ℝ | x i = x j} = {x | L x = 0} := by
    ext x; simp [L, sub_eq_zero]
  rw [hset]; exact this

lemma og_wsum_mono {m : ℕ} (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) {S T : Finset (Fin m)}
    (h : S ⊆ T) : wsum w S ≤ wsum w T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun j _ _ => hw j)

lemma og_not_lt {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α)
    (hw : ∀ j, 0 ≤ w j) (i j : Fin m) (x : Fin m → ℝ)
    (hi : x ∈ pivotSet c α w i) (hj : x ∈ pivotSet c α w j) (hlt : x i < x j) : False := by
  obtain ⟨_, _, hi2⟩ := hi
  obtain ⟨_, hj1, _⟩ := hj
  have hsub : insert i (pred x (x i)) ⊆ pred x (x j) := by
    intro k hk
    simp only [pred, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with rfl | hk
    · exact hlt
    · exact hk.trans hlt
  have hnot : i ∉ pred x (x i) := by simp [pred]
  have h1 := og_wsum_mono w hw hsub
  have h2 : wsum w (insert i (pred x (x i))) = w i + wsum w (pred x (x i)) := by
    unfold wsum; rw [Finset.sum_insert hnot]
  nlinarith

theorem pivotSet_ae_disjoint_core {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α)
    (hw : ∀ j, 0 ≤ w j) (i j : Fin m) (hij : i ≠ j) :
    volume (pivotSet c α w i ∩ pivotSet c α w j) = 0 := by
  apply measure_mono_null _ (og_diag_null i j hij)
  intro x ⟨hi, hj⟩
  simp only [Set.mem_setOf_eq]
  rcases lt_trichotomy (x i) (x j) with h | h | h
  · exact (og_not_lt c α w hα hw i j x hi hj h).elim
  · exact h
  · exact (og_not_lt c α w hα hw j i x hj hi h).elim

end OceanicGames.Interior

open OceanicGames.Interior


theorem solution {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α)
    (hw : ∀ j, 0 ≤ w j) (hc0 : 0 ≤ c) (hcW : c ≤ wsum w Finset.univ + α)
    (i j : Fin m) (hij : i ≠ j) :
    volume (pivotSet c α w i ∩ pivotSet c α w j) = 0 := by
  exact pivotSet_ae_disjoint_core c α w hα hw i j hij
