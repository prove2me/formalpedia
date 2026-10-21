-- Prove2me | solution 1 for ToddKK14.Diameter.base_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:05:06.20653+00:00
-- url     : https://prove2.me/submissions/ed689cef-80df-4839-b7aa-4507414a033a

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

set_option autoImplicit false

namespace ToddKK14.Diameter

open Hirsch

lemma extreme_span {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) :
    Submodule.span ℝ (a '' {i | ⟪a i, v⟫ = b i}) = ⊤ := by
  by_contra hne
  set K := Submodule.span ℝ (a '' {i | ⟪a i, v⟫ = b i}) with hK
  have hbot : Kᗮ ≠ ⊥ := by
    intro h
    exact hne (Submodule.orthogonal_eq_bot_iff.1 h)
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hperp : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, w⟫ = 0 := by
    intro i hi
    exact (Submodule.mem_orthogonal K w).1 hwK (a i) (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hvP : v ∈ Hpoly a b := hv.1
  have hev : ∀ᶠ t in nhds (0 : ℝ), v + t • w ∈ Hpoly a b := by
    have : ∀ i, ∀ᶠ t in nhds (0 : ℝ), ⟪a i, v + t • w⟫ ≤ b i := by
      intro i
      by_cases hi : ⟪a i, v⟫ = b i
      · refine Filter.Eventually.of_forall (fun t => ?_)
        rw [inner_add_right, inner_smul_right, hperp i hi, hi]; simp
      · have hlt : ⟪a i, v⟫ < b i := lt_of_le_of_ne (hvP i) hi
        have hc : Continuous (fun t : ℝ => ⟪a i, v + t • w⟫) := by fun_prop
        have := hc.continuousAt (x := 0) |>.eventually_lt continuousAt_const (by simpa using hlt)
        exact this.mono (fun t ht => le_of_lt ht)
    exact Filter.eventually_all.2 this
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have h1 : v + (ε / 2) • w ∈ Hpoly a b := hball (by simp [abs_of_pos hε]; linarith)
  have h2 : v + (-(ε / 2)) • w ∈ Hpoly a b := hball (by simp [abs_of_pos hε]; linarith)
  have := hv.2 h1 h2 (by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    module)
  have h3 : (ε / 2) • w = 0 := by simpa using this
  rcases smul_eq_zero.1 h3 with h | h
  · linarith
  · exact hw0 h

lemma base_eq' (d : ℕ) (a : Fin d → EuclideanSpace ℝ (Fin d)) (b : Fin d → ℝ) :
    DiamLE (Hpoly a b) 0 := by
  intro u hu v hv
  have hall : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b), ∀ i, ⟪a i, x⟫ = b i := by
    intro x hx
    have hs := extreme_span a b x hx
    classical
    set F : Finset (Fin d) := Finset.univ.filter (fun i => ⟪a i, x⟫ = b i) with hF
    have hspan : Submodule.span ℝ ((F.image a : Finset _) : Set (EuclideanSpace ℝ (Fin d))) = ⊤ := by
      rw [Finset.coe_image, hF]
      convert hs using 3
      ext i; simp
    have h1 := finrank_span_finset_le_card (R := ℝ) (F.image a)
    rw [Set.finrank, hspan, finrank_top, finrank_euclideanSpace_fin] at h1
    have h2 := Finset.card_image_le (s := F) (f := a)
    have h3 : F.card ≤ d := by
      calc F.card ≤ Finset.univ.card := Finset.card_le_univ F
        _ = d := by simp
    have h4 : F = Finset.univ := Finset.eq_univ_of_card F (by simp; omega)
    intro i
    have : i ∈ F := by rw [h4]; exact Finset.mem_univ i
    simpa [hF] using this
  have heq : u = v := by
    set x := u - v with hx
    have hx0 : ∀ i, ⟪a i, x⟫ = 0 := by
      intro i
      simp only [hx, inner_sub_right, hall u hu i, hall v hv i]; simp
    have hspan : Submodule.span ℝ (Set.range a) = ⊤ := by
      have := extreme_span a b u hu
      apply top_le_iff.1
      rw [← this]
      apply Submodule.span_mono
      exact Set.image_subset_range _ _
    have hker : Submodule.span ℝ (Set.range a) ≤ LinearMap.ker (innerSL ℝ x).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
      rw [real_inner_comm]; exact hx0 i
    rw [hspan] at hker
    have := hker (Submodule.mem_top (x := x))
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at this
    have : x = 0 := inner_self_eq_zero.1 this
    exact sub_eq_zero.1 this
  subst heq
  exact ⟨fun _ => u, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩

end ToddKK14.Diameter

theorem solution (d : ℕ) (a : Fin d → EuclideanSpace ℝ (Fin d)) (b : Fin d → ℝ) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) 0 :=
  ToddKK14.Diameter.base_eq' d a b
