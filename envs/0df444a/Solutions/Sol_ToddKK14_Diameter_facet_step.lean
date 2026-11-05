-- Prove2me | solution 1 for ToddKK14.Diameter.facet_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:18:04.577804+00:00
-- url     : https://prove2.me/submissions/a88ccd39-968e-4c16-b10c-7fee50029f0a

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_KalaiKleitman92_Diameter_facet_walk

open scoped RealInnerProductSpace Topology

namespace ToddFacetStepAux

open Hirsch

/-- A vertex of `Hpoly a b` has at least `d` tight rows. -/
theorem card_tight_ge {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    d ≤ (Finset.univ.filter (fun i => ⟪a i, u⟫ = b i)).card := by
  by_contra hlt
  push Not at hlt
  set T := Finset.univ.filter (fun i => ⟪a i, u⟫ = b i) with hT
  let f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (T → ℝ) :=
    LinearMap.pi (fun i => ((innerSL ℝ (a i.1) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ))
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp [hlt]
  obtain ⟨z, hzk, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzT : ∀ i ∈ T, ⟪a i, z⟫ = 0 := by
    intro i hi
    have := congrFun (LinearMap.mem_ker.mp hzk) ⟨i, hi⟩
    simpa [f] using this
  rw [mem_extremePoints] at hu
  obtain ⟨huP, hext⟩ := hu
  -- choose a small ε
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ i, i ∉ T → ε * |⟪a i, z⟫| < b i - ⟪a i, u⟫ := by
    refine Filter.Eventually.and (eventually_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0)) ?_
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ T
    · exact Filter.Eventually.of_forall (fun _ h => absurd hi h)
    · have hs : 0 < b i - ⟪a i, u⟫ := by
        have h1 := huP i
        have h2 : ⟪a i, u⟫ ≠ b i := by
          intro h; exact hi (by simp [hT, h])
        exact sub_pos.mpr (lt_of_le_of_ne h1 h2)
      have hc : Filter.Tendsto (fun ε : ℝ => ε * |⟪a i, z⟫|) (𝓝 0) (𝓝 (0 * |⟪a i, z⟫|)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hc
      have := hc.eventually (gt_mem_nhds hs)
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (this.mono (fun ε h _ => h))
  obtain ⟨ε, hε, hεi⟩ := hev.exists
  have hmem : ∀ s : ℝ, |s| ≤ ε → u + s • z ∈ Hpoly a b := by
    intro s hs i
    rw [inner_add_right, inner_smul_right]
    by_cases hi : i ∈ T
    · rw [hzT i hi, mul_zero, add_zero]; exact huP i
    · have h1 := hεi i hi
      have h2 : s * ⟪a i, z⟫ ≤ ε * |⟪a i, z⟫| := by
        calc s * ⟪a i, z⟫ ≤ |s * ⟪a i, z⟫| := le_abs_self _
          _ = |s| * |⟪a i, z⟫| := abs_mul _ _
          _ ≤ ε * |⟪a i, z⟫| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      linarith
  have hm := hmem (-ε) (by rw [abs_neg, abs_of_pos hε])
  have hp := hmem ε (by rw [abs_of_pos hε])
  have hseg : u ∈ openSegment ℝ (u + (-ε) • z) (u + ε • z) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have := (hext _ hm _ hp hseg).2
  apply hz
  have h2 : ε • z = 0 := by
    have : u + ε • z - u = 0 := by rw [this, sub_self]
    simpa using this
  exact (smul_eq_zero.mp h2).resolve_left hε.ne'

/-- An extreme point of `P` lying in a subset `S ⊆ P` is an extreme point of `S`. -/
theorem extreme_of_subset {E : Type*} [AddCommGroup E] [Module ℝ E] {P S : Set E} {u : E}
    (hSP : S ⊆ P) (huS : u ∈ S) (hu : u ∈ Set.extremePoints ℝ P) :
    u ∈ Set.extremePoints ℝ S := by
  rw [mem_extremePoints] at hu ⊢
  exact ⟨huS, fun x hx y hy hseg => hu.2 x (hSP hx) y (hSP hy) hseg⟩

end ToddFacetStepAux

open Hirsch in
theorem solution (d k : ℕ) (hk : k + 1 < 2 * d)
    (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0)
    (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B) :
    DiamLE (Hpoly a b) B := by
  intro u hu v hv
  have hTu := ToddFacetStepAux.card_tight_ge a b u hu
  have hTv := ToddFacetStepAux.card_tight_ge a b v hv
  -- two sets of size ≥ d in a set of size k + 1 < 2d intersect
  obtain ⟨i, hiu, hiv⟩ : ∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by
    by_contra hno
    push Not at hno
    have hdisj : Disjoint (Finset.univ.filter (fun i => ⟪a i, u⟫ = b i))
        (Finset.univ.filter (fun i => ⟪a i, v⟫ = b i)) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
      exact hno i hi hi'
    have := Finset.card_union_of_disjoint hdisj
    have h2 := Finset.card_le_univ ((Finset.univ.filter (fun i => ⟪a i, u⟫ = b i)) ∪
        (Finset.univ.filter (fun i => ⟪a i, v⟫ = b i)))
    simp only [Fintype.card_fin] at h2
    omega
  have hsub : {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} ⊆ Hpoly a b := fun x hx => hx.1
  have hu' := ToddFacetStepAux.extreme_of_subset hsub ⟨hu.1, hiu⟩ hu
  have hv' := ToddFacetStepAux.extreme_of_subset hsub ⟨hv.1, hiv⟩ hv
  obtain ⟨w, h0, hB, hs, _⟩ :=
    KalaiKleitman92.Diameter.facet_walk d k a b i (hane i) B IH u v hu' hv'
  exact ⟨w, h0, hB, hs⟩
