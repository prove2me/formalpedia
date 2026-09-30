-- Prove2me | solution 1 for UnderstandingML.support_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:14:26.880979+00:00
-- url     : https://prove2.me/submissions/7ce5ed22-9965-4ba0-a6d2-a4442f42799a

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory Filter Topology
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (w₀ : Vec d) (h : IsHomHardSVM x y w₀) :
    ∃ α : Fin m → ℝ, (∀ i, |⟪w₀, x i⟫_ℝ| ≠ 1 → α i = 0) ∧ w₀ = ∑ i, α i • x i := by
  classical
  set x' : Fin m → Vec d := fun i => if |⟪w₀, x i⟫_ℝ| = 1 then x i else 0 with hx'
  set K : Submodule ℝ (Vec d) := Submodule.span ℝ (Set.range x') with hK
  -- Step 1: `w₀ ∈ K`.
  have hmem : w₀ ∈ K := by
    have htop : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
    have : w₀ ∈ K ⊔ Kᗮ := by rw [htop]; exact Submodule.mem_top
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp this
    by_contra hw
    have hq0 : q ≠ 0 := by
      rintro rfl
      apply hw
      rw [← hpq, add_zero]; exact hp
    have hpq0 : ⟪p, q⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
    -- active constraints are orthogonal to `q`
    have hact : ∀ i, |⟪w₀, x i⟫_ℝ| = 1 → ⟪q, x i⟫_ℝ = 0 := by
      intro i hi
      have hxi : x i ∈ K := by
        have : x' i = x i := by simp [hx', hi]
        rw [← this]; exact Submodule.subset_span ⟨i, rfl⟩
      exact Submodule.inner_left_of_mem_orthogonal hxi hq
    -- inactive constraints are strict
    have hstrict : ∀ i, |⟪w₀, x i⟫_ℝ| ≠ 1 → 1 < y i * ⟪w₀, x i⟫_ℝ := by
      intro i hi
      have h1 := h.1 i
      rcases lt_or_eq_of_le h1 with hlt | heq
      · exact hlt
      · exfalso; apply hi
        rcases hy i with hyi | hyi
        · rw [hyi, one_mul] at heq; rw [← heq]; simp
        · rw [hyi] at heq
          have : ⟪w₀, x i⟫_ℝ = -1 := by linarith
          rw [this]; simp
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 ∧
        ∀ i, |⟪w₀, x i⟫_ℝ| ≠ 1 → 1 < y i * (⟪w₀, x i⟫_ℝ - t * ⟪q, x i⟫_ℝ) := by
      apply Filter.Eventually.and
      · exact nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
      · rw [Filter.eventually_all]
        intro i
        by_cases hi : |⟪w₀, x i⟫_ℝ| ≠ 1
        · have hc : Continuous (fun t : ℝ => y i * (⟪w₀, x i⟫_ℝ - t * ⟪q, x i⟫_ℝ)) := by
            fun_prop
          have := (hc.tendsto (0:ℝ)).eventually_const_lt (by simpa using hstrict i hi)
          exact nhdsWithin_le_nhds (this.mono fun t ht _ => ht)
        · exact Filter.Eventually.of_forall fun t h' => absurd h' hi
    obtain ⟨t, ⟨ht1, hti⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht0' : (0:ℝ) < t := ht0
    have hfeas : ∀ i, 1 ≤ y i * ⟪w₀ - t • q, x i⟫_ℝ := by
      intro i
      rw [inner_sub_left, real_inner_smul_left]
      by_cases hi : |⟪w₀, x i⟫_ℝ| = 1
      · rw [hact i hi, mul_zero, sub_zero]; exact h.1 i
      · exact (hti i hi).le
    have hle := h.2 _ hfeas
    have e1 : w₀ - t • q = p + (1 - t) • q := by rw [← hpq]; module
    have hn1 : ‖w₀‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
      rw [← hpq, norm_add_sq_real, hpq0]; ring
    have hn2 : ‖w₀ - t • q‖ ^ 2 = ‖p‖ ^ 2 + (1 - t) ^ 2 * ‖q‖ ^ 2 := by
      rw [e1, norm_add_sq_real, real_inner_smul_right, hpq0, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]; ring
    have hqpos : 0 < ‖q‖ ^ 2 := by positivity
    have hsq : ‖w₀‖ ^ 2 ≤ ‖w₀ - t • q‖ ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [hn1, hn2] at hsq
    have : (1 - t) ^ 2 < 1 := by nlinarith
    nlinarith
  -- Step 2: extract coefficients.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨fun i => if |⟪w₀, x i⟫_ℝ| = 1 then c i else 0, ?_, ?_⟩
  · intro i hi; simp [hi]
  · refine hc.symm.trans ?_
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : |⟪w₀, x i⟫_ℝ| = 1 <;> simp [hx', hi]
