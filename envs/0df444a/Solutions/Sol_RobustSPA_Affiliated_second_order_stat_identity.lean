-- Prove2me | solution 1 for RobustSPA.Affiliated.second_order_stat_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:04:25.939082+00:00
-- url     : https://prove2.me/submissions/7ea6a10e-3d18-4281-92bd-d4149fae3bb0

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

set_option autoImplicit false
open MeasureTheory RobustSPA.IID RobustSPA.Affiliated

theorem solution (n : ℕ) (hn : 2 ≤ n) (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Fexc n) :
    ∀ p : ℝ, F2 μ p = (n : ℝ) * F1k (n - 1) μ p - ((n : ℝ) - 1) * F1 μ p := by
  intro t
  obtain ⟨⟨hprob, -⟩, hperm⟩ := hμ
  have : IsProbabilityMeasure μ := hprob
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let E : Fin n → Set (Fin n → ℝ) := fun i => {u | ∀ j, j ≠ i → u j ≤ t}
  let A : Set (Fin n → ℝ) := {u | ∀ j, u j ≤ t}
  let L : Set (Fin n → ℝ) := {u | ∀ k : Fin n, (k : ℕ) < n - 1 → u k ≤ t}
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    have : E i = ⋂ j, ⋂ (_ : j ≠ i), {u : Fin n → ℝ | u j ≤ t} := by
      ext u; simp [E]
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_pi_apply j) measurable_const
  have hAm : MeasurableSet A := by
    have : A = ⋂ j, {u : Fin n → ℝ | u j ≤ t} := by
      ext u; simp [A]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j) measurable_const
  have hLm : MeasurableSet L := by
    have : L = ⋂ k : Fin n, ⋂ (_ : (k : ℕ) < n - 1), {u : Fin n → ℝ | u k ≤ t} := by
      ext u; simp [L]
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_pi_apply j) measurable_const
  -- characterisations of `second` and `top`
  have hsecond : ∀ u : Fin n → ℝ, second u ≤ t ↔ ∀ i j : Fin n, i ≠ j → min (u i) (u j) ≤ t := by
    intro u
    have : Nonempty {q : Fin n × Fin n // q.1 ≠ q.2} :=
      ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
    unfold second
    rw [ciSup_le_iff (Finite.bddAbove_range _)]
    constructor
    · intro h i j hij; exact h ⟨(i, j), hij⟩
    · intro h q; exact h q.1.1 q.1.2 q.2
  have htop : ∀ u : Fin n → ℝ, top u ≤ t ↔ ∀ i, u i ≤ t := by
    intro u
    unfold top
    rw [ciSup_le_iff (Finite.bddAbove_range _)]
  have hset : {u : Fin n → ℝ | second u ≤ t} = ⋃ i, E i := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hsecond]
    constructor
    · intro h
      by_cases hA : ∀ j, u j ≤ t
      · exact ⟨⟨0, by omega⟩, fun j _ => hA j⟩
      · push Not at hA
        obtain ⟨k, hk⟩ := hA
        refine ⟨k, fun j hjk => ?_⟩
        have := h k j (Ne.symm hjk)
        rcases min_le_iff.mp this with h1 | h1
        · exact absurd h1 (not_le.mpr hk)
        · exact h1
    · rintro ⟨i, hi⟩ a b hab
      by_cases ha : a = i
      · subst ha
        exact (min_le_right _ _).trans (hi b (Ne.symm hab))
      · exact (min_le_left _ _).trans (hi a ha)
  have hF1 : {u : Fin n → ℝ | top u ≤ t} = A := by
    ext u; simp [htop, A]
  -- pointwise indicator identity
  have hind : ∀ u : Fin n → ℝ, (⋃ i, E i).indicator (1 : (Fin n → ℝ) → ℝ) u =
      ∑ i, (E i).indicator (1 : (Fin n → ℝ) → ℝ) u - ((n : ℝ) - 1) * A.indicator (1 : (Fin n → ℝ) → ℝ) u := by
    intro u
    by_cases h2 : ∃ j k : Fin n, j ≠ k ∧ t < u j ∧ t < u k
    · obtain ⟨j, k, hjk, hj, hk⟩ := h2
      have hE : ∀ i, u ∉ E i := by
        intro i hi
        by_cases hij : j = i
        · subst hij
          exact absurd (hi k (Ne.symm hjk)) (not_le.mpr hk)
        · exact absurd (hi j hij) (not_le.mpr hj)
      have hAu : u ∉ A := fun h => absurd (h j) (not_le.mpr hj)
      have hU : u ∉ ⋃ i, E i := by
        simp only [Set.mem_iUnion, not_exists]; exact hE
      have hsum0 : ∑ i, (E i).indicator (1 : (Fin n → ℝ) → ℝ) u = 0 :=
        Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (hE i) _)
      rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hAu, hsum0]
      simp
    · push Not at h2
      by_cases hA : ∀ j, u j ≤ t
      · have hE : ∀ i, u ∈ E i := fun i j _ => hA j
        have hAu : u ∈ A := hA
        have hU : u ∈ ⋃ i, E i := Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, hE _⟩
        rw [Set.indicator_of_mem hU, Set.indicator_of_mem hAu,
          Finset.sum_congr rfl (fun i _ => Set.indicator_of_mem (hE i) (1 : (Fin n → ℝ) → ℝ))]
        simp
      · push Not at hA
        obtain ⟨j, hj⟩ := hA
        have hEj : u ∈ E j := by
          intro k hkj
          by_contra hcon
          exact absurd (h2 j k (Ne.symm hkj) hj) hcon
        have hEne : ∀ i, i ≠ j → u ∉ E i := by
          intro i hij hi
          exact absurd (hi j (Ne.symm hij)) (not_le.mpr hj)
        have hAu : u ∉ A := fun h => absurd (h j) (not_le.mpr hj)
        have hU : u ∈ ⋃ i, E i := Set.mem_iUnion.mpr ⟨j, hEj⟩
        rw [Set.indicator_of_mem hU, Set.indicator_of_notMem hAu,
          Finset.sum_eq_single j (fun i _ hij => Set.indicator_of_notMem (hEne i hij) _)
            (fun h => absurd (Finset.mem_univ j) h), Set.indicator_of_mem hEj]
        simp
  -- exchangeability
  have hexch : ∀ i, μ.real (E i) = μ.real L := by
    intro i
    let last : Fin n := ⟨n - 1, by omega⟩
    let σ : Equiv.Perm (Fin n) := Equiv.swap i last
    have hmeas : Measurable (fun v : Fin n → ℝ => v ∘ σ) :=
      measurable_pi_lambda _ (fun k => measurable_pi_apply _)
    have h1 : μ L = μ ((fun v : Fin n → ℝ => v ∘ σ) ⁻¹' L) := by
      conv_lhs => rw [← hperm σ]
      exact Measure.map_apply hmeas hLm
    have h2 : (fun v : Fin n → ℝ => v ∘ σ) ⁻¹' L = E i := by
      ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq, L, E, Function.comp]
      constructor
      · intro h j hji
        have hk : ((σ j : Fin n) : ℕ) < n - 1 := by
          have hne : σ j ≠ last := by
            intro heq
            apply hji
            have : j = σ last := by rw [← heq]; simp [σ]
            rw [this]; simp [σ]
          have hlt := (σ j).isLt
          have : ((σ j : Fin n) : ℕ) ≠ n - 1 := fun h' => hne (Fin.ext h')
          omega
        have := h (σ j) hk
        simpa [σ] using this
      · intro h k hk
        apply h
        intro hki
        have : k = last := by
          calc k = σ (σ k) := by simp [σ]
            _ = σ i := by rw [hki]
            _ = last := by simp [σ]
        rw [this] at hk
        simp [last] at hk
    have h3 : μ (E i) = μ L := by rw [← h2, ← h1]
    simp only [measureReal_def, h3]
  have hUm : MeasurableSet (⋃ i, E i) := MeasurableSet.iUnion hEm
  have hintg : ∀ S : Set (Fin n → ℝ), MeasurableSet S →
      Integrable (S.indicator (1 : (Fin n → ℝ) → ℝ)) μ :=
    fun S hS => (integrable_const (1 : ℝ)).indicator hS
  have hint : μ.real (⋃ i, E i) = ∑ i, μ.real (E i) - ((n : ℝ) - 1) * μ.real A := by
    rw [← integral_indicator_one hUm, ← integral_indicator_one hAm]
    have hE' : ∀ i, μ.real (E i) = ∫ u, (E i).indicator (1 : (Fin n → ℝ) → ℝ) u ∂μ :=
      fun i => (integral_indicator_one (hEm i)).symm
    simp_rw [hE']
    rw [← integral_finset_sum _ (fun i _ => hintg _ (hEm i)), ← integral_const_mul,
      ← integral_sub (integrable_finset_sum _ (fun i _ => hintg _ (hEm i)))
        ((hintg _ hAm).const_mul _)]
    exact integral_congr_ae (Filter.Eventually.of_forall hind)
  have hF2 : F2 μ t = μ.real (⋃ i, E i) := by
    unfold F2; rw [hset]; rfl
  have hF1' : F1 μ t = μ.real A := by
    unfold F1; rw [hF1]; rfl
  have hFk : F1k (n - 1) μ t = μ.real L := rfl
  rw [hF2, hF1', hFk, hint]
  simp only [hexch, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
