-- Prove2me | solution 1 for RiskUncSets.Distortion.permutohull_robust_iff_linear
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:23:35.537779+00:00
-- url     : https://prove2.me/submissions/59f61bf8-ced8-4ff6-88f4-fd97864f2952

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

open RiskUncSets.Distortion Finset

/-- Telescoping bound, lower-left part. -/
theorem ph84_tel1 (Q C : ℕ → ℝ) (hQ : Monotone Q) (hC : Antitone C) (j : ℕ) :
    ∀ i, j ≤ i → ∑ k ∈ Ico j i, (Q (k+1) - Q k) * C k ≤ (Q i - Q j) * C j := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ i hji ih =>
    rw [Finset.sum_Ico_succ_top hji]
    have h1 : 0 ≤ Q (i+1) - Q i := sub_nonneg.mpr (hQ (Nat.le_succ i))
    have h2 : C i ≤ C j := hC hji
    have := mul_le_mul_of_nonneg_left h2 h1
    nlinarith

theorem ph84_tel2 (Q C : ℕ → ℝ) (hQ : Monotone Q) (hC : Antitone C) (i : ℕ) :
    ∀ j, i ≤ j → (Q j - Q i) * C j ≤ ∑ k ∈ Ico i j, (Q (k+1) - Q k) * C k := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [Finset.sum_Ico_succ_top hij]
    have h1 : 0 ≤ Q (j+1) - Q j := sub_nonneg.mpr (hQ (Nat.le_succ j))
    have h0 : 0 ≤ Q j - Q i := sub_nonneg.mpr (hQ hij)
    have h2 : C (j+1) ≤ C j := hC (Nat.le_succ j)
    have := mul_le_mul_of_nonneg_left h2 h1
    have := mul_le_mul_of_nonneg_left h2 h0
    nlinarith

/-- Core: explicit dual for sorted data (Monge cost). -/
theorem ph84_core {N : ℕ} (Q C : Fin N → ℝ) (hQ : Monotone Q) (hC : Antitone C) :
    ∃ u v : Fin N → ℝ, ∑ i, u i + ∑ j, v j = ∑ k, Q k * C k ∧
      ∀ i j, u i + v j ≤ Q i * C j := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, 0, by simp, fun i => i.elim0⟩
  let e : ℕ → Fin N := fun n => ⟨min n (N-1), by omega⟩
  have he : Monotone e := fun a b h => by
    simp only [e, Fin.mk_le_mk]; omega
  have hei : ∀ i : Fin N, e i.val = i := fun i => by
    ext; simp only [e]; omega
  set Q' : ℕ → ℝ := fun n => Q (e n)
  set C' : ℕ → ℝ := fun n => C (e n)
  have hQ' : Monotone Q' := hQ.comp he
  have hC' : Antitone C' := hC.comp_monotone he
  let u : Fin N → ℝ := fun i => ∑ k ∈ range i.val, (Q' (k+1) - Q' k) * C' k
  refine ⟨u, fun j => Q j * C j - u j, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib]; ring
  · intro i j
    have hQi : Q' i.val = Q i := by simp [Q', hei]
    have hQj : Q' j.val = Q j := by simp [Q', hei]
    have hCj : C' j.val = C j := by simp [C', hei]
    show u i + (Q j * C j - u j) ≤ Q i * C j
    rcases le_total j.val i.val with h | h
    · have hs : u i - u j = ∑ k ∈ Ico j.val i.val, (Q' (k+1) - Q' k) * C' k := by
        simp only [u]
        exact (Finset.sum_Ico_eq_sub _ h).symm
      have := ph84_tel1 Q' C' hQ' hC' j.val i.val h
      rw [hQi, hQj, hCj] at this
      nlinarith
    · have hs : u j - u i = ∑ k ∈ Ico i.val j.val, (Q' (k+1) - Q' k) * C' k := by
        simp only [u]
        exact (Finset.sum_Ico_eq_sub _ h).symm
      have := ph84_tel2 Q' C' hQ' hC' i.val j.val h
      rw [hQi, hQj, hCj] at this
      nlinarith

theorem solution {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (b : ℝ)
    (x : Fin n → ℝ) :
    (∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x) ↔
      ∃ y₁ y₂ : Fin N → ℝ, b ≤ ∑ i, y₁ i + ∑ j, y₂ j ∧
        ∀ i j, y₁ i + y₂ j ≤ q i * (a j ⬝ᵥ x) := by
  set c : Fin N → ℝ := fun j => a j ⬝ᵥ x with hc
  have hval : ∀ σ : Equiv.Perm (Fin N),
      (∑ i, q (σ i) • a i) ⬝ᵥ x = ∑ i, q (σ i) * c i := by
    intro σ
    rw [sum_dotProduct]
    simp [c, smul_dotProduct]
  constructor
  · intro h
    let τ := Tuple.sort q
    let π := Tuple.sort (fun j => -c j)
    have hτ : Monotone (q ∘ τ) := Tuple.monotone_sort q
    have hπ : Antitone (c ∘ π) := by
      intro i j hij
      have := Tuple.monotone_sort (fun j => -c j) hij
      simp only [Function.comp] at this ⊢; linarith
    obtain ⟨u, v, hsum, hle⟩ := ph84_core (q ∘ τ) (c ∘ π) hτ hπ
    refine ⟨fun i => u (τ.symm i), fun j => v (π.symm j), ?_, ?_⟩
    · have hb := h _ (subset_convexHull ℝ _ ⟨π.symm.trans τ, rfl⟩)
      rw [hval] at hb
      have e1 : ∑ i, u (τ.symm i) = ∑ i, u i := Equiv.sum_comp τ.symm u
      have e2 : ∑ j, v (π.symm j) = ∑ j, v j := Equiv.sum_comp π.symm v
      have e3 : ∑ i, q ((π.symm.trans τ) i) * c i = ∑ k, (q ∘ τ) k * (c ∘ π) k := by
        rw [← Equiv.sum_comp π]
        simp
      rw [e1, e2, hsum, ← e3]; exact hb
    · intro i j
      have := hle (τ.symm i) (π.symm j)
      simpa [c] using this
  · rintro ⟨y₁, y₂, hb, hy⟩ a' ha'
    have hconv : Convex ℝ {z : Fin n → ℝ | b ≤ z ⬝ᵥ x} := by
      exact convex_halfSpace_ge (f := fun z : Fin n → ℝ => z ⬝ᵥ x)
        (by constructor <;> intros <;> simp [add_dotProduct, smul_dotProduct]) b
    refine (convexHull_min ?_ hconv) ha'
    rintro _ ⟨σ, rfl⟩
    show b ≤ _
    rw [hval]
    have e1 : ∑ i, y₁ (σ i) = ∑ i, y₁ i := Equiv.sum_comp σ y₁
    calc b ≤ ∑ i, y₁ i + ∑ j, y₂ j := hb
      _ = ∑ i, (y₁ (σ i) + y₂ i) := by rw [Finset.sum_add_distrib, e1]
      _ ≤ ∑ i, q (σ i) * c i := Finset.sum_le_sum fun i _ => hy (σ i) i
