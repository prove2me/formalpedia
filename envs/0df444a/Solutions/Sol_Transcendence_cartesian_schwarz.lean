-- Prove2me | solution 1 for Transcendence.cartesian_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:34:54.488639+00:00
-- url     : https://prove2.me/submissions/9c80718e-2e68-489b-9a33-b39a88f42e04

import Mathlib
import Theorems.Thm_Transcendence_coord_hermite_step

/-!
# Schwarz's lemma for Cartesian products (Waldschmidt, DALAG Prop. 4.7)

`Transcendence.coord_hermite_step` performs one step in one coordinate: it replaces an entire `g`
by its Hermite interpolant `h` in that coordinate, at the nodes `E i` with multiplicity `S₀`, with
`|h| ≤ 3^p K` on the `R`-polydisc and `|g - h| ≤ (2r)^p (3/R)^p K` on the `r`-polydisc, where
`p = S₀S₁`. We run it in the coordinates `0, 1, …, n - 1` in turn. After `m` steps there is an
entire `g` with

- `|g| ≤ (3^p)^m M` on the `R`-polydisc;
- `|f - g| ≤ m (2·3ⁿr/R)^p M` on the `r`-polydisc;
- **V(m)**: the mixed partial derivatives of `g` of order `ℓ` along coordinates `≥ m` vanish at
  every point whose coordinates `j ≥ m` lie in `E j`, whenever `ℓ + m S₀ < n S₀ + m`.

`V(0)` is the hypothesis on `f`. In the step in coordinate `m`, a mixed partial of the new `g` along
coordinates `≥ m + 1` is controlled by mixed partials of the old one along the same coordinates,
followed by `k < S₀` times the coordinate `m`, so `V(m)` gives `V(m + 1)`. After `n` steps, `V(n)`
with `ℓ = 0` says that `g = 0`.
-/

namespace CartesianSchwarz

open Metric Function

/-- The vanishing invariant passes through the step in coordinate `m`. -/
lemma van_step {n m : ℕ} (hm : m < n) {E : Fin n → Finset ℂ} {S₀ : ℕ} {g h : (Fin n → ℂ) → ℂ}
    (hgv : ∀ (ℓ : ℕ) (v : Fin ℓ → Fin n), (∀ t, m ≤ (v t : ℕ)) → ℓ + m * S₀ < n * S₀ + m →
      ∀ ξ : Fin n → ℂ, (∀ j : Fin n, m ≤ (j : ℕ) → ξ j ∈ E j) →
        iteratedFDeriv ℂ ℓ g ξ (fun t => Pi.single (v t) 1) = 0)
    (hh : ∀ (ℓ : ℕ) (v : Fin ℓ → Fin n), (∀ t, v t ≠ ⟨m, hm⟩) → ∀ ξ : Fin n → ℂ,
      (∀ ζ ∈ E ⟨m, hm⟩, ∀ k < S₀, iteratedFDeriv ℂ (ℓ + k) g (update ξ ⟨m, hm⟩ ζ)
        (fun t => Pi.single (Fin.append v (fun _ : Fin k => (⟨m, hm⟩ : Fin n)) t) 1) = 0) →
      iteratedFDeriv ℂ ℓ h ξ (fun t => Pi.single (v t) 1) = 0) :
    ∀ (ℓ : ℕ) (v : Fin ℓ → Fin n), (∀ t, m + 1 ≤ (v t : ℕ)) →
      ℓ + (m + 1) * S₀ < n * S₀ + (m + 1) →
      ∀ ξ : Fin n → ℂ, (∀ j : Fin n, m + 1 ≤ (j : ℕ) → ξ j ∈ E j) →
        iteratedFDeriv ℂ ℓ h ξ (fun t => Pi.single (v t) 1) = 0 := by
  intro ℓ v hv hlen ξ hξ
  refine hh ℓ v (fun t ht => absurd (hv t) (by simp [ht])) ξ fun ζ hζ k hk => ?_
  refine hgv (ℓ + k) _ (fun t => ?_) ?_ _ fun j hj => ?_
  · induction t using Fin.addCases with
    | left t => rw [Fin.append_left]; exact (Nat.le_succ m).trans (hv t)
    | right t => simp
  · rw [Nat.succ_mul] at hlen
    set a := m * S₀
    set b := n * S₀
    omega
  · by_cases h : j = ⟨m, hm⟩
    · subst h
      rw [update_self]
      exact hζ
    · rw [update_of_ne h]
      exact hξ j (by have : (j : ℕ) ≠ m := fun h' => h (Fin.ext h'); omega)

/-- The size of one step: `(2r)^p (3/R)^p (3^p)^m M ≤ (2·3ⁿr/R)^p M` for `m < n`. -/
lemma step_le {n m p : ℕ} (hm : m < n) {r R M : ℝ} (hr : 0 < r) (hR : 0 < R) (hM : 0 ≤ M) :
    (2 * r) ^ p * ((3 / R) ^ p * ((3 ^ p) ^ m * M)) ≤ (2 * 3 ^ n * r / R) ^ p * M := by
  have e : 2 * 3 ^ n * r / R = 2 * r * (3 / R) * 3 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  calc (2 * r) ^ p * ((3 / R) ^ p * ((3 ^ p) ^ m * M))
      = (2 * r) ^ p * (3 / R) ^ p * (3 ^ m) ^ p * M := by
        rw [← pow_mul, mul_comm p m, pow_mul]
        ring
    _ ≤ (2 * r) ^ p * (3 / R) ^ p * (3 ^ (n - 1)) ^ p * M := by
        gcongr
        · norm_num
        · omega
    _ = (2 * 3 ^ n * r / R) ^ p * M := by
        rw [e, mul_pow (2 * r * (3 / R)), mul_pow (2 * r) (3 / R)]

/-- The state after `m ≤ n` steps: the two bounds and the vanishing invariant `V(m)`. -/
lemma exists_after {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    {E : Fin n → Finset ℂ} {S₀ S₁ : ℕ} (hE : ∀ i, (E i).card = S₁)
    {r R M : ℝ} (hr : 0 < r) (hEr : ∀ i, ∀ ζ ∈ E i, ‖ζ‖ ≤ r) (hR : 5 * r ≤ R)
    (hM : ∀ z ∈ closedBall (0 : Fin n → ℂ) R, ‖f z‖ ≤ M)
    (hvan : ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) → ∀ k < n * S₀, iteratedFDeriv ℂ k f ξ = 0) :
    ∀ m ≤ n, ∃ g : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ g Set.univ ∧
      (∀ y ∈ closedBall (0 : Fin n → ℂ) R, ‖g y‖ ≤ (3 ^ (S₀ * S₁)) ^ m * M) ∧
      (∀ z ∈ closedBall (0 : Fin n → ℂ) r,
        ‖f z - g z‖ ≤ m * ((2 * 3 ^ n * r / R) ^ (S₀ * S₁) * M)) ∧
      ∀ (ℓ : ℕ) (v : Fin ℓ → Fin n), (∀ t, m ≤ (v t : ℕ)) → ℓ + m * S₀ < n * S₀ + m →
        ∀ ξ : Fin n → ℂ, (∀ j : Fin n, m ≤ (j : ℕ) → ξ j ∈ E j) →
          iteratedFDeriv ℂ ℓ g ξ (fun t => Pi.single (v t) 1) = 0 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp; linarith))
  intro m
  induction m with
  | zero =>
    refine fun _ => ⟨f, hf, by simpa using hM, fun z _ => by simp, fun ℓ v _ hlen ξ hξ => ?_⟩
    rw [hvan ξ (fun j => hξ j (Nat.zero_le _)) ℓ (by simpa using hlen)]
    rfl
  | succ m ih =>
    intro hm
    obtain ⟨g, hg, hgR, hgr, hgv⟩ := ih (by omega)
    obtain ⟨h, hh, hhR, hhr, hhv⟩ :=
      Transcendence.coord_hermite_step hg ⟨m, hm⟩ (E ⟨m, hm⟩) S₀ hr hR (hEr _) hgR
    rw [hE, mul_comm S₁ S₀] at hhR hhr
    refine ⟨h, hh, fun y hy => ?_, fun z hz => ?_, van_step hm hgv hhv⟩
    · rw [pow_succ', mul_assoc]
      exact hhR y hy
    · calc ‖f z - h z‖ ≤ ‖f z - g z‖ + ‖g z - h z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ m * ((2 * 3 ^ n * r / R) ^ (S₀ * S₁) * M) + (2 * 3 ^ n * r / R) ^ (S₀ * S₁) * M :=
          add_le_add (hgr z hz) ((hhr z hz).trans (step_le hm hr (by linarith) hM0))
        _ = ((m + 1 : ℕ) : ℝ) * ((2 * 3 ^ n * r / R) ^ (S₀ * S₁) * M) := by
          rw [Nat.cast_succ]
          ring

end CartesianSchwarz

/-- **Schwarz's lemma for Cartesian products** (Waldschmidt, DALAG Prop. 4.7, with `2·3ⁿ` for
`18ⁿ`). -/
theorem solution {n : ℕ} (hn : 0 < n) (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (E : Fin n → Finset ℂ) {S₀ S₁ : ℕ} (hE : ∀ i, (E i).card = S₁)
    {r R M : ℝ} (hr : 0 < r) (hEr : ∀ i, ∀ ζ ∈ E i, ‖ζ‖ ≤ r) (hR : 5 * r ≤ R)
    (hM : ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) R, ‖f z‖ ≤ M)
    (hvan : ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) → ∀ k < n * S₀, iteratedFDeriv ℂ k f ξ = 0) :
    ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) r,
      ‖f z‖ ≤ n * (2 * 3 ^ n * r / R) ^ (S₀ * S₁) * M := by
  intro z hz
  obtain ⟨g, -, -, hgr, hgv⟩ := CartesianSchwarz.exists_after hf hE hr hEr hR hM hvan n le_rfl
  have hg0 : g z = 0 := by
    simpa using hgv 0 Fin.elim0 (fun t => t.elim0) (by simp; omega) z
      (fun j hj => absurd j.2 (by omega))
  have h := hgr z hz
  rw [hg0, sub_zero] at h
  rw [mul_assoc]
  exact h
