-- Prove2me | solution 1 for SubSuperStoch.AsyncTrack.error_system
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:37.422502+00:00
-- url     : https://prove2.me/submissions/8bd592cc-de65-4d31-9b4e-1ef63cc665f2

import Definitions.Def_SubSuperStoch_AsyncTrack_SignedDigraph
import Definitions.Def_SubSuperStoch_AsyncTrack_AsyncModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Matrix Finset SubSuperStoch.AsyncTrack
attribute [local instance] Classical.propDecidable Classical.decEq

set_option autoImplicit false

namespace D26Error

noncomputable def gauge {n : ℕ} (V : Set (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ V then 1 else -1

lemma abs_sign (t : ℝ) : |t| * Real.sign t = t := by
  rcases lt_trichotomy t 0 with hn | hz | hp
  · rw [abs_of_neg hn, Real.sign_of_neg hn]
    ring
  · simp [hz]
  · rw [abs_of_pos hp, Real.sign_of_pos hp, mul_one]

lemma gauge_edge {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (V : Set (Fin n)) (h : StructBalanced a b V) (i j : Fin n) :
    gauge V i * a i j = |a i j| * gauge V j := by
  classical
  by_cases hi : i ∈ V <;> by_cases hj : j ∈ V
  · rw [gauge, gauge, if_pos hi, if_pos hj, abs_of_nonneg ((h.1 i j).1 (by simp [hi, hj]))]
    ring
  · rw [gauge, gauge, if_pos hi, if_neg hj, abs_of_nonpos ((h.1 i j).2 (by simp [hi, hj]))]
    ring
  · rw [gauge, gauge, if_neg hi, if_pos hj, abs_of_nonpos ((h.1 i j).2 (by simp [hi, hj]))]
    ring
  · rw [gauge, gauge, if_neg hi, if_neg hj, abs_of_nonneg ((h.1 i j).1 (by simp [hi, hj]))]
    ring

lemma gauge_leader {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (V : Set (Fin n)) (h : StructBalanced a b V) (i : Fin n) :
    gauge V i * b i = |b i| := by
  classical
  by_cases hi : i ∈ V
  · rw [gauge, if_pos hi, abs_of_nonneg ((h.2 i).1 hi), one_mul]
  · rw [gauge, if_neg hi, abs_of_nonpos ((h.2 i).2 hi)]
    ring

lemma scalar_protocol {n : ℕ} (a : Fin n → ℝ) (b si : ℝ) (sj : Fin n → ℝ)
    (hA : ∀ j, si * a j = |a j| * sj j) (hb : si * b = |b|)
    (x z τ ψ : ℝ) (y : Fin n → ℝ) :
    si * (x + τ * (ψ * (∑ j, |a j| * (Real.sign (a j) * y j - x)) +
      ψ * (|b| * (Real.sign b * z - x)))) - z =
    (1 - (τ * ψ) * ((∑ j, |a j|) + |b|)) * (si * x - z) +
      ∑ j, (τ * ψ) * |a j| * (sj j * y j - z) := by
  have hterm : ∀ j, si * (|a j| * (Real.sign (a j) * y j - x)) =
      |a j| * (sj j * y j - si * x) := by
    intro j
    calc
      _ = (si * (|a j| * Real.sign (a j))) * y j - |a j| * (si * x) := by ring
      _ = (|a j| * sj j) * y j - |a j| * (si * x) := by rw [abs_sign, hA]
      _ = _ := by ring
  have hleader : si * (|b| * (Real.sign b * z - x)) = |b| * (z - si * x) := by
    calc
      _ = (si * (|b| * Real.sign b)) * z - |b| * (si * x) := by ring
      _ = |b| * z - |b| * (si * x) := by rw [abs_sign, hb]
      _ = _ := by ring
  have hsum1 : (∑ j, |a j| * (sj j * y j - si * x)) =
      (∑ j, |a j| * (sj j * y j)) - (∑ j, |a j|) * (si * x) := by
    simp only [mul_sub, sum_sub_distrib, sum_mul]
  have hsum2 : (∑ j, (τ * ψ) * |a j| * (sj j * y j - z)) =
      (τ * ψ) * ((∑ j, |a j| * (sj j * y j)) - (∑ j, |a j|) * z) := by
    calc
      _ = (τ * ψ) * ∑ j, |a j| * (sj j * y j - z) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [mul_sub, sum_sub_distrib, sum_mul]
  calc
    _ = (si * x - z) + τ * ψ *
        ((∑ j, si * (|a j| * (Real.sign (a j) * y j - x))) +
          si * (|b| * (Real.sign b * z - x))) := by
      rw [← mul_sum]
      ring
    _ = (si * x - z) + τ * ψ *
        ((∑ j, |a j| * (sj j * y j - si * x)) + |b| * (z - si * x)) := by
      simp_rw [hterm, hleader]
    _ = _ := by
      rw [hsum1, hsum2]
      ring

lemma entry {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (s : Fin n → ℕ → ℕ) (k : ℕ) (i j : Fin n) :
    Mmat a b τ ψ s k i j =
      if active s i k then
        (if i = j then 1 - (τ * ψ) * ((∑ z, |a i z|) + |b i|) else 0) +
          (τ * ψ) * |a i j|
      else if i = j then 1 else 0 := by
  classical
  change ((if i = j then 1 else 0) -
      (τ*ψ) * (if i = j then (∑ z, |if active s i k then a i z else 0|) else 0) -
      (τ*ψ) * (if i = j then (if active s i k then |b i| else 0) else 0) +
      (τ*ψ) * |if active s i k then a i j else 0|) = _
  by_cases hij : i = j
  · subst j
    by_cases ha : active s i k <;> simp [ha] <;> ring
  · by_cases ha : active s i k <;> simp [ha,hij]

end D26Error

theorem solution {n p : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (s : Fin n → ℕ → ℕ)
    (V₁ : Set (Fin n)) (hC1 : StructBalanced a b V₁)
    (x0 : ℕ → EuclideanSpace ℝ (Fin p)) (x : Fin n → ℕ → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun a b τ ψ s x0 x) :
    ∀ k i, errVec V₁ x0 x i (k + 1) = ∑ j, Mmat a b τ ψ s k i j • errVec V₁ x0 x j k := by
  classical
  intro k i
  have herr : ∀ j t, errVec V₁ x0 x j t = D26Error.gauge V₁ j • x j t - x0 t := by
    intro j t
    by_cases hj : j ∈ V₁ <;> simp [errVec, D26Error.gauge, hj]
  simp_rw [herr]
  rw [hrun.2 i k, hrun.1 k]
  by_cases ha : active s i k
  · simp only [protocol, if_pos ha]
    ext ell
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
      smul_eq_mul]
    simp only [D26Error.entry, if_pos ha, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, add_mul, sum_add_distrib]
    have hdiag : (∑ j : Fin n,
        (if i = j then 1 - (τ * ψ) * ((∑ z, |a i z|) + |b i|) else 0) *
          (D26Error.gauge V₁ j * x j k ell - x0 k ell)) =
        (1 - (τ * ψ) * ((∑ z, |a i z|) + |b i|)) *
          (D26Error.gauge V₁ i * x i k ell - x0 k ell) := by
      simp
    rw [hdiag]
    exact D26Error.scalar_protocol (fun j => a i j) (b i) (D26Error.gauge V₁ i)
      (D26Error.gauge V₁) (D26Error.gauge_edge a b V₁ hC1 i)
      (D26Error.gauge_leader a b V₁ hC1 i) (x i k ell) (x0 k ell) τ ψ
      (fun j => x j k ell)
  · simp [protocol, ha, D26Error.entry]

#print axioms solution









