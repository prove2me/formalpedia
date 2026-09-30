-- Prove2me | solution 1 for TranscendenceTheory.analytic_orbit_transverse_derivative
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T19:01:50.29922+00:00
-- url     : https://prove2.me/submissions/d57cd7f2-f63e-4766-a635-843d8a56bbf7

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

open scoped Topology

namespace TranscendenceTheory

private lemma orbit_iterate_germ
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (φ : R →ₐ[ℚ] (ℂ → ℂ)) (z : ℂ)
    (hD : ∀ r, φ (D r) =ᶠ[𝓝 z] deriv (φ r)) (f : R) (n : ℕ) :
    φ ((D^[n]) f) =ᶠ[𝓝 z] iteratedDeriv n (φ f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    exact (hD _).trans ih.deriv


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R)
    (φ : R →ₐ[ℚ] (ℂ → ℂ)) (z : ℂ)
    (hD : ∀ r, φ (D r) =ᶠ[𝓝 z] deriv (φ r))
    (hzero : ∀ r ∈ p, φ r z = 0)
    (f : R) (hf : f ∈ p) (hanalytic : AnalyticAt ℂ (φ f) z)
    (hfinite : analyticOrderAt (φ f) z ≠ ⊤) :
    ∃ n k : ℕ, analyticOrderAt (φ f) z = (n : ℕ∞) ∧ k < n ∧
      (D^[k]) f ∈ p ∧ (D^[k + 1]) f ∉ p := by
  classical
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hnonzero : iteratedDeriv n (φ f) z ≠ 0 :=
    ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hanalytic).mp hn.symm).2
  have hescape : (D^[n]) f ∉ p := by
    intro hmem
    apply hnonzero
    exact (orbit_iterate_germ D φ z hD f n).self_of_nhds.symm.trans (hzero _ hmem)
  have hexists : ∃ j : ℕ, (D^[j]) f ∉ p := ⟨n, hescape⟩
  have hleast := Nat.find_spec hexists
  have hle : Nat.find hexists ≤ n := Nat.find_min' hexists hescape
  have hpos : 0 < Nat.find hexists := by
    by_contra h
    have hz : Nat.find hexists = 0 := by omega
    exact (show f ∉ p by simpa [hz] using hleast) hf
  refine ⟨n, Nat.find hexists - 1, hn.symm, by omega, ?_, ?_⟩
  · by_contra hmem
    exact Nat.find_min hexists (by omega) hmem
  · have heq : Nat.find hexists - 1 + 1 = Nat.find hexists := by omega
    simpa only [heq] using hleast
