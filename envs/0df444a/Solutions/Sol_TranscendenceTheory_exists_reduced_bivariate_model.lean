-- Prove2me | solution 1 for TranscendenceTheory.exists_reduced_bivariate_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T09:52:53.689573+00:00
-- url     : https://prove2.me/submissions/2e2d7876-7b90-4903-9d87-526de1775e94

import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open Polynomial Module
open scoped Polynomial

theorem solution (θ ν : ℂ) (hθ : Transcendental ℚ θ)
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0) :
    ∃ g : ℤ[X][X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ p : ℤ[X][X], p.eval₂ (aeval θ).toRingHom ν = 0 ↔ g ∣ p) ∧
      (∀ p : ℤ[X][X], ∃! q : ℤ[X][X], q.natDegree < g.natDegree ∧
        q.eval₂ (aeval θ).toRingHom ν = p.eval₂ (aeval θ).toRingHom ν) := by
  have hθZ : Transcendental ℤ θ := hθ.restrictScalars (algebraMap ℤ ℚ).injective_int
  let : Algebra ℤ[X] ℂ := (aeval θ).toAlgebra
  have : IsTorsionFree ℤ[X] ℂ := (isTorsionFree_iff_algebraMap_injective).mpr
    (transcendental_iff_injective.mp hθZ)
  have hint : IsIntegral ℤ[X] ν := hν
  let g := minpoly ℤ[X] ν
  have hg : g.Monic := minpoly.monic hint
  have hpos : 0 < g.natDegree := minpoly.natDegree_pos hint
  have hker (p : ℤ[X][X]) : p.eval₂ (aeval θ).toRingHom ν = 0 ↔ g ∣ p :=
    minpoly.isIntegrallyClosed_dvd_iff hint p
  refine ⟨g, hg, hpos, hker, ?_⟩
  intro p
  have hg1 : g ≠ 1 := by
    intro h
    simp [h] at hpos
  have hrem : (p %ₘ g).natDegree < g.natDegree := natDegree_modByMonic_lt p hg hg1
  have heval : (p %ₘ g).eval₂ (aeval θ).toRingHom ν =
      p.eval₂ (aeval θ).toRingHom ν := minpoly.aeval_modByMonic_minpoly p ν
  refine ⟨p %ₘ g, ⟨hrem, heval⟩, ?_⟩
  intro q hq
  apply sub_eq_zero.mp
  by_contra hne
  have hdvd : g ∣ q - p %ₘ g := (hker _).mp (by
    rw [eval₂_sub, hq.2, heval, sub_self])
  have hle := natDegree_le_of_dvd hdvd hne
  have hlt : (q - p %ₘ g).natDegree < g.natDegree :=
    (natDegree_sub_le _ _).trans_lt (max_lt hq.1 hrem)
  exact hlt.not_ge hle

