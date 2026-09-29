-- Prove2me | solution 1 for Rudin.ch10_integral_alternation
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T00:20:43.400883+00:00
-- url     : https://prove2.me/submissions/85455830-a1e2-4412-adef-0ab28575b9e9

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace RudinAux

open Rudin

/-- The standard simplex `Qᵏ` is a measurable subset of `ℝᵏ`. -/
lemma measurableSet_stdSimplex (k : ℕ) : MeasurableSet (Rudin.stdSimplex k) := by
  have h : Rudin.stdSimplex k
      = (⋂ i : Fin k, {u : Fin k → ℝ | 0 ≤ u i}) ∩ {u : Fin k → ℝ | ∑ i, u i ≤ 1} := by
    ext u
    simp [Rudin.stdSimplex, Set.mem_iInter]
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
  · exact measurableSet_le measurable_const (measurable_pi_apply i)
  · exact measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
      measurable_const

/-- Permuting the index tuple of a Jacobian multiplies it by the sign of the permutation. -/
lemma jacobian_comp_perm {k n : ℕ} (Φ : (Fin k → ℝ) → (Fin n → ℝ)) (i : Fin k → Fin n)
    (σ : Equiv.Perm (Fin k)) (u : Fin k → ℝ) :
    Rudin.jacobian Φ (fun r => i (σ r)) u
      = (Equiv.Perm.sign σ : ℝ) * Rudin.jacobian Φ i u := by
  have h := Matrix.det_permute σ
    (Matrix.of fun r s : Fin k => Rudin.partialDeriv (fun v => Φ v (i r)) s u)
  simpa [Rudin.jacobian, Matrix.submatrix] using h

/-- The pointwise statement: a sum `∑_i c_i J_i` against Jacobians vanishes as soon as all the
alternating sums `∑_σ (sgn σ) c_{i∘σ}` vanish. -/
lemma sum_mul_jacobian_eq_zero {k n : ℕ} (Φ : (Fin k → ℝ) → (Fin n → ℝ)) (u : Fin k → ℝ)
    (c : (Fin k → Fin n) → ℝ)
    (hc : ∀ i : Fin k → Fin n,
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * c (fun r => i (σ r)) = 0) :
    ∑ i : Fin k → Fin n, c i * Rudin.jacobian Φ i u = 0 := by
  set S : ℝ := ∑ i : Fin k → Fin n, c i * Rudin.jacobian Φ i u with hS
  have key : ∀ σ : Equiv.Perm (Fin k),
      S = ∑ i : Fin k → Fin n,
        (Equiv.Perm.sign σ : ℝ) * c (fun r => i (σ r)) * Rudin.jacobian Φ i u := by
    intro σ
    have hbij : Function.Bijective
        (fun (i : Fin k → Fin n) => fun r : Fin k => i (σ r)) := by
      constructor
      · intro a b h
        funext r
        have := congrFun h (σ.symm r)
        simpa using this
      · intro b
        exact ⟨fun r => b (σ.symm r), by funext r; simp⟩
    have hsum : ∑ i : Fin k → Fin n,
        c (fun r => i (σ r)) * Rudin.jacobian Φ (fun r => i (σ r)) u
          = ∑ i : Fin k → Fin n, c i * Rudin.jacobian Φ i u :=
      Fintype.sum_bijective _ hbij _ _ fun _ => rfl
    rw [hS, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [jacobian_comp_perm Φ i σ u]
    ring
  have hsum0 : ∑ _σ : Equiv.Perm (Fin k), S = 0 := by
    calc ∑ _σ : Equiv.Perm (Fin k), S
        = ∑ σ : Equiv.Perm (Fin k), ∑ i : Fin k → Fin n,
            (Equiv.Perm.sign σ : ℝ) * c (fun r => i (σ r)) * Rudin.jacobian Φ i u :=
          Finset.sum_congr rfl fun σ _ => key σ
      _ = ∑ i : Fin k → Fin n, ∑ σ : Equiv.Perm (Fin k),
            ((Equiv.Perm.sign σ : ℝ) * c (fun r => i (σ r))) * Rudin.jacobian Φ i u :=
          Finset.sum_comm
      _ = ∑ i : Fin k → Fin n,
            (∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * c (fun r => i (σ r)))
              * Rudin.jacobian Φ i u := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      _ = 0 := Finset.sum_eq_zero fun i _ => by rw [hc i, zero_mul]
  have hcard : ((Finset.univ : Finset (Equiv.Perm (Fin k))).card : ℝ) * S = 0 := by
    rw [Finset.sum_const, nsmul_eq_mul] at hsum0
    exact hsum0
  have hne : ((Finset.univ : Finset (Equiv.Perm (Fin k))).card : ℝ) ≠ 0 := by
    simp [Finset.card_univ, Fintype.card_ne_zero]
  exact (mul_eq_zero.mp hcard).resolve_left hne

end RudinAux

open Rudin in
/-- Rudin, Chapter 10, equations (35) and (38)–(39): the integral of a `k`-form over a
`k`-surface depends on the coefficients only through their alternations. -/
theorem solution (k n : ℕ) (E : Set (Fin n → ℝ)) (ω₁ ω₂ : KForm k n)
    (halt : ∀ x ∈ E, ∀ i : Fin k → Fin n,
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ω₁.coeff (fun r => i (σ r)) x
        = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ω₂.coeff (fun r => i (σ r)) x)
    (Φ : SimplexSurface k n) (hΦ : ∀ u ∈ stdSimplex k, Φ.map u ∈ E) :
    integralOverSimplex ω₁ Φ = integralOverSimplex ω₂ Φ := by
  unfold integralOverSimplex
  refine MeasureTheory.setIntegral_congr_fun (RudinAux.measurableSet_stdSimplex k) ?_
  intro u hu
  have hx : Φ.map u ∈ E := hΦ u hu
  have hzero : ∑ i : Fin k → Fin n,
      (ω₁.coeff i (Φ.map u) - ω₂.coeff i (Φ.map u)) * jacobian Φ.map i u = 0 := by
    refine RudinAux.sum_mul_jacobian_eq_zero Φ.map u _ fun i => ?_
    have h1 := halt (Φ.map u) hx i
    have h2 : ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) *
        (ω₁.coeff (fun r => i (σ r)) (Φ.map u) - ω₂.coeff (fun r => i (σ r)) (Φ.map u))
        = (∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) *
              ω₁.coeff (fun r => i (σ r)) (Φ.map u))
          - ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) *
              ω₂.coeff (fun r => i (σ r)) (Φ.map u) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [h2, h1, sub_self]
  have hexpand : ∑ i : Fin k → Fin n,
      (ω₁.coeff i (Φ.map u) - ω₂.coeff i (Φ.map u)) * jacobian Φ.map i u
      = (∑ i : Fin k → Fin n, ω₁.coeff i (Φ.map u) * jacobian Φ.map i u)
        - ∑ i : Fin k → Fin n, ω₂.coeff i (Φ.map u) * jacobian Φ.map i u := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexpand] at hzero
  linarith
