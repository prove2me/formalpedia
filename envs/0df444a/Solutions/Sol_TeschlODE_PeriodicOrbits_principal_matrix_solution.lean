-- Prove2me | solution 1 for TeschlODE.PeriodicOrbits.principal_matrix_solution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T18:55:47.728871+00:00
-- url     : https://prove2.me/submissions/c0641c22-7844-4409-b44f-67c643a2ba2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Theorems.Thm_TeschlODE_Shared_flow_fderiv_smul_sub_one
import Theorems.Thm_TeschlODE_Shared_flow_fderiv_sub_one_eq_id
import Theorems.Thm_TeschlODE_Shared_flow_periodic_orbit_global_everywhere
import Theorems.Thm_TeschlODE_Shared_flow_mem_of_mem
import Theorems.Thm_TeschlODE_Shared_flow_fderiv_chain_first_variational
import Theorems.Thm_TeschlODE_Shared_flow_tangent_derivative_relation

open TeschlODE.Shared
open TeschlODE.PeriodicOrbits

/-!
Reduction of Teschl, Lemma 12.1 (p. 316) to three published flow-derivative children.

`TeschlODE_Shared_IsMaximalFlow` fixes `Φ` only in the *time* variable, so on its own it does
not determine the Jacobian `∂Φ_t/∂x (Φ t₀ x₀)` that this statement quantifies over, and it does
not give `t - t₀ ∈ I x₀` for arbitrary `t₀, t`. Both gaps are supplied here:

* conjunct (1), `fderiv ℝ (Φ (t₀ - t₀)) (Φ t₀ x₀) = id`, is the zero-shift identity
  `J(t₀, t₀) = I` of (12.5). Since `t₀ - t₀ = 0` and (6.12) gives `Φ 0 y = y`, the derivative is
  taken of the constant identity map, so it is the identity at every point — no child needed.
* conjunct (2a), `DifferentiableAt ℝ (Φ (t - t₀)) (Φ t₀ x₀)`, is conjunct 2 of
  `flow_fderiv_smul_sub_one`, which also supplies `I x₀ = ℝ`. That interval fact is what makes the
  target's `∀ t₀ t : ℝ` quantifier reachable at all: a periodic point of a maximal unique flow has
  global interval of existence, because uniqueness forces `I x₀ - T ⊆ I x₀` and iterating from
  `T ∈ I x₀` fills `ℝ`.
* conjunct (2b), the matrix initial value problem `∂ₜ J(t) = A(t) J(t)`, is
  `flow_fderiv_chain_first_variational`.
* conjunct (3), Eq. (12.6), is `flow_tangent_derivative_relation`.
-/


theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : IsRegularPeriodicPoint I Φ x₀ T) :
    (∀ t₀ : ℝ, fderiv ℝ (Φ (t₀ - t₀)) (Φ t₀ x₀) = ContinuousLinearMap.id ℝ (Fin n → ℝ)) ∧
    ∀ t₀ t : ℝ,
      DifferentiableAt ℝ (Φ (t - t₀)) (Φ t₀ x₀) ∧
      HasDerivAt (fun s : ℝ => fderiv ℝ (Φ (s - t₀)) (Φ t₀ x₀))
        ((fderiv ℝ f (Φ t x₀)).comp (fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀))) t ∧
      f (Φ t x₀) = fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀) (f (Φ t₀ x₀)) := by
  have hper' : 0 < T ∧ T ∈ I x₀ ∧ Φ T x₀ = x₀ := ⟨hper.1, hper.2.1, hper.2.2.1⟩
  obtain ⟨hI, hDiff⟩ :=
    flow_fderiv_smul_sub_one (f := f) (M := M) (hM := hM) (k := k) (hk := hk) (hf := hf)
      (I := I) (Φ := Φ) (hΦ := hΦ) (x₀ := x₀) (hx₀ := hx₀) (T := T) hper'
  constructor
  · intro t₀
    have ht₀ : t₀ ∈ I x₀ := by rw [hI]; exact Set.mem_univ t₀
    have hzM : Φ t₀ x₀ ∈ M :=
      flow_mem_of_mem (f := f) (M := M) (hM := hM) (I := I) (Φ := Φ) (hΦ := hΦ)
        (x := x₀) (hx := hx₀) (t := t₀) ht₀
    have hzI : I (Φ t₀ x₀) = Set.univ :=
      flow_periodic_orbit_global_everywhere (f := f) (M := M) (hM := hM) (I := I) (Φ := Φ)
        (hΦ := hΦ) (x₀ := x₀) (hx₀ := hx₀) (T := T) hper.1 hper.2.1 hper.2.2.1 (z := Φ t₀ x₀) hzM
    have ht₀' : t₀ ∈ I (Φ t₀ x₀) := by rw [hzI]; exact Set.mem_univ t₀
    exact flow_fderiv_sub_one_eq_id (f := f) (M := M) (hM := hM) (k := k) (hk := hk) (hf := hf)
      (I := I) (Φ := Φ) (hΦ := hΦ) (x := Φ t₀ x₀) (s := t₀) (t := 0) hzM ht₀'
      (by rw [hzI]; exact Set.mem_univ 0)
  · intro t₀ t
    refine ⟨hDiff t₀ t, ?_, ?_⟩
    · exact flow_fderiv_chain_first_variational (f := f) (M := M) (hM := hM) (k := k) (hk := hk)
        (hf := hf) (I := I) (Φ := Φ) (hΦ := hΦ) (x₀ := x₀) (hx₀ := hx₀) (T := T) hper' t₀ t
    · exact flow_tangent_derivative_relation (f := f) (M := M) (hM := hM) (k := k) (hk := hk)
        (hf := hf) (I := I) (Φ := Φ) (hΦ := hΦ) (x₀ := x₀) (hx₀ := hx₀) (T := T) hper' t₀ t
