-- Prove2me | solution 1 for UnQuantumMechanics.heisenberg_solution_symplectic_similarity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:41:56.130844+00:00
-- url     : https://prove2.me/submissions/925191fc-151f-4bc6-a27f-f5b8e2337d9e

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQM15714d90

lemma main_gen {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : 𝔸) (S : ℝ → 𝔸) (hS : ∀ t, HasDerivAt S (H * S t - S t * H) t) (τ : ℝ) :
    NormedSpace.exp ((-τ) • H) * S τ * NormedSpace.exp (τ • H) = S 0 := by
  have hcomm : ∀ t : ℝ, Commute H (NormedSpace.exp (t • H)) := fun t =>
    ((Commute.refl H).smul_right t).exp_right
  have hFd : ∀ t, HasDerivAt
      (fun u : ℝ => NormedSpace.exp ((-u) • H) * S u * NormedSpace.exp (u • H)) 0 t := by
    intro t
    have hE := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) H (-t)).scomp t (hasDerivAt_neg t)
    have h := (hE.mul (hS t)).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) H t)
    refine h.congr_deriv ?_
    have hc := (hcomm (-t)).eq
    simp only [neg_one_smul, Pi.mul_apply, Function.comp_def]
    rw [hc]
    noncomm_ring
  have hconst := is_const_of_deriv_eq_zero (fun x => (hFd x).differentiableAt)
      (fun x => (hFd x).deriv) τ 0
  simpa using hconst

lemma exp_pair {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : 𝔸) (τ : ℝ) :
    NormedSpace.exp (τ • H) * NormedSpace.exp ((-τ) • H) = 1 := by
  have e := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl H).smul_left τ).smul_right (-τ))
    ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
  rw [show τ • H + (-τ) • H = 0 by simp, NormedSpace.exp_zero] at e
  exact e.symm

lemma exp_pair' {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : 𝔸) (τ : ℝ) :
    NormedSpace.exp ((-τ) • H) * NormedSpace.exp (τ • H) = 1 := by
  simpa using exp_pair H (-τ)

lemma conclude_gen {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : 𝔸) (S : ℝ → 𝔸) (hS : ∀ t, HasDerivAt S (H * S t - S t * H) t) (τ : ℝ) :
    S τ = NormedSpace.exp (τ • H) * S 0 * NormedSpace.exp ((-τ) • H) := by
  rw [← main_gen H S hS τ]
  calc S τ = (NormedSpace.exp (τ • H) * NormedSpace.exp ((-τ) • H)) * S τ *
      (NormedSpace.exp (τ • H) * NormedSpace.exp ((-τ) • H)) := by rw [exp_pair]; simp
    _ = _ := by simp only [mul_assoc]

lemma matrix_hasDerivAt {m : Type} [Fintype m] (S : ℝ → Matrix m m ℝ) (S' : Matrix m m ℝ)
    (τ : ℝ) (h : ∀ i j, HasDerivAt (fun t => S t i j) (S' i j) τ) :
    HasDerivAt S S' τ := by
  have h1 : ∀ i, HasDerivAt (fun t => S t i) (S' i) τ := fun i =>
    (hasDerivAt_pi (φ := fun t => S t i) (φ' := S' i)).2 (h i)
  exact (hasDerivAt_pi (φ := fun t => (S t : m → m → ℝ)) (φ' := (S' : m → m → ℝ))).2 h1

lemma matrix_case {m : Type} [Fintype m] [DecidableEq m] (H : Matrix m m ℝ)
    (S : ℝ → Matrix m m ℝ)
    (hS : ∀ τ i j, HasDerivAt (fun t => S t i j) ((H * S τ - S τ * H) i j) τ) (τ : ℝ) :
    S τ = NormedSpace.exp (τ • H) * S 0 * NormedSpace.exp ((-τ) • H) := by
  let _ : NormedRing (Matrix m m ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix m m ℝ) := Matrix.linftyOpNormedAlgebra
  exact conclude_gen H S (fun t => matrix_hasDerivAt S _ t (hS t)) τ

end UnQM15714d90

open Matrix in
theorem solution (n : ℕ) (H : Matrix (UnQuantumMechanics.PhaseIdx n) (UnQuantumMechanics.PhaseIdx n) ℝ)
    (hH : UnQuantumMechanics.IsHamiltonianMatrix n H) (S : ℝ → Matrix (UnQuantumMechanics.PhaseIdx n) (UnQuantumMechanics.PhaseIdx n) ℝ)
    (hS : ∀ τ i j, HasDerivAt (fun t => S t i j) ((H * S τ - S τ * H) i j) τ) (τ : ℝ) :
    S τ = NormedSpace.exp (τ • H) * S 0 * NormedSpace.exp ((-τ) • H) := by
  exact UnQM15714d90.matrix_case H S hS τ
