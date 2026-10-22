-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.rank_one_channel_normalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:06:13.404887+00:00
-- url     : https://prove2.me/submissions/3c85a92d-07b2-4da5-839f-b56bb3a695b2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

theorem g67w_eq_one_of_trace {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (h : ∀ ρ : Matrix n n ℂ, (M * ρ).trace = ρ.trace) : M = 1 := by
  rw [Matrix.ext_iff_trace_mul_right]
  intro x
  rw [Matrix.one_mul, h]

theorem g67w_tr {ι A B : Type*} [Fintype ι] [Fintype A] [Fintype B] (F : ι → Matrix B A ℂ)
    (ρ : Matrix A A ℂ) :
    ((∑ j, (F j)ᴴ * F j) * ρ).trace = ∑ j, (F j * ρ * (F j)ᴴ).trace := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

theorem solution [Nonempty A]
    (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    IsChannel (krausApply (rankOneKraus psi phi)) ↔
      ∑ k, ((‖phi k‖ ^ 2 : ℝ) : ℂ) • pureDensity (psi k) = 1 := by
  have hnorm : ∀ k, ((‖phi k‖ ^ 2 : ℝ) : ℂ) = ∑ b, conj (phi k b) * phi k b := by
    intro k
    have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (phi k)
    rw [PiLp.inner_apply] at h1
    have h2 : ∀ x : ℂ, inner ℂ x x = conj x * x := fun x => by simp [Complex.conj_mul']
    simp only [h2] at h1
    rw [h1]
    push_cast
    rfl
  have hKK : ∀ k, (rankOneKraus psi phi k)ᴴ * rankOneKraus psi phi k =
      ((‖phi k‖ ^ 2 : ℝ) : ℂ) • pureDensity (psi k) := by
    intro k
    ext a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rankOneKraus, Matrix.smul_apply,
      pureDensity, Matrix.of_apply, smul_eq_mul, hnorm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [star_mul', RCLike.star_def, Complex.conj_conj]
    ring
  have hsum : ∑ k, (rankOneKraus psi phi k)ᴴ * rankOneKraus psi phi k =
      ∑ k, ((‖phi k‖ ^ 2 : ℝ) : ℂ) • pureDensity (psi k) := Finset.sum_congr rfl fun k _ => hKK k
  constructor
  · rintro ⟨m, E, hE, hΦ⟩
    rw [← hsum]
    apply g67w_eq_one_of_trace
    intro ρ
    have h := congrArg Matrix.trace (hΦ ρ)
    simp only [krausApply, Matrix.trace_sum] at h
    rw [g67w_tr, h, ← g67w_tr, hE, Matrix.one_mul]
  · intro h
    refine ⟨Fintype.card K, fun j => rankOneKraus psi phi ((Fintype.equivFin K).symm j), ?_, fun ρ => ?_⟩
    · show ∑ j, _ = _
      rw [Equiv.sum_comp (Fintype.equivFin K).symm (fun k => (rankOneKraus psi phi k)ᴴ * rankOneKraus psi phi k),
        hsum, h]
    · simp only [krausApply]
      exact (Equiv.sum_comp (Fintype.equivFin K).symm
        (fun k => rankOneKraus psi phi k * ρ * (rankOneKraus psi phi k)ᴴ)).symm
