-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P19.positiveFilter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:22:29.74699+00:00
-- url     : https://prove2.me/submissions/571455cf-979c-4025-933d-5e35113f04f3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

namespace X7pf

open QAlgorithms

theorem sep_conj {K J : Type*} [Fintype K] [Fintype J] [DecidableEq K]
    (X : Matrix (K × J) (K × J) ℂ) (hX : Entanglement.IsSeparablePositive X)
    (Y : Matrix J J ℂ) (hY : Y.PosSemidef) :
    Entanglement.IsSeparablePositive
      (Matrix.kronecker (1 : Matrix K K ℂ) Y * X * Matrix.kronecker (1 : Matrix K K ℂ) Y) := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  have hYh : Yᴴ = Y := hY.isHermitian
  set t : Fin q → ℝ := fun j => (Y * B j * Y).trace.re with htdef
  have hpsd : ∀ j, (Y * B j * Y).PosSemidef := by
    intro j
    have := (hAB j).2.1.conjTranspose_mul_mul_same Y
    rwa [hYh] at this
  have ht0 : ∀ j, 0 ≤ t j := fun j => (Complex.nonneg_iff.mp (hpsd j).trace_nonneg).1
  have htc : ∀ j, (Y * B j * Y).trace = (t j : ℂ) := by
    intro j
    have h := Complex.nonneg_iff.mp (hpsd j).trace_nonneg
    apply Complex.ext <;> simp [htdef, h.2.symm]
  let B' : Fin q → Matrix J J ℂ := fun j => if t j = 0 then B j else ((t j)⁻¹ : ℂ) • (Y * B j * Y)
  refine ⟨q, fun j => w j * t j, A, B', fun j => mul_nonneg (hw j) (ht0 j), fun j => ⟨(hAB j).1, ?_⟩, ?_⟩
  · by_cases h : t j = 0
    · simp only [B', if_pos h]; exact (hAB j).2
    · simp only [B', if_neg h]
      refine ⟨(hpsd j).smul ?_, ?_⟩
      · have : (0 : ℝ) ≤ (t j)⁻¹ := inv_nonneg.mpr (ht0 j)
        exact_mod_cast this
      · rw [Matrix.trace_smul, htc, smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
          inv_mul_cancel₀ h, Complex.ofReal_one]
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Matrix.kronecker
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
    by_cases h : t j = 0
    · have hz : Y * B j * Y = 0 := by
        rw [← (hpsd j).trace_eq_zero_iff, htc, h, Complex.ofReal_zero]
      simp [B', h, hz]
    · simp only [B', if_neg h, Matrix.kronecker_smul, smul_smul]
      congr 1
      push_cast
      field_simp

end X7pf

end

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal
open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)
open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

theorem X7pf_main [Nonempty I] [Nonempty J] (N : Superop I J) (hCP : FiniteKrausCP N) (hEB : IsEB N)
    (Y : Matrix J J ℂ) (hY : Y.PosSemidef) :
    FiniteKrausCP (filtered Y N) ∧ IsEB (filtered Y N) := by
  have hYh : Yᴴ = Y := hY.isHermitian
  constructor
  · obtain ⟨r, E, hE⟩ := hCP
    refine ⟨r, fun k => Y * E k, ?_⟩
    funext X
    simp only [filtered, hE, krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, hYh,
      Matrix.mul_assoc]
  · intro k hk rho hrho
    have e : idTensorSuperop (filtered Y N) rho =
        Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Y * idTensorSuperop N rho *
          Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Y := by
      ext ⟨p, a⟩ ⟨q, b⟩
      simp only [idTensorSuperop, filtered, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
      rw [Fintype.sum_eq_single q (fun s hs => by simp [hs])]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    rw [e]
    exact X7pf.sep_conj _ (hEB k hk rho hrho) Y hY

end QAlgorithms.Papers.Independent.Support50.P19

end

section
open scoped Matrix ComplexOrder ComplexConjugate ENNReal
open Filter Topology
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P19
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)
open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

theorem solution [Nonempty I] [Nonempty J] (N : Superop I J) (hCP : FiniteKrausCP N) (hEB : IsEB N)
    (Y : Matrix J J ℂ) (hY : Y.PosSemidef) :
    FiniteKrausCP (filtered Y N) ∧ IsEB (filtered Y N) :=
  X7pf_main N hCP hEB Y hY

end
