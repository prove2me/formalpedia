-- Prove2me | solution 1 for ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c92fa88b-f876-5507-9649-409507f35eaa

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Algebraic.Integral
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup

open scoped Pointwise

namespace NIsoAux

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem apply_mem_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A :=
    MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

theorem apply_mem_nonunits_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A.nonunits ↔ x ∈ A.nonunits := by
  have h1 : σ x = 0 ↔ x = 0 := by
    constructor
    · intro h; exact σ.injective (by rw [h, _root_.map_zero])
    · intro h; rw [h, _root_.map_zero]
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, h1,
    apply_mem_iff hσ]

theorem valuation_lt_of_lt {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {a b : L}
    (h : A.valuation a < A.valuation b) : A.valuation (σ a) < A.valuation (σ b) := by
  have hb : b ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at h
    exact (not_lt_of_ge zero_le') h
  have hb' : σ b ≠ 0 := fun h0 => hb (σ.injective (by rw [h0, _root_.map_zero]))
  have hvb : 0 < A.valuation b := lt_of_le_of_lt zero_le' h
  have hvb' : 0 < A.valuation (σ b) :=
    lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr hb'))

  have hab : a / b ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀ hvb]
    exact h
  have hab' : σ a / σ b ∈ A.nonunits := by
    rw [← map_div₀, apply_mem_nonunits_iff hσ]
    exact hab
  rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀ hvb'] at hab'
  exact hab'

theorem exists_pow_apply_eq [Algebra.IsAlgebraic K L] (σ : L ≃ₐ[K] L) (z : L) :
    ∃ N : ℕ, 0 < N ∧ (σ ^ N) z = z := by
  classical
  have hz : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hp0 : minpoly K z ≠ 0 := minpoly.ne_zero hz
  have hmem : ∀ n : ℕ, (σ ^ n) z ∈ (minpoly K z).rootSet L := by
    intro n
    rw [Polynomial.mem_rootSet]
    refine ⟨hp0, ?_⟩
    rw [Polynomial.aeval_algHom_apply (σ ^ n) z (minpoly K z), minpoly.aeval, _root_.map_zero]
  let f : ℕ → (minpoly K z).rootSet L := fun n => ⟨(σ ^ n) z, hmem n⟩
  obtain ⟨m, n, hmn, hfmn⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hval : (σ ^ m) z = (σ ^ n) z := congrArg Subtype.val hfmn

  have key : ∀ m n : ℕ, m < n → (σ ^ m) z = (σ ^ n) z → ∃ N : ℕ, 0 < N ∧ (σ ^ N) z = z := by
    intro m n hlt heq
    refine ⟨n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    apply (σ ^ m).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    exact heq.symm
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · exact key m n hlt hval
  · exact key n m hlt hval.symm

theorem not_valuation_apply_lt [Algebra.IsAlgebraic K L] {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) (z : L) :
    ¬ A.valuation (σ z) < A.valuation z := by
  intro h

  have step : ∀ k : ℕ, A.valuation ((σ ^ (k + 1)) z) < A.valuation ((σ ^ k) z) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have := valuation_lt_of_lt hσ ih
      rwa [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ', ← pow_succ'] at this
  have chain : ∀ k : ℕ, A.valuation ((σ ^ (k + 1)) z) < A.valuation z := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih => exact lt_trans (step (k + 1)) ih

  obtain ⟨N, hN, hfix⟩ := exists_pow_apply_eq σ z
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have := chain k
  rw [hfix] at this
  exact lt_irrefl _ this

theorem valuation_apply_eq [Algebra.IsAlgebraic K L] {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) (z : L) :
    A.valuation (σ z) = A.valuation z := by
  rcases lt_trichotomy (A.valuation (σ z)) (A.valuation z) with h | h | h
  · exact absurd h (not_valuation_apply_lt hσ z)
  · exact h
  · exfalso
    have hσ' : σ⁻¹ ∈ A.decompositionSubgroup K := (A.decompositionSubgroup K).inv_mem hσ
    apply not_valuation_apply_lt hσ' (σ z)
    have e : σ⁻¹ (σ z) = z := by
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [e]
    exact h

end NIsoAux

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (A : ValuationSubring (AlgebraicClosure ℚ)) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.decompositionSubgroup ℚ) (z : AlgebraicClosure ℚ) : A.valuation (σ z) = A.valuation z := by

  have halg : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    inferInstance
  exact @NIsoAux.valuation_apply_eq ℚ (AlgebraicClosure ℚ) _ _ _ halg A σ hσ z

end S_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
end P2MW
export P2MW.S_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup (solution)
