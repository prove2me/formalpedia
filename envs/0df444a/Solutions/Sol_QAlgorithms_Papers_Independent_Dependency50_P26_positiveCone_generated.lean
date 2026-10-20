-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.positiveCone_generated
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:47.714853+00:00
-- url     : https://prove2.me/submissions/dfce980f-8693-4ba2-aeb5-8dbd73371873

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

open scoped MatrixOrder Matrix.Norms.L2Operator in
lemma g52a_psd_le_norm {I : Type*} [Fintype I] [DecidableEq I] (R : Matrix I I ℂ)
    (hR : R.PosSemidef) : ∃ B : ℝ, 0 < B ∧ ((B : ℂ) • (1 : Matrix I I ℂ) - R).PosSemidef := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self (a := R) hR.1
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  refine ⟨‖R‖ + 1, by positivity, ?_⟩
  have e : (((‖R‖ + 1 : ℝ) : ℂ) • (1 : Matrix I I ℂ) - R) = (‖R‖ • (1 : Matrix I I ℂ) - R) + 1 := by
    rw [← Complex.coe_smul]; simp [add_smul]; abel
  rw [e]
  exact h.add Matrix.PosSemidef.one

lemma g52a_tl {α β : Type*} [Fintype α] {_i1 : DecidableEq (α × β)} {_i2 : DecidableEq β}
    (c : ℂ) : traceLeft (c • (1 : Matrix (α × β) (α × β) ℂ)) =
      (c * Fintype.card α) • (1 : Matrix β β ℂ) := by
  ext b b'
  by_cases h : b = b' <;> simp [traceLeft, Matrix.one_apply, h, Finset.sum_const, mul_comm]

lemma g52a_kr {α β : Type*} {_i0 : DecidableEq α} {_i1 : DecidableEq (α × β)}
    {_i2 : DecidableEq β} (c : ℂ) :
    Matrix.kronecker (1 : Matrix α α ℂ) (c • (1 : Matrix β β ℂ)) =
      c • (1 : Matrix (α × β) (α × β) ℂ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [Matrix.one_apply, h1, h2]

lemma g52a_norm_scalar (s : Signature) : ∀ n : ℕ,
    Normalized s n ((((∏ j ∈ Finset.range n, (s.output j : ℝ))⁻¹ : ℝ) : ℂ) •
      (1 : Matrix (Basis s n) (Basis s n) ℂ)) := by
  intro n
  induction n with
  | zero => simp [Normalized]
  | succ n ih =>
    refine ⟨Matrix.PosSemidef.one.smul ?_, _, ih, ?_⟩
    · have : (0:ℝ) ≤ (∏ j ∈ Finset.range (n+1), (s.output j : ℝ))⁻¹ := by positivity
      exact_mod_cast this
    · have hPc : (∏ j ∈ Finset.range n, (s.output j : ℂ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (s.output_pos j).ne'
      have hoc : (s.output n : ℂ) ≠ 0 := by exact_mod_cast (s.output_pos n).ne'
      refine (g52a_tl (α := Fin (s.output n)) (β := Fin (s.input n) × Basis s n)
        (_i2 := Classical.decEq _) _).trans ?_
      refine Eq.trans ?_ (g52a_kr (α := Fin (s.input n)) (β := Basis s n)
        (_i1 := Classical.decEq _) _).symm
      congr 1
      rw [Finset.prod_range_succ, Fintype.card_fin]
      push_cast
      field_simp

/-- PDF p.11, Lemma 5: the proof's positive rescaling formulation of generation of the cone. -/
theorem solution (s : Signature) (n : ℕ) (hn : 0 < n)
    (R : Matrix (Basis s n) (Basis s n) ℂ) (hR : R.PosSemidef) :
    ∃ a : ℝ, 0 < a ∧ ∃ S, Normalized s n S ∧
      (S - (a : ℂ) • R).PosSemidef := by
  obtain ⟨B, hB, hBR⟩ := g52a_psd_le_norm R hR
  set c : ℝ := (∏ j ∈ Finset.range n, (s.output j : ℝ))⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (Finset.prod_pos fun j _ => by exact_mod_cast s.output_pos j)
  refine ⟨c / B, div_pos hcpos hB, _, g52a_norm_scalar s n, ?_⟩
  have e : ((c : ℂ) • (1 : Matrix (Basis s n) (Basis s n) ℂ) - ((c / B : ℝ) : ℂ) • R) =
      ((c / B : ℝ) : ℂ) • ((B : ℂ) • (1 : Matrix (Basis s n) (Basis s n) ℂ) - R) := by
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hB.ne']
  rw [e]
  exact hBR.smul (by exact_mod_cast (div_pos hcpos hB).le)


end

