-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.positiveHistory_instrumentExtension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:08:03.555575+00:00
-- url     : https://prove2.me/submissions/1790569a-1290-40bb-95c9-51a5119943a2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

theorem g52b_rank1_qf {ι : Type*} [Fintype ι] (v x : ι → ℂ) :
    star x ⬝ᵥ (Matrix.vecMulVec v (star v) *ᵥ x) = ((‖x ⬝ᵥ star v‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : star x ⬝ᵥ (Matrix.vecMulVec v (star v) *ᵥ x) = (star x ⬝ᵥ v) * (star v ⬝ᵥ x) := by
    rw [dotProduct, dotProduct, dotProduct, Finset.sum_mul_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : star x ⬝ᵥ v = (starRingEnd ℂ) (x ⬝ᵥ star v) := by
    simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.star_def, mul_comm]
  rw [h1, h2, dotProduct_comm (star v) x, Complex.conj_mul']
  push_cast; ring

theorem g52b_cs {ι : Type*} [Fintype ι] (v x : ι → ℂ) :
    ‖x ⬝ᵥ star v‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * (∑ i, ‖x i‖ ^ 2) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
  change ‖x ⬝ᵥ star v‖ ≤ _ at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

theorem g52b_qf_bound {ι : Type*} [Fintype ι] (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (x : ι → ℂ) : (star x ⬝ᵥ (R *ᵥ x)).re ≤ R.trace.re * ∑ i, ‖x i‖ ^ 2 := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hR
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, Matrix.trace_sum, Complex.re_sum,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [g52b_rank1_qf, Complex.ofReal_re]
  have ht : (Matrix.vecMulVec (v i) (star (v i))).trace.re = ∑ j, ‖v i j‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show star (v i j) = (starRingEnd ℂ) (v i j) from rfl, Complex.mul_conj']
    norm_cast
  rw [ht]
  exact g52b_cs (v i) x

theorem g52b_tl {α β : Type*} [Fintype α] [DecidableEq β] [inst : DecidableEq (α × β)] (c : ℂ) :
    traceLeft (c • (1 : Matrix (α × β) (α × β) ℂ)) = (c * Fintype.card α) • 1 := by
  ext b b'
  by_cases h : b = b' <;> simp [traceLeft, Matrix.one_apply, h, mul_comm]

theorem g52b_kr {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] (d : ℂ) :
    Matrix.kronecker (1 : Matrix γ γ ℂ) (d • (1 : Matrix δ δ ℂ)) = d • 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;>
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, h1, h2]

theorem g52b_ent (s : Signature) (m : ℕ) (c : ℂ) (z w : Basis s m) :
    (c • (1 : Matrix (Basis s m) (Basis s m) ℂ)) z w = if z = w then c else 0 := by
  simp [Matrix.one_apply]

theorem g52b_scalar_normalized (s : Signature) : ∀ m : ℕ,
    Normalized s m (((((∏ j ∈ Finset.range m, s.output j : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • 1)
  | 0 => by
      show _ = _
      simp
  | m + 1 => by
      have hpos : (0 : ℝ) < ((∏ j ∈ Finset.range (m+1), s.output j : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos fun j _ => s.output_pos j
      refine ⟨Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)), _,
        g52b_scalar_normalized s m, ?_⟩
      have ho : (s.output m : ℂ) ≠ 0 := by exact_mod_cast (s.output_pos m).ne'
      have hp : ((∏ j ∈ Finset.range m, s.output j : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Finset.prod_pos fun j _ => s.output_pos j).ne'
      have e1 := g52b_tl (α := Fin (s.output m)) (β := Fin (s.input m) × Basis s m)
        (inst := Classical.decEq (Basis s (m+1)))
        ((((((∏ j ∈ Finset.range (m+1), s.output j : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)))
      have e2 := g52b_kr (γ := Fin (s.input m)) (δ := Basis s m)
        ((((((∏ j ∈ Finset.range m, s.output j : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)))
      have e3 : ((((((∏ j ∈ Finset.range (m+1), s.output j : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))) *
          (Fintype.card (Fin (s.output m)) : ℂ) =
          ((((((∏ j ∈ Finset.range m, s.output j : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))) := by
        rw [Finset.prod_range_succ, Fintype.card_fin]
        push_cast at ho hp ⊢
        field_simp
      rw [e3, ← e2] at e1
      exact e1

/-- PDF p.21, question 1: every positive operator, including zero and rank-one histories,
can be positively scaled into a probabilistic comb and a branch of one instrument. -/
theorem solution (s : Signature) (n : ℕ) (hn : 0 < n)
    (R : Matrix (Basis s n) (Basis s n) ℂ) (hR : R.PosSemidef) :
    ∃ a : ℝ, 0 < a ∧ Probabilistic s n ((a : ℂ) • R) ∧
      ∃ k, ∃ P : Fin k → Matrix (Basis s n) (Basis s n) ℂ,
        CombInstrument s n k P ∧ ∃ i, P i = (a : ℂ) • R := by
  set cR : ℝ := (((∏ j ∈ Finset.range n, s.output j : ℕ) : ℝ))⁻¹ with hcR
  have hc : 0 < cR := by
    rw [hcR]; apply inv_pos.mpr
    exact_mod_cast Finset.prod_pos fun j _ => s.output_pos j
  have hS : Normalized s n ((cR : ℂ) • 1) := g52b_scalar_normalized s n
  have hT0 : 0 ≤ R.trace.re := (Complex.nonneg_iff.mp hR.trace_nonneg).1
  set a : ℝ := cR / (R.trace.re + 1) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have haT : a * R.trace.re ≤ cR := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hA : ((a : ℂ) • R).PosSemidef := hR.smul (Complex.zero_le_real.mpr hapos.le)
  have hB : ((cR : ℂ) • (1 : Matrix (Basis s n) (Basis s n) ℂ) - (a : ℂ) • R).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have h1 : ((cR : ℂ) • (1 : Matrix (Basis s n) (Basis s n) ℂ)).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
        simp
      exact h1.sub hA.1
    · intro x
      have hq := Complex.nonneg_iff.mp (hR.dotProduct_mulVec_nonneg x)
      have hb := g52b_qf_bound R hR x
      have hxx : star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [dotProduct, Pi.star_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show star (x i) = (starRingEnd ℂ) (x i) from rfl, Complex.conj_mul']
      have hX : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, hxx]
      rw [Complex.nonneg_iff]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_im, Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
      refine ⟨?_, ?_⟩
      · have : a * (star x ⬝ᵥ (R *ᵥ x)).re ≤ a * (R.trace.re * ∑ i, ‖x i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb hapos.le
        nlinarith
      · rw [← hq.2]; ring
  refine ⟨a, hapos, ⟨hn, hA, _, hS, by simpa using hB⟩, 2,
    ![(a : ℂ) • R, (cR : ℂ) • 1 - (a : ℂ) • R], ⟨hn, by norm_num, ?_, ?_⟩, 0, rfl⟩
  · intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
  · simpa [Fin.sum_univ_two] using hS


end

