-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.flowRatio_dualities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:15:18.985317+00:00
-- url     : https://prove2.me/submissions/4c093afa-d77c-4a23-8011-c86d541ea8b3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace X6P16F

open QAlgorithms.Papers.Independent.Dependency50.P16

variable {n r : ℕ}

theorem rates_nonneg (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : 0 ≤ rates V U i j :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem inflow_nonneg (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (d : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ inflow V d U :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> simp [rates_nonneg]

theorem outflow_nonneg (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (d : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ outflow V d U :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> simp [rates_nonneg]

theorem rates_adj (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : rates (fun k => (V k)ᴴ) U i j = rates V U j i := by
  unfold rates
  refine Finset.sum_congr rfl fun k _ => ?_
  have : Uᴴ * (V k)ᴴ * U = (Uᴴ * V k * U)ᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, Matrix.conjTranspose_apply]
  simp

theorem inflow_adj (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (d : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    inflow (fun k => (V k)ᴴ) d U = outflow V d U := by
  unfold inflow outflow
  simp_rw [rates_adj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : d ≤ i.val ∧ j.val < d
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]

theorem outflow_adj (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (d : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    outflow (fun k => (V k)ᴴ) d U = inflow V d U := by
  unfold inflow outflow
  simp_rw [rates_adj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i.val < d ∧ d ≤ j.val
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]

theorem sup_of_eq_inv (S T : Set ℝ≥0∞) (h : T = (fun a => a⁻¹) '' S) : sSup T = (sInf S)⁻¹ := by
  rw [h, sSup_image, ENNReal.inv_sInf]

theorem ratio_inv (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    (ENNReal.ofReal a / ENNReal.ofReal b)⁻¹ = ENNReal.ofReal b / ENNReal.ofReal a := by
  rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)]
  by_cases hb0 : b = 0
  · right; rw [ENNReal.ofReal_ne_zero_iff]; subst hb0; linarith
  · left; rw [ENNReal.ofReal_ne_zero_iff]; exact lt_of_le_of_ne hb (Ne.symm hb0)

/-- relabelled unitary -/
def σ (n : ℕ) : Equiv.Perm (Fin n) := Fin.revPerm

def ω (n : ℕ) : ℂ :=
  if ((Equiv.Perm.sign (σ n) : ℤ) : ℂ) = 1 then 1 else Complex.exp (Real.pi * Complex.I / n)

def T (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := ω n • U.submatrix id (σ n)

theorem ω_norm (n : ℕ) : star (ω n) * ω n = 1 := by
  have h : ‖ω n‖ = 1 := by
    unfold ω
    split_ifs
    · simp
    · rw [show (Real.pi : ℂ) * Complex.I / n = ((Real.pi / n : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
  rw [Complex.star_def, Complex.conj_mul', h]; simp

theorem ω_det (hn : 0 < n) : ω n ^ n * ((Equiv.Perm.sign (σ n) : ℤ) : ℂ) = 1 := by
  unfold ω
  split_ifs with h
  · rw [h]; simp
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (σ n)) with h1 | h1
    · exact absurd (by rw [h1]; simp) h
    · rw [h1, ← Complex.exp_nat_mul]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (n : ℂ) * (Real.pi * Complex.I / n) = Real.pi * Complex.I := by
        field_simp
      rw [this, Complex.exp_pi_mul_I]; simp

theorem T_conj (U M : Matrix (Fin n) (Fin n) ℂ) :
    (T U)ᴴ * M * T U = (Uᴴ * M * U).submatrix (σ n) (σ n) := by
  unfold T
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_submatrix]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm (ω n), ω_norm, one_smul]
  have h1 : Uᴴ.submatrix (σ n) id * M = (Uᴴ * M).submatrix (σ n) id := by
    have := Matrix.submatrix_mul_equiv Uᴴ M (σ n) (Equiv.refl _) id
    simpa using this
  rw [h1]
  exact Matrix.submatrix_mul_equiv (Uᴴ * M) U (σ n) (Equiv.refl _) (σ n) |>.trans (by simp)

theorem T_SU (hn : 0 < n) (U : Matrix (Fin n) (Fin n) ℂ) (hU : specialUnitary U) :
    specialUnitary (T U) := by
  obtain ⟨hU1, hU2⟩ := hU
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have := T_conj U 1
    simp only [Matrix.mul_one] at this
    rw [show star (T U) = (T U)ᴴ from rfl, this]
    rw [Matrix.mem_unitaryGroup_iff'] at hU1
    rw [show Uᴴ * U = star U * U from rfl, hU1, Matrix.submatrix_one_equiv]
  · unfold T
    rw [Matrix.det_smul, Matrix.det_permute', hU2, Fintype.card_fin, mul_one]
    exact ω_det hn

theorem T_rates (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    rates V (T U) i j = rates V U (σ n i) (σ n j) := by
  unfold rates
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [T_conj]; rfl

theorem T_in (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (c : ℕ)
    (hc : c ≤ n) : inflow V c (T U) = outflow V (n - c) U := by
  unfold inflow outflow
  simp_rw [T_rates]
  rw [← Equiv.sum_comp (σ n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (σ n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [σ, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hi := i.2; have hj := j.2
  by_cases h : n - c ≤ i.val ∧ j.val < n - c
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem T_out (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (c : ℕ)
    (hc : c ≤ n) : outflow V c (T U) = inflow V (n - c) U := by
  unfold inflow outflow
  simp_rw [T_rates]
  rw [← Equiv.sum_comp (σ n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (σ n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [σ, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hi := i.2; have hj := j.2
  by_cases h : i.val < n - c ∧ n - c ≤ j.val
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

end X6P16F

open X6P16F QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n r : ℕ} (hn : 2 ≤ n) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (d : ℕ) (hd : 1 ≤ d) (hdn : d < n) :
    flowSup V (n - d) = (flowInf V d)⁻¹ ∧
      flowSup (fun k => (V k)ᴴ) d = (flowInf V d)⁻¹ := by
  refine ⟨sup_of_eq_inv _ _ ?_, sup_of_eq_inv _ _ ?_⟩
  · ext z
    constructor
    · rintro ⟨U, hU, hpos, rfl⟩
      refine ⟨_, ⟨T U, T_SU (by omega) U hU, ?_, rfl⟩, ?_⟩
      · rw [T_in V U d hdn.le, T_out V U d hdn.le]; linarith
      · simp only
        rw [T_in V U d hdn.le, T_out V U d hdn.le]
        exact ratio_inv _ _ (outflow_nonneg _ _ _) (inflow_nonneg _ _ _) (by linarith)
    · rintro ⟨a, ⟨U, hU, hpos, rfl⟩, rfl⟩
      refine ⟨T U, T_SU (by omega) U hU, ?_, ?_⟩
      · rw [T_in V U (n - d) (by omega), T_out V U (n - d) (by omega),
          show n - (n - d) = d by omega]; linarith
      · rw [T_in V U (n - d) (by omega), T_out V U (n - d) (by omega),
          show n - (n - d) = d by omega]
        exact ratio_inv _ _ (inflow_nonneg _ _ _) (outflow_nonneg _ _ _) hpos
  · ext z
    constructor
    · rintro ⟨U, hU, hpos, rfl⟩
      rw [inflow_adj, outflow_adj] at hpos ⊢
      refine ⟨_, ⟨U, hU, by linarith, rfl⟩, ?_⟩
      exact ratio_inv _ _ (inflow_nonneg _ _ _) (outflow_nonneg _ _ _) (by linarith)
    · rintro ⟨a, ⟨U, hU, hpos, rfl⟩, rfl⟩
      refine ⟨U, hU, ?_, ?_⟩
      · rw [inflow_adj, outflow_adj]; linarith
      · rw [inflow_adj, outflow_adj]
        exact ratio_inv _ _ (inflow_nonneg _ _ _) (outflow_nonneg _ _ _) hpos
