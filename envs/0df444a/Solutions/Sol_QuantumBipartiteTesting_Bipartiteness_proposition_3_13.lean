-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.proposition_3_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:35:12.403096+00:00
-- url     : https://prove2.me/submissions/3fe1e558-71ba-4e98-be3b-9c90fd19dbc5

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_proposition_3_10
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_12
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_11
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section

private lemma denominator_nonzero {N M l q : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (hgrid : Grid N M l) (hq : (q : ℝ) ≤ (N : ℝ)^(1/3 : ℝ)) :
    Eval (Denominator q) M l ≠ 0 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hR : (Radius N : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)/100 := Nat.floor_le (by positivity)
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hlR : (l : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)/100 :=
    (show (l : ℝ) ≤ Radius N by exact_mod_cast hgrid.2.1).trans hR
  have hqR : (q : ℝ)*l ≤ (N : ℝ)/100 := by
    calc
      _ ≤ (N : ℝ)^(1/3 : ℝ) * ((N : ℝ)^(2/3 : ℝ)/100) :=
        mul_le_mul hq hlR hl (by positivity)
      _ = _ := by rw [← mul_div_assoc, ← Real.rpow_add hNr]; norm_num
  simp only [Denominator, Eval, map_prod, map_pow, map_sub, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  apply prod_ne_zero_iff.mpr
  intro a ha
  apply pow_ne_zero
  have hodd : ((2*(a+1)-1 : ℕ) : ℝ) ≤ 4*q := by
    have ha' := mem_range.mp ha
    have : 2*(a+1)-1 ≤ 4*q := by omega
    exact_mod_cast this
  have hprod := mul_le_mul_of_nonneg_right hodd hl
  have hMN : (N : ℝ) ≤ M := by exact_mod_cast hNM
  apply ne_of_gt
  nlinarith

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness

theorem solution : ∃ Cdeg c₀ : ℝ, 0 < Cdeg ∧ 0 < c₀ ∧ UniformGapVanishing c₀ ∧
    (∀ N k w q : ℕ, ∀ E : Encoding (Fin N × Bool) k,
      ∀ A : Algorithm (Address N 3) k w q,
      ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
      ∃ H : Bivariate, (H.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
        ∀ M l : ℕ, Grid N M l → Eval (Denominator q) M l ≠ 0 →
          FeasibleGap E A out M l =
            l * Eval H M l / Eval (Denominator q) M l + GapError E A out M l) ∧
    (∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q : ℕ, (q : ℝ) ≤ c₀ * LowerBoundScale N →
      ∀ M l : ℕ, Grid N M l → Eval (Denominator q) M l ≠ 0) := by
  obtain ⟨Cdeg,hCdeg,hformal⟩ := proposition_3_10
  obtain ⟨c₀,hc₀,hvan⟩ := lemma_3_12.2
  refine ⟨Cdeg,c₀,hCdeg,hc₀,hvan,?_,?_⟩
  · intro N k w q E A out
    obtain ⟨H,hH,hid⟩ := hformal N k w q E A out
    refine ⟨H,hH,?_⟩
    intro M l hgrid hden
    have hl : (l : ℝ) ≠ 0 := by
      have := hgrid.1
      exact_mod_cast (show l ≠ 0 by omega)
    have he := hid M l hl hden
    unfold GapError
    linarith
  · obtain ⟨_,_,N₁,hN₁⟩ := lemma_3_11
    refine ⟨max (max N₁ 2) ⌈Real.exp c₀⌉₊, ?_⟩
    intro N hN q hq M l hgrid
    have hNpos : 0 < N := by omega
    have hExp : Real.exp c₀ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast (le_trans (le_max_right _ _) hN))
    have hlog : c₀ ≤ Real.log (N : ℝ) := by
      calc
        _ = Real.log (Real.exp c₀) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) hExp
    have hlogpos : 0 < Real.log (N : ℝ) := hc₀.trans_le hlog
    have hqN : (q : ℝ) ≤ (N : ℝ)^(1/3 : ℝ) := by
      apply hq.trans
      unfold LowerBoundScale
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hlogpos).mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlog
        (show (0 : ℝ) ≤ (N : ℝ)^(1/3 : ℝ) from Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact denominator_nonzero hNpos (hN₁ N (by omega) M l hgrid).1.2.1 hgrid hqN
