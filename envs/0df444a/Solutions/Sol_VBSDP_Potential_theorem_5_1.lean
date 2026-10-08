-- Prove2me | solution 1 for VBSDP.Potential.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:39:03.029994+00:00
-- url     : https://prove2.me/submissions/7243fe7e-f6f2-4915-95d2-cacf1e88aed4

import Theorems.Thm_VBSDP_Potential_gap_le_exp

open Matrix VBSDP.Potential
open scoped MatrixOrder

private theorem trace_product_positive {n : ℕ} [NeZero n]
    (A Z : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hZ : Z.PosDef) :
    0 < (A * Z).trace := by
  let B := CFC.sqrt A
  have hB : B.IsHermitian := by simpa [B] using (CFC.sqrt_nonneg A).isHermitian
  have hBB : B * B = A := by
    simpa [B, pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hu : IsUnit B := isUnit_of_mul_isUnit_left (hBB.symm ▸ hA.isUnit)
  have hM : (B * Z * B).PosDef := by
    have hc := hZ.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hu)
    rw [hB.eq] at hc
    exact hc
  have hp := hM.trace_pos
  rwa [trace_mul_cycle, hBB] at hp

theorem solution {m n : ℕ} [NeZero n] (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (xs : ℕ → Fin m → ℝ) (Zs : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (hfeas : ∀ j ≤ k, IsStrictlyFeasiblePair c F₀ F (xs j) (Zs j))
    (δ : ℝ) (hδ : 0 < δ)
    (h56 : ∀ j < k, phi ν F₀ F (xs (j + 1)) (Zs (j + 1)) ≤
      phi ν F₀ F (xs j) (Zs j) - δ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hk : (ν * Real.sqrt n * Real.log (1 / ε) +
      psi F₀ F (xs 0) (Zs 0)) / δ ≤ k) :
    (VBSDP.Duality.lmi F₀ F (xs k) * Zs k).trace ≤
      ε * (VBSDP.Duality.lmi F₀ F (xs 0) * Zs 0).trace := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hv : 0 < ν * Real.sqrt n :=
    mul_pos (lt_of_lt_of_le zero_lt_one hν) (Real.sqrt_pos.mpr hn)
  have hgap0 : 0 < (VBSDP.Duality.lmi F₀ F (xs 0) * Zs 0).trace :=
    trace_product_positive _ _ (hfeas 0 (Nat.zero_le k)).1
      (hfeas 0 (Nat.zero_le k)).2.1
  have ht : ∀ j : ℕ, j ≤ k →
      phi ν F₀ F (xs j) (Zs j) ≤ phi ν F₀ F (xs 0) (Zs 0) - (j : ℝ) * δ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hp := ih (Nat.le_of_succ_le hj)
      have hs := h56 j (lt_of_lt_of_le (Nat.lt_succ_self j) hj)
      push_cast
      linarith
  have hbudget := (div_le_iff₀ hδ).mp hk
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hε0.ne', Real.log_one] at hbudget
  have hphi := ht k le_rfl
  have hinitial : phi ν F₀ F (xs 0) (Zs 0) =
      ν * Real.sqrt n * Real.log (VBSDP.Duality.lmi F₀ F (xs 0) * Zs 0).trace +
        psi F₀ F (xs 0) (Zs 0) := rfl
  rw [hinitial] at hphi
  have hexponent : phi ν F₀ F (xs k) (Zs k) / (ν * Real.sqrt n) ≤
      Real.log (VBSDP.Duality.lmi F₀ F (xs 0) * Zs 0).trace + Real.log ε := by
    apply (div_le_iff₀ hv).mpr
    nlinarith
  calc
    (VBSDP.Duality.lmi F₀ F (xs k) * Zs k).trace ≤
        Real.exp (phi ν F₀ F (xs k) (Zs k) / (ν * Real.sqrt n)) :=
      gap_le_exp ν hν c F₀ F hF₀ hF hlin (xs k) (Zs k) (hfeas k le_rfl)
    _ ≤ Real.exp (Real.log (VBSDP.Duality.lmi F₀ F (xs 0) * Zs 0).trace + Real.log ε) :=
      Real.exp_le_exp.mpr hexponent
    _ = ε * (VBSDP.Duality.lmi F₀ F (xs 0) * Zs 0).trace := by
      rw [Real.exp_add, Real.exp_log hgap0, Real.exp_log hε0]
      ring

#print axioms solution
