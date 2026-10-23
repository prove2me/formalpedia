-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.thermalGramConservation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:51:17.590165+00:00
-- url     : https://prove2.me/submissions/25376229-a943-46f6-9f3f-9ce284d707c8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma X7_shell_apply {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (r i : Fin d) (a : Fin b × Fin b) :
    (shellVector D r i) a = thermalKraus D a r i := by
  simp only [shellVector]
  split_ifs with h
  · rfl
  · simp only [thermalKraus]
    rw [D.support r i a.2 a.1 (fun h' => h h'), mul_zero]

lemma X7_gibbs_nonneg {n : ℕ} (E : Fin n → ℝ) (beta : ℝ) (i : Fin n) : 0 ≤ gibbsWeight E beta i := by
  unfold gibbsWeight
  exact div_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)

lemma X7_gibbs_sum {n : ℕ} (hn : 0 < n) (E : Fin n → ℝ) (beta : ℝ) :
    ∑ i, gibbsWeight E beta i = 1 := by
  unfold gibbsWeight
  rw [← Finset.sum_div]
  apply div_self
  apply ne_of_gt
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


lemma X7_gibbs_eq {n m : ℕ} (E : Fin n → ℝ) (B : Fin m → ℝ) (beta : ℝ) (i r : Fin n) (μ ν : Fin m)
    (h : E i + B μ = E r + B ν) :
    gibbsWeight B beta μ * gibbsWeight E beta i = gibbsWeight E beta r * gibbsWeight B beta ν := by
  unfold gibbsWeight
  have : Real.exp (-beta * B μ) * Real.exp (-beta * E i) =
      Real.exp (-beta * E r) * Real.exp (-beta * B ν) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; linear_combination (-beta) * h
  simp only [div_eq_mul_inv]
  linear_combination ((∑ j, Real.exp (-beta * B j))⁻¹ * (∑ j, Real.exp (-beta * E j))⁻¹) * this

lemma X7_inner {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (s j r i : Fin d) :
    inner ℂ (shellVector D s j) (shellVector D r i) = ∑ a : Fin b × Fin b,
      (gibbsWeight D.bathEnergy beta a.1 : ℂ) *
      (conj ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (s, a.2) (j, a.1)) *
        (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [X7_shell_apply, X7_shell_apply]
  simp only [thermalKraus, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have hg : ((Real.sqrt (gibbsWeight D.bathEnergy beta a.1) : ℂ)) *
      (Real.sqrt (gibbsWeight D.bathEnergy beta a.1) : ℂ) = (gibbsWeight D.bathEnergy beta a.1 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (X7_gibbs_nonneg _ _ _)]
  linear_combination ((conj ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (s, a.2) (j, a.1)) *
        (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1))) * hg

lemma X7_gibbs_sumC {n : ℕ} (hn : 0 < n) (E : Fin n → ℝ) (beta : ℝ) :
    ∑ i, (gibbsWeight E beta i : ℂ) = 1 := by
  rw [← Complex.ofReal_sum, X7_gibbs_sum hn]; simp

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) :
    (∀ i j, (∑ r, inner ℂ (shellVector D r j) (shellVector D r i)) =
      if i = j then 1 else 0) ∧
    (∀ r s, (∑ i, (gibbsWeight E beta i : ℂ) *
      inner ℂ (shellVector D s i) (shellVector D r i)) =
        if r = s then (gibbsWeight E beta r : ℂ) else 0) := by
  have hc := Matrix.mem_unitaryGroup_iff'.mp D.U.2
  have hr := Matrix.mem_unitaryGroup_iff.mp D.U.2
  constructor
  · intro i j
    simp_rw [X7_inner]
    calc ∑ r, ∑ a : Fin b × Fin b, (gibbsWeight D.bathEnergy beta a.1 : ℂ) *
          (conj ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (j, a.1)) *
            (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1))
        = ∑ μ, (gibbsWeight D.bathEnergy beta μ : ℂ) *
          (star (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) *
            (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ)) (j, μ) (i, μ) := by
          simp_rw [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_prod_type, Finset.mul_sum]
          rw [Finset.sum_comm]
          rfl
      _ = if i = j then 1 else 0 := by
          rw [hc]
          simp_rw [Matrix.one_apply, Prod.mk.injEq, and_true, mul_ite, mul_one, mul_zero]
          by_cases h : j = i
          · subst h; simp [X7_gibbs_sumC D.bathPositive]
          · simp [h, Ne.symm h]
  · intro r s
    simp_rw [X7_inner, Finset.mul_sum]
    have key : ∀ (i : Fin d) (a : Fin b × Fin b),
        (gibbsWeight E beta i : ℂ) * ((gibbsWeight D.bathEnergy beta a.1 : ℂ) *
          (conj ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (s, a.2) (i, a.1)) *
            (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1))) =
        (gibbsWeight E beta r : ℂ) * ((gibbsWeight D.bathEnergy beta a.2 : ℂ) *
          ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1) *
            star ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (s, a.2) (i, a.1)))) := by
      intro i a
      by_cases h : E i + D.bathEnergy a.1 = E r + D.bathEnergy a.2
      · have := X7_gibbs_eq E D.bathEnergy beta i r a.1 a.2 h
        have hC : (gibbsWeight D.bathEnergy beta a.1 : ℂ) * (gibbsWeight E beta i : ℂ) =
            (gibbsWeight E beta r : ℂ) * (gibbsWeight D.bathEnergy beta a.2 : ℂ) := by
          exact_mod_cast this
        rw [Complex.star_def]
        linear_combination ((conj ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (s, a.2) (i, a.1)) *
            (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1))) * hC
      · simp [D.support r i a.2 a.1 h]
    simp_rw [key, ← Finset.mul_sum]
    calc (gibbsWeight E beta r : ℂ) * ∑ i, ∑ a : Fin b × Fin b, (gibbsWeight D.bathEnergy beta a.2 : ℂ) *
          ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1) *
            star ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (s, a.2) (i, a.1)))
        = (gibbsWeight E beta r : ℂ) * ∑ ν, (gibbsWeight D.bathEnergy beta ν : ℂ) *
          ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) *
            star (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ)) (r, ν) (s, ν) := by
          congr 1
          simp_rw [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_prod_type, Finset.mul_sum]
          conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
      _ = if r = s then (gibbsWeight E beta r : ℂ) else 0 := by
          rw [hr]
          simp_rw [Matrix.one_apply, Prod.mk.injEq, and_true, mul_ite, mul_one, mul_zero]
          by_cases h : r = s
          · subst h; simp [X7_gibbs_sumC D.bathPositive]
          · simp [h]


end
