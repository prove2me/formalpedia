-- Prove2me | solution 1 for QAlgorithms.Arunachalam.shadowTomography
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:25:03.697975+00:00
-- url     : https://prove2.me/submissions/786ea7c7-6405-4aef-bfc1-19a943297c19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Theorems.Thm_ShadowTomography_UpperBound_theorem_2

set_option autoImplicit false

open QAlgorithms
open QAlgorithms.Learning
open scoped Matrix ComplexOrder MatrixOrder

private lemma piKron_eq_star_mul_self {d k : ℕ} {ρ B : Matrix (Fin d) (Fin d) ℂ}
    (hB : ρ = star B * B) :
    piKron k ρ = star (piKron k B) * piKron k B := by
  ext x z
  rw [hB]
  simp only [piKron, Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply]
  rw [Fintype.prod_sum (fun i j => star (B j (x i)) * B j (z i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.prod_mul_distrib, star_prod]

private lemma effectProb_piKron_nonneg {d k : ℕ} {Ω : Type} [Fintype Ω]
    (P : ShadowTomography.UpperBound.POVM Ω (Fin k → Fin d)) (ω : Ω)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef) :
    0 ≤ effectProb (P.op ω) (piKron k ρ) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  have hp := ((P.psd ω).mul_mul_conjTranspose_same (piKron k B)).trace_nonneg
  rw [effectProb, piKron_eq_star_mul_self hB]
  have ht : (P.op ω * (star (piKron k B) * piKron k B)).trace =
      (piKron k B * P.op ω * (piKron k B)ᴴ).trace := by
    simp only [Matrix.star_eq_conjTranspose]
    rw [← Matrix.trace_mul_cycle]
    simp [Matrix.mul_assoc]
  rw [ht]
  exact hp.1

private lemma log_two_ge_half : (2⁻¹ : ℝ) ≤ Real.log 2 := by
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
  rw [Real.log_inv] at h1
  linarith

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

private lemma log_le_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have h1 := Real.log_le_sub_one_of_pos hx
  linarith

open Classical in
theorem solution :
    ∃ p : MvPolynomial (Fin 4) ℝ, ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 →
      ∀ m d : ℕ, 0 < m → 0 < d →
        ∀ E : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ i, IsEffect (E i)) →
          ∃ k : ℕ, (k : ℝ) ≤ MvPolynomial.eval
              ![Real.log (m : ℝ), Real.log (d : ℝ), 1 / ε, Real.log (1 / δ)] p ∧
            ∃ (O : Type) (_ : Fintype O) (Mo : O → Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)
              (b : O → Fin m → ℝ), IsPOVM Mo ∧ (∀ o i, 0 ≤ b o i ∧ b o i ≤ 1) ∧
              ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix ρ →
                povmEventProb Mo (piKron k ρ)
                  (fun o => ∀ i, |effectProb (E i) ρ - b o i| ≤ ε) ≥ 1 - δ := by
  obtain ⟨C, hC, hthm2⟩ := ShadowTomography.UpperBound.theorem_2
  let p : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.C C *
      (2 * MvPolynomial.X 1 * MvPolynomial.X 2) *
      ((MvPolynomial.X 1 + 2 * MvPolynomial.X 2) * (4 * MvPolynomial.X 2 ^ 2)) ^ 2 *
      (1 + MvPolynomial.X 0) ^ 4 *
      (1 + MvPolynomial.X 0 + MvPolynomial.X 1 + 2 * MvPolynomial.X 2 + 1 + MvPolynomial.X 3)
  refine ⟨p, fun ε δ hε0 hε1 hδ0 hδ1 m d hm hd E hE => ?_⟩
  have hM2 : 2 ≤ 2 * m := by omega
  have hε'0 : 0 < ε / 2 := by linarith
  have hε'1 : ε / 2 ≤ 1 / 2 := by linarith
  have hδ'0 : 0 < δ / 2 := by linarith
  have hδ'1 : δ / 2 ≤ 1 / 2 := by linarith
  let E' : Fin (2 * m) → Matrix (Fin d) (Fin d) ℂ :=
    fun j => E ⟨j.1 % m, Nat.mod_lt _ hm⟩
  have hE' : ∀ j, ShadowTomography.UpperBound.IsEffect (E' j) :=
    fun j => hE ⟨j.1 % m, Nat.mod_lt _ hm⟩
  obtain ⟨k, hk_bound, hrest⟩ := hthm2 d (2 * m) (ε / 2) (δ / 2) hM2 hε'0 hε'1 hδ'0 hδ'1
  obtain ⟨Ω, hΩ, P, b', hb'_Icc, hprob⟩ := hrest E' hE'
  refine ⟨k, ?_, Ω, hΩ, P.op, fun o i => b' o ⟨i.1, by omega⟩, ⟨P.psd, P.complete⟩,
    fun o i => hb'_Icc o ⟨i.1, by omega⟩, ?_⟩
  · have hX0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hX1 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
    have hX2 : 1 ≤ 1 / ε := one_le_one_div hε0 hε1
    have hX2_0 : 0 ≤ 1 / ε := by linarith
    have hX3 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδ1)
    have heval : MvPolynomial.eval ![Real.log (m : ℝ), Real.log (d : ℝ), 1 / ε, Real.log (1 / δ)] p =
        C * (2 * Real.log (d : ℝ) * (1 / ε)) *
          ((Real.log (d : ℝ) + 2 * (1 / ε)) * (4 * (1 / ε) ^ 2)) ^ 2 *
          (1 + Real.log (m : ℝ)) ^ 4 *
          (1 + Real.log (m : ℝ) + Real.log (d : ℝ) + 2 * (1 / ε) + 1 + Real.log (1 / δ)) := by
      simp only [p, map_mul, map_add, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
        map_ofNat, map_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    rw [heval]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd) with rfl | hd2
    · have hk0 : (k : ℝ) ≤ 0 := by
        simpa [Real.log_one] using hk_bound
      have hrhs : 0 ≤ C * (2 * Real.log ((1 : ℕ) : ℝ) * (1 / ε)) *
          ((Real.log ((1 : ℕ) : ℝ) + 2 * (1 / ε)) * (4 * (1 / ε) ^ 2)) ^ 2 *
          (1 + Real.log (m : ℝ)) ^ 4 *
          (1 + Real.log (m : ℝ) + Real.log ((1 : ℕ) : ℝ) + 2 * (1 / ε) + 1 + Real.log (1 / δ)) := by
        positivity
      exact hk0.trans hrhs
    · have hd2_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
      have hM2_real : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hM2
      have hlogd_ge : 2⁻¹ ≤ Real.log (d : ℝ) :=
        log_two_ge_half.trans (Real.log_le_log (by norm_num) hd2_real)
      have hlogd_pos : 0 < Real.log (d : ℝ) := by linarith
      have hlogM_ge : 2⁻¹ ≤ Real.log ((2 * m : ℕ) : ℝ) :=
        log_two_ge_half.trans (Real.log_le_log (by norm_num) hM2_real)
      have hlogM_pos : 0 < Real.log ((2 * m : ℕ) : ℝ) := by linarith
      have h2eps : 2 ≤ 1 / (ε / 2) := by
        rw [one_div_div]
        have : 2 * 1 ≤ 2 * (1 / ε) := by linarith
        simpa [div_eq_mul_inv] using this
      have h2delta : 2 ≤ 1 / (δ / 2) := by
        rw [one_div_div]
        have : 1 ≤ 1 / δ := one_le_one_div hδ0 hδ1
        have : 2 * 1 ≤ 2 * (1 / δ) := by linarith
        simpa [div_eq_mul_inv] using this
      have hlog_ll_d : -Real.log 2 ≤ Real.log (Real.log (d : ℝ)) := by
        rw [← Real.log_inv]
        exact Real.log_le_log (by norm_num) hlogd_ge
      have hlog_ll_M : -Real.log 2 ≤ Real.log (Real.log ((2 * m : ℕ) : ℝ)) := by
        rw [← Real.log_inv]
        exact Real.log_le_log (by norm_num) hlogM_ge
      have hlog_eps_ge : Real.log 2 ≤ Real.log (1 / (ε / 2)) :=
        Real.log_le_log (by norm_num) h2eps
      have hlog_delta_ge : Real.log 2 ≤ Real.log (1 / (δ / 2)) :=
        Real.log_le_log (by norm_num) h2delta
      have hlog_eps_le : Real.log (1 / (ε / 2)) ≤ 2 * (1 / ε) := by
        have hpos : 0 < 1 / (ε / 2) := by positivity
        have h1 := log_le_self_of_pos hpos
        have h2 : 1 / (ε / 2) = 2 * (1 / ε) := by ring
        linarith
      have hlog_delta_le : Real.log (1 / (δ / 2)) ≤ 1 + Real.log (1 / δ) := by
        have h1 : 1 / (δ / 2) = 2 * (1 / δ) := by ring
        rw [h1, Real.log_mul (by norm_num) (by positivity)]
        linarith [log_two_le_one]
      have hlog_M_le : Real.log ((2 * m : ℕ) : ℝ) ≤ 1 + Real.log (m : ℝ) := by
        push_cast
        rw [Real.log_mul (by norm_num) (by positivity)]
        linarith [log_two_le_one]
      have hlog_ll_d_le : Real.log (Real.log (d : ℝ)) ≤ Real.log (d : ℝ) :=
        log_le_self_of_pos hlogd_pos
      have hlog_ll_M_le : Real.log (Real.log ((2 * m : ℕ) : ℝ)) ≤ 1 + Real.log (m : ℝ) :=
        (log_le_self_of_pos hlogM_pos).trans hlog_M_le
      have hf1_eq : Real.log (d : ℝ) / (ε / 2) = 2 * Real.log (d : ℝ) * (1 / ε) := by ring
      have hf2_inner_nonneg : 0 ≤ Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2)) := by
        linarith
      have hf2_inner_le : Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2)) ≤
          Real.log (d : ℝ) + 2 * (1 / ε) := by linarith
      have hf2_div_eq : (Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) / (ε / 2) ^ 2 =
          (Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) * (4 * (1 / ε) ^ 2) := by ring
      have hf2_div_nonneg : 0 ≤ (Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) / (ε / 2) ^ 2 := by
        rw [hf2_div_eq]
        positivity
      have hf2_div_le : (Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) / (ε / 2) ^ 2 ≤
          (Real.log (d : ℝ) + 2 * (1 / ε)) * (4 * (1 / ε) ^ 2) := by
        rw [hf2_div_eq]
        exact mul_le_mul_of_nonneg_right hf2_inner_le (by positivity)
      have hf2_le : (((Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) / (ε / 2) ^ 2)) ^ 2 ≤
          ((Real.log (d : ℝ) + 2 * (1 / ε)) * (4 * (1 / ε) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hf2_div_nonneg hf2_div_le 2
      have hf3_le : Real.log ((2 * m : ℕ) : ℝ) ^ 4 ≤ (1 + Real.log (m : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (le_of_lt hlogM_pos) hlog_M_le 4
      have hf4_nonneg : 0 ≤ Real.log (Real.log ((2 * m : ℕ) : ℝ)) + Real.log (Real.log (d : ℝ)) +
          Real.log (1 / (ε / 2)) + Real.log (1 / (δ / 2)) := by linarith
      have hf4_le : Real.log (Real.log ((2 * m : ℕ) : ℝ)) + Real.log (Real.log (d : ℝ)) +
          Real.log (1 / (ε / 2)) + Real.log (1 / (δ / 2)) ≤
          1 + Real.log (m : ℝ) + Real.log (d : ℝ) + 2 * (1 / ε) + 1 + Real.log (1 / δ) := by
        linarith
      have hprod12 : C * (Real.log (d : ℝ) / (ε / 2)) *
          (((Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) / (ε / 2) ^ 2)) ^ 2 ≤
          C * (2 * Real.log (d : ℝ) * (1 / ε)) *
          ((Real.log (d : ℝ) + 2 * (1 / ε)) * (4 * (1 / ε) ^ 2)) ^ 2 := by
        rw [hf1_eq]
        exact mul_le_mul_of_nonneg_left hf2_le (by positivity)
      have hprod123 : C * (Real.log (d : ℝ) / (ε / 2)) *
          (((Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) / (ε / 2) ^ 2)) ^ 2 *
          Real.log ((2 * m : ℕ) : ℝ) ^ 4 ≤
          C * (2 * Real.log (d : ℝ) * (1 / ε)) *
          ((Real.log (d : ℝ) + 2 * (1 / ε)) * (4 * (1 / ε) ^ 2)) ^ 2 *
          (1 + Real.log (m : ℝ)) ^ 4 :=
        mul_le_mul hprod12 hf3_le (by positivity) (by positivity)
      have hprod1234 : C * (Real.log (d : ℝ) / (ε / 2)) *
          (((Real.log (Real.log (d : ℝ)) + Real.log (1 / (ε / 2))) / (ε / 2) ^ 2)) ^ 2 *
          Real.log ((2 * m : ℕ) : ℝ) ^ 4 *
          (Real.log (Real.log ((2 * m : ℕ) : ℝ)) + Real.log (Real.log (d : ℝ)) +
            Real.log (1 / (ε / 2)) + Real.log (1 / (δ / 2))) ≤
          C * (2 * Real.log (d : ℝ) * (1 / ε)) *
          ((Real.log (d : ℝ) + 2 * (1 / ε)) * (4 * (1 / ε) ^ 2)) ^ 2 *
          (1 + Real.log (m : ℝ)) ^ 4 *
          (1 + Real.log (m : ℝ) + Real.log (d : ℝ) + 2 * (1 / ε) + 1 + Real.log (1 / δ)) :=
        mul_le_mul hprod123 hf4_le hf4_nonneg (by positivity)
      exact hk_bound.trans hprod1234
  · intro ρ hρ
    have hρ' : WildeQIT.IsDensityOperator ρ := hρ
    have hp := hprob ρ hρ'
    have hle : ShadowTomography.UpperBound.POVM.prob P
        (ShadowTomography.UpperBound.tensorPow ρ k)
        (fun ω : Ω => ∀ j : Fin (2 * m), |b' ω j - ((E' j) * ρ).trace.re| ≤ ε / 2) ≤
        povmEventProb P.op (piKron k ρ)
        (fun o : Ω => ∀ i : Fin m, |effectProb (E i) ρ - b' o ⟨i.1, by omega⟩| ≤ ε) := by
      have htp : ShadowTomography.UpperBound.tensorPow ρ k = piKron k ρ := rfl
      rw [ShadowTomography.UpperBound.POVM.prob, htp, povmEventProb]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ω _ _ =>
        effectProb_piKron_nonneg P ω hρ.1)
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      intro i
      let j : Fin (2 * m) := ⟨i.1, by omega⟩
      have hj := hω j
      have hEj : E' j = E i := by
        simp only [E', j]
        congr 1
        ext
        exact Nat.mod_eq_of_lt i.isLt
      rw [hEj] at hj
      have heq : |effectProb (E i) ρ - b' ω j| = |b' ω j - ((E i) * ρ).trace.re| :=
        abs_sub_comm _ _
      linarith
    linarith
