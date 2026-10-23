-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.subexponentialSourceConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:44:43.646847+00:00
-- url     : https://prove2.me/submissions/6abb58bd-56f2-43af-8515-830c5d200685

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_strongSourceConverse

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open Filter

namespace X6SubC

lemma exists_res {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∃ S : FineResolution d, S.state = A := by
  refine ⟨⟨hA.1.eigenvalues, hA.eigenvalues_nonneg, ?_, hA.1.eigenvectorUnitary⟩, ?_⟩
  · have h := hA.1.trace_eq_sum_eigenvalues
    rw [htr] at h
    have := congrArg Complex.re h
    simpa using this.symm
  · conv_rhs => rw [hA.1.spectral_theorem]
    simp only [FineResolution.state, QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum.density,
      conjSuperop, Unitary.conjStarAlgAut_apply]
    rfl

lemma average_psd {a d : ℕ} (S : PureSource a d) : S.average.PosSemidef ∧ S.average.trace = 1 := by
  choose vx hvx1 hvx using S.pure
  have hl : ∑ x, (S.law x).toReal = 1 := by
    have h := S.law.tsum_coe
    rw [tsum_fintype] at h
    rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ _), h]; simp
  have hpd : ∀ x, (S.letter x).PosSemidef := by
    intro x; rw [hvx]
    have : pureDensity (vx x) = Matrix.vecMulVec (vx x).ofLp (star (vx x).ofLp) := by
      ext i j; simp [pureDensity, Matrix.vecMulVec_apply]
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  have htr : ∀ x, (S.letter x).trace = 1 := by
    intro x; rw [hvx]
    have h := hvx1 x
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    exact_mod_cast h
  refine ⟨Matrix.posSemidef_sum _ fun x _ => (hpd x).smul (by
    exact_mod_cast (ENNReal.toReal_nonneg : 0 ≤ (S.law x).toReal)), ?_⟩
  simp only [PureSource.average, Matrix.trace_sum, Matrix.trace_smul, htr, smul_eq_mul, mul_one]
  exact_mod_cast hl

end X6SubC

open X6SubC

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {a d : ℕ} (S : PureSource a d)
    (E lambda : ℕ → ℝ) (hsublinear : Tendsto (fun n : ℕ => E n / (n+1 : ℝ)) atTop (nhds 0))
    (c : ∀ n, SourceCode S (n+1))
    (hcode : ∀ n, 1 - (c n).fidelity ≤ lambda n)
    (herror : ∀ n, lambda n ≤ 1 - Real.exp (-E n)) :
    Filter.liminf (fun n => ENNReal.ofReal (c n).rate) atTop ≥
      ENNReal.ofReal (vnEntropy S.average) := by
  obtain ⟨sp, hsp⟩ := exists_res S.average (average_psd S).1 (average_psd S).2
  set H := vnEntropy S.average
  set N : ℝ := (spectralN sp : ℝ)
  set μ := spectralMu sp
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  -- μ = 0 forces N = 0
  have hμN : μ ≤ 0 → N = 0 := by
    intro hμ
    simp only [N, Nat.cast_eq_zero, spectralN, Finset.card_eq_zero]
    by_contra hne
    have hne' := Finset.nonempty_iff_ne_empty.mpr hne
    have : 0 < μ := by
      simp only [μ, spectralMu]
      rw [dif_pos hne']
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hne'
        (fun j => Real.sqrt ((sp.law j).toReal * (1 - (sp.law j).toReal)))
      rw [hjeq]; exact (Finset.mem_filter.mp hj).2
    linarith
  set μ' := if 0 < μ then μ else 1
  have hμ' : 0 < μ' := by simp only [μ']; split_ifs with h; exact h; norm_num
  set L0 := Real.log (8 * Real.sqrt N + 1)
  have hL0 : 0 ≤ L0 := Real.log_nonneg (by linarith [Real.sqrt_nonneg N])
  set Ep : ℕ → ℝ := fun n => max (E n) 0
  set α : ℕ → ℝ := fun n => Real.sqrt (Ep n + L0 + 1) / μ'
  have hEp0 : ∀ n, 0 ≤ Ep n := fun n => le_max_right _ _
  have hα : ∀ n, 0 < α n := fun n => div_pos (Real.sqrt_pos.mpr (by linarith [hEp0 n])) hμ'
  -- the tail term is at most e^{-Ep}/2
  have hterm : ∀ n, 4 * Real.sqrt N * Real.exp (-μ ^ 2 * α n ^ 2) ≤ Real.exp (-Ep n) / 2 := by
    intro n
    by_cases hμ : 0 < μ
    · have hμμ : μ' = μ := by simp [μ', hμ]
      have e1 : μ ^ 2 * α n ^ 2 = Ep n + L0 + 1 := by
        simp only [α, hμμ, div_pow, Real.sq_sqrt (by linarith [hEp0 n] : 0 ≤ Ep n + L0 + 1)]
        field_simp
      rw [neg_mul, e1, show -(Ep n + L0 + 1) = -Ep n + (-L0 + -1) by ring, Real.exp_add, Real.exp_add,
        Real.exp_neg L0, Real.exp_log (by positivity)]
      have h1 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
      have hs := Real.sqrt_nonneg N
      have hE := Real.exp_pos (-Ep n)
      have h8 : 0 < 8 * Real.sqrt N + 1 := by positivity
      rw [show 4 * Real.sqrt N * (Real.exp (-Ep n) * ((8 * Real.sqrt N + 1)⁻¹ * Real.exp (-1))) =
        Real.exp (-Ep n) * Real.exp (-1) * (4 * Real.sqrt N / (8 * Real.sqrt N + 1)) by field_simp]
      have h2 : 4 * Real.sqrt N / (8 * Real.sqrt N + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ h8]; linarith
      calc Real.exp (-Ep n) * Real.exp (-1) * (4 * Real.sqrt N / (8 * Real.sqrt N + 1))
          ≤ Real.exp (-Ep n) * 1 * (1 / 2) := by
            gcongr
      _ = Real.exp (-Ep n) / 2 := by ring
    · rw [hμN (not_lt.mp hμ)]; simp; positivity
  -- the per-length rate bound
  set K := varianceConstant * d
  set ε : ℕ → ℝ := fun n => Ep n / Real.log 2 / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) +
    K * (Real.sqrt ((Ep n + L0 + 1) / (n + 1 : ℝ)) / μ')
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : ∀ n, H - ε n ≤ (c n).rate := by
    intro n
    have h19 := strongSourceConverse S sp hsp (c n) (lambda n) (α n) (hcode n) (hα n)
    set m : ℝ := ((n + 1 : ℕ) : ℝ)
    have hm : 0 < m := by positivity
    have hmc : m = (n + 1 : ℝ) := by simp [m]
    set X := m * H - K * α n * Real.sqrt m
    have hB : Real.exp (-Ep n) / 2 ≤ 1 - lambda n - 4 * Real.sqrt N * Real.exp (-μ ^ 2 * α n ^ 2) := by
      have h1 : Real.exp (-E n) ≥ Real.exp (-Ep n) := Real.exp_le_exp.mpr (by simp [Ep])
      have := hterm n
      have h2 := herror n
      have h3 : Real.exp (-Ep n) / 2 ≤ Real.exp (-Ep n) - Real.exp (-Ep n) / 2 := by linarith
      nlinarith
    have hX : 0 < exp2 X := by simp only [exp2]; positivity
    have hdim : Real.exp (-Ep n) / 2 * exp2 X ≤ (c n).dim := by
      refine le_trans ?_ (ge_iff_le.mp h19)
      have : -(spectralMu sp) ^ 2 * α n ^ 2 = -μ ^ 2 * α n ^ 2 := rfl
      rw [this]
      exact mul_le_mul_of_nonneg_right hB hX.le
    have hlog : -Ep n / Real.log 2 - 1 + X ≤ Real.logb 2 (c n).dim := by
      have hpos : 0 < Real.exp (-Ep n) / 2 * exp2 X := by positivity
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hdim
      refine le_trans (le_of_eq ?_) this
      rw [Real.logb_mul (by positivity) hX.ne', Real.logb_div (by positivity) (by norm_num),
        Real.logb_self_eq_one (by norm_num)]
      simp only [exp2, Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
      rw [Real.logb, Real.log_exp]
    have hrate : (c n).rate = Real.logb 2 (c n).dim / m := rfl
    rw [hrate, le_div_iff₀ hm]
    have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
    have key : ∀ t : ℝ, 0 < t → ∀ A B x : ℝ,
        (A / t ^ 2 + B / t ^ 2 + K * (x / t / μ')) * t ^ 2 = A + B + K * (x / μ') * t := by
      intro t ht A B x; field_simp
    have hεm : ε n * m = Ep n / Real.log 2 + 1 + K * α n * Real.sqrt m := by
      calc ε n * m = (Ep n / Real.log 2 / Real.sqrt m ^ 2 + 1 / Real.sqrt m ^ 2 +
            K * (Real.sqrt (Ep n + L0 + 1) / Real.sqrt m / μ')) * Real.sqrt m ^ 2 := by
            simp only [ε]; rw [← hmc, Real.sqrt_div' _ hm.le, Real.sq_sqrt hm.le]
        _ = _ := key _ hsm0 _ _ _
        _ = Ep n / Real.log 2 + 1 + K * α n * Real.sqrt m := by simp only [α]
    have : (H - ε n) * m = X - (Ep n / Real.log 2 + 1) := by
      rw [sub_mul, hεm]; simp only [X]; ring
    rw [this]
    have : -Ep n / Real.log 2 = -(Ep n / Real.log 2) := by ring
    linarith
  -- ε → 0
  have hEp : Tendsto (fun n : ℕ => Ep n / (n + 1 : ℝ)) atTop (nhds 0) := by
    have h := hsublinear.max (tendsto_const_nhds (x := (0 : ℝ)))
    simp only [max_self] at h
    refine h.congr fun n => ?_
    simp only [Ep]
    rw [← max_div_div_right (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), zero_div]
  have hinv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hε : Tendsto ε atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => Ep n / Real.log 2 / (n + 1 : ℝ)) atTop (nhds 0) := by
      have := hEp.div_const (Real.log 2)
      simp only [zero_div] at this
      exact this.congr fun n => by ring
    have h2 : Tendsto (fun n : ℕ => (Ep n + L0 + 1) / (n + 1 : ℝ)) atTop (nhds 0) := by
      have := hEp.add (hinv.const_mul (L0 + 1))
      simp only [mul_zero, add_zero] at this
      exact this.congr fun n => by ring
    have h3 : Tendsto (fun n : ℕ => K * (Real.sqrt ((Ep n + L0 + 1) / (n + 1 : ℝ)) / μ')) atTop (nhds 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp h2).div_const μ'
      simp only [Real.sqrt_zero, zero_div] at this
      have := this.const_mul K
      simp only [mul_zero] at this
      exact this
    have := (h1.add hinv).add h3
    simp only [add_zero] at this
    exact this
  have htend : Tendsto (fun n => ENNReal.ofReal (H - ε n)) atTop (nhds (ENNReal.ofReal H)) := by
    have := (tendsto_const_nhds (x := H)).sub hε
    simp only [sub_zero] at this
    exact ENNReal.tendsto_ofReal this
  rw [ge_iff_le, ← htend.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hbound n))

