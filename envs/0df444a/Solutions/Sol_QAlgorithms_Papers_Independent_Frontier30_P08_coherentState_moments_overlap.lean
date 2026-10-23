-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P08.coherentState_moments_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:54:31.593088+00:00
-- url     : https://prove2.me/submissions/eac79201-f593-4982-aba6-81fc4216525b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
noncomputable section
open scoped BigOperators ComplexOrder ENNReal ComplexConjugate Nat

namespace X5CS
open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)

lemma exp_tsum (z : ℂ) : Complex.exp z = ∑' n : ℕ, z ^ n / n ! := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

lemma rexp_tsum (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / n ! := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma csum (z : ℂ) : Summable (fun n : ℕ => z ^ n / (n ! : ℂ)) := by
  have := Real.summable_pow_div_factorial ‖z‖
  refine Summable.of_norm_bounded this fun n => ?_
  rw [norm_div, norm_pow, Complex.norm_natCast]

lemma coef_mul (α β : ℂ) (n : ℕ) :
    conj (coherentCoefficient β n) * coherentCoefficient α n =
      ((Real.exp (-Complex.normSq β / 2) * Real.exp (-Complex.normSq α / 2) : ℝ) : ℂ) *
        ((conj β * α) ^ n / (n ! : ℂ)) := by
  simp only [coherentCoefficient, map_div₀, map_mul, map_pow, Complex.conj_ofReal]
  have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs : ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) = (n ! : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hf.le]; push_cast; rfl
  have hs0 : ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hf).ne'
  have hn0 : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [← hs]
  field_simp
  push_cast
  ring

lemma coef_sum (α β : ℂ) :
    HasSum (fun n => conj (coherentCoefficient β n) * coherentCoefficient α n)
      (((Real.exp (-Complex.normSq β / 2) * Real.exp (-Complex.normSq α / 2) : ℝ) : ℂ) *
        Complex.exp (conj β * α)) := by
  simp_rw [coef_mul]
  rw [exp_tsum]
  exact ((csum _).hasSum).mul_left _

lemma coef_norm_sq (α : ℂ) (n : ℕ) :
    ‖coherentCoefficient α n‖ ^ 2 = (conj (coherentCoefficient α n) * coherentCoefficient α n).re := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma coef_summable (α : ℂ) : Summable (fun n => ‖coherentCoefficient α n‖ ^ 2) := by
  simp_rw [coef_norm_sq]
  exact Complex.reCLM.summable (coef_sum α α).summable

lemma coef_mem (α : ℂ) : Memℓp (fun n => coherentCoefficient α n) 2 := by
  apply memℓp_gen
  simpa using coef_summable α

def psi (α : ℂ) : Fock := ⟨fun n => coherentCoefficient α n, coef_mem α⟩

@[simp] lemma psi_apply (α : ℂ) (n : ℕ) : psi α n = coherentCoefficient α n := rfl

lemma inner_psi (α β : ℂ) :
    inner ℂ (psi β) (psi α) =
      ((Real.exp (-Complex.normSq β / 2) * Real.exp (-Complex.normSq α / 2) : ℝ) : ℂ) *
        Complex.exp (conj β * α) := by
  rw [lp.inner_eq_tsum]
  simp only [psi_apply, RCLike.inner_apply]
  simp_rw [mul_comm _ (conj _)]
  exact (coef_sum α β).tsum_eq

lemma inner_self_psi (α : ℂ) : inner ℂ (psi α) (psi α) = 1 := by
  rw [inner_psi]
  have : conj α * α = ((Complex.normSq α : ℝ) : ℂ) := by rw [mul_comm, Complex.mul_conj]
  rw [this, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  norm_num

lemma norm_psi (α : ℂ) : ‖psi α‖ = 1 := by
  have h := inner_self_psi α
  rw [inner_self_eq_norm_sq_to_K] at h
  have : ‖psi α‖ ^ 2 = 1 := by
    have h2 : ((‖psi α‖ ^ 2 : ℝ) : ℂ) = 1 := by rw [← h]; push_cast; rfl
    exact_mod_cast h2
  have := norm_nonneg (psi α)
  nlinarith

lemma overlap (α β : ℂ) : ‖inner ℂ (psi β) (psi α)‖ ^ 2 = Real.exp (-‖β - α‖ ^ 2) := by
  rw [inner_psi, norm_mul, Complex.norm_real, Complex.norm_exp,
    Real.norm_of_nonneg (by positivity), mul_pow, mul_pow, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma coef_succ (α : ℂ) (n : ℕ) :
    ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * coherentCoefficient α (n + 1) =
      α * coherentCoefficient α n := by
  simp only [coherentCoefficient]
  have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hfs : Real.sqrt (((n + 1) ! : ℕ) : ℝ) = Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt (n ! : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul hn.le]
  rw [hfs]
  have h1 : ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hn).ne'
  have h2 : ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hf).ne'
  push_cast
  field_simp
  ring

end X5CS

noncomputable section
open scoped BigOperators ComplexOrder ENNReal ComplexConjugate Nat

namespace X5CS
open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)
open QAlgorithms.Papers.Independent.Frontier30.P08

lemma sq_sum (α : ℂ) : HasSum (fun n => ‖coherentCoefficient α n‖ ^ 2) 1 := by
  have h := (coef_sum α α)
  have hre := Complex.reCLM.hasSum h
  simp only [Complex.reCLM_apply] at hre
  have e : (((Real.exp (-Complex.normSq α / 2) * Real.exp (-Complex.normSq α / 2) : ℝ) : ℂ) *
      Complex.exp (conj α * α)).re = 1 := by
    have : conj α * α = ((Complex.normSq α : ℝ) : ℂ) := by rw [mul_comm, Complex.mul_conj]
    rw [this, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [e] at hre
  convert hre using 1
  funext n; exact coef_norm_sq α n

lemma msq_sum (α : ℂ) : HasSum (fun n : ℕ => (n : ℝ) * ‖coherentCoefficient α n‖ ^ 2)
    (‖α‖ ^ 2) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ‖coherentCoefficient α (k + 1)‖ ^ 2) =
      fun k => ‖α‖ ^ 2 * ‖coherentCoefficient α k‖ ^ 2 := by
    funext k
    have h := congrArg (fun z : ℂ => ‖z‖ ^ 2) (coef_succ α k)
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)] at h
    exact h
  push_cast at this ⊢
  rw [this]
  simpa using (sq_sum α).mul_left (‖α‖ ^ 2)

def Cseq (α : ℂ) (n : ℕ) : ℂ := creationSequence (psi α) n

lemma Cseq_succ (α : ℂ) (m : ℕ) :
    Cseq α (m + 1) = ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * coherentCoefficient α m := by
  simp [Cseq, creationSequence]

lemma Cseq_zero (α : ℂ) : Cseq α 0 = 0 := by simp [Cseq, creationSequence]

lemma Cnorm_sum (α : ℂ) : HasSum (fun n => ‖Cseq α n‖ ^ 2) (1 + ‖α‖ ^ 2) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Cseq_zero, norm_zero, sub_zero]
  have : (fun m => ‖Cseq α (m + 1)‖ ^ 2) =
      fun m : ℕ => ‖coherentCoefficient α m‖ ^ 2 + (m : ℝ) * ‖coherentCoefficient α m‖ ^ 2 := by
    funext m
    rw [Cseq_succ, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast; ring
  rw [this]
  simpa using (sq_sum α).add (msq_sum α)

lemma C_mem (α : ℂ) : Memℓp (Cseq α) 2 := by
  apply memℓp_gen
  simpa using (Cnorm_sum α).summable

def Cv (α : ℂ) : Fock := ⟨Cseq α, C_mem α⟩

@[simp] lemma Cv_apply (α : ℂ) (n : ℕ) : Cv α n = Cseq α n := rfl

lemma inner_C_C (α : ℂ) : inner ℂ (Cv α) (Cv α) = 1 + ((‖α‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (Cv α)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Cv_apply] at h
  rw [(Cnorm_sum α).tsum_eq] at h
  have : ‖Cv α‖ ^ 2 = 1 + ‖α‖ ^ 2 := h
  have h3 : ((‖Cv α‖ ^ 2 : ℝ) : ℂ) = 1 + ((‖α‖ ^ 2 : ℝ) : ℂ) := by rw [this]; push_cast; ring
  convert h3 using 1
  simp

lemma inner_psi_C (α : ℂ) : inner ℂ (psi α) (Cv α) = conj α := by
  rw [lp.inner_eq_tsum]
  simp only [psi_apply, Cv_apply, RCLike.inner_apply]
  have hs : Summable (fun n => Cseq α n * conj (coherentCoefficient α n)) := by
    have := lp.summable_inner (𝕜 := ℂ) (psi α) (Cv α)
    simpa [RCLike.inner_apply] using this
  rw [hs.tsum_eq_zero_add]
  simp only [Cseq_zero, zero_mul, zero_add]
  have : (fun m => Cseq α (m + 1) * conj (coherentCoefficient α (m + 1))) =
      fun m => conj α * (conj (coherentCoefficient α m) * coherentCoefficient α m) := by
    funext m
    rw [Cseq_succ]
    have h := congrArg conj (coef_succ α m)
    simp only [map_mul, Complex.conj_ofReal] at h
    calc ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * coherentCoefficient α m *
          conj (coherentCoefficient α (m + 1))
        = coherentCoefficient α m * (((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          conj (coherentCoefficient α (m + 1))) := by ring
      _ = _ := by rw [h]; ring
  rw [this, tsum_mul_left]
  have := inner_self_psi α
  rw [lp.inner_eq_tsum] at this
  simp only [psi_apply, RCLike.inner_apply] at this
  simp_rw [mul_comm (conj _)] at this ⊢
  rw [this, one_mul]

end X5CS

noncomputable section
open scoped BigOperators ComplexOrder ENNReal ComplexConjugate Nat

namespace X5CS
open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)
open QAlgorithms.Papers.Independent.Frontier30.P08

lemma ann_eq (α : ℂ) (n : ℕ) : annihilationSequence (psi α) n = α * psi α n := by
  simp only [annihilationSequence, psi_apply]
  exact coef_succ α n

def v0 (α : ℂ) : Fock := α • psi α + Cv α
def v1 (α : ℂ) : Fock := Complex.I • (Cv α - α • psi α)

lemma q0_eq (α : ℂ) : quadratureSequence 0 (psi α) = fun n => v0 α n := by
  funext n
  simp only [quadratureSequence, if_true, v0, ann_eq]
  rfl

lemma q1_eq (α : ℂ) : quadratureSequence 1 (psi α) = fun n => v1 α n := by
  funext n
  simp only [quadratureSequence, show (1 : Fin 2) ≠ 0 by decide, if_false, v1, ann_eq]
  rfl

lemma qk_eq (α : ℂ) (k : Fin 2) :
    quadratureSequence k (psi α) = fun n => (if k = 0 then v0 α else v1 α) n := by
  fin_cases k
  · simp [q0_eq]
  · simp [q1_eq]

lemma lp_sq_summable (v : Fock) : Summable (fun n => ‖v n‖ ^ 2) := by
  have := (v.2).summable (p := 2) (by norm_num)
  simpa [Real.rpow_two] using this

lemma tsum_inner (u v : Fock) :
    (∑' n : ℕ, star (u n) * v n) = inner ℂ u v := by
  rw [lp.inner_eq_tsum]
  congr 1; funext n
  simp [RCLike.inner_apply, mul_comm]

lemma I3 (α : ℂ) : inner ℂ (Cv α) (psi α) = α := by
  rw [← inner_conj_symm, inner_psi_C]; simp

lemma finite_quad (α : ℂ) : finitePureQuadratures (psi α) := by
  intro k
  rw [qk_eq]
  exact lp_sq_summable _

lemma mean0 (α : ℂ) : pureMean (psi α) 0 = 2 * α.re := by
  simp only [pureMean, q0_eq, tsum_inner, v0, inner_add_right, inner_smul_right, inner_self_psi,
    inner_psi_C]
  simp [Complex.add_re]; ring

lemma mean1 (α : ℂ) : pureMean (psi α) 1 = 2 * α.im := by
  simp only [pureMean, q1_eq, tsum_inner, v1, inner_smul_right, inner_sub_right, inner_smul_right,
    inner_self_psi, inner_psi_C]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]; ring

lemma cov (α : ℂ) : pureQuadratureCovariance (psi α) = 1 := by
  have hA := inner_self_psi α
  have hB := inner_psi_C α
  have hC := I3 α
  have hn : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hD : inner ℂ (Cv α) (Cv α) = 1 + ((α.re ^ 2 + α.im ^ 2 : ℝ) : ℂ) := by
    rw [inner_C_C, hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [pureQuadratureCovariance, Fin.zero_eta, Fin.mk_one, Fin.isValue, mean0, mean1,
    q0_eq, q1_eq, tsum_inner, v0, v1, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right, hA, hB, hC, hD, Matrix.one_apply] <;>
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.add_im,
    Complex.sub_im, -Complex.ofReal_add, -Complex.ofReal_pow] <;> ring

end X5CS

noncomputable section
open scoped BigOperators ComplexOrder ENNReal ComplexConjugate Nat NNReal

namespace X5CS
open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)
open QAlgorithms.Papers.Independent.Frontier30.P08

lemma inner_psi_x (α : ℂ) (x : Fock) :
    inner ℂ (psi α) x = ((Real.exp (-Complex.normSq α / 2) : ℝ) : ℂ) *
      ∑' n : ℕ, (x n / ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ)) * (conj α) ^ n := by
  rw [lp.inner_eq_tsum, ← tsum_mul_left]
  congr 1; funext n
  simp only [psi_apply, RCLike.inner_apply, coherentCoefficient, map_div₀, map_mul, map_pow,
    Complex.conj_ofReal]
  ring

lemma series_zero (a : ℕ → ℂ) (C : ℝ) (hC : ∀ n, ‖a n‖ ≤ C)
    (h : ∀ z : ℂ, ∑' n : ℕ, a n * z ^ n = 0) : ∀ n, a n = 0 := by
  set p := FormalMultilinearSeries.ofScalars ℂ a
  have hr : ((1 : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound C
    intro n
    simp only [NNReal.coe_one, one_pow, mul_one, p, FormalMultilinearSeries.ofScalars_norm]
    exact hC n
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hr
  have hf := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hsum : p.sum = 0 := by
    funext z
    simp only [FormalMultilinearSeries.sum, p, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, Pi.zero_apply]
    exact h z
  rw [hsum] at hf
  have h0 := hf.eq_zero
  intro n
  have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff n) h0
  simp only [p, FormalMultilinearSeries.coeff_ofScalars] at this
  rw [this]
  simp [FormalMultilinearSeries.coeff]

lemma dense_span : Dense (↑(Submodule.span ℂ {psi : Fock | ∃ alpha : ℂ,
      HasCoherentCoefficients alpha psi}) : Set Fock) := by
  set K := Submodule.span ℂ {psi : Fock | ∃ alpha : ℂ, HasCoherentCoefficients alpha psi}
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hzero : ∀ α : ℂ, inner ℂ (psi α) x = 0 := by
    intro α
    have hmem : psi α ∈ K := Submodule.subset_span ⟨α, fun n => rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hmem hx
  set a : ℕ → ℂ := fun n => x n / ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ)
  have ha : ∀ n, a n = 0 := by
    apply series_zero a ‖x‖
    · intro n
      simp only [a, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have h1 : (1 : ℝ) ≤ Real.sqrt (n ! : ℝ) := by
        rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
      have h2 : ‖x n‖ ≤ ‖x‖ := lp.norm_apply_le_norm (by norm_num) x n
      calc ‖x n‖ / Real.sqrt (n ! : ℝ) ≤ ‖x n‖ / 1 :=
            div_le_div_of_nonneg_left (norm_nonneg _) one_pos h1
        _ ≤ ‖x‖ := by simpa using h2
    · intro z
      have := hzero (conj z)
      rw [inner_psi_x, Complex.conj_conj] at this
      have hne : ((Real.exp (-Complex.normSq (conj z) / 2) : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; exact (Real.exp_pos _).ne'
      exact (mul_eq_zero.mp this).resolve_left hne
  apply lp.ext
  funext n
  have := ha n
  have hs : ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos n)).ne'
  simp only [a, div_eq_zero_iff, hs, or_false] at this
  simpa using this

end X5CS


open scoped BigOperators ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient) in
open QAlgorithms.Papers.Independent.Frontier30.P08 in
theorem solution :
    (∀ alpha : ℂ, ∃ psi : Fock,
      HasCoherentCoefficients alpha psi ∧ ‖psi‖ = 1 ∧
      finitePureQuadratures psi ∧
      (∀ n, annihilationSequence psi n = alpha * psi n) ∧
      pureMean psi 0 = 2 * alpha.re ∧ pureMean psi 1 = 2 * alpha.im ∧
      pureQuadratureCovariance psi = 1) ∧
    (∀ alpha beta : ℂ, ∀ psi phi : Fock,
      HasCoherentCoefficients alpha psi → HasCoherentCoefficients beta phi →
      ‖inner ℂ phi psi‖ ^ 2 = Real.exp (-‖beta - alpha‖ ^ 2)) ∧
    Dense (↑(Submodule.span ℂ {psi : Fock | ∃ alpha : ℂ,
      HasCoherentCoefficients alpha psi}) : Set Fock) := by
  refine ⟨fun α => ⟨X5CS.psi α, fun n => rfl, X5CS.norm_psi α, X5CS.finite_quad α,
    X5CS.ann_eq α, X5CS.mean0 α, X5CS.mean1 α, X5CS.cov α⟩, ?_, X5CS.dense_span⟩
  intro α β ψ0 φ0 hψ hφ
  have e1 : ψ0 = X5CS.psi α := lp.ext (funext hψ)
  have e2 : φ0 = X5CS.psi β := lp.ext (funext hφ)
  rw [e1, e2]
  exact X5CS.overlap α β

