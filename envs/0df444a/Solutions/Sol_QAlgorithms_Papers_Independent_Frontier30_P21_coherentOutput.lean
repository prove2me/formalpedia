-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P21.coherentOutput
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:42:43.011589+00:00
-- url     : https://prove2.me/submissions/ba1f778a-8a5c-4d20-8103-9d188949b060

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

-- ===== P21Coh =====

noncomputable section

namespace X4P21

open QAlgorithms.Papers.Independent.Frontier30.P21
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

lemma rexp (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

lemma sq_norm_coh (α : ℂ) (n : ℕ) :
    ‖coherentCoefficient α n‖ ^ 2 =
      Real.exp (-Complex.normSq α) * (Complex.normSq α ^ n / (n.factorial : ℝ)) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  unfold coherentCoefficient
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [div_pow, mul_pow, Real.sq_sqrt hf.le, ← Real.exp_nat_mul, ← pow_mul, mul_comm n 2, pow_mul,
    ← Complex.normSq_eq_norm_sq]
  push_cast
  ring_nf

lemma hs (α : ℂ) : HasSum (fun n => ‖coherentCoefficient α n‖ ^ 2) 1 := by
  simp_rw [sq_norm_coh]
  have := (rexp (Complex.normSq α)).mul_left (Real.exp (-Complex.normSq α))
  rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this

lemma pure (α : ℂ) : IsPureFockDensity (coherentDensity α) := by
  have hm : Memℓp (fun n => coherentCoefficient α n) 2 := by
    apply memℓp_gen
    simpa using (hs α).summable
  refine ⟨⟨_, hm⟩, ?_, fun m n => rfl⟩
  have h2 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ⟨_, hm⟩
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  have : ‖(⟨_, hm⟩ : QAlgorithms.RealRegisters.Hilbert ℕ)‖ ^ 2 = 1 := by
    rw [h2]; exact (hs α).tsum_eq
  have h0 := norm_nonneg (⟨_, hm⟩ : QAlgorithms.RealRegisters.Hilbert ℕ)
  nlinarith


lemma sc (m l : ℕ) : Real.sqrt ((m + l).choose l : ℝ) =
    Real.sqrt ((m + l).factorial : ℝ) / (Real.sqrt (m.factorial : ℝ) * Real.sqrt (l.factorial : ℝ)) := by
  have h : ((m + l).factorial : ℝ) = ((m + l).choose l : ℝ) * (m.factorial * l.factorial) := by
    rw [← mul_assoc]; exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial m l).symm
  have h1 : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have h2 : (0 : ℝ) < l.factorial := by exact_mod_cast l.factorial_pos
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_mul h1.le]
  have : 0 < Real.sqrt (m.factorial : ℝ) * Real.sqrt (l.factorial : ℝ) := by positivity
  field_simp

lemma term (η : ℝ) (α : ℂ) (m n l : ℕ) :
    vacuumLossTerm η (coherentDensity α) m n l =
      (((Real.exp (-Complex.normSq α) * Real.sqrt η ^ m * Real.sqrt η ^ n /
        (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) : ℝ) : ℂ) *
        α ^ m * (starRingEnd ℂ α) ^ n) *
      (((Complex.normSq α * (1 - η)) ^ l / (l.factorial : ℝ) : ℝ) : ℂ) := by
  have hm : (0 : ℝ) < Real.sqrt (m.factorial : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast m.factorial_pos)
  have hn : (0 : ℝ) < Real.sqrt (n.factorial : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast n.factorial_pos)
  have hl : (0 : ℝ) < Real.sqrt (l.factorial : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast l.factorial_pos)
  have hml : (0 : ℝ) < Real.sqrt ((m + l).factorial : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (m + l).factorial_pos)
  have hnl : (0 : ℝ) < Real.sqrt ((n + l).factorial : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (n + l).factorial_pos)
  have hll : (l.factorial : ℝ) = Real.sqrt (l.factorial : ℝ) * Real.sqrt (l.factorial : ℝ) :=
    (Real.mul_self_sqrt (by positivity)).symm
  have he : Real.exp (-Complex.normSq α) = Real.exp (-Complex.normSq α / 2) * Real.exp (-Complex.normSq α / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hc : (Complex.normSq α : ℂ) = α * starRingEnd ℂ α := (Complex.mul_conj α).symm
  unfold vacuumLossTerm coherentDensity coherentCoefficient
  rw [sc m l, sc n l, he]
  simp only [star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal, map_pow]
  push_cast
  rw [hc]
  have hm' : (Real.sqrt (m.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl' : (Real.sqrt (l.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hml' : (Real.sqrt ((m + l).factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hml.ne'
  have hnl' : (Real.sqrt ((n + l).factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnl.ne'
  have hsq : ((Real.sqrt (l.factorial : ℝ) : ℝ) : ℂ) ^ 2 = (l.factorial : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
  field_simp
  rw [hsq]
  have hlf : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
  rw [eq_div_iff hlf]
  rw [mul_pow, mul_pow]
  ring

lemma lossSum (η : ℝ) (hη : 0 ≤ η) (α : ℂ) (m n : ℕ) :
    HasSum (vacuumLossTerm η (coherentDensity α) m n)
      (coherentDensity ((Real.sqrt η : ℂ) * α) m n) := by
  have h := (Complex.hasSum_ofReal.2 (rexp (Complex.normSq α * (1 - η)))).mul_left
    (((Real.exp (-Complex.normSq α) * Real.sqrt η ^ m * Real.sqrt η ^ n /
        (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) : ℝ) : ℂ) *
        α ^ m * (starRingEnd ℂ) α ^ n)
  simp_rw [← term] at h
  suffices eq : coherentDensity ((Real.sqrt η : ℂ) * α) m n =
      ((Real.exp (-Complex.normSq α) * Real.sqrt η ^ m * Real.sqrt η ^ n /
        (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) : ℝ) : ℂ) *
        α ^ m * (starRingEnd ℂ) α ^ n * ((Real.exp (Complex.normSq α * (1 - η)) : ℝ) : ℂ) by
    rw [eq]; exact h
  have hN : Complex.normSq ((Real.sqrt η : ℂ) * α) = η * Complex.normSq α := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hη]
  have hE : Real.exp (-(η * Complex.normSq α / 2)) * Real.exp (-(η * Complex.normSq α / 2)) =
      Real.exp (-Complex.normSq α) * Real.exp (Complex.normSq α * (1 - η)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  unfold coherentDensity coherentCoefficient
  rw [hN, neg_div]
  simp only [star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal, map_pow, mul_pow]
  have hm : (Real.sqrt (m.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast m.factorial_pos)).ne'
  have hn : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast n.factorial_pos)).ne'
  have hE' : ((Real.exp (-(η * Complex.normSq α / 2)) : ℝ) : ℂ) * (Real.exp (-(η * Complex.normSq α / 2)) : ℝ) =
      (Real.exp (-Complex.normSq α) : ℝ) * (Real.exp (Complex.normSq α * (1 - η)) : ℝ) := by
    exact_mod_cast hE
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]
  field_simp
  linear_combination (↑√η ^ m * α ^ m * ↑√η ^ n * (starRingEnd ℂ) α ^ n) * hE'

theorem main (eta : ℝ) (heta0 : 0 ≤ eta) (_heta1 : eta ≤ 1) (alpha : ℂ) :
    IsPureFockDensity (coherentDensity alpha) ∧
    IsPureFockDensity (coherentDensity ((Real.sqrt eta : ℂ) * alpha)) ∧
    (∀ m n, HasSum (vacuumLossTerm eta (coherentDensity alpha) m n)
      (coherentDensity ((Real.sqrt eta : ℂ) * alpha) m n)) ∧
    vacuumLossKernel eta (coherentDensity alpha) =
      coherentDensity ((Real.sqrt eta : ℂ) * alpha) :=
  ⟨pure _, pure _, lossSum eta heta0 alpha, by
    funext m n; exact (lossSum eta heta0 alpha m n).tsum_eq⟩

end X4P21

-- ===== P21CohSol =====

noncomputable section

open Filter
open QAlgorithms.Papers.Independent.Frontier30.P21
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem solution (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (alpha : ℂ) :
    IsPureFockDensity (coherentDensity alpha) ∧
    IsPureFockDensity (coherentDensity ((Real.sqrt eta : ℂ) * alpha)) ∧
    (∀ m n, HasSum (vacuumLossTerm eta (coherentDensity alpha) m n)
      (coherentDensity ((Real.sqrt eta : ℂ) * alpha) m n)) ∧
    vacuumLossKernel eta (coherentDensity alpha) =
      coherentDensity ((Real.sqrt eta : ℂ) * alpha) :=
  X4P21.main eta heta0 heta1 alpha

end

#print axioms solution
