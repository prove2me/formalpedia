-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.referenceMinimumUpperBound
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-29T18:25:08.915743+00:00
-- url     : https://prove2.me/submissions/ee118ada-7bb3-48c0-ba29-2cb2ad5b919d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_relativeEntropy_sum_le
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_relativeEntropy_le_of_dominated
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_sub_minEigenvalue_smul_one_posSemidef
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_exists_jordan_decomposition
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_relativeEntropy_smul_smul

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)
theorem rmub_supp {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) (a b : ℝ)
    (hb : b ≠ 0) : IsSupported ((a : ℂ) • X) ((b : ℂ) • X) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec] at hv ⊢
  rcases smul_eq_zero.mp hv with h | h
  · exact absurd (Complex.ofReal_eq_zero.mp h) hb
  · rw [h, smul_zero]

theorem rmub_main {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    let beta := minEigenvalue sigma
    let T := traceDistance rho sigma
    (T ≤ beta → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log (1 + T / beta) +
        (beta - T) * Real.log (1 - T / beta) : ℝ) : EReal)) ∧
    (beta ≤ T → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log (1 + T / beta) : ℝ) : EReal)) := by
  intro beta T
  obtain ⟨Xp, Xm, hXp, hXm, hdiff, htrp, htrm, hle⟩ :=
    exists_jordan_decomposition rho sigma hrho hsigma
  have hσβ : (sigma - (beta : ℂ) • (1 : Matrix I I ℂ)).PosSemidef :=
    sub_minEigenvalue_smul_one_posSemidef sigma hsigma.1.isHermitian
  have hTd : traceDistance rho sigma = T := rfl
  have hbd : minEigenvalue sigma = beta := rfl
  rw [hTd] at htrp htrm hle
  rw [hbd] at hbeta
  clear_value beta T
  have hρ : rho = sigma + Xp - Xm := by
    rw [← sub_add_cancel rho sigma, hdiff]; abel
  have hT0 : 0 ≤ T := by
    have := hXp.trace_nonneg
    rw [htrp] at this
    exact Complex.zero_le_real.mp this
  have hss : ∀ R : Matrix I I ℂ, relativeEntropy (((1 : ℝ) : ℂ) • R) (((1 : ℝ) : ℂ) • R) =
      relativeEntropy R R := by intro R; simp
  rcases hT0.eq_or_lt with hT | hT
  · -- T = 0: rho = sigma
    have hXp0 : Xp = 0 := hXp.trace_eq_zero_iff.mp (by rw [htrp, ← hT]; simp)
    have hXm0 : Xm = 0 := hXm.trace_eq_zero_iff.mp (by rw [htrm, ← hT]; simp)
    have hD : relativeEntropy rho sigma = 0 := by
      rw [hρ, hXp0, hXm0, add_zero, sub_zero, ← hss,
        relativeEntropy_smul_smul sigma hsigma.1 zero_le_one one_pos]
      simp
    rw [hD, ← hT]
    refine ⟨fun _ => by simp, fun _ => by simp⟩
  -- T > 0
  set c : ℝ := beta / T with hc
  have hc0 : 0 < c := div_pos hbeta hT
  have hcT : c * T = beta := by rw [hc]; field_simp
  have hcTC : (c : ℂ) * (T : ℂ) = (beta : ℂ) := by exact_mod_cast hcT
  have hcC : (0 : ℂ) ≤ (c : ℂ) := Complex.zero_le_real.mpr hc0.le
  have hR : (sigma - (c : ℂ) • (Xp + Xm)).PosSemidef := by
    have e : sigma - (c : ℂ) • (Xp + Xm) =
        (sigma - (beta : ℂ) • (1 : Matrix I I ℂ)) +
          (c : ℂ) • ((T : ℂ) • (1 : Matrix I I ℂ) - (Xp + Xm)) := by
      rw [smul_sub, smul_smul, hcTC]; abel
    rw [e]; exact hσβ.add (hle.smul hcC)
  have htrpre : Xp.trace.re = T := by rw [htrp]; simp
  have htrmre : Xm.trace.re = T := by rw [htrm]; simp
  have hlogp : (c + 1) / c = 1 + T / beta := by rw [hc]; field_simp
  refine ⟨fun hTb => ?_, fun _ => ?_⟩
  · -- three-piece splitting
    have hc1 : 0 ≤ c - 1 := by
      rw [hc, sub_nonneg, le_div_iff₀ hT]; linarith
    have hlogm : (c - 1) / c = 1 - T / beta := by rw [hc]; field_simp
    set R := sigma - (c : ℂ) • (Xp + Xm) with hRdef
    let A : Fin 3 → Matrix I I ℂ :=
      ![((1 : ℝ) : ℂ) • R, ((c + 1 : ℝ) : ℂ) • Xp, ((c - 1 : ℝ) : ℂ) • Xm]
    let B : Fin 3 → Matrix I I ℂ :=
      ![((1 : ℝ) : ℂ) • R, ((c : ℝ) : ℂ) • Xp, ((c : ℝ) : ℂ) • Xm]
    have hsA : ∑ i, A i = rho := by
      simp only [A, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hρ, hRdef]; push_cast; module
    have hsB : ∑ i, B i = sigma := by
      simp only [B, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hRdef]; module
    have h := relativeEntropy_sum_le Finset.univ A B
      (by
        intro i _; fin_cases i
        · exact hR.smul (Complex.zero_le_real.mpr zero_le_one)
        · exact hXp.smul (Complex.zero_le_real.mpr (by linarith))
        · exact hXm.smul (Complex.zero_le_real.mpr hc1))
      (by
        intro i _; fin_cases i
        · exact hR.smul (Complex.zero_le_real.mpr zero_le_one)
        · exact hXp.smul hcC
        · exact hXm.smul hcC)
      (by
        intro i _; fin_cases i
        · exact rmub_supp R 1 1 one_ne_zero
        · exact rmub_supp Xp _ _ hc0.ne'
        · exact rmub_supp Xm _ _ hc0.ne')
    rw [hsA, hsB] at h
    simp only [A, B, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    rw [relativeEntropy_smul_smul R hR zero_le_one one_pos,
      relativeEntropy_smul_smul Xp hXp (by linarith) hc0,
      relativeEntropy_smul_smul Xm hXm hc1 hc0] at h
    refine h.trans (le_of_eq ?_)
    rw [← EReal.coe_add, ← EReal.coe_add, htrpre, htrmre, hlogp, hlogm]
    congr 1
    simp only [div_one, Real.log_one, mul_zero, zero_mul, zero_add]
    linear_combination (Real.log (1 + T / beta) + Real.log (1 - T / beta)) * hcT
  · -- domination by W = sigma + Xp, then two-piece splitting
    have hσpd : sigma.PosDef := by
      have e : sigma = (sigma - (beta : ℂ) • (1 : Matrix I I ℂ)) +
          (beta : ℂ) • (1 : Matrix I I ℂ) := by abel
      rw [e]
      exact Matrix.PosDef.posSemidef_add hσβ (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hbeta))
    have hdom := relativeEntropy_le_of_dominated rho sigma (sigma + Xp) hrho.1 hσpd
      (by rw [hρ]; simpa using hXm) (by simpa using hXp)
    set R := sigma - (c : ℂ) • Xp with hRdef
    have hR' : R.PosSemidef := by
      have e : R = (sigma - (c : ℂ) • (Xp + Xm)) + (c : ℂ) • Xm := by
        rw [hRdef, smul_add]; abel
      rw [e]; exact hR.add (hXm.smul hcC)
    let A : Fin 2 → Matrix I I ℂ := ![((1 : ℝ) : ℂ) • R, ((c + 1 : ℝ) : ℂ) • Xp]
    let B : Fin 2 → Matrix I I ℂ := ![((1 : ℝ) : ℂ) • R, ((c : ℝ) : ℂ) • Xp]
    have hsA : ∑ i, A i = sigma + Xp := by
      simp only [A, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hRdef]; push_cast; module
    have hsB : ∑ i, B i = sigma := by
      simp only [B, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hRdef]; module
    have h := relativeEntropy_sum_le Finset.univ A B
      (by
        intro i _; fin_cases i
        · exact hR'.smul (Complex.zero_le_real.mpr zero_le_one)
        · exact hXp.smul (Complex.zero_le_real.mpr (by linarith)))
      (by
        intro i _; fin_cases i
        · exact hR'.smul (Complex.zero_le_real.mpr zero_le_one)
        · exact hXp.smul hcC)
      (by
        intro i _; fin_cases i
        · exact rmub_supp R 1 1 one_ne_zero
        · exact rmub_supp Xp _ _ hc0.ne')
    rw [hsA, hsB] at h
    simp only [A, B, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [relativeEntropy_smul_smul R hR' zero_le_one one_pos,
      relativeEntropy_smul_smul Xp hXp (by linarith) hc0] at h
    refine hdom.trans (h.trans (le_of_eq ?_))
    rw [← EReal.coe_add, htrpre, hlogp]
    congr 1
    simp only [div_one, Real.log_one, mul_zero, zero_mul, zero_add]
    linear_combination Real.log (1 + T / beta) * hcT

end QAlgorithms.Papers.Independent.Support50.P17

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P17 in
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy) in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    let beta := minEigenvalue sigma
    let T := traceDistance rho sigma
    (T ≤ beta → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log (1 + T / beta) +
        (beta - T) * Real.log (1 - T / beta) : ℝ) : EReal)) ∧
    (beta ≤ T → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log (1 + T / beta) : ℝ) : EReal)) :=
  rmub_main rho sigma hrho hsigma hbeta

end
