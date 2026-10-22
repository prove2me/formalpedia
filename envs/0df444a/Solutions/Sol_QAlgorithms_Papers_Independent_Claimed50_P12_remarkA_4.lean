-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.remarkA_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:51:07.519328+00:00
-- url     : https://prove2.me/submissions/45277ae3-ef75-4ad6-800c-2036feef2a51

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

lemma g67u_nlb_anti {x y : ℝ≥0∞} (h : x ≤ y) : negLogBits y ≤ negLogBits x := by
  unfold negLogBits
  by_cases hy0 : y = 0
  · have hx0 : x = 0 := le_antisymm (hy0 ▸ h) (zero_le)
    simp [hx0, hy0]
  by_cases hx0 : x = 0
  · simp only [hx0, if_true]; exact le_top
  by_cases hyt : y = ⊤
  · rw [if_neg hy0, if_pos hyt]; exact bot_le
  have hxt : x ≠ ⊤ := ne_top_of_le_ne_top hyt h
  rw [if_neg hy0, if_neg hyt, if_neg hx0, if_neg hxt]
  have hxpos : 0 < x.toReal := ENNReal.toReal_pos hx0 hxt
  have hle : x.toReal ≤ y.toReal := ENNReal.toReal_mono hyt h
  exact EReal.coe_le_coe_iff.2 (neg_le_neg (Real.logb_le_logb_of_le (by norm_num) hxpos hle))

lemma g67u_tv_mono {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Op I) {e f : ℝ}
    (he : 0 < e) (hef : e ≤ f) : testingValue e rho sigma ≤ testingValue f rho sigma := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  unfold testingValue
  refine le_sInf ?_
  rintro v ⟨Q, hQ, hfQ, rfl⟩
  set t : ℝ := e / f with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (div_le_one hf).2 hef
  have htc : (0 : ℂ) ≤ (t : ℂ) := Complex.zero_le_real.2 ht0
  have htc1 : (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) := Complex.zero_le_real.2 (by linarith)
  refine sInf_le_of_le ⟨(t : ℂ) • Q, ⟨hQ.1.smul htc, ?_⟩, ?_, rfl⟩ (le_of_eq ?_)
  · have e1 : (1 : Matrix I I ℂ) - (t : ℂ) • Q = ((1 - t : ℝ) : ℂ) • (1 : Matrix I I ℂ) + (t : ℂ) • (1 - Q) := by
      rw [smul_sub, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      abel
    rw [e1]
    exact (Matrix.PosSemidef.one.smul htc1).add (hQ.2.smul htc)
  · rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    calc e = t * f := by rw [ht]; field_simp
      _ ≤ t * (Q * rho).trace.re := mul_le_mul_of_nonneg_left hfQ ht0
  · congr 1
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, ht]
    field_simp

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (e f : ℝ) (he : 0 ≤ e) (hef : e ≤ f)
    (hf : f ≤ rho.trace.re) :
    endpointTestingEntropyBits f rho sigma ≤ endpointTestingEntropyBits e rho sigma := by
  unfold endpointTestingEntropyBits
  apply g67u_nlb_anti
  unfold endpointTestingValue
  by_cases he0 : e = 0
  · by_cases hf0 : f = 0
    · rw [he0, hf0]
    · rw [if_pos he0, if_neg hf0]
      exact sInf_le ⟨f, lt_of_le_of_ne (he.trans hef) (Ne.symm hf0), rfl⟩
  · have hf0 : f ≠ 0 := by
      intro h; apply he0; linarith
    rw [if_neg he0, if_neg hf0]
    exact g67u_tv_mono rho sigma (lt_of_le_of_ne he (Ne.symm he0)) hef
