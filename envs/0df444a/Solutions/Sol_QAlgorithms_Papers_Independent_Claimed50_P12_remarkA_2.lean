-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.remarkA_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:31:13.118774+00:00
-- url     : https://prove2.me/submissions/3b76841f-904a-46a7-8ff7-182e432469b1

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

lemma g68m_sInf_mul {α : Type*} (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) (P : α → Prop)
    (f : α → ℝ≥0∞) :
    sInf {v | ∃ a, P a ∧ v = c * f a} = c * sInf {v | ∃ a, P a ∧ v = f a} := by
  have h1 : {v | ∃ a, P a ∧ v = c * f a} = (fun a => c * f a) '' {a | P a} := by
    ext v; simp [eq_comm]
  have h2 : {v | ∃ a, P a ∧ v = f a} = f '' {a | P a} := by
    ext v; simp [eq_comm]
  rw [h1, h2, sInf_image, sInf_image, iInf_subtype', iInf_subtype', ENNReal.mul_iInf_of_ne hc0 hct]

lemma g68m_negLog_mul (lam : ℝ) (hlam : 0 < lam) (v : ℝ≥0∞) :
    negLogBits (ENNReal.ofReal lam * v) = negLogBits v - ((Real.logb 2 lam : ℝ) : EReal) := by
  have hc0 : ENNReal.ofReal lam ≠ 0 := by simpa using hlam
  unfold negLogBits
  by_cases h0 : v = 0
  · simp [h0]
  by_cases ht : v = ⊤
  · simp [ht, ENNReal.mul_top hc0, EReal.bot_sub]
  have hm0 : ENNReal.ofReal lam * v ≠ 0 := mul_ne_zero hc0 h0
  have hmt : ENNReal.ofReal lam * v ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht
  rw [if_neg hm0, if_neg hmt, if_neg h0, if_neg ht, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hlam.le]
  have hv : 0 < v.toReal := ENNReal.toReal_pos h0 ht
  rw [Real.logb_mul hlam.ne' hv.ne', ← EReal.coe_sub]
  congr 1; ring

lemma g68m_testing (lam : ℝ) (hlam : 0 < lam) {I : Type*} [Fintype I] [DecidableEq I]
    (e : ℝ) (rho sigma : Op I) :
    testingValue e rho ((lam : ℂ) • sigma) = ENNReal.ofReal lam * testingValue e rho sigma := by
  unfold testingValue
  have hc0 : ENNReal.ofReal lam ≠ 0 := by simpa using hlam
  have key := g68m_sInf_mul _ hc0 ENNReal.ofReal_ne_top
    (fun Q : Op I => IsEffect Q ∧ e ≤ (Q * rho).trace.re)
    (fun Q => ENNReal.ofReal ((Q * sigma).trace.re / e))
  simp only [and_assoc] at key
  rw [← key]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, and_assoc]
  refine exists_congr fun Q => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [← ENNReal.ofReal_mul hlam.le, Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.re_ofReal_mul]
  rw [mul_div_assoc]

lemma g68m_sInf_sub (S : Set EReal) (c : ℝ) :
    sInf ((fun x => x - (c : EReal)) '' S) = sInf S - (c : EReal) := by
  apply le_antisymm
  · rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]
    apply le_sInf
    intro x hx
    have : sInf ((fun x => x - (c : EReal)) '' S) ≤ x - c := sInf_le ⟨x, hx, rfl⟩
    calc sInf ((fun x => x - (c : EReal)) '' S) + c ≤ x - c + c := add_le_add_left this _
      _ = x := EReal.sub_add_cancel
  · apply le_sInf
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.sub_le_sub (sInf_le hx) le_rfl

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (lam : ℝ) (hlam : 0 < lam) :
    (∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ rho.trace.re →
      endpointTestingEntropyBits epsilon rho ((lam : ℂ) • sigma) =
        endpointTestingEntropyBits epsilon rho sigma - ((Real.logb 2 lam : ℝ) : EReal)) ∧
    (IsDensityMatrix rho → ∀ epsilon : ℝ, 0 ≤ epsilon →
      maxEntropy epsilon rho ((lam : ℂ) • sigma) =
        maxEntropy epsilon rho sigma - ((Real.logb 2 lam : ℝ) : EReal)) := by
  have hc0 : ENNReal.ofReal lam ≠ 0 := by simpa using hlam
  refine ⟨fun epsilon _ _ => ?_, fun _ epsilon _ => ?_⟩
  · unfold endpointTestingEntropyBits
    rw [← g68m_negLog_mul lam hlam]
    congr 1
    unfold endpointTestingValue
    split_ifs
    · rw [← g68m_sInf_mul _ hc0 ENNReal.ofReal_ne_top (fun e : ℝ => 0 < e)
        (fun e => testingValue e rho sigma)]
      simp only [g68m_testing lam hlam]
    · exact g68m_testing lam hlam _ _ _
  · unfold maxEntropy
    rw [← g68m_sInf_sub]
    congr 1
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨l, bar, hl, hb, ht, hf, hle, rfl⟩
      refine ⟨((Real.logb 2 (l * lam) : ℝ) : EReal), ⟨l * lam, bar, mul_pos hl hlam, hb, ht, hf, ?_, rfl⟩, ?_⟩
      · rw [smul_smul] at hle; push_cast; exact hle
      · rw [Real.logb_mul hl.ne' hlam.ne', ← EReal.coe_sub]; congr 1; ring
    · rintro ⟨_, ⟨l, bar, hl, hb, ht, hf, hle, rfl⟩, rfl⟩
      refine ⟨l / lam, bar, div_pos hl hlam, hb, ht, hf, ?_, ?_⟩
      · rw [smul_smul]
        have : ((l / lam : ℝ) : ℂ) * (lam : ℂ) = (l : ℂ) := by
          rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hlam.ne']
        rw [this]; exact hle
      · rw [Real.logb_div hl.ne' hlam.ne', ← EReal.coe_sub]

end
