-- Prove2me | solution 1 for TractableDRO.MeanCov.theorem_2_upper
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T09:16:47.277355+00:00
-- url     : https://prove2.me/submissions/e24e242a-deae-4f6e-8db7-913c99218a31

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

open Matrix MeasureTheory ProbabilityTheory TractableDRO.MeanSupport
set_option maxHeartbeats 40000

private theorem int_dot {n : ℕ} (P : Measure (Fin n → ℝ)) (s : Fin n → ℝ)
    (hi : ∀ i, Integrable (fun z : Fin n → ℝ => z i) P) :
    (∫ z, s ⬝ᵥ z ∂P) = s ⬝ᵥ MomentDRO.Conf.meanVec P := by
  simp only [dotProduct, MomentDRO.Conf.meanVec]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_const_mul _ _
  · intro i _
    exact (hi i).const_mul _

private theorem scalar_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) :
    (∫ z, max (X z) 0 ∂P) ≤
      ((∫ z, X z ∂P) + Real.sqrt (∫ z, (X z)^2 ∂P)) / 2 := by
  have hi := hX.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have ha : MemLp (fun z => |X z|) 2 P := by simpa only [Real.norm_eq_abs] using hX.norm
  have hvar := variance_nonneg (fun z => |X z|) P
  rw [variance_eq_sub ha] at hvar
  simp only [Pi.pow_apply] at hvar
  have he : (∫ z, |X z| ^ 2 ∂P) = ∫ z, X z ^ 2 ∂P := by
    simp only [sq_abs]
  rw [he] at hvar
  have habs : (∫ z, |X z| ∂P) ≤ Real.sqrt (∫ z, X z ^ 2 ∂P) := by
    apply (Real.le_sqrt (integral_nonneg (fun z => abs_nonneg _))
      (integral_nonneg (fun z => sq_nonneg _))).2
    linarith
  have hp : (∫ z, max (X z) 0 ∂P) =
      ((∫ z, X z ∂P) + ∫ z, |X z| ∂P) / 2 := by
    have hf : (fun z => max (X z) 0) = fun z => (X z + |X z|) / 2 := by
      funext z
      rcases le_total (X z) 0 with h | h
      · rw [max_eq_right h, abs_of_nonpos h]; ring
      · rw [max_eq_left h, abs_of_nonneg h]; ring
    rw [hf, integral_div, integral_add hi hi.abs]
  rw [hp]
  linarith

private theorem affine_second {n : ℕ} (P : Measure (Fin n → ℝ))
    [IsProbabilityMeasure P] (hlp : ∀ i, MemLp (fun z : Fin n → ℝ => z i) 2 P)
    (r0 : ℝ) (r : Fin n → ℝ) :
    (∫ z, (r0 + r ⬝ᵥ z)^2 ∂P) =
      (r0 + r ⬝ᵥ MomentDRO.Conf.meanVec P)^2 +
        r ⬝ᵥ MomentDRO.Conf.covMat P *ᵥ r := by
  classical
  let m := MomentDRO.Conf.meanVec P
  let Z : (Fin n → ℝ) → Fin n → ℝ := fun z i => z i - m i
  have hZ (i : Fin n) : MemLp (fun z => Z z i) 2 P :=
    (hlp i).sub (memLp_const _)
  have hi (i : Fin n) : Integrable (fun z : Fin n → ℝ => z i) P :=
    (hlp i).integrable (by norm_num)
  have hz (i : Fin n) : (∫ z, Z z i ∂P) = 0 := by
    dsimp [Z, m, MomentDRO.Conf.meanVec]
    rw [integral_sub (hi i) (integrable_const _)]
    simp
  have hd : MemLp (fun z => r ⬝ᵥ Z z) 2 P :=
    memLp_finsetSum _ (fun i _ => (hZ i).const_mul _)
  have hid := hd.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hd0 : (∫ z, r ⬝ᵥ Z z ∂P) = 0 := by
    simp only [dotProduct]
    rw [integral_finsetSum _ (fun i _ => ((hZ i).integrable (by norm_num)).const_mul _)]
    simp only [integral_const_mul, hz, mul_zero, Finset.sum_const_zero]
  have hdsq : (∫ z, (r ⬝ᵥ Z z)^2 ∂P) =
      r ⬝ᵥ MomentDRO.Conf.covMat P *ᵥ r := by
    have hex (z : Fin n → ℝ) :
        (r ⬝ᵥ Z z)^2 = ∑ i, ∑ j, (r i * r j) * (Z z i * Z z j) := by
      simp only [dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hex]
    rw [integral_finsetSum]
    · simp only [dotProduct, Matrix.mulVec, MomentDRO.Conf.covMat,
        MomentDRO.Conf.secondMomentAbout, Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [Z, m]
        ring
      · intro j _
        exact ((hZ i).integrable_mul (hZ j)).const_mul (r i * r j)
    · intro i _
      exact integrable_finsetSum _ (fun j _ =>
        ((hZ i).integrable_mul (hZ j)).const_mul _)
  have he (z : Fin n → ℝ) :
      (r0 + r ⬝ᵥ z)^2 = (r0 + r ⬝ᵥ m)^2 +
        (2 * (r0 + r ⬝ᵥ m)) * (r ⬝ᵥ Z z) + (r ⬝ᵥ Z z)^2 := by
    have hh : r ⬝ᵥ Z z = r ⬝ᵥ z - r ⬝ᵥ m := by
      exact dotProduct_sub r z m
    rw [hh]
    ring
  have hefun : (fun z => (r0 + r ⬝ᵥ z)^2) = fun z =>
      (r0 + r ⬝ᵥ m)^2 + (2 * (r0 + r ⬝ᵥ m)) * (r ⬝ᵥ Z z) +
        (r ⬝ᵥ Z z)^2 := by funext z; exact he z
  rw [hefun]
  rw [integral_add]
  · rw [integral_add]
    · rw [integral_const_mul, hd0, hdsq]
      simp [m]
    · exact integrable_const _
    · exact hid.const_mul _
  · exact (integrable_const _).add (hid.const_mul _)
  · exact hd.integrable_sq

theorem solution {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ)
    (Sig : Matrix (Fin N) (Fin N) ℝ) (Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) :
    worstCase (TractableDRO.MeanCov.family2 F Sig Vhat) r0 r ≤
      TractableDRO.MeanCov.pi2 F Sig Vhat r0 r := by
  classical
  unfold worstCase TractableDRO.MeanCov.pi2
  apply iSup_le
  intro P
  apply iSup_le
  rintro ⟨⟨hprob, hlp⟩, hmean, hcov⟩
  letI := hprob
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  have hX : MemLp (fun z => r0 + r ⬝ᵥ z) 2 P :=
    (memLp_const r0).add (memLp_finsetSum _ (fun i _ => (hlp i).const_mul _))
  have hb := scalar_bound P (fun z => r0 + r ⬝ᵥ z) hX
  have hi (i : Fin n) := (hlp i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hd : Integrable (fun z => r ⬝ᵥ z) P :=
    integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  rw [integral_add (integrable_const _) hd, int_dot P r hi,
    affine_second P hlp r0 r] at hb
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
  have hc : r ⬝ᵥ MomentDRO.Conf.covMat P *ᵥ r = y ⬝ᵥ Sig *ᵥ y := by
    rw [← hcov]
    change Fᵀ *ᵥ y = r at hy
    rw [← hy]
    simp only [← Matrix.mulVec_mulVec]
    rw [dotProduct_mulVec y F]
    rw [Matrix.mulVec_transpose]
  rw [hc] at hb
  apply le_iSup_of_le (MomentDRO.Conf.meanVec P)
  apply le_iSup_of_le hmean
  rw [EReal.coe_le_coe_iff]
  dsimp [expPos]
  linarith

#print axioms solution
