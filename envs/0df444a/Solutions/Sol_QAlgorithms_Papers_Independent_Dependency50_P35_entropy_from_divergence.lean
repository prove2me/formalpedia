-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P35.entropy_from_divergence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:08:30.715541+00:00
-- url     : https://prove2.me/submissions/d25fa9ef-cccf-4b0a-82bb-87ee664f9c9a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

section H54D
variable {I : Type} [Fintype I] [DecidableEq I]

lemma h54d_cfc_trace {Y : Matrix I I ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma h54d_co (f : ℝ → ℝ) (X : Mat I) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum).continuousOn _

lemma h54d_co' (g f : ℝ → ℝ) (X : Mat I) : ContinuousOn g (f '' spectrum ℝ X) :=
  ((Matrix.finite_real_spectrum).image f).continuousOn _

lemma h54d_tr {X : Mat I} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    tr (cfc f X) = ∑ i, f (hX.eigenvalues i) := by
  unfold tr; rw [h54d_cfc_trace hX f, Complex.re_sum]; simp

lemma h54d_tr2 {X : Mat I} (hX : X.IsHermitian) (f g : ℝ → ℝ) :
    tr (cfc f X * cfc g X) = ∑ i, f (hX.eigenvalues i) * g (hX.eigenvalues i) := by
  rw [← cfc_mul f g X (h54d_co _ _) (h54d_co _ _), h54d_tr hX]

lemma h54d_comp {X : Mat I} (hX : X.IsHermitian) (g f : ℝ → ℝ) :
    cfc g (cfc f X) = cfc (g ∘ f) X := by
  exact (cfc_comp g f X hX (h54d_co' _ _ _) (h54d_co _ _)).symm

def h54d_ind : ℝ → ℝ := fun x => if x = 0 then 0 else 1
def h54d_pw (t : ℝ) : ℝ → ℝ := fun x => if x = 0 then 0 else x ^ t

lemma h54d_sp {X : Mat I} (t : ℝ) (ht : t ≠ 0) : spectralPower X t = cfc (h54d_pw t) X := by
  unfold spectralPower h54d_pw; rw [if_neg ht]

lemma h54d_sp' {X : Mat I} (hX : X.IsHermitian) (t : ℝ) (ht : t ≠ 0) (f : ℝ → ℝ) :
    spectralPower (cfc f X) t = cfc (h54d_pw t ∘ f) X := by
  rw [h54d_sp t ht, h54d_comp hX]

lemma h54d_trace_smul (k : ℝ) (M : Mat I) : tr (((k : ℂ)) • M) = k * tr M := by
  unfold tr; rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma h54d_dom {X : Mat I} (hX : X.IsHermitian) (c : ℝ) (hc : c ≠ 0) :
    Dominates (cfc (fun x => c * h54d_ind x) X) X := by
  have h : X = cfc (fun x => x * c⁻¹) X * cfc (fun x => c * h54d_ind x) X := by
    rw [← cfc_mul _ _ X (h54d_co _ _) (h54d_co _ _)]
    conv_lhs => rw [← cfc_id' ℝ X]
    apply cfc_congr
    intro x _
    simp only [h54d_ind]; split_ifs with hx
    · simp [hx]
    · field_simp
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- the Petz quantity against c times the support projector -/
lemma h54d_petz {X : Mat I} (hX : X.PosSemidef) (htr : 0 < tr X) (a : ℝ) (ha : 0 < a)
    (c : ℝ) (hc : 0 < c) :
    petz a X (cfc (fun x => c * h54d_ind x) X) =
      (((if a = 1 then tr (X * logOp X) / tr X
        else Real.logb 2 (tr (spectralPower X a) / tr X) / (a - 1)) - Real.logb 2 c : ℝ) : EReal) := by
  have hH := hX.1
  have hX1 : X = cfc (fun x => x) X := (cfc_id' ℝ X).symm
  have htrX : tr X = ∑ i, hH.eigenvalues i :=
    calc tr X = tr (cfc (fun x => x) X) := by rw [cfc_id' ℝ X]
      _ = _ := h54d_tr hH _
  have hev : ∀ i, 0 ≤ hH.eigenvalues i := hX.eigenvalues_nonneg
  have hdom := h54d_dom hH c hc.ne'
  unfold petz
  by_cases ha1 : a = 1
  · subst ha1
    simp only [if_true]
    unfold relative
    rw [if_pos hdom]
    congr 1
    unfold logOp
    rw [← smul_sub]
    simp only [Matrix.mul_smul, h54d_trace_smul]
    rw [Matrix.mul_sub]
    have e1 : tr (X * lnOp X - X * lnOp (cfc (fun x => c * h54d_ind x) X)) =
        tr (X * lnOp X) - Real.log c * tr X := by
      unfold tr; rw [Matrix.trace_sub, Complex.sub_re]
      congr 1
      have h := h54d_tr2 hH (fun x => x) (Real.log ∘ fun x => c * h54d_ind x)
      rw [cfc_id' ℝ X] at h
      unfold lnOp
      rw [h54d_comp hH]
      have htrX' : X.trace.re = ∑ i, hH.eigenvalues i := htrX
      unfold tr at h
      rw [h, htrX', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h0 : hH.eigenvalues i = 0
      · simp [h0]
      · simp [h0, Function.comp, h54d_ind]; ring
    rw [e1]
    have : tr X ≠ 0 := htr.ne'
    rw [Real.logb]
    field_simp
  · simp only [if_neg ha1]
    have hT : tr (spectralPower X a * spectralPower (cfc (fun x => c * h54d_ind x) X) (1 - a)) =
        c ^ (1 - a) * tr (spectralPower X a) := by
      rw [h54d_sp a ha.ne', h54d_sp' hH (1 - a) (sub_ne_zero.mpr (Ne.symm ha1)), h54d_tr2 hH,
        h54d_tr hH, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [h54d_ind, h54d_pw, Function.comp]
      by_cases h0 : hH.eigenvalues i = 0
      · simp [h0]
      · have : c ≠ 0 := hc.ne'
        simp [h0, this]; ring
    have hTpos : 0 < tr (spectralPower X a) := by
      rw [h54d_sp a ha.ne', h54d_tr hH]
      have : ∃ i, hH.eigenvalues i ≠ 0 := by
        by_contra hne; push_neg at hne
        rw [htrX] at htr; simp [hne] at htr
      obtain ⟨i, hi⟩ := this
      refine Finset.sum_pos' ?_ ⟨i, Finset.mem_univ _, ?_⟩
      · intro j _; unfold h54d_pw; split_ifs
        · exact le_refl _
        · exact Real.rpow_nonneg (hev j) _
      · unfold h54d_pw; rw [if_neg hi]
        exact Real.rpow_pos_of_pos (lt_of_le_of_ne (hev i) (Ne.symm hi)) _
    have hne : X * cfc (fun x => c * h54d_ind x) X ≠ 0 := by
      intro h0
      have := h54d_tr2 hH (fun x => x) (fun x => c * h54d_ind x)
      rw [← hX1, h0] at this
      have hz : tr (0 : Mat I) = 0 := by simp [tr]
      rw [hz] at this
      have h2 : ∑ i, hH.eigenvalues i * (c * h54d_ind (hH.eigenvalues i)) = c * tr X := by
        rw [htrX, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _; unfold h54d_ind; split_ifs with h0 <;> simp [h0]; ring
      have : c * tr X = 0 := by rw [← h2]; exact this.symm
      have : 0 < c * tr X := mul_pos hc htr
      linarith
    rw [if_pos ⟨hne, Or.inl hdom⟩, hT]
    have hpos : 0 < c ^ (1 - a) * tr (spectralPower X a) / tr X := by positivity
    unfold elog
    rw [if_pos hpos, ← EReal.coe_mul]
    congr 1
    rw [mul_div_assoc, Real.logb_mul (by positivity) (by positivity),
      Real.logb_rpow_eq_mul_logb_of_pos hc]
    have : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    field_simp
    ring

lemma h54d_renyi_neg {X : Mat I} (a : ℝ) :
    renyiEntropy a X = -(if a = 1 then tr (X * logOp X) / tr X
        else Real.logb 2 (tr (spectralPower X a) / tr X) / (a - 1)) := by
  unfold renyiEntropy
  split_ifs with h
  · ring
  · have : a - 1 ≠ 0 := sub_ne_zero.mpr h
    have : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp
    ring

lemma h54d_renyi_mixed {X : Mat I} (hX : X.IsHermitian) (a : ℝ) (ha : 0 < a) (c : ℝ) (hc : 0 < c)
    (hr : 0 < ∑ i, h54d_ind (hX.eigenvalues i)) :
    renyiEntropy a (cfc (fun x => c * h54d_ind x) X) = -Real.logb 2 c := by
  set r := ∑ i, h54d_ind (hX.eigenvalues i)
  have htr : tr (cfc (fun x => c * h54d_ind x) X) = c * r := by
    rw [h54d_tr hX, Finset.mul_sum]
  unfold renyiEntropy
  split_ifs with ha1
  · unfold logOp
    rw [Matrix.mul_smul, h54d_trace_smul, htr]
    unfold lnOp
    rw [h54d_comp hX, h54d_tr2 hX]
    have : ∑ i, c * h54d_ind (hX.eigenvalues i) * (Real.log ∘ fun x => c * h54d_ind x) (hX.eigenvalues i)
        = c * Real.log c * r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; unfold h54d_ind; simp only [Function.comp]; split_ifs <;> simp
    rw [this, Real.logb]
    field_simp
  · rw [h54d_sp' hX a ha.ne', h54d_tr hX, htr]
    have : ∑ i, (h54d_pw a ∘ fun x => c * h54d_ind x) (hX.eigenvalues i) = c ^ a * r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; unfold h54d_ind h54d_pw; simp only [Function.comp]
      split_ifs <;> simp_all
    rw [this]
    have e : c ^ a * r / (c * r) = c ^ (a - 1) := by
      rw [Real.rpow_sub hc, Real.rpow_one]; field_simp
    rw [e, Real.logb_rpow_eq_mul_logb_of_pos hc]
    have : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
    field_simp
    ring

end H54D

theorem solution {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a) (rho : Mat I) (hr : Substate rho) :
    (renyiEntropy a rho : EReal) = -petz a rho (supportId rho) ∧
    (renyiEntropy a rho : EReal) = (Real.logb 2 (supportRank rho : ℝ) : EReal) -
      petz a rho (supportMixed rho) ∧
    (renyiEntropy a rho : EReal) = (renyiEntropy a (supportMixed rho) : EReal) -
      petz a rho (supportMixed rho) := by
  obtain ⟨hX, htr, _⟩ := hr
  have hH := hX.1
  have hId : supportId rho = cfc (fun x => (1:ℝ) * h54d_ind x) rho := by
    unfold supportId h54d_ind; congr 1; funext x; simp
  -- rank
  have hrank : (supportRank rho : ℝ) = ∑ i, h54d_ind (hH.eigenvalues i) := by
    have : supportRank rho = rho.rank := rfl
    rw [this, hH.rank_eq_card_non_zero_eigs]
    unfold h54d_ind
    rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add, nsmul_eq_mul, mul_one,
      Fintype.card_subtype]
  have hX1 : rho = cfc (fun x => x) rho := (cfc_id' ℝ rho).symm
  have hrpos : 0 < ∑ i, h54d_ind (hH.eigenvalues i) := by
    have : ∃ i, hH.eigenvalues i ≠ 0 := by
      by_contra hne; push_neg at hne
      have h := h54d_tr hH (fun x => x)
      rw [← hX1] at h
      rw [h] at htr; simp [hne] at htr
    obtain ⟨i, hi⟩ := this
    refine Finset.sum_pos' ?_ ⟨i, Finset.mem_univ _, ?_⟩
    · intro j _; unfold h54d_ind; split_ifs <;> norm_num
    · unfold h54d_ind; rw [if_neg hi]; norm_num
  set r := ∑ i, h54d_ind (hH.eigenvalues i) with hrdef
  have hMix : supportMixed rho = cfc (fun x => r⁻¹ * h54d_ind x) rho := by
    unfold supportMixed
    rw [hId, cfc_const_mul _ _ _ (h54d_co _ _), cfc_const_mul _ _ _ (h54d_co _ _), Complex.coe_smul,
      smul_smul, hrank, mul_one]
  have P1 := h54d_petz hX htr a ha 1 one_pos
  have Pr := h54d_petz hX htr a ha r⁻¹ (inv_pos.mpr hrpos)
  rw [← hId] at P1
  rw [← hMix] at Pr
  have R := h54d_renyi_neg (X := rho) a
  have RM := h54d_renyi_mixed hH a ha r⁻¹ (inv_pos.mpr hrpos) hrpos
  rw [← hMix] at RM
  set V := (if a = 1 then tr (rho * logOp rho) / tr rho
        else Real.logb 2 (tr (spectralPower rho a) / tr rho) / (a - 1))
  refine ⟨?_, ?_, ?_⟩
  · rw [P1, R, Real.logb_one, sub_zero, EReal.coe_neg]
  · rw [Pr, R, hrank, ← EReal.coe_sub, Real.logb_inv]
    congr 1; ring
  · rw [Pr, R, RM, ← EReal.coe_sub, Real.logb_inv]
    congr 1; ring

end
