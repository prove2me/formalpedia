-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P44.measured_entropy_second_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:32:46.492424+00:00
-- url     : https://prove2.me/submissions/b74c9d2a-4911-411d-82bd-f0068060fc05

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

open QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix InnerProductSpace

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace P44Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} (b : HilbertBasis I ℂ H)

omit [CompleteSpace H] in
lemma parseval (x : H) : HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply] at h
  simpa [LinearIsometryEquiv.norm_map] using h

lemma parseval_enn (x : H) :
    ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (parseval b x).summable,
    (parseval b x).tsum_eq]

/-- Cauchy–Schwarz for basis coefficients. -/
lemma cs_enn (u v : H) :
    ∑' i, ENNReal.ofReal (‖⟪b i, v⟫_ℂ‖ * ‖⟪b i, u⟫_ℂ‖) ≤ ENNReal.ofReal (‖u‖ * ‖v‖) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set c : ℝ := ‖u‖ / ‖v‖ with hc
  have hc0 : 0 < c := div_pos hu' hv'
  have key : ∀ i, ENNReal.ofReal (‖⟪b i, v⟫_ℂ‖ * ‖⟪b i, u⟫_ℂ‖) ≤
      ENNReal.ofReal (c / 2) * ENNReal.ofReal (‖⟪b i, v⟫_ℂ‖ ^ 2) +
        ENNReal.ofReal (1 / (2 * c)) * ENNReal.ofReal (‖⟪b i, u⟫_ℂ‖ ^ 2) := by
    intro i
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set a := ‖⟪b i, v⟫_ℂ‖
    set d := ‖⟪b i, u⟫_ℂ‖
    have : 0 ≤ (c * a - d) ^ 2 := sq_nonneg _
    have h2 : c / 2 * a ^ 2 + 1 / (2 * c) * d ^ 2 - a * d = (c * a - d) ^ 2 / (2 * c) := by
      field_simp; ring
    have : 0 ≤ (c * a - d) ^ 2 / (2 * c) := by positivity
    linarith
  calc _ ≤ ∑' i, (ENNReal.ofReal (c / 2) * ENNReal.ofReal (‖⟪b i, v⟫_ℂ‖ ^ 2) +
        ENNReal.ofReal (1 / (2 * c)) * ENNReal.ofReal (‖⟪b i, u⟫_ℂ‖ ^ 2)) :=
          ENNReal.tsum_le_tsum key
    _ = ENNReal.ofReal (c / 2) * ENNReal.ofReal (‖v‖ ^ 2) +
        ENNReal.ofReal (1 / (2 * c)) * ENNReal.ofReal (‖u‖ ^ 2) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
            parseval_enn, parseval_enn]
    _ = ENNReal.ofReal (‖u‖ * ‖v‖) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hc]; field_simp; ring

omit [CompleteSpace H] in
lemma summable_of_ofReal {J : Type*} {f : J → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : ∑' i, ENNReal.ofReal (f i) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal h
  simpa [ENNReal.toReal_ofReal (hf _)] using this

lemma nuclear_summable {σ : H →L[ℂ] H} {u v : ℕ → H}
    (hn : QAlgorithms.Papers.Independent.Dependency50.P13.NuclearRepresentation σ u v) (x : H) :
    Summable (fun r => ⟪v r, x⟫_ℂ • u r) := by
  refine Summable.of_norm_bounded (g := fun r => ‖x‖ * (‖u r‖ * ‖v r‖))
    (hn.1.mul_left _) (fun r => ?_)
  rw [norm_smul]
  calc ‖⟪v r, x⟫_ℂ‖ * ‖u r‖ ≤ (‖v r‖ * ‖x‖) * ‖u r‖ := by
        gcongr; exact norm_inner_le_norm _ _
    _ = _ := by ring

lemma diag_enn_lt_top {σ : H →L[ℂ] H} (hσ : IsTraceClass σ) :
    ∑' i, ENNReal.ofReal ‖⟪b i, σ (b i)⟫_ℂ‖ ≠ ⊤ := by
  obtain ⟨u, v, hn⟩ := hσ
  have h1 : ∀ i, ⟪b i, σ (b i)⟫_ℂ = ∑' r, ⟪v r, b i⟫_ℂ * ⟪b i, u r⟫_ℂ := by
    intro i
    rw [hn.2 (b i)]
    have := (innerSL ℂ (b i)).map_tsum (nuclear_summable hn (b i))
    simpa [inner_smul_right] using this
  have hrow : ∀ i, Summable (fun r => ‖⟪v r, b i⟫_ℂ * ⟪b i, u r⟫_ℂ‖) := by
    intro i
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => ?_)
      (hn.1)
    rw [norm_mul]
    calc ‖⟪v r, b i⟫_ℂ‖ * ‖⟪b i, u r⟫_ℂ‖ ≤ (‖v r‖ * ‖b i‖) * (‖b i‖ * ‖u r‖) := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ = ‖u r‖ * ‖v r‖ := by simp [b.orthonormal.1 i]; ring
  have h2 : ∀ i, ENNReal.ofReal ‖⟪b i, σ (b i)⟫_ℂ‖ ≤
      ∑' r, ENNReal.ofReal (‖⟪b i, v r⟫_ℂ‖ * ‖⟪b i, u r⟫_ℂ‖) := by
    intro i
    rw [h1 i]
    calc ENNReal.ofReal ‖∑' r, ⟪v r, b i⟫_ℂ * ⟪b i, u r⟫_ℂ‖
        ≤ ENNReal.ofReal (∑' r, ‖⟪v r, b i⟫_ℂ * ⟪b i, u r⟫_ℂ‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm (hrow i))
      _ = ∑' r, ENNReal.ofReal (‖⟪v r, b i⟫_ℂ * ⟪b i, u r⟫_ℂ‖) :=
          ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hrow i)
      _ = _ := by
          congr 1; funext r; rw [norm_mul, norm_inner_symm]
  have h3 : ∑' r, ENNReal.ofReal (‖u r‖ * ‖v r‖) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hn.1]
    exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top h3 ?_
  calc _ ≤ ∑' i, ∑' r, ENNReal.ofReal (‖⟪b i, v r⟫_ℂ‖ * ‖⟪b i, u r⟫_ℂ‖) :=
        ENNReal.tsum_le_tsum h2
    _ = ∑' r, ∑' i, ENNReal.ofReal (‖⟪b i, v r⟫_ℂ‖ * ‖⟪b i, u r⟫_ℂ‖) := ENNReal.tsum_comm
    _ ≤ _ := ENNReal.tsum_le_tsum (fun r => cs_enn b (u r) (v r))

lemma diag_summable {σ : H →L[ℂ] H} (hσ : IsTraceClass σ) :
    Summable (fun i => ‖⟪b i, σ (b i)⟫_ℂ‖) :=
  summable_of_ofReal (fun _ => norm_nonneg _) (diag_enn_lt_top b hσ)

lemma hs_prod (C : H →L[ℂ] H) (hC : Summable fun j => ‖C (b j)‖ ^ 2) :
    Summable (fun p : I × I => ‖⟪b p.1, C (b p.2)⟫_ℂ‖ ^ 2) := by
  refine summable_of_ofReal (fun _ => by positivity) ?_
  rw [ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (‖⟪b i, C (b j)⟫_ℂ‖ ^ 2)),
    ENNReal.tsum_comm]
  simp_rw [parseval_enn]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hC]
  exact ENNReal.ofReal_ne_top

lemma hs_adjoint (A : H →L[ℂ] H) (hA : Summable fun j => ‖A (b j)‖ ^ 2) :
    Summable fun i => ‖(ContinuousLinearMap.adjoint A) (b i)‖ ^ 2 := by
  refine summable_of_ofReal (fun _ => by positivity) ?_
  have e : ∀ i, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint A) (b i)‖ ^ 2) =
      ∑' j, ENNReal.ofReal (‖⟪b i, A (b j)⟫_ℂ‖ ^ 2) := by
    intro i
    rw [← parseval_enn b ((ContinuousLinearMap.adjoint A) (b i))]
    refine tsum_congr (fun j => ?_)
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  simp_rw [e]
  rw [ENNReal.tsum_comm]
  simp_rw [parseval_enn]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hA]
  exact ENNReal.ofReal_ne_top

lemma hs_swap (A B : H →L[ℂ] H) (hA : Summable fun j => ‖A (b j)‖ ^ 2)
    (hB : Summable fun j => ‖B (b j)‖ ^ 2) :
    ∑' i, ⟪A (b i), B (b i)⟫_ℂ =
      ∑' j, ⟪(ContinuousLinearMap.adjoint B) (b j), (ContinuousLinearMap.adjoint A) (b j)⟫_ℂ := by
  set A' := ContinuousLinearMap.adjoint A
  set B' := ContinuousLinearMap.adjoint B
  let F : I → I → ℂ := fun i j => ⟪B' (b j), b i⟫_ℂ * ⟪b i, A' (b j)⟫_ℂ
  have h1 : ∀ i, ⟪A (b i), B (b i)⟫_ℂ = ∑' j, F i j := by
    intro i
    rw [← b.tsum_inner_mul_inner]
    congr 1; funext j
    simp only [F, A', B', ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
    ring
  have h2 : ∀ j, ∑' i, F i j = ⟪B' (b j), A' (b j)⟫_ℂ := fun j => b.tsum_inner_mul_inner _ _
  have hsum : Summable (Function.uncurry F) := by
    have sA := hs_prod b A' (hs_adjoint b A hA)
    have sB := hs_prod b B' (hs_adjoint b B hB)
    refine Summable.of_norm_bounded ((sA.add sB).div_const 2) (fun p => ?_)
    simp only [Function.uncurry, F, norm_mul]
    rw [norm_inner_symm (B' (b p.2))]
    have := two_mul_le_add_sq ‖⟪b p.1, B' (b p.2)⟫_ℂ‖ ‖⟪b p.1, A' (b p.2)⟫_ℂ‖
    linarith
  simp_rw [h1, ← h2]
  exact (hsum.tsum_comm).symm

lemma trace_comp_pos (M σ : H →L[ℂ] H) (hM : M.IsPositive) (hσ : IsTraceClass σ)
    (hσp : σ.IsPositive) :
    Summable (fun i => ⟪b i, M (σ (b i))⟫_ℂ) ∧ 0 ≤ (∑' i, ⟪b i, M (σ (b i))⟫_ℂ).re := by
  have h0 : 0 ≤ σ := (ContinuousLinearMap.nonneg_iff_isPositive σ).mpr hσp
  set S := CFC.sqrt σ with hSdef
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ h0
  have hSadj : ContinuousLinearMap.adjoint S = S := (CFC.sqrt_nonneg σ).isSelfAdjoint.adjoint_eq
  have hMadj : ContinuousLinearMap.adjoint M = M := hM.isSelfAdjoint.adjoint_eq
  have hSsym : ∀ x y, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ := by
    intro x y; rw [← ContinuousLinearMap.adjoint_inner_right, hSadj]
  have hMsym : ∀ x y, ⟪M x, y⟫_ℂ = ⟪x, M y⟫_ℂ := by
    intro x y; rw [← ContinuousLinearMap.adjoint_inner_right, hMadj]
  have hSSx : ∀ x, S (S x) = σ x := by
    intro x; rw [← hSS]; rfl
  have hnormS : ∀ x, ‖S x‖ ^ 2 ≤ ‖⟪x, σ x⟫_ℂ‖ := by
    intro x
    have : (⟪S x, S x⟫_ℂ).re = ‖S x‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (S x))
    rw [← this, hSsym, hSSx]
    exact Complex.re_le_norm _
  have hSHS : Summable fun j => ‖S (b j)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => hnormS (b j)) (diag_summable b hσ)
  have hMSHS : Summable fun j => ‖(M.comp S) (b j)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) (hSHS.mul_left (‖M‖ ^ 2))
    simp only [ContinuousLinearMap.comp_apply]
    rw [← mul_pow]
    gcongr
    exact M.le_opNorm _
  have hadjMS : ContinuousLinearMap.adjoint (M.comp S) = S.comp M := by
    rw [ContinuousLinearMap.adjoint_comp, hSadj, hMadj]
  have hSMHS : Summable fun j => ‖(S.comp M) (b j)‖ ^ 2 := by
    have := hs_adjoint b (M.comp S) hMSHS
    rwa [hadjMS] at this
  have hterm : ∀ i, ⟪b i, M (σ (b i))⟫_ℂ = ⟪(S.comp M) (b i), S (b i)⟫_ℂ := by
    intro i
    simp only [ContinuousLinearMap.comp_apply]
    rw [hSsym, hSSx, hMsym]
  have hsum : Summable (fun i => ⟪b i, M (σ (b i))⟫_ℂ) := by
    simp_rw [hterm]
    refine Summable.of_norm_bounded ((hSMHS.add hSHS).div_const 2) (fun i => ?_)
    have h1 := norm_inner_le_norm (𝕜 := ℂ) ((S.comp M) (b i)) (S (b i))
    have h2 := two_mul_le_add_sq ‖(S.comp M) (b i)‖ ‖S (b i)‖
    linarith
  refine ⟨hsum, ?_⟩
  simp_rw [hterm]
  rw [hs_swap b (S.comp M) S hSMHS hSHS, hSadj, ContinuousLinearMap.adjoint_comp, hSadj, hMadj]
  by_cases hs : Summable (fun j => ⟪S (b j), (M.comp S) (b j)⟫_ℂ)
  · rw [Complex.re_tsum hs]
    refine tsum_nonneg (fun j => ?_)
    have := hM.re_inner_nonneg_right (S (b j))
    simpa using this
  · rw [tsum_eq_zero_of_not_summable hs]; simp

lemma kl_convex {n : ℕ} (P Q1 Q2 : Fin n → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ1 : ∀ i, 0 ≤ Q1 i)
    (hQ2 : ∀ i, 0 ≤ Q2 i) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    classicalKL P (fun i => p * Q1 i + (1 - p) * Q2 i) ≤
      ENNReal.ofReal p * classicalKL P Q1 + ENNReal.ofReal (1 - p) * classicalKL P Q2 := by
  rcases hp0.eq_or_lt with rfl | hp0'
  · simp
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp
  have hpe : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0').ne'
  have hqe : ENNReal.ofReal (1 - p) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  unfold classicalKL
  by_cases h1 : ∃ x, 0 < P x ∧ Q1 x = 0
  · rw [if_pos h1, ENNReal.mul_top hpe, top_add]; exact le_top
  by_cases h2 : ∃ x, 0 < P x ∧ Q2 x = 0
  · rw [if_pos h2, ENNReal.mul_top hqe, add_top]; exact le_top
  push Not at h1 h2
  have hpos1 : ∀ x, 0 < P x → 0 < Q1 x := fun x hx => lt_of_le_of_ne (hQ1 x) (h1 x hx).symm
  have hpos2 : ∀ x, 0 < P x → 0 < Q2 x := fun x hx => lt_of_le_of_ne (hQ2 x) (h2 x hx).symm
  have h3 : ¬ ∃ x, 0 < P x ∧ p * Q1 x + (1 - p) * Q2 x = 0 := by
    rintro ⟨x, hx, hx0⟩
    have a1 := hpos1 x hx
    have a2 := hpos2 x hx
    have : 0 < p * Q1 x := mul_pos hp0' a1
    have : 0 ≤ (1 - p) * Q2 x := mul_nonneg (by linarith) a2.le
    linarith
  rw [if_neg h3, if_neg (by push Not; exact h1), if_neg (by push Not; exact h2),
    ← ENNReal.ofReal_mul hp0'.le, ← ENNReal.ofReal_mul (by linarith)]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun x _ => ?_)
  by_cases hx : P x = 0
  · simp [hx]
  have hPx : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
  have q1 := hpos1 x hPx
  have q2 := hpos2 x hPx
  have hm : 0 < p * Q1 x + (1 - p) * Q2 x := by
    have : 0 < p * Q1 x := mul_pos hp0' q1
    have : 0 ≤ (1 - p) * Q2 x := mul_nonneg (by linarith) q2.le
    linarith
  simp only [hx, if_false]
  have key : p * Real.log (Q1 x) + (1 - p) * Real.log (Q2 x) ≤
      Real.log (p * Q1 x + (1 - p) * Q2 x) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr q1) (Set.mem_Ioi.mpr q2)
      hp0'.le (by linarith : (0:ℝ) ≤ 1 - p) (by ring)
    simpa [smul_eq_mul] using this
  have hL : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  simp only [Real.logb, div_eq_mul_inv]
  rw [Real.log_mul hPx.ne' (inv_pos.mpr hm).ne', Real.log_mul hPx.ne' (inv_pos.mpr q1).ne',
    Real.log_mul hPx.ne' (inv_pos.mpr q2).ne', Real.log_inv, Real.log_inv, Real.log_inv]
  have := mul_nonneg (mul_nonneg hL.le hPx.le) (sub_nonneg.mpr key)
  nlinarith

end P44Aux

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (rho sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hsigma : IsHilbertDensity b sigma)
    (hsigma2 : IsHilbertDensity b sigma2) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    measuredRelativeEntropy b rho (hilbertMix p sigma sigma2) ≤
      ENNReal.ofReal p * measuredRelativeEntropy b rho sigma +
        ENNReal.ofReal (1-p) * measuredRelativeEntropy b rho sigma2 := by
  unfold measuredRelativeEntropy
  refine iSup_le (fun n => iSup_le (fun M => ?_))
  have hMpos := M.2.1
  have tr_eq : ∀ (T : H →L[ℂ] H) i,
      hilbertTrace b ((M.val i).comp T) = ∑' j, ⟪b j, (M.val i) (T (b j))⟫_ℂ := fun _ _ => rfl
  have nn : ∀ (T : H →L[ℂ] H), IsHilbertDensity b T → ∀ i,
      0 ≤ (hilbertTrace b ((M.val i).comp T)).re := by
    intro T hT i
    rw [tr_eq]
    exact (P44Aux.trace_comp_pos b (M.val i) T (hMpos i) hT.1 hT.2.1).2
  have mix : ∀ i, (hilbertTrace b ((M.val i).comp (hilbertMix p sigma sigma2))).re =
      p * (hilbertTrace b ((M.val i).comp sigma)).re +
        (1 - p) * (hilbertTrace b ((M.val i).comp sigma2)).re := by
    intro i
    have s1 := (P44Aux.trace_comp_pos b (M.val i) sigma (hMpos i) hsigma.1 hsigma.2.1).1
    have s2 := (P44Aux.trace_comp_pos b (M.val i) sigma2 (hMpos i) hsigma2.1 hsigma2.2.1).1
    rw [tr_eq, tr_eq, tr_eq]
    simp only [hilbertMix, add_apply, smul_apply,
      map_add, map_smul, inner_add_right, inner_smul_right]
    rw [(s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left]
    simp [Complex.add_re]
  have hfun : (fun i => (hilbertTrace b ((M.val i).comp (hilbertMix p sigma sigma2))).re) =
      (fun i => p * (hilbertTrace b ((M.val i).comp sigma)).re +
        (1 - p) * (hilbertTrace b ((M.val i).comp sigma2)).re) := funext mix
  rw [hfun]
  refine le_trans (P44Aux.kl_convex _ _ _ (nn rho hrho) (nn sigma hsigma) (nn sigma2 hsigma2)
    p hp0 hp1) ?_
  gcongr
  · exact le_iSup_of_le n (le_iSup_of_le M le_rfl)
  · exact le_iSup_of_le n (le_iSup_of_le M le_rfl)

end
