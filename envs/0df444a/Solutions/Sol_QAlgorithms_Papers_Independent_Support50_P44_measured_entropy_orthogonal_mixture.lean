-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P44.measured_entropy_orthogonal_mixture
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:49:45.659811+00:00
-- url     : https://prove2.me/submissions/fe0939c3-f5aa-44c8-a441-a1a644c11d1e

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
    Summable (fun i => ⟪b i, M (σ (b i))⟫_ℂ) ∧
    ∑' i, ⟪b i, M (σ (b i))⟫_ℂ = ∑' j, ⟪CFC.sqrt σ (b j), M (CFC.sqrt σ (b j))⟫_ℂ ∧
    0 ≤ (∑' i, ⟪b i, M (σ (b i))⟫_ℂ).re := by
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
  have heq : ∑' i, ⟪b i, M (σ (b i))⟫_ℂ = ∑' j, ⟪S (b j), M (S (b j))⟫_ℂ := by
    simp_rw [hterm]
    rw [hs_swap b (S.comp M) S hSMHS hSHS, hSadj, ContinuousLinearMap.adjoint_comp, hSadj, hMadj]
    rfl
  refine ⟨hsum, heq, ?_⟩
  rw [heq]
  by_cases hs : Summable (fun j => ⟪S (b j), M (S (b j))⟫_ℂ)
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

namespace P44Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} (b : HilbertBasis I ℂ H)

omit [CompleteSpace H] in
lemma trace_eq (K T : H →L[ℂ] H) :
    hilbertTrace b (K.comp T) = ∑' j, ⟪b j, K (T (b j))⟫_ℂ := rfl

lemma trace_mix_re (K X Y : H →L[ℂ] H) (hK : K.IsPositive) (hX : IsHilbertDensity b X)
    (hY : IsHilbertDensity b Y) (p : ℝ) :
    (hilbertTrace b (K.comp (hilbertMix p X Y))).re =
      p * (hilbertTrace b (K.comp X)).re + (1 - p) * (hilbertTrace b (K.comp Y)).re := by
  have s1 := (trace_comp_pos b K X hK hX.1 hX.2.1).1
  have s2 := (trace_comp_pos b K Y hK hY.1 hY.2.1).1
  rw [trace_eq, trace_eq, trace_eq]
  simp only [hilbertMix, add_apply, smul_apply,
    map_add, map_smul, inner_add_right, inner_smul_right]
  rw [(s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left]
  simp [Complex.add_re]

lemma trace_nonneg (K X : H →L[ℂ] H) (hK : K.IsPositive) (hX : IsHilbertDensity b X) :
    0 ≤ (hilbertTrace b (K.comp X)).re :=
  (trace_comp_pos b K X hK hX.1 hX.2.1).2.2

lemma povm_trace_sum {n : ℕ} (M : Fin n → H →L[ℂ] H) (hM : IsHilbertPOVM M)
    (X : H →L[ℂ] H) (hX : IsHilbertDensity b X) :
    ∑ k, (hilbertTrace b ((M k).comp X)).re = 1 := by
  have hs : ∀ k, Summable (fun j => ⟪b j, M k (X (b j))⟫_ℂ) :=
    fun k => (trace_comp_pos b (M k) X (hM.1 k) hX.1 hX.2.1).1
  have h1 : ∑ k, hilbertTrace b ((M k).comp X) = hilbertTrace b X := by
    simp only [trace_eq]
    rw [← Summable.tsum_finsetSum (fun k _ => hs k)]
    unfold hilbertTrace
    congr 1; funext j
    rw [← inner_sum]
    congr 1
    have := congrArg (fun T : H →L[ℂ] H => T (X (b j))) hM.2
    simpa using this
  rw [← Complex.re_sum, h1, hX.2.2]; simp

lemma block_projection (ρ ρ2 σ σ2 : H →L[ℂ] H) (hρ : ρ.IsPositive) (hρ2 : ρ2.IsPositive)
    (hσ : σ.IsPositive) (hσ2 : σ2.IsPositive) (horth : OrthogonalBlocks ρ ρ2 σ σ2) :
    ∃ P : H →L[ℂ] H, ContinuousLinearMap.adjoint P = P ∧ P * P = P ∧
      P.comp ρ = ρ ∧ P.comp σ = σ ∧ P.comp ρ2 = 0 ∧ P.comp σ2 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := horth
  have adj0 : ∀ A B : H →L[ℂ] H, A.IsPositive → B.IsPositive → A.comp B = 0 →
      ∀ x, B (A x) = 0 := by
    intro A B hA hB h x
    have := congrArg ContinuousLinearMap.adjoint h
    rw [ContinuousLinearMap.adjoint_comp, hA.isSelfAdjoint.adjoint_eq,
      hB.isSelfAdjoint.adjoint_eq, map_zero] at this
    simpa using congrArg (fun T : H →L[ℂ] H => T x) this
  let K : Submodule ℂ H := LinearMap.ker (ρ2 : H →ₗ[ℂ] H) ⊓ LinearMap.ker (σ2 : H →ₗ[ℂ] H)
  have hKc : IsClosed (K : Set H) := (ρ2.isClosed_ker).inter (σ2.isClosed_ker)
  have : CompleteSpace K := hKc.completeSpace_coe
  have memK : ∀ x, x ∈ K ↔ ρ2 x = 0 ∧ σ2 x = 0 := by
    intro x; simp [K, Submodule.mem_inf]
  have orthK : ∀ (T : H →L[ℂ] H), T.IsPositive → (∀ u ∈ K, T u = 0) → ∀ x, T x ∈ Kᗮ := by
    intro T hT hTK x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← hT.inner_left_eq_inner_right, hTK u hu, inner_zero_left]
  refine ⟨K.starProjection, (isSelfAdjoint_starProjection K).adjoint_eq,
    K.isIdempotentElem_starProjection, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [Submodule.starProjection_eq_self_iff, memK]
    exact ⟨adj0 _ _ hρ hρ2 h1 x, adj0 _ _ hρ hσ2 h2 x⟩
  · ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [Submodule.starProjection_eq_self_iff, memK]
    exact ⟨adj0 _ _ hσ hρ2 h3 x, adj0 _ _ hσ hσ2 h4 x⟩
  · ext x
    simp only [ContinuousLinearMap.comp_apply, zero_apply]
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact orthK ρ2 hρ2 (fun u hu => ((memK u).1 hu).1) x
  · ext x
    simp only [ContinuousLinearMap.comp_apply, zero_apply]
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact orthK σ2 hσ2 (fun u hu => ((memK u).1 hu).2) x

lemma qmq_pos (Q M : H →L[ℂ] H) (hQ : ContinuousLinearMap.adjoint Q = Q)
    (hM : M.IsPositive) : (Q * M * Q).IsPositive := by
  have := hM.conj_adjoint Q
  rw [hQ] at this
  exact this

lemma sqrt_comp_eq (σ Q : H →L[ℂ] H) (hσp : σ.IsPositive) (hQ : ContinuousLinearMap.adjoint Q = Q)
    (c : ℝ) (h : Q.comp σ = (c : ℂ) • σ) :
    Q.comp (CFC.sqrt σ) = (c : ℂ) • CFC.sqrt σ := by
  have h0 : 0 ≤ σ := (ContinuousLinearMap.nonneg_iff_isPositive σ).mpr hσp
  set S := CFC.sqrt σ
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ h0
  have hSadj : ContinuousLinearMap.adjoint S = S :=
    (CFC.sqrt_nonneg σ).isSelfAdjoint.adjoint_eq
  have hσadj : ContinuousLinearMap.adjoint σ = σ := hσp.isSelfAdjoint.adjoint_eq
  have hadj : ∀ T : H →L[ℂ] H, ContinuousLinearMap.adjoint ((c : ℂ) • T) =
      (c : ℂ) • ContinuousLinearMap.adjoint T := by
    intro T
    rw [map_smulₛₗ]; simp
  have hσQ : ∀ x, σ (Q x) = (c : ℂ) • σ x := by
    have := congrArg ContinuousLinearMap.adjoint h
    rw [ContinuousLinearMap.adjoint_comp, hσadj, hQ, hadj, hσadj] at this
    intro x
    simpa using congrArg (fun T : H →L[ℂ] H => T x) this
  have hSQ : ∀ x, S (Q x) = (c : ℂ) • S x := by
    intro x
    set y := Q x - (c : ℂ) • x
    have e : (⟪S y, S y⟫_ℂ).re = ‖S y‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (S y))
    have e2 : ⟪S y, S y⟫_ℂ = ⟪y, σ y⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hSadj, ← hSS]; rfl
    have e3 : σ y = 0 := by
      simp only [y, map_sub, map_smul, hσQ, sub_self]
    rw [e2, e3, inner_zero_right] at e
    have : ‖S y‖ ^ 2 = 0 := by simpa using e.symm
    have hy : S y = 0 := by simpa using this
    simp only [y, map_sub, map_smul] at hy
    exact sub_eq_zero.mp hy
  have hcomp : S.comp Q = (c : ℂ) • S := by
    ext x; simp [hSQ]
  have := congrArg ContinuousLinearMap.adjoint hcomp
  rw [ContinuousLinearMap.adjoint_comp, hSadj, hQ, hadj, hSadj] at this
  exact this

lemma proj_trace (Q M X : H →L[ℂ] H) (hQ : ContinuousLinearMap.adjoint Q = Q)
    (hM : M.IsPositive) (hX : IsHilbertDensity b X) (c : ℝ) (hc : c = 0 ∨ c = 1)
    (hQX : Q.comp X = (c : ℂ) • X) :
    hilbertTrace b ((Q * M * Q).comp X) = (c : ℂ) * hilbertTrace b (M.comp X) := by
  have hpos := qmq_pos Q M hQ hM
  rw [trace_eq, (trace_comp_pos b _ X hpos hX.1 hX.2.1).2.1, trace_eq,
    (trace_comp_pos b M X hM hX.1 hX.2.1).2.1, ← tsum_mul_left]
  have hQS := sqrt_comp_eq X Q hX.2.1 hQ c hQX
  refine tsum_congr (fun j => ?_)
  have e : Q (CFC.sqrt X (b j)) = (c : ℂ) • CFC.sqrt X (b j) := by
    have := congrArg (fun T : H →L[ℂ] H => T (b j)) hQS
    simpa using this
  have hQs : ∀ x y, ⟪x, Q y⟫_ℂ = ⟪Q x, y⟫_ℂ := by
    intro x y
    have := ContinuousLinearMap.adjoint_inner_right Q x y
    rwa [hQ] at this
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, e, hQs, e]
  rcases hc with rfl | rfl <;> simp

end P44Aux

namespace P44Aux

def klTerm (a c : ℝ) : ℝ := if a = 0 then 0 else a * Real.logb 2 (a / c)

lemma kl_unfold {n : ℕ} (a c : Fin n → ℝ) :
    classicalKL a c = if ∃ x, 0 < a x ∧ c x = 0 then ⊤
      else ENNReal.ofReal (∑ x, klTerm (a x) (c x)) := by
  unfold classicalKL klTerm
  congr

lemma klTerm_scale (t a c : ℝ) (ht : 0 < t) : klTerm (t * a) (t * c) = t * klTerm a c := by
  unfold klTerm
  by_cases ha : a = 0
  · simp [ha]
  · have : t * a ≠ 0 := mul_ne_zero ht.ne' ha
    rw [if_neg this, if_neg ha, mul_div_mul_left _ _ ht.ne']
    ring

lemma klTerm_logsum (x y u w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hxu : 0 < x → 0 < u) (hyw : 0 < y → 0 < w) :
    klTerm (x + y) (u + w) ≤ klTerm x u + klTerm y w := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold klTerm
  rcases hx.eq_or_lt with rfl | hx'
  · rcases hy.eq_or_lt with rfl | hy'
    · simp
    · have hw' := hyw hy'
      simp only [zero_add, if_true, hy'.ne', if_false]
      have : Real.logb 2 (y / (u + w)) ≤ Real.logb 2 (y / w) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        exact div_le_div_of_nonneg_left hy hw' (by linarith)
      nlinarith
  rcases hy.eq_or_lt with rfl | hy'
  · have hu' := hxu hx'
    simp only [add_zero, if_true, hx'.ne', if_false]
    have : Real.logb 2 (x / (u + w)) ≤ Real.logb 2 (x / u) := by
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      exact div_le_div_of_nonneg_left hx hu' (by linarith)
    nlinarith
  have hu' := hxu hx'
  have hw' := hyw hy'
  have hxy : x + y ≠ 0 := by positivity
  rw [if_neg hxy, if_neg hx'.ne', if_neg hy'.ne']
  -- concavity of log with weights x/(x+y), y/(x+y)
  have hs : 0 < x + y := by positivity
  have key := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr (div_pos hu' hx'))
    (Set.mem_Ioi.mpr (div_pos hw' hy')) (div_pos hx' hs).le (div_pos hy' hs).le
    (by field_simp)
  simp only [smul_eq_mul] at key
  have e1 : x / (x + y) * (u / x) + y / (x + y) * (w / y) = (u + w) / (x + y) := by
    field_simp
  rw [e1] at key
  simp only [Real.logb]
  rw [Real.log_div hxy (by positivity), Real.log_div hx'.ne' hu'.ne',
    Real.log_div hy'.ne' hw'.ne']
  rw [Real.log_div hu'.ne' hx'.ne', Real.log_div hw'.ne' hy'.ne',
    Real.log_div (by positivity) hxy] at key
  have key2 : x * (Real.log u - Real.log x) + y * (Real.log w - Real.log y) ≤
      (x + y) * (Real.log (u + w) - Real.log (x + y)) := by
    have := mul_le_mul_of_nonneg_left key hs.le
    have e2 : (x + y) * (x / (x + y) * (Real.log u - Real.log x) +
        y / (x + y) * (Real.log w - Real.log y)) =
        x * (Real.log u - Real.log x) + y * (Real.log w - Real.log y) := by
      field_simp
    linarith
  rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', ← add_div]
  apply div_le_div_of_nonneg_right _ hL.le
  nlinarith

lemma gibbs {n : ℕ} (a c : Fin n → ℝ) (ha : ∀ x, 0 ≤ a x) (hc : ∀ x, 0 ≤ c x) (hac : ∀ x, 0 < a x → 0 < c x)
    (ha1 : ∑ x, a x = 1) (hc1 : ∑ x, c x = 1) : 0 ≤ ∑ x, klTerm (a x) (c x) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have term : ∀ x, (a x - c x) / Real.log 2 ≤ klTerm (a x) (c x) := by
    intro x
    unfold klTerm
    by_cases hx : a x = 0
    · rw [if_pos hx, hx]
      have := hc x
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le
    · rw [if_neg hx]
      have hpos : 0 < a x := lt_of_le_of_ne (ha x) (Ne.symm hx)
      · have hcx := hac x hpos
        have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hpos hcx)
        rw [inv_div] at hlog
        simp only [Real.logb]
        rw [mul_div_assoc']
        apply div_le_div_of_nonneg_right _ hL.le
        have : a x * (1 - c x / a x) = a x - c x := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hlog hpos.le]
  calc (0 : ℝ) = ∑ x, (a x - c x) / Real.log 2 := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, ha1, hc1]; simp
    _ ≤ _ := Finset.sum_le_sum (fun x _ => term x)

end P44Aux

namespace P44Aux

lemma kl_joint {n : ℕ} (a a2 c c2 : Fin n → ℝ) (ha : ∀ x, 0 ≤ a x) (ha2 : ∀ x, 0 ≤ a2 x)
    (hc : ∀ x, 0 ≤ c x) (hc2 : ∀ x, 0 ≤ c2 x) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    classicalKL (fun x => p * a x + (1 - p) * a2 x) (fun x => p * c x + (1 - p) * c2 x) ≤
      ENNReal.ofReal p * classicalKL a c + ENNReal.ofReal (1 - p) * classicalKL a2 c2 := by
  rcases hp0.eq_or_lt with rfl | hp0'
  · simp
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp
  have hq : 0 < 1 - p := by linarith
  have hpe : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0').ne'
  have hqe : ENNReal.ofReal (1 - p) ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  by_cases h1 : ∃ x, 0 < a x ∧ c x = 0
  · rw [kl_unfold a c, if_pos h1, ENNReal.mul_top hpe, top_add]; exact le_top
  by_cases h2 : ∃ x, 0 < a2 x ∧ c2 x = 0
  · rw [kl_unfold a2 c2, if_pos h2, ENNReal.mul_top hqe, add_top]; exact le_top
  have hac : ∀ x, 0 < a x → 0 < c x := fun x hx =>
    lt_of_le_of_ne (hc x) (fun h => h1 ⟨x, hx, h.symm⟩)
  have hac2 : ∀ x, 0 < a2 x → 0 < c2 x := fun x hx =>
    lt_of_le_of_ne (hc2 x) (fun h => h2 ⟨x, hx, h.symm⟩)
  have h3 : ¬ ∃ x, 0 < p * a x + (1 - p) * a2 x ∧ p * c x + (1 - p) * c2 x = 0 := by
    rintro ⟨x, hx, hx0⟩
    have e1 : 0 ≤ p * c x := mul_nonneg hp0'.le (hc x)
    have e2 : 0 ≤ (1 - p) * c2 x := mul_nonneg hq.le (hc2 x)
    have : 0 < a x ∨ 0 < a2 x := by
      by_contra hh
      push Not at hh
      nlinarith [mul_le_mul_of_nonneg_left hh.1 hp0'.le, mul_le_mul_of_nonneg_left hh.2 hq.le]
    rcases this with h | h
    · linarith [mul_pos hp0' (hac x h)]
    · linarith [mul_pos hq (hac2 x h)]
  rw [kl_unfold, kl_unfold a c, kl_unfold a2 c2, if_neg h3, if_neg h1, if_neg h2,
    ← ENNReal.ofReal_mul hp0'.le, ← ENNReal.ofReal_mul hq.le]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun x _ => ?_)
  rw [← klTerm_scale p _ _ hp0', ← klTerm_scale (1 - p) _ _ hq]
  exact klTerm_logsum _ _ _ _ (mul_nonneg hp0'.le (ha x)) (mul_nonneg hq.le (ha2 x))
    (mul_nonneg hp0'.le (hc x)) (mul_nonneg hq.le (hc2 x))
    (fun h => mul_pos hp0' (hac x (pos_of_mul_pos_right h hp0'.le)))
    (fun h => mul_pos hq (hac2 x (pos_of_mul_pos_right h hq.le)))

lemma kl_append {n m : ℕ} (a c : Fin n → ℝ) (a2 c2 : Fin m → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hc : ∀ x, 0 ≤ c x) (ha2 : ∀ x, 0 ≤ a2 x) (hc2 : ∀ x, 0 ≤ c2 x)
    (hsa : ∑ x, a x = 1) (hsc : ∑ x, c x = 1) (hsa2 : ∑ x, a2 x = 1) (hsc2 : ∑ x, c2 x = 1)
    (p : ℝ) (hp0' : 0 < p) (hp1' : p < 1) :
    ENNReal.ofReal p * classicalKL a c + ENNReal.ofReal (1 - p) * classicalKL a2 c2 ≤
      classicalKL (Fin.append (fun k => p * a k) (fun l => (1 - p) * a2 l))
        (Fin.append (fun k => p * c k) (fun l => (1 - p) * c2 l)) := by
  have hq : 0 < 1 - p := by linarith
  by_cases h1 : ∃ x, 0 < a x ∧ c x = 0
  · obtain ⟨x, hx, hcx⟩ := h1
    rw [kl_unfold (Fin.append _ _), if_pos ⟨Fin.castAdd m x, by
      simp [Fin.append_left, mul_pos hp0' hx, hcx]⟩]
    exact le_top
  by_cases h2 : ∃ x, 0 < a2 x ∧ c2 x = 0
  · obtain ⟨x, hx, hcx⟩ := h2
    rw [kl_unfold (Fin.append _ _), if_pos ⟨Fin.natAdd n x, by
      simp [Fin.append_right, mul_pos hq hx, hcx]⟩]
    exact le_top
  have hac : ∀ x, 0 < a x → 0 < c x := fun x hx =>
    lt_of_le_of_ne (hc x) (fun h => h1 ⟨x, hx, h.symm⟩)
  have hac2 : ∀ x, 0 < a2 x → 0 < c2 x := fun x hx =>
    lt_of_le_of_ne (hc2 x) (fun h => h2 ⟨x, hx, h.symm⟩)
  have h3 : ¬ ∃ x, 0 < Fin.append (fun k => p * a k) (fun l => (1 - p) * a2 l) x ∧
      Fin.append (fun k => p * c k) (fun l => (1 - p) * c2 l) x = 0 := by
    rintro ⟨x, hx, hx0⟩
    induction x using Fin.addCases with
    | left k =>
      simp only [Fin.append_left] at hx hx0
      have := mul_pos hp0' (hac k (pos_of_mul_pos_right hx hp0'.le))
      linarith
    | right l =>
      simp only [Fin.append_right] at hx hx0
      have := mul_pos hq (hac2 l (pos_of_mul_pos_right hx hq.le))
      linarith
  rw [kl_unfold a c, kl_unfold a2 c2, kl_unfold (Fin.append _ _), if_neg h1, if_neg h2,
    if_neg h3, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  simp_rw [klTerm_scale p _ _ hp0', klTerm_scale (1 - p) _ _ hq]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have g1 := gibbs a c ha hc hac hsa hsc
  have g2 := gibbs a2 c2 ha2 hc2 hac2 hsa2 hsc2
  rw [← ENNReal.ofReal_mul hp0'.le, ← ENNReal.ofReal_mul hq.le,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end P44Aux

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (rho rho2 sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hrho2 : IsHilbertDensity b rho2)
    (hsigma : IsHilbertDensity b sigma) (hsigma2 : IsHilbertDensity b sigma2)
    (horth : OrthogonalBlocks rho rho2 sigma sigma2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    measuredRelativeEntropy b (hilbertMix p rho rho2) (hilbertMix p sigma sigma2) =
      ENNReal.ofReal p * measuredRelativeEntropy b rho sigma +
        ENNReal.ofReal (1-p) * measuredRelativeEntropy b rho2 sigma2 := by
  rcases hp0.eq_or_lt with rfl | hp0'
  · simp [hilbertMix]
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp [hilbertMix]
  apply le_antisymm
  · unfold measuredRelativeEntropy
    refine iSup_le (fun n => iSup_le (fun M => ?_))
    have hMpos := M.2.1
    have hfa : (fun i => (hilbertTrace b ((M.val i).comp (hilbertMix p rho rho2))).re) =
        fun i => p * (hilbertTrace b ((M.val i).comp rho)).re +
          (1 - p) * (hilbertTrace b ((M.val i).comp rho2)).re :=
      funext (fun i => P44Aux.trace_mix_re b _ _ _ (hMpos i) hrho hrho2 p)
    have hfc : (fun i => (hilbertTrace b ((M.val i).comp (hilbertMix p sigma sigma2))).re) =
        fun i => p * (hilbertTrace b ((M.val i).comp sigma)).re +
          (1 - p) * (hilbertTrace b ((M.val i).comp sigma2)).re :=
      funext (fun i => P44Aux.trace_mix_re b _ _ _ (hMpos i) hsigma hsigma2 p)
    rw [hfa, hfc]
    refine le_trans (P44Aux.kl_joint _ _ _ _
      (fun i => P44Aux.trace_nonneg b _ _ (hMpos i) hrho)
      (fun i => P44Aux.trace_nonneg b _ _ (hMpos i) hrho2)
      (fun i => P44Aux.trace_nonneg b _ _ (hMpos i) hsigma)
      (fun i => P44Aux.trace_nonneg b _ _ (hMpos i) hsigma2) p hp0'.le hp1'.le) ?_
    gcongr
    · exact le_iSup_of_le n (le_iSup_of_le M le_rfl)
    · exact le_iSup_of_le n (le_iSup_of_le M le_rfl)
  · obtain ⟨P, hPadj, hPP, hPr, hPs, hPr2, hPs2⟩ := P44Aux.block_projection rho rho2 sigma sigma2
      hrho.2.1 hrho2.2.1 hsigma.2.1 hsigma2.2.1 horth
    set P' : H →L[ℂ] H := 1 - P with hP'def
    have hP'adj : ContinuousLinearMap.adjoint P' = P' := by
      rw [hP'def, map_sub, ContinuousLinearMap.adjoint_one, hPadj]
    have hP'P' : P' * P' = P' := by
      rw [hP'def, sub_mul, one_mul, mul_sub, mul_one, hPP, sub_self, sub_zero]
    have hP'X : ∀ X : H →L[ℂ] H, P.comp X = X → P'.comp X = 0 := by
      intro X h
      rw [hP'def, ContinuousLinearMap.sub_comp, h]
      ext x; simp
    have hP'Y : ∀ Y : H →L[ℂ] H, P.comp Y = 0 → P'.comp Y = Y := by
      intro Y h
      rw [hP'def, ContinuousLinearMap.sub_comp, h]
      ext x; simp
    have key : ∀ n (M : {M : Fin n → H →L[ℂ] H // IsHilbertPOVM M})
        m (N : {N : Fin m → H →L[ℂ] H // IsHilbertPOVM N}),
        ENNReal.ofReal p * classicalKL (fun i => (hilbertTrace b ((M.val i).comp rho)).re)
            (fun i => (hilbertTrace b ((M.val i).comp sigma)).re) +
          ENNReal.ofReal (1 - p) * classicalKL (fun i => (hilbertTrace b ((N.val i).comp rho2)).re)
            (fun i => (hilbertTrace b ((N.val i).comp sigma2)).re) ≤
        measuredRelativeEntropy b (hilbertMix p rho rho2) (hilbertMix p sigma sigma2) := by
      intro n M m N
      let K : Fin (n + m) → H →L[ℂ] H :=
        Fin.append (fun k => P * M.val k * P) (fun l => P' * N.val l * P')
      have hKpos : ∀ i, (K i).IsPositive := by
        intro i
        induction i using Fin.addCases with
        | left k =>
          simp only [K, Fin.append_left]; exact P44Aux.qmq_pos P _ hPadj (M.2.1 k)
        | right l =>
          simp only [K, Fin.append_right]; exact P44Aux.qmq_pos P' _ hP'adj (N.2.1 l)
      have hKsum : ∑ i, K i = 1 := by
        rw [Fin.sum_univ_add]
        simp only [K, Fin.append_left, Fin.append_right]
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, M.2.2, N.2.2,
          mul_one, mul_one, hPP, hP'P', hP'def]
        abel
      have hval : ∀ (X Y : H →L[ℂ] H), IsHilbertDensity b X → IsHilbertDensity b Y →
          P.comp X = X → P.comp Y = 0 →
          (fun i => (hilbertTrace b ((K i).comp (hilbertMix p X Y))).re) =
            Fin.append (fun k => p * (hilbertTrace b ((M.val k).comp X)).re)
              (fun l => (1 - p) * (hilbertTrace b ((N.val l).comp Y)).re) := by
        intro X Y hX hY hPX hPY
        funext i
        induction i using Fin.addCases with
        | left k =>
          simp only [K, Fin.append_left]
          rw [P44Aux.trace_mix_re b _ X Y (P44Aux.qmq_pos P _ hPadj (M.2.1 k)) hX hY p,
            P44Aux.proj_trace b P (M.val k) X hPadj (M.2.1 k) hX 1 (Or.inr rfl)
              (by simpa using hPX),
            P44Aux.proj_trace b P (M.val k) Y hPadj (M.2.1 k) hY 0 (Or.inl rfl)
              (by simpa using hPY)]
          simp
        | right l =>
          simp only [K, Fin.append_right]
          rw [P44Aux.trace_mix_re b _ X Y (P44Aux.qmq_pos P' _ hP'adj (N.2.1 l)) hX hY p,
            P44Aux.proj_trace b P' (N.val l) X hP'adj (N.2.1 l) hX 0 (Or.inl rfl)
              (by simpa using hP'X X hPX),
            P44Aux.proj_trace b P' (N.val l) Y hP'adj (N.2.1 l) hY 1 (Or.inr rfl)
              (by simpa using hP'Y Y hPY)]
          simp
      calc _ ≤ classicalKL
            (Fin.append (fun k => p * (hilbertTrace b ((M.val k).comp rho)).re)
              (fun l => (1 - p) * (hilbertTrace b ((N.val l).comp rho2)).re))
            (Fin.append (fun k => p * (hilbertTrace b ((M.val k).comp sigma)).re)
              (fun l => (1 - p) * (hilbertTrace b ((N.val l).comp sigma2)).re)) :=
          P44Aux.kl_append _ _ _ _
            (fun i => P44Aux.trace_nonneg b _ _ (M.2.1 i) hrho)
            (fun i => P44Aux.trace_nonneg b _ _ (M.2.1 i) hsigma)
            (fun i => P44Aux.trace_nonneg b _ _ (N.2.1 i) hrho2)
            (fun i => P44Aux.trace_nonneg b _ _ (N.2.1 i) hsigma2)
            (P44Aux.povm_trace_sum b _ M.2 _ hrho) (P44Aux.povm_trace_sum b _ M.2 _ hsigma)
            (P44Aux.povm_trace_sum b _ N.2 _ hrho2) (P44Aux.povm_trace_sum b _ N.2 _ hsigma2)
            p hp0' hp1'
        _ = classicalKL (fun i => (hilbertTrace b ((K i).comp (hilbertMix p rho rho2))).re)
            (fun i => (hilbertTrace b ((K i).comp (hilbertMix p sigma sigma2))).re) := by
          rw [hval rho rho2 hrho hrho2 hPr hPr2, hval sigma sigma2 hsigma hsigma2 hPs hPs2]
        _ ≤ _ := by
          unfold measuredRelativeEntropy
          exact le_iSup_of_le (n + m) (le_iSup_of_le ⟨K, hKpos, hKsum⟩ le_rfl)
    have e1 : ∀ X Y : H →L[ℂ] H, measuredRelativeEntropy b X Y =
        ⨆ x : (Σ n, {M : Fin n → H →L[ℂ] H // IsHilbertPOVM M}),
          classicalKL (fun i => (hilbertTrace b ((x.2.val i).comp X)).re)
            (fun i => (hilbertTrace b ((x.2.val i).comp Y)).re) := by
      intro X Y
      unfold measuredRelativeEntropy
      rw [iSup_sigma]
    have : Nonempty (Σ n, {M : Fin n → H →L[ℂ] H // IsHilbertPOVM M}) :=
      ⟨⟨1, fun _ => 1, by simp [IsHilbertPOVM, ContinuousLinearMap.isPositive_one]⟩⟩
    rw [e1 rho sigma, e1 rho2 sigma2, ENNReal.mul_iSup, ENNReal.mul_iSup]
    exact ENNReal.iSup_add_iSup_le (fun x y => key x.1 x.2 y.1 y.2)

end
