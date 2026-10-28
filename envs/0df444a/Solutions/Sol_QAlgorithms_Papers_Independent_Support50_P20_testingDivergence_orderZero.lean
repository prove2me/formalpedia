-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P20.testingDivergence_orderZero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:50:25.417967+00:00
-- url     : https://prove2.me/submissions/caa7cf95-1e2d-42a9-bda1-291ca40f7af2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal ComplexOrder InnerProductSpace

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P20

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

namespace P20Aux

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


lemma toML {T : H →L[ℂ] H} (h : QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive T) :
    T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨?_, fun x => ?_⟩
  · rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]; exact h.1
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]; exact h.2 x

lemma fromML {T : H →L[ℂ] H} (h : T.IsPositive) :
    QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive T :=
  ⟨h.isSelfAdjoint.adjoint_eq, fun x => h.re_inner_nonneg_right x⟩

lemma trace_zero (A σ : H →L[ℂ] H) (hA : A.IsPositive) (hσ : IsTraceClass σ)
    (hσp : σ.IsPositive) (h0 : (∑' i, ⟪b i, A (σ (b i))⟫_ℂ).re = 0) :
    A.comp σ = 0 := by
  have h0σ : 0 ≤ σ := (ContinuousLinearMap.nonneg_iff_isPositive σ).mpr hσp
  have h0A : 0 ≤ A := (ContinuousLinearMap.nonneg_iff_isPositive A).mpr hA
  set S := CFC.sqrt σ with hSdef
  set T := CFC.sqrt A with hTdef
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ h0σ
  have hTT : T * T = A := CFC.sqrt_mul_sqrt_self A h0A
  have hSadj : ContinuousLinearMap.adjoint S = S := (CFC.sqrt_nonneg σ).isSelfAdjoint.adjoint_eq
  have hTadj : ContinuousLinearMap.adjoint T = T := (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq
  have hAadj : ContinuousLinearMap.adjoint A = A := hA.isSelfAdjoint.adjoint_eq
  have hSsym : ∀ x y, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ := by
    intro x y; rw [← ContinuousLinearMap.adjoint_inner_right, hSadj]
  have hTsym : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro x y; rw [← ContinuousLinearMap.adjoint_inner_right, hTadj]
  have hAsym : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
    intro x y; rw [← ContinuousLinearMap.adjoint_inner_right, hAadj]
  have hSSx : ∀ x, S (S x) = σ x := by
    intro x; rw [← hSS]; rfl
  have hTTx : ∀ x, T (T x) = A x := by
    intro x; rw [← hTT]; rfl
  have hnormS : ∀ x, ‖S x‖ ^ 2 ≤ ‖⟪x, σ x⟫_ℂ‖ := by
    intro x
    have : (⟪S x, S x⟫_ℂ).re = ‖S x‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (S x))
    rw [← this, hSsym, hSSx]
    exact Complex.re_le_norm _
  have hSHS : Summable fun j => ‖S (b j)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => hnormS (b j)) (diag_summable b hσ)
  have hMSHS : Summable fun j => ‖(A.comp S) (b j)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) (hSHS.mul_left (‖A‖ ^ 2))
    simp only [ContinuousLinearMap.comp_apply]
    rw [← mul_pow]
    gcongr
    exact A.le_opNorm _
  have hadjMS : ContinuousLinearMap.adjoint (A.comp S) = S.comp A := by
    rw [ContinuousLinearMap.adjoint_comp, hSadj, hAadj]
  have hSMHS : Summable fun j => ‖(S.comp A) (b j)‖ ^ 2 := by
    have := hs_adjoint b (A.comp S) hMSHS
    rwa [hadjMS] at this
  have hterm : ∀ i, ⟪b i, A (σ (b i))⟫_ℂ = ⟪(S.comp A) (b i), S (b i)⟫_ℂ := by
    intro i
    simp only [ContinuousLinearMap.comp_apply]
    rw [hSsym, hSSx, hAsym]
  simp_rw [hterm] at h0
  rw [hs_swap b (S.comp A) S hSMHS hSHS, hSadj, ContinuousLinearMap.adjoint_comp, hSadj,
    hAadj] at h0
  have hs : Summable (fun j => ⟪S (b j), (A.comp S) (b j)⟫_ℂ) := by
    refine Summable.of_norm_bounded ((hMSHS.add hSHS).div_const 2) (fun i => ?_)
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (S (b i)) ((A.comp S) (b i))
    have h2 := two_mul_le_add_sq ‖(A.comp S) (b i)‖ ‖S (b i)‖
    linarith
  rw [Complex.re_tsum hs] at h0
  have hnn : ∀ j, 0 ≤ (⟪S (b j), (A.comp S) (b j)⟫_ℂ).re := by
    intro j
    simpa using hA.re_inner_nonneg_right (S (b j))
  have hall := (hasSum_zero_iff_of_nonneg hnn).mp (h0 ▸ (Complex.reCLM.summable hs).hasSum)
  have hTS : ∀ j, T (S (b j)) = 0 := by
    intro j
    have e := congrFun hall j
    have : (⟪T (S (b j)), T (S (b j))⟫_ℂ).re = (⟪S (b j), (A.comp S) (b j)⟫_ℂ).re := by
      rw [hTsym, hTTx]; rfl
    rw [e, Pi.zero_apply] at this
    have h2 : ‖T (S (b j))‖ ^ 2 = 0 := by
      rw [← this]; simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (T (S (b j)))).symm
    simpa using h2
  have hTS0 : T.comp S = 0 := by
    ext x
    have hx := (b.hasSum_repr x).mapL (T.comp S)
    simp only [map_smul, ContinuousLinearMap.comp_apply, hTS, smul_zero] at hx
    simpa using hx.unique hasSum_zero
  ext x
  have : A (σ x) = T ((T.comp S) (S x)) := by
    rw [← hSSx, ← hTTx]; rfl
  simp [this, hTS0]

end P20Aux

open P20Aux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : QAlgorithms.Papers.Independent.Dependency50.P13.State b) :
    hilbertTestingDivergence b 0 rho.val.val sigma.val.val =
      orderZeroDivergence b rho.val.val sigma.val.val := by
  have hρtc : IsTraceClass rho.val.val := rho.val.property
  have hσtc : IsTraceClass sigma.val.val := sigma.val.property
  have hρp : (rho.val.val).IsPositive := toML rho.property.1
  have hσp : (sigma.val.val).IsPositive := toML sigma.property.1
  set ρ := rho.val.val with hρdef
  set σ := sigma.val.val with hσdef
  set K : Submodule ℂ H := (LinearMap.ker ρ.toLinearMap)ᗮ with hK
  set P : H →L[ℂ] H := K.starProjection with hP
  have hρadj : ContinuousLinearMap.adjoint ρ = ρ := hρp.isSelfAdjoint.adjoint_eq
  have hPadj : ContinuousLinearMap.adjoint P = P := (isSelfAdjoint_starProjection K).adjoint_eq
  have hPpos : P.IsPositive := by
    have h := ContinuousLinearMap.IsPositive.conj_starProjection K
      (ContinuousLinearMap.isPositive_one (E := H) (𝕜 := ℂ))
    have e : K.starProjection ∘L (1 : H →L[ℂ] H) ∘L K.starProjection = P := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
      exact Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
    rw [e] at h; exact h
  have h1Ppos : (1 - P).IsPositive := by
    rw [hP, ← Submodule.starProjection_orthogonal']
    have h := ContinuousLinearMap.IsPositive.conj_starProjection Kᗮ
      (ContinuousLinearMap.isPositive_one (E := H) (𝕜 := ℂ))
    have e : Kᗮ.starProjection ∘L (1 : H →L[ℂ] H) ∘L Kᗮ.starProjection = Kᗮ.starProjection := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
      exact Submodule.starProjection_eq_self_iff.mpr (Kᗮ.starProjection_apply_mem x)
    rw [e] at h; exact h
  have hρK : ∀ x, ρ x ∈ K := by
    intro x
    rw [hK, Submodule.mem_orthogonal]
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left, hρadj]
    have : ρ y = 0 := hy
    simp [this]
  have hPρ : P.comp ρ = ρ := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (hρK x)
  have htr : ∀ T : H →L[ℂ] H, operatorTrace b T = ∑' i, ⟪b i, T (b i)⟫_ℂ := fun _ => rfl
  unfold hilbertTestingDivergence orderZeroDivergence
  congr 1
  unfold hilbertTestingBeta
  apply le_antisymm
  · refine sInf_le ⟨⟨P, fromML hPpos, ?_⟩, ?_, rfl⟩
    · have : (1 : H →L[ℂ] H) - P = 1 - P := rfl
      exact fromML h1Ppos
    · unfold traceAcceptance
      rw [hPρ, rho.property.2]
      simp
  · refine le_sInf ?_
    rintro z ⟨Q, hQ, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    have hQp : (Q.val).IsPositive := toML Q.property.1
    have h1Qp : (1 - Q.val).IsPositive := toML Q.property.2
    set q := Q.val with hq
    have hqadj : ContinuousLinearMap.adjoint q = q := hQp.isSelfAdjoint.adjoint_eq
    unfold traceAcceptance at hQ ⊢
    rw [htr] at hQ ⊢
    rw [htr]
    -- trace of (1-q)ρ vanishes
    obtain ⟨s1, n1⟩ := trace_comp_pos b (1 - q) ρ h1Qp hρtc hρp
    obtain ⟨sq, _⟩ := trace_comp_pos b q ρ hQp hρtc hρp
    obtain ⟨sone, _⟩ := trace_comp_pos b 1 ρ ContinuousLinearMap.isPositive_one hρtc hρp
    have hρ1 : (∑' i, ⟪b i, ρ (b i)⟫_ℂ) = 1 := rho.property.2
    have hsplit : (∑' i, ⟪b i, (1 - q) (ρ (b i))⟫_ℂ) =
        (∑' i, ⟪b i, ρ (b i)⟫_ℂ) - ∑' i, ⟪b i, q (ρ (b i))⟫_ℂ := by
      simp only [ContinuousLinearMap.one_apply] at sone
      rw [← sone.tsum_sub sq]
      refine tsum_congr (fun i => ?_)
      simp
    have hz : (∑' i, ⟪b i, (1 - q) (ρ (b i))⟫_ℂ).re = 0 := by
      rw [hsplit, Complex.sub_re, hρ1, Complex.one_re] at n1 ⊢
      simp only [ContinuousLinearMap.comp_apply] at hQ
      linarith
    have hkill := trace_zero b (1 - q) ρ h1Qp hρtc hρp hz
    -- (1 - q) vanishes on K
    have hKker : K ≤ LinearMap.ker ((1 - q : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      have hcl : K = (LinearMap.range (ρ : H →ₗ[ℂ] H)).topologicalClosure := by
        rw [hK]
        have := ContinuousLinearMap.orthogonal_ker ρ
        rw [hρadj] at this
        exact this
      rw [hcl]
      refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · rintro _ ⟨y, rfl⟩
        have := congrArg (fun T : H →L[ℂ] H => T y) hkill
        simpa using this
      · exact ContinuousLinearMap.isClosed_ker _
    have hqP : q.comp P = P := by
      ext x
      have hx : (1 - q) (P x) = 0 := hKker (K.starProjection_apply_mem x)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hx
      simp [hx.symm]
    have hPq : P.comp q = P := by
      have := congrArg ContinuousLinearMap.adjoint hqP
      rw [ContinuousLinearMap.adjoint_comp, hqadj, hPadj] at this
      exact this
    have hdiff : q - P = (1 - P).comp (q.comp (1 - P)) := by
      have hPP : P.comp P = P := by
        ext x
        exact Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
      have e1 : ∀ A B : H →L[ℂ] H, A.comp B = A * B := fun _ _ => rfl
      rw [e1, e1]
      rw [e1] at hPP hqP hPq
      rw [mul_sub q 1 P, mul_one, hqP, sub_mul, one_mul, mul_sub, hPq, hPP]
      abel
    have hdpos : (q - P).IsPositive := by
      rw [hdiff]
      have h := hQp.conj_adjoint (1 - P)
      rw [h1Ppos.isSelfAdjoint.adjoint_eq] at h
      exact h
    obtain ⟨tq, _⟩ := trace_comp_pos b q σ hQp hσtc hσp
    obtain ⟨tP, _⟩ := trace_comp_pos b P σ hPpos hσtc hσp
    obtain ⟨_, td⟩ := trace_comp_pos b (q - P) σ hdpos hσtc hσp
    have hsub : (∑' i, ⟪b i, (q - P) (σ (b i))⟫_ℂ) =
        (∑' i, ⟪b i, q (σ (b i))⟫_ℂ) - ∑' i, ⟪b i, P (σ (b i))⟫_ℂ := by
      rw [← tq.tsum_sub tP]
      refine tsum_congr (fun i => ?_)
      simp
    rw [hsub, Complex.sub_re] at td
    simp only [ContinuousLinearMap.comp_apply]
    rw [show closedSupportProjector ρ = P from rfl]
    linarith
