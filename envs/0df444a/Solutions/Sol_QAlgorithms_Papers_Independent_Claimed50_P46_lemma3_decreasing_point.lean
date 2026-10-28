-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P46.lemma3_decreasing_point
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:07:33.22904+00:00
-- url     : https://prove2.me/submissions/50d7eb56-2ca3-4054-8552-83b60378457d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46
noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

open QAlgorithms.Papers.Independent.Claimed50.P46

namespace P46Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {J : Type*}

def ptr (b : HilbertBasis J ℂ E) (A : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' j, ENNReal.ofReal (inner ℂ (b j) (A (b j))).re

lemma sa_inner {R : E →L[ℂ] E} (h : IsSelfAdjoint R) (x y : E) :
    inner ℂ x (R y) = inner ℂ (R x) y := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, h.star_eq]

lemma isPos_nonneg {T : E →L[ℂ] E} (h : IsPositive T) : 0 ≤ T := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  refine ⟨?_, fun x => ?_⟩
  · rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]; exact h.1
  · have := h.2 x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]; exact this

lemma nonneg_re {T : E →L[ℂ] E} (h : 0 ≤ T) (x : E) : 0 ≤ (inner ℂ x (T x)).re := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at h
  have := h.2 x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm] at this; exact this

lemma sqrt_sa (T : E →L[ℂ] E) : IsSelfAdjoint (cfc Real.sqrt T) := cfc_predicate _ _

lemma sqrt_mul (T : E →L[ℂ] E) (hT : 0 ≤ T) : cfc Real.sqrt T * cfc Real.sqrt T = T := by
  rw [← cfc_mul Real.sqrt Real.sqrt T]
  conv_rhs => rw [← cfc_id' ℝ T]
  apply cfc_congr
  intro x hx
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hT hx)

lemma norm_sq_eq_re (x : E) : ‖x‖ ^ 2 = (inner ℂ x x).re := by
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm

lemma parseval (b : HilbertBasis J ℂ E) (x : E) :
    ENNReal.ofReal (‖x‖ ^ 2) = ∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  have h2 : HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
    have := Complex.hasSum_re h
    rw [norm_sq_eq_re]
    convert this using 1
    funext i
    rw [← inner_conj_symm (b i) x, mul_comm, Complex.conj_mul', Complex.norm_conj]
    norm_cast
  rw [← h2.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h2.summable]

/-- contraction: Tr(R Y R) ≤ Tr Y for R = sqrt T, 0 ≤ T ≤ 1, 0 ≤ Y. -/
lemma contraction (b : HilbertBasis J ℂ E) (T Y : E →L[ℂ] E) (hT : 0 ≤ T) (hT1 : 0 ≤ 1 - T)
    (hY : 0 ≤ Y) :
    ptr b ((cfc Real.sqrt T).comp (Y.comp (cfc Real.sqrt T))) ≤ ptr b Y := by
  set R := cfc Real.sqrt T with hRdef
  set B := cfc Real.sqrt Y with hBdef
  have hR : IsSelfAdjoint R := sqrt_sa T
  have hB : IsSelfAdjoint B := sqrt_sa Y
  have hRR : R * R = T := sqrt_mul T hT
  have hBB : B * B = Y := sqrt_mul Y hY
  have hRc : ∀ u : E, ‖R u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    intro u
    have h1 := nonneg_re hT1 u
    rw [norm_sq_eq_re, norm_sq_eq_re, ← sa_inner hR]
    have : R (R u) = T u := by rw [← hRR]; rfl
    rw [this]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
      Complex.sub_re] at h1
    linarith
  have hterm : ∀ v : E, (inner ℂ v (Y v)).re = ‖B v‖ ^ 2 := by
    intro v
    rw [norm_sq_eq_re, ← sa_inner hB]
    rw [← hBB]; rfl
  unfold ptr
  have lhs : ∀ j, ENNReal.ofReal (inner ℂ (b j) ((R.comp (Y.comp R)) (b j))).re =
      ∑' i, ENNReal.ofReal (‖inner ℂ (b j) (R (B (b i)))‖ ^ 2) := by
    intro j
    have : (inner ℂ (b j) ((R.comp (Y.comp R)) (b j))).re = ‖B (R (b j))‖ ^ 2 := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [sa_inner hR, hterm]
    rw [this, parseval b]
    congr 1; funext i
    congr 2
    rw [sa_inner hB, sa_inner hR (b j), norm_inner_symm]
  have rhs : ∀ i, ENNReal.ofReal (‖R (B (b i))‖ ^ 2) ≤
      ENNReal.ofReal (inner ℂ (b i) (Y (b i))).re := by
    intro i
    rw [hterm]
    exact ENNReal.ofReal_le_ofReal (hRc _)
  simp_rw [lhs]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← parseval b]
  exact rhs i

def W (M T : E →L[ℂ] E) : E →L[ℂ] E := (cfc Real.sqrt T).comp (M.comp (cfc Real.sqrt T))

lemma W_inner (M T : E →L[ℂ] E) (x : E) :
    inner ℂ x (W M T x) = inner ℂ (cfc Real.sqrt T x) (M (cfc Real.sqrt T x)) := by
  unfold W
  simp only [ContinuousLinearMap.comp_apply]
  rw [sa_inner (sqrt_sa T)]

lemma W_nonneg (b : HilbertBasis J ℂ E) (M T : E →L[ℂ] E) (hM : 0 ≤ M) (j : J) :
    0 ≤ (inner ℂ (b j) (W M T (b j))).re := by
  rw [W_inner]; exact nonneg_re hM _

lemma qkey (b : HilbertBasis J ℂ E) (ρ σ S X : E →L[ℂ] E) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hS0 : 0 ≤ S) (hS1 : 0 ≤ 1 - S) (hX0 : 0 ≤ X) (hX1 : 0 ≤ 1 - X) (c : ℝ) (hc : 0 < c)
    (h1 : (cfc (fun x : ℝ => max x 0) (ρ - (c : ℂ) • σ)).comp (1 - S) = 0)
    (h2 : (cfc (fun x : ℝ => max x 0) (-(ρ - (c : ℂ) • σ))).comp S = 0) :
    ptr b (W ρ (1 - S)) + ENNReal.ofReal c * ptr b (W σ (1 - X)) ≤
      ptr b (W ρ (1 - X)) + ENNReal.ofReal c * ptr b (W σ (1 - S)) := by
  have hA : IsSelfAdjoint (ρ - (c : ℂ) • σ) := by
    have h3 : IsSelfAdjoint ((c : ℂ) • σ) := by
      rw [Complex.coe_smul]
      exact IsSelfAdjoint.smul (IsSelfAdjoint.all c) (IsSelfAdjoint.of_nonneg hσ)
    exact (IsSelfAdjoint.of_nonneg hρ).sub h3
  obtain ⟨A, hAdef⟩ : ∃ A, A = ρ - (c : ℂ) • σ := ⟨_, rfl⟩
  rw [← hAdef] at h1 h2 hA
  obtain ⟨Ap, hApdef⟩ : ∃ Ap, Ap = cfc (fun x : ℝ => max x 0) A := ⟨_, rfl⟩
  obtain ⟨Am, hAmdef⟩ : ∃ Am, Am = cfc (fun x : ℝ => max x 0) (-A) := ⟨_, rfl⟩
  rw [← hApdef] at h1
  rw [← hAmdef] at h2
  have hAm' : Am = cfc (fun x : ℝ => max (-x) 0) A := by
    rw [hAmdef, ← cfc_comp_neg (fun x : ℝ => max x 0) A]
  have hAApAm : A = Ap - Am := by
    rw [hAm', hApdef, ← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) A]
    conv_lhs => rw [← cfc_id' ℝ A]
    apply cfc_congr
    intro x _
    exact (max_zero_sub_max_neg_zero_eq_self x).symm
  have hAp0 : 0 ≤ Ap := hApdef ▸ cfc_nonneg (fun x _ => le_max_right _ _)
  have hAm0 : 0 ≤ Am := hAmdef ▸ cfc_nonneg (fun x _ => le_max_right _ _)
  have hApsa : IsSelfAdjoint Ap := IsSelfAdjoint.of_nonneg hAp0
  have hAmsa : IsSelfAdjoint Am := IsSelfAdjoint.of_nonneg hAm0
  obtain ⟨R, hRdef⟩ : ∃ R, R = cfc Real.sqrt (1 - S) := ⟨_, rfl⟩
  have hR : IsSelfAdjoint R := hRdef ▸ sqrt_sa _
  have hRR : R * R = 1 - S := hRdef ▸ sqrt_mul _ hS1
  have hSS : 0 ≤ 1 - (1 - S) := by simpa using hS0
  have hXX : 0 ≤ 1 - (1 - X) := by simpa using hX0
  -- Ap * R = 0
  have h1' : Ap * (R * R) = 0 := by rw [hRR]; exact h1
  have h1s : R * R * Ap = 0 := by
    have := congrArg star h1'
    rwa [star_mul, star_mul, hR.star_eq, hApsa.star_eq, star_zero] at this
  have hRAp : R * Ap = 0 := by
    ext v
    have hn : ‖R (Ap v)‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re, ← sa_inner hR]
      have : R (R (Ap v)) = (R * R * Ap) v := rfl
      rw [this, h1s]; simp
    simpa using hn
  have hApR : Ap * R = 0 := by
    have := congrArg star hRAp
    rwa [star_mul, hR.star_eq, hApsa.star_eq, star_zero] at this
  -- Am = (1-S) Am (1-S)
  have h2s : S * Am = 0 := by
    have := congrArg star h2
    rwa [show (Am.comp S) = Am * S from rfl, star_mul, hAmsa.star_eq,
      (IsSelfAdjoint.of_nonneg hS0).star_eq, star_zero] at this
  have hAmeq : R * (R * Am * R) * R = Am := by
    have e1 : (1 - S) * Am = Am := by rw [sub_mul, h2s, one_mul, sub_zero]
    have e2 : Am * (1 - S) = Am := by
      rw [mul_sub, show Am * S = Am.comp S from rfl, h2, mul_one, sub_zero]
    calc R * (R * Am * R) * R = (R * R) * Am * (R * R) := by noncomm_ring
      _ = Am := by rw [hRR, e1, e2]
  have hY : 0 ≤ R * Am * R := hR.conjugate_nonneg hAm0
  have hcontr : ptr b Am ≤ ptr b (W Am (1 - S)) := by
    have := contraction b (1 - S) (R * Am * R) hS1 hSS hY
    have e : R.comp ((R * Am * R).comp R) = Am := by
      conv_rhs => rw [← hAmeq]
      rfl
    rw [← hRdef, e] at this
    unfold W
    rw [← hRdef]
    exact this
  -- equality for S
  have eqS : ptr b (W ρ (1 - S)) + ptr b (W Am (1 - S)) =
      ENNReal.ofReal c * ptr b (W σ (1 - S)) := by
    unfold ptr
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [← ENNReal.ofReal_add (W_nonneg b _ _ hρ j) (W_nonneg b _ _ hAm0 j),
      ← ENNReal.ofReal_mul hc.le]
    congr 1
    simp only [W_inner]
    rw [← hRdef]
    set w := R (b j)
    have hAw : inner ℂ w (A w) = inner ℂ w (ρ w) - (c : ℂ) * inner ℂ w (σ w) := by
      rw [hAdef]; simp [inner_sub_right, inner_smul_right]
    have hAw2 : inner ℂ w (A w) = inner ℂ w (Ap w) - inner ℂ w (Am w) := by
      conv_lhs => rw [hAApAm]
      simp [inner_sub_right]
    have hApw : Ap w = 0 := by
      show (Ap * R) (b j) = 0
      rw [hApR]; rfl
    rw [hApw, inner_zero_right, zero_sub] at hAw2
    have := congrArg Complex.re (hAw.symm.trans hAw2)
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at this
    linarith
  -- inequality for X
  have leX : ENNReal.ofReal c * ptr b (W σ (1 - X)) ≤
      ptr b (W ρ (1 - X)) + ptr b (W Am (1 - X)) := by
    unfold ptr
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ENNReal.ofReal_add (W_nonneg b _ _ hρ j) (W_nonneg b _ _ hAm0 j),
      ← ENNReal.ofReal_mul hc.le]
    apply ENNReal.ofReal_le_ofReal
    simp only [W_inner]
    set w := cfc Real.sqrt (1 - X) (b j)
    have hAw : inner ℂ w (A w) = inner ℂ w (ρ w) - (c : ℂ) * inner ℂ w (σ w) := by
      rw [hAdef]; simp [inner_sub_right, inner_smul_right]
    have hAw2 : inner ℂ w (A w) = inner ℂ w (Ap w) - inner ℂ w (Am w) := by
      conv_lhs => rw [hAApAm]
      simp [inner_sub_right]
    have hpos := nonneg_re hAp0 w
    have := congrArg Complex.re (hAw.symm.trans hAw2)
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at this
    linarith
  have hcX : ptr b (W Am (1 - X)) ≤ ptr b Am := contraction b (1 - X) Am hX1 hXX hAm0
  calc ptr b (W ρ (1 - S)) + ENNReal.ofReal c * ptr b (W σ (1 - X))
      ≤ ptr b (W ρ (1 - S)) + (ptr b (W ρ (1 - X)) + ptr b (W Am (1 - S))) := by
        gcongr
        exact leX.trans (add_le_add_right (hcX.trans hcontr) _)
    _ = ptr b (W ρ (1 - X)) + (ptr b (W ρ (1 - S)) + ptr b (W Am (1 - S))) := by ring
    _ = _ := by rw [eqS]

lemma qle (b : HilbertBasis J ℂ E) (σ X : E →L[ℂ] E) (hσ : 0 ≤ σ) (hX0 : 0 ≤ X) (hX1 : 0 ≤ 1 - X) :
    ptr b (W σ (1 - X)) ≤ ptr b σ :=
  contraction b (1 - X) σ hX1 (by simpa using hX0) hσ

lemma qtest_nonneg (Q : QuantumData.{u}) (X : SimpleHypothesisTest (.quantum Q)) :
    0 ≤ X.val ∧ 0 ≤ 1 - X.val :=
  ⟨isPos_nonneg X.property.1, isPos_nonneg X.property.2⟩

lemma key (P : SimpleHypothesisSystem.{u}) (k : ℕ) (a : ℝ) (S X : SimpleHypothesisTest P)
    (hS : IsLikelihood P k a S) :
    testingTypeI S + ENNReal.ofReal (Real.exp (((k : ℝ) + 1) * a)) * testingTypeII (testRejection X) ≤
      testingTypeI X + ENNReal.ofReal (Real.exp (((k : ℝ) + 1) * a)) *
        testingTypeII (testRejection S) := by
  cases P with
  | quantum Q =>
    obtain ⟨h1, h2⟩ := hS
    have hS' := qtest_nonneg Q S
    have hX' := qtest_nonneg Q X
    exact qkey Q.basis Q.rho Q.sigma S.val X.val (isPos_nonneg Q.rho_positive)
      (isPos_nonneg Q.sigma_positive) hS'.1 hS'.2 hX'.1 hX'.2 _ (Real.exp_pos _) h1 h2
  | classical C =>
    set c := Real.exp (((k : ℝ) + 1) * a) with hc
    have hc0 : 0 < c := Real.exp_pos _
    show ∑' x, (C.rho x : ℝ≥0∞) * ENNReal.ofReal (1 - (S x).val) +
        ENNReal.ofReal c * ∑' x, (C.sigma x : ℝ≥0∞) * ENNReal.ofReal (1 - (X x).val) ≤
      ∑' x, (C.rho x : ℝ≥0∞) * ENNReal.ofReal (1 - (X x).val) +
        ENNReal.ofReal c * ∑' x, (C.sigma x : ℝ≥0∞) * ENNReal.ofReal (1 - (S x).val)
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    have hs := (S x).property
    have hx := (X x).property
    obtain ⟨hS1, hS2⟩ := hS x
    simp only [← ENNReal.ofReal_coe_nnreal]
    have r0 : (0 : ℝ) ≤ C.rho x := (C.rho x).2
    have s0 : (0 : ℝ) ≤ C.sigma x := (C.sigma x).2
    rw [← ENNReal.ofReal_mul r0, ← ENNReal.ofReal_mul r0, ← ENNReal.ofReal_mul s0,
      ← ENNReal.ofReal_mul s0, ← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_mul hc0.le,
      ← ENNReal.ofReal_add (mul_nonneg r0 (by linarith [hs.2]))
        (mul_nonneg hc0.le (mul_nonneg s0 (by linarith [hx.2]))),
      ← ENNReal.ofReal_add (mul_nonneg r0 (by linarith [hx.2]))
        (mul_nonneg hc0.le (mul_nonneg s0 (by linarith [hs.2])))]
    apply ENNReal.ofReal_le_ofReal
    rcases lt_trichotomy (C.rho x : ℝ) (c * (C.sigma x : ℝ)) with h | h | h
    · have := hS2 h
      rw [this]; nlinarith [hx.1, hx.2]
    · have : (C.rho x : ℝ) = c * C.sigma x := h
      rw [this]; nlinarith
    · have := hS1 h
      rw [this]; nlinarith [hx.1, hx.2]

lemma le_one (P : SimpleHypothesisSystem.{u}) (hσ : totalMass P true = 1)
    (X : SimpleHypothesisTest P) : testingTypeII (testRejection X) ≤ 1 := by
  cases P with
  | quantum Q =>
    have hX' := qtest_nonneg Q X
    rw [← hσ]
    exact qle Q.basis Q.sigma X.val (isPos_nonneg Q.sigma_positive) hX'.1 hX'.2
  | classical C =>
    rw [← hσ]
    show ∑' x, (C.sigma x : ℝ≥0∞) * ENNReal.ofReal (1 - (X x).val) ≤ ∑' x, (C.sigma x : ℝ≥0∞)
    refine ENNReal.tsum_le_tsum fun x => ?_
    have hx := (X x).property
    exact mul_le_of_le_one_right (by positivity) (ENNReal.ofReal_le_one.2 (by linarith [hx.1]))

def allAccept : (P : SimpleHypothesisSystem.{u}) → SimpleHypothesisTest P
  | .classical _ => fun _ => ⟨1, by norm_num, le_refl _⟩
  | .quantum _ => ⟨1, ⟨by rw [← ContinuousLinearMap.star_eq_adjoint, star_one],
      fun x => by simp only [ContinuousLinearMap.one_apply]; exact inner_self_nonneg (𝕜 := ℂ)⟩,
      ⟨by rw [sub_self, ← ContinuousLinearMap.star_eq_adjoint, star_zero], fun x => by simp⟩⟩

lemma allAccept_I (P : SimpleHypothesisSystem.{u}) : testingTypeI (allAccept P) = 0 := by
  cases P with
  | quantum Q =>
    show ptr Q.basis (W Q.rho (1 - 1)) = 0
    simp [W, ptr]
  | classical C =>
    show ∑' x, (C.rho x : ℝ≥0∞) * ENNReal.ofReal (1 - 1) = 0
    simp

lemma allAccept_II (P : SimpleHypothesisSystem.{u}) :
    testingTypeII (testRejection (allAccept P)) = 0 := by
  cases P with
  | quantum Q =>
    show ptr Q.basis (W Q.sigma (1 - 1)) = 0
    simp [W, ptr]
  | classical C =>
    show ∑' x, (C.sigma x : ℝ≥0∞) * ENNReal.ofReal (1 - 1) = 0
    simp

lemma K1 (P : SimpleHypothesisSystem.{u}) (k : ℕ) (a : ℝ) (S : SimpleHypothesisTest P)
    (hS : IsLikelihood P k a S) :
    testingTypeI S ≤ ENNReal.ofReal (Real.exp (((k : ℝ) + 1) * a)) *
        testingTypeII (testRejection S) := by
  have := key P k a S (allAccept P) hS
  rwa [allAccept_I, allAccept_II, mul_zero, add_zero, zero_add] at this

lemma bee_real (k : ℕ) (q : ℝ≥0∞) (h0 : q ≠ 0) (ht : q ≠ ⊤) :
    blockErrorExponent k q = ((-(Real.log q.toReal) / ((k : ℝ) + 1) : ℝ) : EReal) := by
  unfold blockErrorExponent perBlock
  rw [ENNReal.log_pos_real h0 ht, ← EReal.coe_mul, ← EReal.coe_neg]
  congr 1
  ring

lemma bee_zero (k : ℕ) : blockErrorExponent k 0 = ⊤ := by
  unfold blockErrorExponent perBlock
  rw [ENNReal.log_zero, EReal.coe_mul_bot_of_pos (by positivity), EReal.neg_bot]

lemma bee_top (k : ℕ) : blockErrorExponent k ⊤ = ⊥ := by
  unfold blockErrorExponent perBlock
  rw [ENNReal.log_top, EReal.coe_mul_top_of_pos (by positivity), EReal.neg_top]

lemma bee_lt (k : ℕ) (q : ℝ≥0∞) (r : ℝ) :
    blockErrorExponent k q < (r : EReal) ↔
      ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * r))) < q := by
  by_cases h0 : q = 0
  · subst h0; simp [bee_zero]
  by_cases ht : q = ⊤
  · subst ht; simp [bee_top]
  rw [bee_real k q h0 ht, EReal.coe_lt_coe_iff,
    ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le ht]
  have hn : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hq : 0 < q.toReal := ENNReal.toReal_pos h0 ht
  rw [← Real.lt_log_iff_exp_lt hq, div_lt_iff₀ hn]
  constructor <;> intro h <;> linarith

lemma lt_bee (k : ℕ) (q : ℝ≥0∞) (r : ℝ) :
    (r : EReal) < blockErrorExponent k q ↔
      q < ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * r))) := by
  by_cases h0 : q = 0
  · subst h0; simp [bee_zero, Real.exp_pos]
  by_cases ht : q = ⊤
  · subst ht; simp [bee_top]
  rw [bee_real k q h0 ht, EReal.coe_lt_coe_iff,
    ENNReal.lt_ofReal_iff_toReal_lt ht]
  have hn : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hq : 0 < q.toReal := ENNReal.toReal_pos h0 ht
  rw [← Real.log_lt_iff_lt_exp hq, lt_div_iff₀ hn]
  constructor <;> intro h <;> linarith

lemma bee_anti (k : ℕ) {p p' : ℝ≥0∞} (h : p ≤ p') :
    blockErrorExponent k p' ≤ blockErrorExponent k p := by
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  rw [lt_bee] at hz
  exact ((lt_bee k p z).2 (lt_of_le_of_lt h hz)).le

lemma le_add_of (a : ℝ) (Z M : EReal) (h : ∀ s : ℝ, M < s → Z ≤ ((a + s : ℝ) : EReal)) :
    Z ≤ (a : EReal) + M := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have : M < ((z - a : ℝ) : EReal) := by
    by_contra hc
    push Not at hc
    have := add_le_add (le_refl (a : EReal)) hc
    rw [← EReal.coe_add, show a + (z - a) = z by ring] at this
    exact absurd hz (not_lt.2 this)
  have := h _ this
  rwa [show a + (z - a) = z by ring] at this

lemma add_le_of (a : ℝ) (M Z : EReal) (h : ∀ s : ℝ, (s : EReal) < M → ((a + s : ℝ) : EReal) ≤ Z) :
    (a : EReal) + M ≤ Z := by
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have : ((z - a : ℝ) : EReal) < M := by
    by_contra hc
    push Not at hc
    have := add_le_add (le_refl (a : EReal)) hc
    rw [← EReal.coe_add, show a + (z - a) = z by ring] at this
    exact absurd hz (not_lt.2 this)
  have := h _ this
  rwa [show a + (z - a) = z by ring] at this

lemma part1 (P : ℕ → SimpleHypothesisSystem.{u}) (S : LikelihoodFamily P) (a : ℝ) :
    zetaUc (S.tests a) ≤ (a : EReal) + etaU (S.tests a) := by
  apply le_add_of
  intro s hs
  have ev : ∀ᶠ k in atTop, blockErrorExponent k (testingTypeI (S.tests a k)) < (s : EReal) :=
    Filter.eventually_lt_of_limsup_lt hs
  apply Filter.limsup_le_of_le (by isBoundedDefault)
  filter_upwards [ev] with k hk
  apply le_of_lt
  rw [bee_lt] at hk ⊢
  have hK := K1 (P k) k a (S.tests a k) (S.valid a k)
  by_contra hc
  push Not at hc
  have h2 := mul_le_mul_right hc (ENNReal.ofReal (Real.exp (((k : ℝ) + 1) * a)))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at h2
  have : ((k : ℝ) + 1) * a + -(((k : ℝ) + 1) * (a + s)) = -(((k : ℝ) + 1) * s) := by ring
  rw [this] at h2
  exact absurd (hk.trans_le (hK.trans h2)) (lt_irrefl _)

lemma p_mono (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) (k : ℕ) {b' b : ℝ} (h : b' ≤ b) :
    testingTypeI (S.tests b' k) ≤ testingTypeI (S.tests b k) := by
  rcases h.eq_or_lt with h | h
  · rw [h]
  have Ka := key (P k) k b' (S.tests b' k) (S.tests b k) (S.valid b' k)
  have Kb := key (P k) k b (S.tests b k) (S.tests b' k) (S.valid b k)
  have q1 := le_one (P k) (hP.2 k).2 (S.tests b k)
  have q2 := le_one (P k) (hP.2 k).2 (S.tests b' k)
  have p1 := K1 (P k) k b (S.tests b k) (S.valid b k)
  have p2 := K1 (P k) k b' (S.tests b' k) (S.valid b' k)
  set q := testingTypeII (testRejection (S.tests b k))
  set q' := testingTypeII (testRejection (S.tests b' k))
  set p := testingTypeI (S.tests b k)
  set p' := testingTypeI (S.tests b' k)
  set c := Real.exp (((k : ℝ) + 1) * b)
  set c' := Real.exp (((k : ℝ) + 1) * b')
  have hcc : c' < c := Real.exp_lt_exp.2 (by
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    nlinarith)
  have hq : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top q1
  have hq' : q' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top q2
  have hp : p ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq) p1
  have hp' : p' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq') p2
  have Ka' := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 Ka
  have Kb' := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 Kb
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at Ka' Kb'
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hc0' : 0 < c' := Real.exp_pos _
  simp only [ENNReal.toReal_mul] at Ka' Kb'
  rw [ENNReal.toReal_ofReal hc0'.le] at Ka'
  rw [ENNReal.toReal_ofReal hc0] at Kb'
  rw [← ENNReal.toReal_le_toReal hp' hp]
  have hQ : q'.toReal ≤ q.toReal := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith [Real.exp_pos (((k : ℝ) + 1) * b')]

lemma etaL_anti (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) {b' b : ℝ} (h : b' ≤ b) :
    etaL (S.tests b) ≤ etaL (S.tests b') := by
  exact Filter.liminf_le_liminf <| Filter.Eventually.of_forall fun k => bee_anti k (p_mono P hP S k h)

lemma core (P : ℕ → SimpleHypothesisSystem.{u}) (S : LikelihoodFamily P) (a e s : ℝ)
    (hs : (s : EReal) < etaL (S.tests (a + e)))
    (hlt : zetaUc (S.tests (a + e)) < zetaUc (S.tests (a - e))) :
    (((a - e + s : ℝ)) : EReal) ≤ zetaUc (S.tests (a + e)) := by
  by_contra hcon
  push Not at hcon
  have hm : zetaUc (S.tests (a + e)) <
      min (zetaUc (S.tests (a - e))) (((a - e + s : ℝ)) : EReal) := lt_min hlt hcon
  obtain ⟨r1, hr1, hr1m⟩ := EReal.lt_iff_exists_real_btwn.1 hm
  obtain ⟨r2, hr12, hr2m⟩ := EReal.lt_iff_exists_real_btwn.1 hr1m
  have hr12' : r1 < r2 := EReal.coe_lt_coe_iff.1 hr12
  have hr2a : r2 < zetaUc (S.tests (a - e)) := lt_of_lt_of_le hr2m (min_le_left _ _)
  have hr2b : r2 < a - e + s := EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le hr2m (min_le_right _ _))
  have ev1 : ∀ᶠ k in atTop, blockErrorExponent k
      (testingTypeII (testRejection (S.tests (a + e) k))) < (r1 : EReal) :=
    Filter.eventually_lt_of_limsup_lt hr1
  have fr2 : ∃ᶠ k in atTop, (r2 : EReal) < blockErrorExponent k
      (testingTypeII (testRejection (S.tests (a - e) k))) :=
    Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hr2a
  have ev3 : ∀ᶠ k in atTop, (s : EReal) < blockErrorExponent k (testingTypeI (S.tests (a + e) k)) :=
    Filter.eventually_lt_of_lt_liminf hs
  have ev4 : ∀ᶠ k : ℕ in atTop, 1 / (r2 - r1) ≤ (k : ℝ) :=
    (Filter.eventually_ge_atTop ⌈1 / (r2 - r1)⌉₊).mono fun k hk =>
      (Nat.le_ceil _).trans (by exact_mod_cast hk)
  obtain ⟨k, h2, h1, h3, h4⟩ := (fr2.and_eventually (ev1.and (ev3.and ev4))).exists
  rw [bee_lt] at h1
  rw [lt_bee] at h2 h3
  set n : ℝ := (k : ℝ) + 1 with hn
  have hn0 : 0 < n := by positivity
  have K := key (P k) k (a - e) (S.tests (a - e) k) (S.tests (a + e) k) (S.valid (a - e) k)
  set c := Real.exp (((k : ℝ) + 1) * (a - e))
  have hc0 : 0 < c := Real.exp_pos _
  have K2 : ENNReal.ofReal c * testingTypeII (testRejection (S.tests (a + e) k)) ≤
      testingTypeI (S.tests (a + e) k) +
        ENNReal.ofReal c * testingTypeII (testRejection (S.tests (a - e) k)) :=
    le_trans le_add_self K
  have L : ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-(n * r1))) <
      ENNReal.ofReal c * testingTypeII (testRejection (S.tests (a + e) k)) :=
    ENNReal.mul_right_strictMono (by simpa using hc0) ENNReal.ofReal_ne_top h1
  have U : testingTypeI (S.tests (a + e) k) +
        ENNReal.ofReal c * testingTypeII (testRejection (S.tests (a - e) k)) ≤
      ENNReal.ofReal (Real.exp (-(n * s))) +
        ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-(n * r2))) := by
    gcongr
  have T := lt_of_lt_of_le L (K2.trans U)
  rw [← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_mul hc0.le,
    ← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity),
    ENNReal.ofReal_lt_ofReal_iff (by positivity)] at T
  -- real contradiction
  have hcexp : c = Real.exp (n * (a - e)) := rfl
  rw [hcexp, ← Real.exp_add, ← Real.exp_add] at T
  have hs' : Real.exp (-(n * s)) < Real.exp (n * (a - e) + -(n * r2)) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have hsplit : Real.exp (n * (a - e) + -(n * r1)) =
      Real.exp (n * (a - e) + -(n * r2)) * Real.exp (n * (r2 - r1)) := by
    rw [← Real.exp_add]; ring_nf
  have hbig : 2 ≤ Real.exp (n * (r2 - r1)) := by
    have h5 : 1 ≤ n * (r2 - r1) := by
      have hd : 0 < r2 - r1 := by linarith
      rw [div_le_iff₀ hd] at h4
      nlinarith
    have := Real.add_one_le_exp (n * (r2 - r1))
    linarith
  have hpos := Real.exp_pos (n * (a - e) + -(n * r2))
  rw [hsplit] at T
  nlinarith

theorem part2 (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) (a : ℝ)
    (hdec : ∀ e : ℝ, 0 < e → zetaUc (S.tests (a + e)) < zetaUc (S.tests (a - e))) :
    (a : EReal) + decreasingRight (fun b => etaL (S.tests b)) a ≤
      decreasingRight (fun b => zetaUc (S.tests b)) a := by
  apply add_le_of
  intro s hs
  obtain ⟨z, ⟨b, hab, rfl⟩, hsz⟩ := (lt_sSup_iff).1 hs
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro t ht
  have ht' : t < a + s := EReal.coe_lt_coe_iff.1 ht
  set e := min (a + s - t) (b - a) / 2 with he
  have he0 : 0 < e := by
    have : 0 < min (a + s - t) (b - a) := lt_min (by linarith) (by linarith)
    positivity
  have he1 : e ≤ (a + s - t) / 2 := by
    rw [he]; gcongr; exact min_le_left _ _
  have he2 : e ≤ (b - a) / 2 := by
    rw [he]; gcongr; exact min_le_right _ _
  have hsa : (s : EReal) < etaL (S.tests (a + e)) :=
    lt_of_lt_of_le hsz (etaL_anti P hP S (by linarith))
  have hc := core P S a e s hsa (hdec e he0)
  have hZ : zetaUc (S.tests (a + e)) ≤ decreasingRight (fun b => zetaUc (S.tests b)) a :=
    le_sSup ⟨a + e, by linarith, rfl⟩
  refine le_trans ?_ (hc.trans hZ)
  exact EReal.coe_le_coe_iff.2 (by linarith)

end P46Aux

/-- Lemma 3, PDF p.15: (76) uses etaU, whereas (77) uses etaL at a decreasing point. -/
theorem solution (P : ℕ → SimpleHypothesisSystem.{u}) (hP : SwitchedNormalization P)
    (S : LikelihoodFamily P) (a : ℝ) :
    zetaUc (S.tests a) ≤ (a : EReal) + etaU (S.tests a) ∧
    ((∀ e : ℝ, 0 < e → zetaUc (S.tests (a + e)) < zetaUc (S.tests (a - e))) →
      (a : EReal) + decreasingRight (fun b => etaL (S.tests b)) a ≤
        decreasingRight (fun b => zetaUc (S.tests b)) a) :=
  ⟨P46Aux.part1 P S a, P46Aux.part2 P hP S a⟩

end
