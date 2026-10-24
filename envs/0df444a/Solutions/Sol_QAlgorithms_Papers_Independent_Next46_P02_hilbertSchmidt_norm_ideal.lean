-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P02.hilbertSchmidt_norm_ideal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:27:21.936988+00:00
-- url     : https://prove2.me/submissions/69597b24-d164-4c99-a6d4-b445067025e6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology ENNReal

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

lemma X7A14_minkowski {I : Type*} (b : HilbertBasis I F H) (S T : H →L[F] H)
    (hS : Summable (fun i => ‖S (b i)‖ ^ 2)) (hT : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    Summable (fun i => ‖(S + T) (b i)‖ ^ 2) ∧
      Real.sqrt (∑' i, ‖(S + T) (b i)‖ ^ 2) ≤
        Real.sqrt (∑' i, ‖S (b i)‖ ^ 2) + Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
  have hS' : Summable (fun i => ‖S (b i)‖ ^ (2:ℝ)) := by simpa [Real.rpow_two] using hS
  have hT' : Summable (fun i => ‖T (b i)‖ ^ (2:ℝ)) := by simpa [Real.rpow_two] using hT
  obtain ⟨h1, h2⟩ := Real.Lp_add_le_tsum_of_nonneg (by norm_num : (1:ℝ) ≤ 2)
    (fun i => norm_nonneg (S (b i))) (fun i => norm_nonneg (T (b i))) hS' hT'
  simp only [Real.rpow_two] at h1 h2
  have hle : ∀ i, ‖(S + T) (b i)‖ ^ 2 ≤ (‖S (b i)‖ + ‖T (b i)‖) ^ 2 := fun i => by
    gcongr; exact norm_add_le _ _
  have hsum : Summable (fun i => ‖(S + T) (b i)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hle h1
  refine ⟨hsum, ?_⟩
  simp only [Real.sqrt_eq_rpow]
  refine le_trans ?_ h2
  exact Real.rpow_le_rpow (tsum_nonneg fun i => by positivity) (hsum.tsum_le_tsum hle h1)
    (by norm_num)

lemma X7A14_eq_zero_of_basis {I : Type*} (b : HilbertBasis I F H) (T : H →L[F] H)
    (h : ∀ i, T (b i) = 0) : T = 0 := by
  ext x
  have := (b.hasSum_repr x).mapL T
  simp only [map_smul, h, smul_zero] at this
  simpa using this.unique hasSum_zero

lemma X7A14_summable_inner {I : Type*} (b : HilbertBasis I F H) (S T : H →L[F] H)
    (hS : Summable (fun i => ‖S (b i)‖ ^ 2)) (hT : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    Summable (fun i => inner F (S (b i)) (T (b i))) := by
  refine Summable.of_norm_bounded ((hS.add hT).div_const 2) fun i => ?_
  have h1 := norm_inner_le_norm (𝕜 := F) (S (b i)) (T (b i))
  have h2 := sq_nonneg (‖S (b i)‖ - ‖T (b i)‖)
  nlinarith

lemma X7A14_hsInner_eq (S T : H →L[F] H) :
    hilbertSchmidtInner S T =
      ∑' i : basisIndex F H, inner F (S (referenceBasis i)) (T (referenceBasis i)) := by
  unfold hilbertSchmidtInner basisOperatorTrace basisDiagonal
  congr 1; funext i
  simp [ContinuousLinearMap.adjoint_inner_right]

lemma X7A14_innerProductOn :
    InnerProductOn (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm hilbertSchmidtInner := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [IsHilbertSchmidt]
  · simp [hilbertSchmidtNorm]
  · intro T hT
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    constructor
    · intro h0
      have h0' : ∑' i : basisIndex F H, ‖T (referenceBasis i)‖ ^ 2 = 0 := by
        have := Real.sqrt_eq_zero (tsum_nonneg fun i => by positivity) |>.mp h0
        exact this
      have hz : ∀ i : basisIndex F H, ‖T (referenceBasis i)‖ ^ 2 = 0 := fun i =>
        le_antisymm (h0' ▸ hT.le_tsum i (fun j _ => by positivity)) (by positivity)
      apply X7A14_eq_zero_of_basis (referenceBasis : HilbertBasis (basisIndex F H) F H)
      intro i
      have := hz i
      simpa using this
    · rintro rfl; simp [hilbertSchmidtNorm]
  · intro S T hS hT
    exact X7A14_minkowski _ S T hS hT
  · intro a T hT
    have e : ∀ i : basisIndex F H, ‖(a • T) (referenceBasis i)‖ ^ 2 =
        ‖a‖ ^ 2 * ‖T (referenceBasis i)‖ ^ 2 := fun i => by
      rw [smul_apply, norm_smul, mul_pow]
    refine ⟨?_, ?_⟩
    · unfold IsHilbertSchmidt; simp only [e]; exact hT.mul_left _
    · unfold hilbertSchmidtNorm; simp only [e]
      rw [tsum_mul_left, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  · intro S T _ _
    rw [X7A14_hsInner_eq, X7A14_hsInner_eq, tsum_star]
    congr 1; funext i
    simp
  · intro S T U hS hT hU
    simp only [X7A14_hsInner_eq, add_apply, inner_add_right]
    exact (X7A14_summable_inner _ S T hS hT).tsum_add (X7A14_summable_inner _ S U hS hU)
  · intro a S T _ _
    simp only [X7A14_hsInner_eq, smul_apply, inner_smul_right]
    exact tsum_mul_left
  · intro T hT
    rw [X7A14_hsInner_eq]
    unfold hilbertSchmidtNorm
    rw [Real.sq_sqrt (tsum_nonneg fun i => by positivity)]
    have hs := X7A14_summable_inner _ T T hT hT
    rw [show RCLike.re (∑' i : basisIndex F H, inner F (T (referenceBasis i)) (T (referenceBasis i)))
        = ∑' i : basisIndex F H, RCLike.re (inner F (T (referenceBasis i)) (T (referenceBasis i)))
        from (RCLike.reCLM.map_tsum hs)]
    congr 1; funext i
    simp

lemma X7A14_parseval {J : Type*} (c : HilbertBasis J F H) (v : H) :
    HasSum (fun j => ‖inner F (c j) v‖ ^ 2) (‖v‖ ^ 2) := by
  have h := RCLike.reCLM.hasSum (c.hasSum_inner_mul_inner v v)
  simp only [RCLike.reCLM_apply] at h
  have e : (fun j => ‖inner F (c j) v‖ ^ 2) =
      fun b => RCLike.re (inner F v (c b) * inner F (c b) v) := by
    funext j
    rw [← inner_conj_symm v (c j), RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [e, ← inner_self_eq_norm_sq (𝕜 := F)]
  exact h

lemma X7A14_ennsum {I J : Type*} (b : HilbertBasis I F H) (c : HilbertBasis J F H)
    (A : H →L[F] H) :
    ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) =
      ∑' j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint A) (c j)‖ ^ 2) := by
  have e1 : ∀ v : H, ENNReal.ofReal (‖v‖ ^ 2) = ∑' j, ENNReal.ofReal (‖inner F (c j) v‖ ^ 2) :=
    fun v => by
      rw [← (X7A14_parseval c v).tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (X7A14_parseval c v).summable]
  have e2 : ∀ v : H, ENNReal.ofReal (‖v‖ ^ 2) = ∑' i, ENNReal.ofReal (‖inner F (b i) v‖ ^ 2) :=
    fun v => by
      rw [← (X7A14_parseval b v).tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (X7A14_parseval b v).summable]
  conv_lhs => simp only [e1]
  conv_rhs => simp only [e2]
  rw [ENNReal.tsum_comm]
  congr 1; funext j; congr 1; funext i
  rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]

lemma X7A14_ennsum_basis {I J : Type*} (b : HilbertBasis I F H) (c : HilbertBasis J F H)
    (A : H →L[F] H) :
    ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) = ∑' j, ENNReal.ofReal (‖A (c j)‖ ^ 2) := by
  rw [X7A14_ennsum b b A, X7A14_ennsum c b A]

lemma X7A14_real_of_enn {I : Type*} (g : I → ℝ) (hg : ∀ i, 0 ≤ g i)
    (h : ∑' i, ENNReal.ofReal (g i) ≠ ∞) :
    HasSum g (∑' i, ENNReal.ofReal (g i)).toReal := by
  have hs := ENNReal.summable_toReal h
  simp only [ENNReal.toReal_ofReal (hg _)] at hs
  rw [← ENNReal.ofReal_tsum_of_nonneg hg hs, ENNReal.toReal_ofReal (tsum_nonneg hg)]
  exact hs.hasSum

lemma X7A14_transfer {I J : Type*} (b : HilbertBasis I F H) (c : HilbertBasis J F H)
    (A : H →L[F] H) (hA : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    HasSum (fun j => ‖A (c j)‖ ^ 2) (∑' i, ‖A (b i)‖ ^ 2) := by
  have hb := ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hA
  rw [X7A14_ennsum_basis b c A] at hb
  have hne : ∑' j, ENNReal.ofReal (‖A (c j)‖ ^ 2) ≠ ∞ := by rw [← hb]; exact ENNReal.ofReal_ne_top
  have := X7A14_real_of_enn _ (fun j => by positivity) hne
  rwa [← hb, ENNReal.toReal_ofReal (tsum_nonneg fun i => by positivity)] at this

lemma X7A14_hs_add {S T : H →L[F] H} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S + T) := (X7A14_innerProductOn.1.2.2.2.1 S T hS hT).1

lemma X7A14_hs_smul (a : F) {T : H →L[F] H} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (a • T) := (X7A14_innerProductOn.1.2.2.2.2 a T hT).1

lemma X7A14_key {J : Type*} (c : HilbertBasis J F H) (S T : H →L[F] H)
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    HasSum (fun j => inner F (S (c j)) (T (c j)))
      ((((∑' i : basisIndex F H, ‖(S + T) (referenceBasis i)‖ ^ 2 : ℝ) : F) -
          ((∑' i : basisIndex F H, ‖(S + (-1 : F) • T) (referenceBasis i)‖ ^ 2 : ℝ) : F) +
        (((∑' i : basisIndex F H, ‖(S + (-(RCLike.I : F)) • T) (referenceBasis i)‖ ^ 2 : ℝ) : F) -
          ((∑' i : basisIndex F H, ‖(S + (RCLike.I : F) • T) (referenceBasis i)‖ ^ 2 : ℝ) : F)) *
          RCLike.I) / 4) := by
  have h1 : IsHilbertSchmidt (S + T) := X7A14_hs_add hS hT
  have h2 : IsHilbertSchmidt (S + (-1 : F) • T) := X7A14_hs_add hS (X7A14_hs_smul _ hT)
  have h3 : IsHilbertSchmidt (S + (-(RCLike.I : F)) • T) := X7A14_hs_add hS (X7A14_hs_smul _ hT)
  have h4 : IsHilbertSchmidt (S + (RCLike.I : F) • T) := X7A14_hs_add hS (X7A14_hs_smul _ hT)
  have t1 := (RCLike.hasSum_ofReal (𝕜 := F)).mpr (X7A14_transfer referenceBasis c _ h1)
  have t2 := (RCLike.hasSum_ofReal (𝕜 := F)).mpr (X7A14_transfer referenceBasis c _ h2)
  have t3 := (RCLike.hasSum_ofReal (𝕜 := F)).mpr (X7A14_transfer referenceBasis c _ h3)
  have t4 := (RCLike.hasSum_ofReal (𝕜 := F)).mpr (X7A14_transfer referenceBasis c _ h4)
  have := (((t1.sub t2).add ((t3.sub t4).mul_right RCLike.I)).div_const 4)
  convert this using 1
  funext j
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := F) (S (c j)) (T (c j))]
  simp only [add_apply, smul_apply,
    neg_smul, one_smul, ← sub_eq_add_neg]
  push_cast
  simp only [Pi.sub_apply, Pi.smul_apply]
  all_goals ring

lemma X7A14_hasSum_inner_any {I : Type*} (b : HilbertBasis I F H) (S T : H →L[F] H)
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    HasSum (fun i => inner F (S (b i)) (T (b i))) (hilbertSchmidtInner S T) := by
  have hr := X7A14_key (referenceBasis : HilbertBasis (basisIndex F H) F H) S T hS hT
  rw [X7A14_hsInner_eq, hr.tsum_eq]
  exact X7A14_key b S T hS hT

lemma X7A14_hs_schwarz (S T : H →L[F] H) (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    ‖hilbertSchmidtInner S T‖ ≤ hilbertSchmidtNorm S * hilbertSchmidtNorm T := by
  rw [X7A14_hsInner_eq]
  set r : HilbertBasis (basisIndex F H) F H := referenceBasis
  have hS' : Summable (fun i => ‖S (r i)‖ ^ (2:ℝ)) := by
    unfold IsHilbertSchmidt at hS; simpa [Real.rpow_two] using hS
  have hT' : Summable (fun i => ‖T (r i)‖ ^ (2:ℝ)) := by
    unfold IsHilbertSchmidt at hT; simpa [Real.rpow_two] using hT
  obtain ⟨hsum, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg (S (r i))) (fun i => norm_nonneg (T (r i))) hS' hT'
  have hn : Summable (fun i => ‖inner F (S (r i)) (T (r i))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => norm_inner_le_norm _ _) hsum
  calc ‖∑' i, inner F (S (r i)) (T (r i))‖ ≤ ∑' i, ‖inner F (S (r i)) (T (r i))‖ :=
        norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i, ‖S (r i)‖ * ‖T (r i)‖ := hn.tsum_le_tsum (fun i => norm_inner_le_norm _ _) hsum
    _ ≤ _ := hle
    _ = hilbertSchmidtNorm S * hilbertSchmidtNorm T := by
        simp only [hilbertSchmidtNorm, Real.sqrt_eq_rpow, Real.rpow_two, r]

lemma X7A14_trace_adj_self (T : H →L[F] H) (hT : IsHilbertSchmidt T) :
    basisOperatorTrace ((ContinuousLinearMap.adjoint T).comp T) = (hilbertSchmidtNorm T ^ 2 : F) := by
  have : basisOperatorTrace ((ContinuousLinearMap.adjoint T).comp T) = hilbertSchmidtInner T T := rfl
  rw [this, X7A14_hsInner_eq, hilbertSchmidtNorm, ← RCLike.ofReal_pow, Real.sq_sqrt (tsum_nonneg fun i => by positivity),
    RCLike.ofReal_tsum]
  congr 1; funext i
  rw [inner_self_eq_norm_sq_to_K]
  push_cast; ring

lemma X7A14_hilbertSchmidt_inner_product :
    InnerProductOn (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm hilbertSchmidtInner ∧
    (∀ {I : Type*} (b : HilbertBasis I F H) (S T : H →L[F] H),
      IsHilbertSchmidt S → IsHilbertSchmidt T →
      HasSum (fun i => inner F (S (b i)) (T (b i))) (hilbertSchmidtInner S T) ∧
      ‖hilbertSchmidtInner S T‖ ≤ hilbertSchmidtNorm S * hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, IsHilbertSchmidt T →
      basisOperatorTrace ((ContinuousLinearMap.adjoint T).comp T) = (hilbertSchmidtNorm T ^ 2 : F)) :=
  ⟨X7A14_innerProductOn, fun b S T hS hT => ⟨X7A14_hasSum_inner_any b S T hS hT,
    X7A14_hs_schwarz S T hS hT⟩, X7A14_trace_adj_self⟩

lemma X7A14_transfer_adj {I J : Type*} (b : HilbertBasis I F H) (c : HilbertBasis J F H)
    (A : H →L[F] H) (hA : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    HasSum (fun j => ‖(ContinuousLinearMap.adjoint A) (c j)‖ ^ 2) (∑' i, ‖A (b i)‖ ^ 2) := by
  have hb := ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hA
  rw [X7A14_ennsum b c A] at hb
  have hne : ∑' j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint A) (c j)‖ ^ 2) ≠ ∞ := by
    rw [← hb]; exact ENNReal.ofReal_ne_top
  have := X7A14_real_of_enn _ (fun j => by positivity) hne
  rwa [← hb, ENNReal.toReal_ofReal (tsum_nonneg fun i => by positivity)] at this

lemma X7A14_hs_adj (T : H →L[F] H) :
    (IsHilbertSchmidt (ContinuousLinearMap.adjoint T) ↔ IsHilbertSchmidt T) ∧
      (IsHilbertSchmidt T → hilbertSchmidtNorm T = hilbertSchmidtNorm (ContinuousLinearMap.adjoint T)) := by
  refine ⟨⟨fun h => ?_, fun h => (X7A14_transfer_adj referenceBasis referenceBasis T h).summable⟩,
    fun h => ?_⟩
  · have := (X7A14_transfer_adj referenceBasis referenceBasis _ h).summable
    rwa [ContinuousLinearMap.adjoint_adjoint] at this
  · unfold hilbertSchmidtNorm
    rw [(X7A14_transfer_adj referenceBasis referenceBasis T h).tsum_eq]

lemma X7A14_op_bound (A : H →L[F] H) (hA : IsHilbertSchmidt A) (x : H) :
    ‖A x‖ ≤ hilbertSchmidtNorm A * ‖x‖ := by
  set r : HilbertBasis (basisIndex F H) F H := referenceBasis
  have hadj := X7A14_transfer_adj r r A hA
  have hp := X7A14_parseval r (A x)
  have hle : ∀ j, ‖inner F (r j) (A x)‖ ^ 2 ≤ ‖(ContinuousLinearMap.adjoint A) (r j)‖ ^ 2 * ‖x‖ ^ 2 :=
    fun j => by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← mul_pow]
      gcongr
      exact norm_inner_le_norm _ _
  have h2 : ‖A x‖ ^ 2 ≤ (hilbertSchmidtNorm A * ‖x‖) ^ 2 := by
    rw [← hp.tsum_eq, mul_pow, hilbertSchmidtNorm, Real.sq_sqrt (tsum_nonneg fun i => by positivity),
      ← hadj.tsum_eq, ← tsum_mul_right]
    exact hp.summable.tsum_le_tsum hle (hadj.summable.mul_right _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by unfold hilbertSchmidtNorm; positivity)
    two_ne_zero).mp h2

lemma X7A14_opNorm_le (A : H →L[F] H) (hA : IsHilbertSchmidt A) : ‖A‖ ≤ hilbertSchmidtNorm A :=
  ContinuousLinearMap.opNorm_le_bound _ (by unfold hilbertSchmidtNorm; positivity)
    (X7A14_op_bound A hA)

lemma X7A14_comp_left (S T : H →L[F] H) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S.comp T) ∧ hilbertSchmidtNorm (S.comp T) ≤ ‖S‖ * hilbertSchmidtNorm T := by
  have hle : ∀ i : basisIndex F H, ‖(S.comp T) (referenceBasis i)‖ ^ 2 ≤
      ‖S‖ ^ 2 * ‖T (referenceBasis i)‖ ^ 2 := fun i => by
    rw [← mul_pow]; gcongr; exact S.le_opNorm _
  have hs : IsHilbertSchmidt (S.comp T) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hle (hT.mul_left _)
  refine ⟨hs, ?_⟩
  unfold hilbertSchmidtNorm
  rw [← Real.sqrt_sq (norm_nonneg S), ← Real.sqrt_mul (by positivity), ← tsum_mul_left]
  exact Real.sqrt_le_sqrt (hs.tsum_le_tsum hle (hT.mul_left _))

lemma X7A14_comp_right (S T : H →L[F] H) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (T.comp S) ∧ hilbertSchmidtNorm (T.comp S) ≤ ‖S‖ * hilbertSchmidtNorm T := by
  have hT' : IsHilbertSchmidt (ContinuousLinearMap.adjoint T) := (X7A14_hs_adj T).1.mpr hT
  obtain ⟨h1, h2⟩ := X7A14_comp_left (ContinuousLinearMap.adjoint S) _ hT'
  have e : (ContinuousLinearMap.adjoint S).comp (ContinuousLinearMap.adjoint T) =
      ContinuousLinearMap.adjoint (T.comp S) := (ContinuousLinearMap.adjoint_comp T S).symm
  rw [e] at h1 h2
  have hTS : IsHilbertSchmidt (T.comp S) := (X7A14_hs_adj _).1.mp h1
  refine ⟨hTS, ?_⟩
  rw [(X7A14_hs_adj _).2 hTS]
  rw [← (X7A14_hs_adj T).2 hT] at h2
  simpa only [LinearIsometryEquiv.norm_map] using h2

/-- finite truncation -/
def X7A14_trunc (T : H →L[F] H) (s : Finset (basisIndex F H)) : H →L[F] H :=
  ∑ i ∈ s, (ContinuousLinearMap.toSpanSingleton F (T (referenceBasis i))).comp
    (innerSL F ((referenceBasis : HilbertBasis (basisIndex F H) F H) i))

lemma X7A14_trunc_compact (T : H →L[F] H) (s : Finset (basisIndex F H)) :
    IsCompactOperator (X7A14_trunc T s) := by
  unfold X7A14_trunc
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ContinuousLinearMap.coe_add']
    refine IsCompactOperator.add ?_ ih
    exact (isCompactOperator_of_locallyCompactSpace_dom
      (innerSL F ((referenceBasis : HilbertBasis (basisIndex F H) F H) a))).clm_comp
      (ContinuousLinearMap.toSpanSingleton F (T (referenceBasis a)))

lemma X7A14_trunc_apply (T : H →L[F] H) (s : Finset (basisIndex F H)) (j : basisIndex F H) :
    (T - X7A14_trunc T s) (referenceBasis j) = if j ∈ s then 0 else T (referenceBasis j) := by
  have ho := (referenceBasis : HilbertBasis (basisIndex F H) F H).orthonormal
  rw [orthonormal_iff_ite] at ho
  simp only [X7A14_trunc, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ho, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']
  split_ifs <;> simp

lemma X7A14_compact (T : H →L[F] H) (hT : IsHilbertSchmidt T) : IsCompactOperator T := by
  refine isCompactOperator_of_tendsto (l := atTop) (F := X7A14_trunc T) ?_
    (Eventually.of_forall (X7A14_trunc_compact T))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set f : basisIndex F H → ℝ :=
    fun i => ‖T ((referenceBasis : HilbertBasis (basisIndex F H) F H) i)‖ ^ 2
  have hf := hT.hasSum
  -- bound
  have hb : ∀ s, ‖X7A14_trunc T s - T‖ ≤ Real.sqrt (∑' i, f i - ∑ i ∈ s, f i) := fun s => by
    rw [norm_sub_rev]
    have hsum : HasSum (fun j : basisIndex F H => ‖(T - X7A14_trunc T s) (referenceBasis j)‖ ^ 2)
        (∑' i, f i - ∑ i ∈ s, f i) := by
      have h2 : HasSum (fun j => if j ∈ s then f j else 0) (∑ i ∈ s, f i) := by
        have : HasSum (fun j => if j ∈ s then f j else 0) (∑ b ∈ s, if b ∈ s then f b else 0) :=
          hasSum_sum_of_ne_finset_zero (fun j hj => if_neg hj)
        rwa [Finset.sum_congr rfl (fun b hb => if_pos hb)] at this
      have e : (fun j : basisIndex F H => ‖(T - X7A14_trunc T s) (referenceBasis j)‖ ^ 2) =
          fun j => f j - (if j ∈ s then f j else 0) := by
        funext j
        rw [X7A14_trunc_apply]
        split_ifs <;> simp [f]
      rw [e]
      exact hf.sub h2
    have hHS : IsHilbertSchmidt (T - X7A14_trunc T s) := hsum.summable
    refine le_trans (X7A14_opNorm_le _ hHS) (le_of_eq ?_)
    unfold hilbertSchmidtNorm
    rw [hsum.tsum_eq]
  have ht : Tendsto (fun s : Finset (basisIndex F H) => Real.sqrt (∑' i, f i - ∑ i ∈ s, f i))
      atTop (𝓝 0) := by
    have : Tendsto (fun s : Finset (basisIndex F H) => ∑' i, f i - ∑ i ∈ s, f i) atTop (𝓝 0) := by
      have h1 : Tendsto (fun s : Finset (basisIndex F H) => ∑ i ∈ s, f i) atTop
          (𝓝 (∑' i, f i)) := hf
      have := (tendsto_const_nhds (x := ∑' i, f i)).sub h1
      simpa using this
    simpa using this.sqrt
  exact squeeze_zero (fun s => norm_nonneg _) hb ht

lemma X7A14_hilbertSchmidt_norm_ideal :
    NormOn (F := F) (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm ∧
    (∀ (S T : H →L[F] H), IsHilbertSchmidt T →
      IsHilbertSchmidt (S.comp T) ∧ IsHilbertSchmidt (T.comp S) ∧
      max (hilbertSchmidtNorm (S.comp T)) (hilbertSchmidtNorm (T.comp S)) ≤
        ‖S‖ * hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, IsHilbertSchmidt T → IsCompactOperator T ∧ ‖T‖ ≤ hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, (IsHilbertSchmidt (ContinuousLinearMap.adjoint T) ↔ IsHilbertSchmidt T) ∧
      (IsHilbertSchmidt T → hilbertSchmidtNorm T = hilbertSchmidtNorm (ContinuousLinearMap.adjoint T))) := by
  refine ⟨X7A14_innerProductOn.1, fun S T hT => ?_, fun T hT => ⟨X7A14_compact T hT,
    X7A14_opNorm_le T hT⟩, X7A14_hs_adj⟩
  obtain ⟨h1, h2⟩ := X7A14_comp_left S T hT
  obtain ⟨h3, h4⟩ := X7A14_comp_right S T hT
  exact ⟨h1, h3, max_le h2 h4⟩

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end

noncomputable section

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

open QAlgorithms.Papers.Independent.Next46.P02 in
theorem solution :
    NormOn (F := F) (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm ∧
    (∀ (S T : H →L[F] H), IsHilbertSchmidt T →
      IsHilbertSchmidt (S.comp T) ∧ IsHilbertSchmidt (T.comp S) ∧
      max (hilbertSchmidtNorm (S.comp T)) (hilbertSchmidtNorm (T.comp S)) ≤
        ‖S‖ * hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, IsHilbertSchmidt T → IsCompactOperator T ∧ ‖T‖ ≤ hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, (IsHilbertSchmidt (ContinuousLinearMap.adjoint T) ↔ IsHilbertSchmidt T) ∧
      (IsHilbertSchmidt T → hilbertSchmidtNorm T = hilbertSchmidtNorm (ContinuousLinearMap.adjoint T))) :=
  X7A14_hilbertSchmidt_norm_ideal

end Hilbert

end
