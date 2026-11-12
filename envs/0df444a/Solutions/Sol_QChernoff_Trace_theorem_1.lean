-- Prove2me | solution 1 for QChernoff.Trace.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T08:26:51.36212+00:00
-- url     : https://prove2.me/submissions/9ea0472f-8b43-4b94-9c73-3ee11c0d7f27

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power

/-! 84f95c10 QChernoff.Trace.theorem_1 -- trace library, stage 1 (ENNReal Hilbert-Schmidt sums).
Plan: scratch/decomp/84f95c10.plan.md -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal InnerProductSpace ComplexOrder

namespace QCT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- ENNReal Hilbert-Schmidt square sum of `Z` in the basis `b`. -/
noncomputable def hsSq {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ((‖Z (b i)‖₊ : ℝ≥0∞)) ^ 2

/-- Parseval in ENNReal form. -/
lemma parseval_enn {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    ∑' i, ((‖⟪b i, x⟫_ℂ‖₊ : ℝ≥0∞)) ^ 2 = ((‖x‖₊ : ℝ≥0∞)) ^ 2 := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  have h2 : HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
    simpa [b.repr_apply_apply, LinearIsometryEquiv.norm_map] using h
  have h3 : HasSum (fun i => ‖⟪b i, x⟫_ℂ‖₊ ^ 2) (‖x‖₊ ^ 2) := by
    rw [← NNReal.hasSum_coe]; simpa using h2
  have h4 := ENNReal.hasSum_coe.mpr h3
  simpa [ENNReal.coe_pow] using h4.tsum_eq

/-- Swap lemma: the HS square sum of `Z` in `b` equals that of `Z†` in `b'`. -/
lemma hsSq_adjoint {ι κ : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H)
    (Z : H →L[ℂ] H) : hsSq b Z = hsSq b' (ContinuousLinearMap.adjoint Z) := by
  unfold hsSq
  calc ∑' i, ((‖Z (b i)‖₊ : ℝ≥0∞)) ^ 2
      = ∑' i, ∑' j, ((‖⟪b' j, Z (b i)⟫_ℂ‖₊ : ℝ≥0∞)) ^ 2 := by
        congr 1; ext i; rw [parseval_enn b']
    _ = ∑' j, ∑' i, ((‖⟪b' j, Z (b i)⟫_ℂ‖₊ : ℝ≥0∞)) ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ((‖⟪b i, ContinuousLinearMap.adjoint Z (b' j)⟫_ℂ‖₊ : ℝ≥0∞)) ^ 2 := by
        congr 1; ext j; congr 1; ext i
        rw [ContinuousLinearMap.adjoint_inner_right]
        congr 2; exact NNReal.eq (norm_inner_symm _ _)
    _ = ∑' j, ((‖ContinuousLinearMap.adjoint Z (b' j)‖₊ : ℝ≥0∞)) ^ 2 := by
        congr 1; ext j; rw [parseval_enn b]

/-- Basis independence of the HS square sum. -/
lemma hsSq_basis {ι κ : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H)
    (Z : H →L[ℂ] H) : hsSq b Z = hsSq b' Z := by
  rw [hsSq_adjoint b b' Z, hsSq_adjoint b' b' (ContinuousLinearMap.adjoint Z),
    ContinuousLinearMap.adjoint_adjoint]

/-- T2: the diagonal of a positive operator is a square norm of its square root. -/
lemma re_inner_eq_sqrt {C : H →L[ℂ] H} (hC : 0 ≤ C) (x : H) :
    RCLike.re ⟪x, C x⟫_ℂ = ‖CFC.sqrt C x‖ ^ 2 := by
  have hs : IsSelfAdjoint (CFC.sqrt C) := (CFC.sqrt_nonneg C).isSelfAdjoint
  have hC' : C = CFC.sqrt C * CFC.sqrt C := (CFC.sqrt_mul_sqrt_self C hC).symm
  conv_lhs => rw [hC']
  rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left, hs.adjoint_eq]
  exact inner_self_eq_norm_sq _

/-- The positive trace `tau_b(C) = sum ||sqrt C b_i||^2` in `[0, top]`. -/
noncomputable def tau {ι : Type*} (b : HilbertBasis ι ℂ H) (C : H →L[ℂ] H) : ℝ≥0∞ :=
  hsSq b (CFC.sqrt C)

lemma tau_basis {ι κ : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H)
    (C : H →L[ℂ] H) : tau b C = tau b' C := hsSq_basis b b' _

/-- T2': diagonal monotonicity in the Loewner order. -/
lemma re_inner_mono {C C' : H →L[ℂ] H} (h : C ≤ C') (x : H) :
    RCLike.re ⟪x, C x⟫_ℂ ≤ RCLike.re ⟪x, C' x⟫_ℂ := by
  have hp : (C' - C).IsPositive := (ContinuousLinearMap.le_def C C').mp h
  have := hp.re_inner_nonneg_right x
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub] at this
  linarith

/-! Stage 2: the diagonal positive trace `tauD` and the operator-monotone chain. -/

/-- Diagonal positive trace: `sum ofReal (re <b_i, C b_i>)`. -/
noncomputable def tauD {ι : Type*} (b : HilbertBasis ι ℂ H) (C : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, C (b i)⟫_ℂ)

lemma re_inner_star_mul (Z : H →L[ℂ] H) (x : H) :
    RCLike.re ⟪x, (star Z * Z) x⟫_ℂ = ‖Z x‖ ^ 2 := by
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq _

lemma ofReal_sq_norm (x : H) : ENNReal.ofReal (‖x‖ ^ 2) = ((‖x‖₊ : ℝ≥0∞)) ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

lemma tauD_star_mul {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H) :
    tauD b (star Z * Z) = hsSq b Z := by
  unfold tauD hsSq
  congr 1; ext i; rw [re_inner_star_mul, ofReal_sq_norm]

lemma tauD_star_comm {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H) :
    tauD b (star Z * Z) = tauD b (Z * star Z) := by
  have h : Z * star Z = star (star Z) * star Z := by rw [star_star]
  rw [h, tauD_star_mul, tauD_star_mul, hsSq_adjoint b b Z, ContinuousLinearMap.star_eq_adjoint]

lemma eq_star_sqrt {C : H →L[ℂ] H} (hC : 0 ≤ C) : C = star (CFC.sqrt C) * CFC.sqrt C := by
  rw [(CFC.sqrt_nonneg C).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self C hC]

lemma tauD_basis {ι κ : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H)
    {C : H →L[ℂ] H} (hC : 0 ≤ C) : tauD b C = tauD b' C := by
  rw [eq_star_sqrt hC, tauD_star_mul, tauD_star_mul, hsSq_basis]

lemma re_inner_nonneg {C : H →L[ℂ] H} (hC : 0 ≤ C) (x : H) : 0 ≤ RCLike.re ⟪x, C x⟫_ℂ := by
  have := re_inner_mono hC x
  simpa using this

lemma tauD_add {ι : Type*} (b : HilbertBasis ι ℂ H) {C C' : H →L[ℂ] H} (hC : 0 ≤ C)
    (hC' : 0 ≤ C') : tauD b (C + C') = tauD b C + tauD b C' := by
  unfold tauD
  rw [← ENNReal.tsum_add]
  congr 1; ext i
  rw [ContinuousLinearMap.add_apply, inner_add_right, map_add,
    ENNReal.ofReal_add (re_inner_nonneg hC _) (re_inner_nonneg hC' _)]

lemma tauD_mono {ι : Type*} (b : HilbertBasis ι ℂ H) {C C' : H →L[ℂ] H} (h : C ≤ C') :
    tauD b C ≤ tauD b C' :=
  ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (re_inner_mono h _)

lemma tauD_conj_swap {ι : Type*} (b : HilbertBasis ι ℂ H) {x y : H →L[ℂ] H}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    tauD b (x * (y * y) * x) = tauD b (y * (x * x) * y) := by
  have h := tauD_star_comm b (y * x)
  rw [star_mul, hx.star_eq, hy.star_eq] at h
  simpa only [mul_assoc] using h

lemma conj_nonneg' {x y : H →L[ℂ] H} (hx : IsSelfAdjoint x) (hy : 0 ≤ y) : 0 ≤ x * y * x := by
  simpa [hx.star_eq] using star_left_conjugate_nonneg hy x

lemma conj_le' {x y z : H →L[ℂ] H} (hx : IsSelfAdjoint x) (h : y ≤ z) :
    x * y * x ≤ x * z * x := by
  simpa [hx.star_eq] using star_left_conjugate_le_conjugate h x

lemma rpow_add_pos {a : H →L[ℂ] H} {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    a ^ (x + y) = a ^ x * a ^ y := by
  lift x to ℝ≥0 using hx.le
  lift y to ℝ≥0 using hy.le
  have hx' : (0 : ℝ≥0) < x := by exact_mod_cast hx
  have hy' : (0 : ℝ≥0) < y := by exact_mod_cast hy
  rw [← NNReal.coe_add, ← CFC.nnrpow_eq_rpow (add_pos hx' hy'), ← CFC.nnrpow_eq_rpow hx',
    ← CFC.nnrpow_eq_rpow hy', CFC.nnrpow_add hx' hy']

lemma rpow_sandwich {a : H →L[ℂ] H} (ha : 0 ≤ a) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t = 1) : a = a ^ (s / 2) * a ^ t * a ^ (s / 2) := by
  have h1 : (1 : ℝ) = s / 2 + t + s / 2 := by linarith
  conv_lhs => rw [← CFC.rpow_one a ha, h1, rpow_add_pos (by positivity) (by positivity),
    rpow_add_pos (by positivity) ht]

lemma rpow_half_sq {a : H →L[ℂ] H} {s : ℝ} (hs : 0 < s) : a ^ s = a ^ (s / 2) * a ^ (s / 2) := by
  rw [← rpow_add_pos (by positivity) (by positivity)]; congr 1; ring

/-- The Audenaert chain in the positive trace: `tau A <= tau(A^{s/2} B^t A^{s/2}) + tau P`
whenever `A <= B + P`, all positive, `tau B` finite, `s, t > 0`, `s + t = 1`. -/
theorem chain {ι : Type*} (b : HilbertBasis ι ℂ H) {A B P : H →L[ℂ] H} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hABP : A ≤ B + P) (hBfin : tauD b B ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    tauD b A ≤ tauD b (A ^ (s / 2) * B ^ t * A ^ (s / 2)) + tauD b P := by
  set D := B + P with hDdef
  have hD : 0 ≤ D := add_nonneg hB hP
  have hBD : B ≤ D := le_add_of_nonneg_right hP
  have hBt : B ^ t ≤ D ^ t := CFC.rpow_le_rpow ⟨ht.le, by linarith⟩ hBD
  have hAs : A ^ s ≤ D ^ s := CFC.rpow_le_rpow ⟨hs.le, by linarith⟩ hABP
  have hAt : A ^ t ≤ D ^ t := CFC.rpow_le_rpow ⟨ht.le, by linarith⟩ hABP
  have hBs : B ^ s ≤ D ^ s := CFC.rpow_le_rpow ⟨hs.le, by linarith⟩ hBD
  set E := D ^ t - B ^ t with hEdef
  have hE : 0 ≤ E := sub_nonneg.mpr hBt
  set a := A ^ (s / 2)
  set d := D ^ (s / 2)
  set g := B ^ (t / 2)
  set e := CFC.sqrt E
  have ha : IsSelfAdjoint a := CFC.rpow_nonneg.isSelfAdjoint
  have hd : IsSelfAdjoint d := CFC.rpow_nonneg.isSelfAdjoint
  have hg : IsSelfAdjoint g := CFC.rpow_nonneg.isSelfAdjoint
  have he : IsSelfAdjoint e := (CFC.sqrt_nonneg E).isSelfAdjoint
  have hee : e * e = E := CFC.sqrt_mul_sqrt_self E hE
  have hBt0 : 0 ≤ B ^ t := CFC.rpow_nonneg
  have hDt0 : 0 ≤ D ^ t := CFC.rpow_nonneg
  -- step 1-2
  have s1 : tauD b A ≤ tauD b (a * B ^ t * a) + tauD b (a * E * a) := by
    have hA1 := rpow_sandwich hA hs ht hst
    have hle : A ≤ a * B ^ t * a + a * E * a := by
      calc A = a * A ^ t * a := hA1
        _ ≤ a * D ^ t * a := conj_le' ha hAt
        _ = a * B ^ t * a + a * E * a := by
          rw [hEdef]; noncomm_ring
    calc tauD b A ≤ tauD b (a * B ^ t * a + a * E * a) := tauD_mono b hle
      _ = _ := tauD_add b (conj_nonneg' ha hBt0) (conj_nonneg' ha hE)
  -- step 3-4
  have s2 : tauD b (a * E * a) ≤ tauD b (d * E * d) := by
    calc tauD b (a * E * a) = tauD b (a * (e * e) * a) := by rw [hee]
      _ = tauD b (e * (a * a) * e) := tauD_conj_swap b ha he
      _ = tauD b (e * A ^ s * e) := by rw [← rpow_half_sq hs]
      _ ≤ tauD b (e * D ^ s * e) := tauD_mono b (conj_le' he hAs)
      _ = tauD b (e * (d * d) * e) := by rw [← rpow_half_sq hs]
      _ = tauD b (d * (e * e) * d) := (tauD_conj_swap b hd he).symm
      _ = tauD b (d * E * d) := by rw [hee]
  -- step 5-7
  have s3 : tauD b (d * E * d) ≤ tauD b P := by
    have hD1 : D = d * B ^ t * d + d * E * d := by
      calc D = d * D ^ t * d := rpow_sandwich hD hs ht hst
        _ = _ := by rw [hEdef]; noncomm_ring
    have hsum : tauD b D = tauD b (d * B ^ t * d) + tauD b (d * E * d) := by
      conv_lhs => rw [hD1]
      exact tauD_add b (conj_nonneg' hd hBt0) (conj_nonneg' hd hE)
    have hBle : tauD b B ≤ tauD b (d * B ^ t * d) := by
      have hB1 : B = g * B ^ s * g := by
        have := rpow_sandwich hB ht hs (by linarith)
        exact this
      calc tauD b B = tauD b (g * B ^ s * g) := by rw [← hB1]
        _ ≤ tauD b (g * D ^ s * g) := tauD_mono b (conj_le' hg hBs)
        _ = tauD b (g * (d * d) * g) := by rw [← rpow_half_sq hs]
        _ = tauD b (d * (g * g) * d) := (tauD_conj_swap b hd hg).symm
        _ = tauD b (d * B ^ t * d) := by rw [← rpow_half_sq ht]
    have hDsplit : tauD b D = tauD b B + tauD b P := tauD_add b hB hP
    have : tauD b B + tauD b (d * E * d) ≤ tauD b B + tauD b P := by
      rw [← hDsplit, hsum]; gcongr
    exact (ENNReal.add_le_add_iff_left hBfin).mp this
  calc tauD b A ≤ tauD b (a * B ^ t * a) + tauD b (a * E * a) := s1
    _ ≤ tauD b (a * B ^ t * a) + tauD b P := by gcongr; exact s2.trans s3


/-! Stage 3: the platform definitions (modulus of a positive operator, trace class => finite tau). -/

open QAlgorithms.Papers.Independent.Next46.P02 in
lemma modulus_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : hilbertOperatorModulus A = A := by
  have hsa' : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hsa : ContinuousLinearMap.adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa'.star_eq
  have hAA : (ContinuousLinearMap.adjoint A).comp A = A * A := by rw [hsa]; rfl
  have hApos : A.IsPositive := by simpa using (ContinuousLinearMap.le_def 0 A).mp hA
  unfold hilbertOperatorModulus hilbertPositiveSqrt
  rw [hsa]
  by_cases h0 : A.comp A = 0
  · rw [if_pos h0]
    have : star A * A = 0 := by rw [hsa'.star_eq]; exact h0
    exact ((CStarRing.star_mul_self_eq_zero_iff A).mp this).symm
  · rw [if_neg h0]
    have hex : ∃ B : H →L[ℂ] H, B.IsPositive ∧ B.comp B = A.comp A := ⟨A, hApos, rfl⟩
    rw [dif_pos hex]
    obtain ⟨hXp, hXX⟩ := Classical.choose_spec hex
    have hX0 : 0 ≤ Classical.choose hex := by
      rw [ContinuousLinearMap.le_def]; simpa using hXp
    have h1 : CFC.sqrt (Classical.choose hex * Classical.choose hex) = Classical.choose hex :=
      CFC.sqrt_mul_self _ hX0
    have h2 : CFC.sqrt (A * A) = A := CFC.sqrt_mul_self _ hA
    have h3 : Classical.choose hex * Classical.choose hex = A * A := hXX
    rw [← h1, h3, h2]

open QAlgorithms.Papers.Independent.Next46.P02 in
lemma tauD_ref_ne_top {A : H →L[ℂ] H} (hA : 0 ≤ A) (htr : IsModulusTraceClass A) :
    tauD (referenceBasis (F := ℂ) (H := H)) A ≠ ⊤ := by
  unfold IsModulusTraceClass basisDiagonal at htr
  rw [modulus_of_nonneg hA] at htr
  unfold tauD
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => re_inner_nonneg hA _) htr]
  exact ENNReal.ofReal_ne_top

/-! Stage 4: Hilbert-Schmidt trace swap (complex), basis independence. -/

lemma sq_summable_of_hs {ι κ : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H)
    (Z : H →L[ℂ] H) (hZ : hsSq b Z ≠ ⊤) :
    Summable (fun p : ι × κ => ‖⟪b' p.2, Z (b p.1)⟫_ℂ‖ ^ 2) := by
  have h1 : ∑' p : ι × κ, (((‖⟪b' p.2, Z (b p.1)⟫_ℂ‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) = hsSq b Z := by
    rw [ENNReal.tsum_prod']
    unfold hsSq
    refine tsum_congr (fun i => ?_)
    rw [← parseval_enn b' (Z (b i))]
    exact tsum_congr (fun j => ENNReal.coe_pow _ _)
  have h2 : Summable (fun p : ι × κ => ‖⟪b' p.2, Z (b p.1)⟫_ℂ‖₊ ^ 2) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable, h1]; exact hZ
  have h3 := NNReal.summable_coe.mpr h2
  simpa using h3

lemma norm_mul_le_half {a c : ℂ} : ‖a * c‖ ≤ (‖a‖ ^ 2 + ‖c‖ ^ 2) / 2 := by
  rw [norm_mul]
  nlinarith [sq_nonneg (‖a‖ - ‖c‖)]

/-- HS trace swap: if `U†` and `V` are Hilbert-Schmidt, the diagonal of `U V` in `b` and of
`V U` in `b'` are summable with the same sum. -/
theorem trace_swap {ι κ : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H)
    (U V : H →L[ℂ] H) (hU : hsSq b (ContinuousLinearMap.adjoint U) ≠ ⊤) (hV : hsSq b V ≠ ⊤) :
    HasSum (fun i => ⟪b i, (U * V) (b i)⟫_ℂ) (∑' j, ⟪b' j, (V * U) (b' j)⟫_ℂ) ∧
    HasSum (fun j => ⟪b' j, (V * U) (b' j)⟫_ℂ) (∑' j, ⟪b' j, (V * U) (b' j)⟫_ℂ) := by
  set U' := ContinuousLinearMap.adjoint U with hU'def
  let f : ι × κ → ℂ := fun p => ⟪U' (b p.1), b' p.2⟫_ℂ * ⟪b' p.2, V (b p.1)⟫_ℂ
  have hsU := sq_summable_of_hs b b' U' hU
  have hsV := sq_summable_of_hs b b' V hV
  have hb : Summable (fun p : ι × κ =>
      (‖⟪b' p.2, U' (b p.1)⟫_ℂ‖ ^ 2 + ‖⟪b' p.2, V (b p.1)⟫_ℂ‖ ^ 2) / 2) :=
    (hsU.add hsV).div_const 2
  have hle : ∀ p : ι × κ, ‖⟪U' (b p.1), b' p.2⟫_ℂ * ⟪b' p.2, V (b p.1)⟫_ℂ‖ ≤
      (‖⟪b' p.2, U' (b p.1)⟫_ℂ‖ ^ 2 + ‖⟪b' p.2, V (b p.1)⟫_ℂ‖ ^ 2) / 2 := by
    intro p
    have := norm_mul_le_half (a := ⟪U' (b p.1), b' p.2⟫_ℂ) (c := ⟪b' p.2, V (b p.1)⟫_ℂ)
    rwa [norm_inner_symm (U' (b p.1)) (b' p.2)] at this
  have hf : Summable f :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hle hb)
  have hrow : ∀ i, HasSum (fun j => f (i, j)) ⟪b i, (U * V) (b i)⟫_ℂ := by
    intro i
    have := b'.hasSum_inner_mul_inner (U' (b i)) (V (b i))
    rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left]
    exact this
  have hcol : ∀ j, HasSum (fun i => f (i, j)) ⟪b' j, (V * U) (b' j)⟫_ℂ := by
    intro j
    have := b.hasSum_inner_mul_inner (ContinuousLinearMap.adjoint V (b' j)) (U (b' j))
    rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left]
    have e : (fun i => f (i, j)) = fun i =>
        ⟪ContinuousLinearMap.adjoint V (b' j), b i⟫_ℂ * ⟪b i, U (b' j)⟫_ℂ := by
      funext i
      show ⟪U' (b i), b' j⟫_ℂ * ⟪b' j, V (b i)⟫_ℂ = _
      rw [hU'def, ContinuousLinearMap.adjoint_inner_left U (b' j) (b i),
        ContinuousLinearMap.adjoint_inner_left V (b i) (b' j), mul_comm]
    rw [e]; exact this
  have hS := hf.hasSum
  have h1 := hS.prod_fiberwise hrow
  have hS' : HasSum (fun q : κ × ι => f q.swap) (∑' p, f p) :=
    (Equiv.prodComm κ ι).hasSum_iff.mpr hS
  have h2 := hS'.prod_fiberwise (fun j => hcol j)
  rw [h2.tsum_eq]
  exact ⟨h1, h2⟩

/-! Stage 5: eigenvectors of `A` are eigenvectors of `A ^ r`. -/

lemma rpow_apply_eigen {A : H →L[ℂ] H} (hA : 0 ≤ A) {e : H} {μ : ℂ} (he : A e = μ • e)
    (r : ℝ) : ∃ c : ℂ, (A ^ r) e = c • e := by
  by_cases he0 : e = 0
  · exact ⟨0, by simp [he0]⟩
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hsym : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := fun x y => hsa.isSymmetric x y
  have hee : ⟪e, e⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr he0
  have hμ : (starRingEnd ℂ) μ = μ := by
    have h1 := hsym e e
    rw [he, inner_smul_left, inner_smul_right] at h1
    exact mul_right_cancel₀ hee h1
  let Q : H →L[ℂ] H := (innerSL ℂ e).smulRight e
  have hQ : ∀ x, Q x = ⟪e, x⟫_ℂ • e := fun x => by simp [Q]
  have hcomm : Commute A Q := by
    show A * Q = Q * A
    ext x
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hQ, hQ, map_smul, he,
      ← hsym, he, inner_smul_left, hμ, smul_smul, mul_comm]
  have hc : Commute (A ^ r) Q := by rw [CFC.rpow_def]; exact hcomm.cfc_nnreal _
  refine ⟨⟪e, (A ^ r) e⟫_ℂ / ⟪e, e⟫_ℂ, ?_⟩
  have h2 := congrArg (fun T : H →L[ℂ] H => T e) hc.eq
  simp only [ContinuousLinearMap.mul_apply, hQ, map_smul] at h2
  rw [div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hee, one_smul]

/-! Stage 6: Hilbert-Schmidt operators are compact. -/

lemma isCompactOperator_to_complex (f : H →L[ℂ] ℂ) : IsCompactOperator f := by
  refine ⟨Metric.closedBall 0 ‖f‖, isCompact_closedBall _ _, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) one_pos) (fun x hx => ?_)
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  have h1 := f.le_opNorm x
  have h2 : ‖x‖ < 1 := by simpa using hx
  nlinarith [norm_nonneg f, norm_nonneg x]

lemma isCompactOperator_rankOne (f : H →L[ℂ] ℂ) (v : H) :
    IsCompactOperator (f.smulRight v) := by
  have h := (isCompactOperator_to_complex f).clm_comp (ContinuousLinearMap.toSpanSingleton ℂ v)
  have he : ⇑(f.smulRight v) = ⇑(ContinuousLinearMap.toSpanSingleton ℂ v) ∘ ⇑f := by
    funext x; simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [he]; exact h

/-- Operator norm controlled by the Hilbert-Schmidt square sum. -/
lemma norm_apply_sq_le_hsSq {ι : Type*} (b : HilbertBasis ι ℂ H) (W : H →L[ℂ] H) (x : H) :
    ((‖W x‖₊ : ℝ≥0∞)) ^ 2 ≤ hsSq b W * ((‖x‖₊ : ℝ≥0∞)) ^ 2 := by
  rw [← parseval_enn b (W x), hsSq_adjoint b b W]
  unfold hsSq
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum (fun i => ?_)
  rw [← ContinuousLinearMap.adjoint_inner_left, ← mul_pow]
  gcongr
  rw [← ENNReal.coe_mul]
  exact_mod_cast nnnorm_inner_le_nnnorm _ _

lemma opNorm_le_of_hsSq {ι : Type*} (b : HilbertBasis ι ℂ H) (W : H →L[ℂ] H) {c : ℝ}
    (hc : 0 ≤ c) (h : hsSq b W ≤ ENNReal.ofReal (c ^ 2)) : ‖W‖ ≤ c := by
  refine W.opNorm_le_bound hc (fun x => ?_)
  have h1 := (norm_apply_sq_le_hsSq b W x).trans (mul_le_mul_of_nonneg_right h (zero_le))
  rw [← ofReal_sq_norm, ← ofReal_sq_norm, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have h2 : ‖W x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by rw [mul_pow]; exact h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- Finite-rank truncation of `Z` along the basis `b`. -/
noncomputable def truncOp {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H) (F : Finset ι) :
    H →L[ℂ] H :=
  ∑ i ∈ F, (innerSL ℂ (b i)).smulRight (Z (b i))

lemma truncOp_compact {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H) (F : Finset ι) :
    IsCompactOperator (truncOp b Z F) := by
  classical
  unfold truncOp
  induction F using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, ContinuousLinearMap.coe_add']
    exact (isCompactOperator_rankOne _ _).add ih

lemma truncOp_basis {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H)
    (F : Finset ι) (j : ι) :
    (Z - truncOp b Z F) (b j) = if j ∈ F then 0 else Z (b j) := by
  have hF : truncOp b Z F (b j) = if j ∈ F then Z (b j) else 0 := by
    unfold truncOp
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    simp_rw [orthonormal_iff_ite.mp b.orthonormal, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq']
  rw [ContinuousLinearMap.sub_apply, hF]
  by_cases hj : j ∈ F <;> simp [hj]

lemma tendsto_truncOp {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H) (hZ : hsSq b Z ≠ ⊤) :
    Filter.Tendsto (truncOp b Z) Filter.atTop (nhds Z) := by
  classical
  have ht := ENNReal.tendsto_tsum_compl_atTop_zero (f := fun i => ((‖Z (b i)‖₊ : ℝ≥0∞)) ^ 2) hZ
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((ε / 2) ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
  filter_upwards [(tendsto_order.1 ht).2 _ hpos] with F hF
  have hhs : hsSq b (Z - truncOp b Z F) ≤ ENNReal.ofReal ((ε / 2) ^ 2) := by
    refine le_of_lt (lt_of_eq_of_lt ?_ hF)
    unfold hsSq
    have hpt : ∀ i, ((‖(Z - truncOp b Z F) (b i)‖₊ : ℝ≥0∞)) ^ 2 =
        Set.indicator {x | x ∉ F} (fun i => ((‖Z (b i)‖₊ : ℝ≥0∞)) ^ 2) i := by
      intro i; rw [truncOp_basis]; by_cases hi : i ∈ F <;> simp [hi]
    simp_rw [hpt]
    exact (tsum_subtype {x | x ∉ F} _).symm
  have := opNorm_le_of_hsSq b _ (by positivity) hhs
  rw [dist_eq_norm, norm_sub_rev]
  linarith

lemma isCompactOperator_of_hs {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H)
    (hZ : hsSq b Z ≠ ⊤) : IsCompactOperator Z :=
  isCompactOperator_of_tendsto (tendsto_truncOp b Z hZ)
    (Filter.Eventually.of_forall (truncOp_compact b Z))

open QAlgorithms.Papers.Independent.Next46.P02 in
lemma isCompactOperator_of_tauD {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (htr : IsModulusTraceClass A) : IsCompactOperator A := by
  have h := tauD_ref_ne_top hA htr
  rw [eq_star_sqrt hA, tauD_star_mul] at h
  have hc := (isCompactOperator_of_hs _ _ h).clm_comp (star (CFC.sqrt A))
  rw [eq_star_sqrt hA]
  exact hc

/-! Stage 7: eigen Hilbert basis of a compact self-adjoint operator. -/

section Eig
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma exists_eigen_hilbertBasis {A : E →L[ℂ] E} (hsa : IsSelfAdjoint A)
    (hc : IsCompactOperator A) :
    ∃ (κ : Type u) (e : HilbertBasis κ ℂ E), ∀ k, ∃ μ : ℂ, A (e k) = μ • e k := by
  have hT : (A : E →ₗ[ℂ] E).IsSymmetric := fun x y => hsa.isSymmetric x y
  let V : ℂ → Submodule ℂ E := fun μ => Module.End.eigenspace (A : Module.End ℂ E) μ
  have hcl : ∀ μ, IsClosed (V μ : Set E) := by
    intro μ
    have : (V μ : Set E) = {x | A x = μ • x} := by
      ext x; exact Module.End.mem_eigenspace_iff
    rw [this]; exact isClosed_eq A.continuous (continuous_const_smul μ)
  have hcs : ∀ μ, CompleteSpace (V μ) := fun μ => (hcl μ).completeSpace_coe
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hT
  choose w b _ using fun μ => by haveI := hcs μ; exact exists_hilbertBasis ℂ (V μ)
  let v : (Σ μ, w μ) → E := fun a => (V a.1).subtypeₗᵢ (b a.1 a.2)
  have hon : Orthonormal ℂ v :=
    hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal (fun μ => (b μ).orthonormal)
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hv : ∀ a, ⟪v a, x⟫_ℂ = 0 := fun a =>
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self a)) hx
    have hV : ∀ μ, ∀ y ∈ V μ, ⟪y, x⟫_ℂ = 0 := by
      intro μ y hy
      have h := ((b μ).hasSum_repr ⟨y, hy⟩).mapL ((innerSL ℂ x).comp (V μ).subtypeL)
      have h0 : (fun k => ((innerSL ℂ x).comp (V μ).subtypeL) ((b μ).repr ⟨y, hy⟩ k • b μ k)) =
          fun _ => (0 : ℂ) := by
        funext k
        have := hv ⟨μ, k⟩
        simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Submodule.subtypeL_apply,
          Submodule.coe_smul, inner_smul_right]
        rw [← inner_conj_symm, show ⟪((b μ k : V μ) : E), x⟫_ℂ = 0 from this]
        simp
      rw [h0] at h
      have h1 : ⟪x, y⟫_ℂ = 0 := by simpa using h.unique hasSum_zero
      rw [← inner_conj_symm, h1, map_zero]
    have hx' : x ∈ (⨆ μ, V μ)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      refine Submodule.iSup_induction (motive := fun u => ⟪u, x⟫_ℂ = 0) V hu
        (fun μ y hy => hV μ y hy) (by simp) (fun y z hy hz => ?_)
      rw [inner_add_left, hy, hz, add_zero]
    have hbot' : (⨆ μ, V μ)ᗮ = ⊥ := hbot
    rw [hbot'] at hx'
    exact hx'
  refine ⟨Σ μ, w μ, HilbertBasis.mkOfOrthogonalEqBot hon hsp, fun a => ⟨a.1, ?_⟩⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact Module.End.mem_eigenspace_iff.mp (b a.1 a.2).2

end Eig

/-! Stage 8: projections, HS sums of products, endpoint chain, finiteness, LHS. -/

lemma hsSq_star {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H) :
    hsSq b (star Z) = hsSq b Z := by
  rw [ContinuousLinearMap.star_eq_adjoint, ← hsSq_adjoint b b Z]

lemma tauD_eq_hsSq {ι : Type*} (b : HilbertBasis ι ℂ H) {C : H →L[ℂ] H} (hC : 0 ≤ C) :
    tauD b C = hsSq b (CFC.sqrt C) := by
  conv_lhs => rw [eq_star_sqrt hC]
  exact tauD_star_mul b _

lemma hsSq_le_of_norm_le {ι : Type*} (b : HilbertBasis ι ℂ H) (K Z : H →L[ℂ] H)
    (hK : ∀ x, ‖K x‖ ≤ ‖x‖) : hsSq b (K * Z) ≤ hsSq b Z := by
  unfold hsSq
  refine ENNReal.tsum_le_tsum (fun i => ?_)
  have h : ((‖(K * Z) (b i)‖₊ : ℝ≥0∞)) ≤ ((‖Z (b i)‖₊ : ℝ≥0∞)) := by
    rw [ContinuousLinearMap.mul_apply, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
      coe_nnnorm]
    exact hK _
  exact pow_le_pow_left₀ zero_le h 2

lemma proj_pythag {p : H →L[ℂ] H} (hp : IsStarProjection p) (x : H) :
    ‖x‖ ^ 2 = ‖p x‖ ^ 2 + ‖(1 - p) x‖ ^ 2 := by
  have hsa : ∀ u v : H, ⟪p u, v⟫_ℂ = ⟪u, p v⟫_ℂ := fun u v => hp.isSelfAdjoint.isSymmetric u v
  have hid : ∀ u, p (p u) = p u := fun u => by
    have := congrArg (fun T : H →L[ℂ] H => T u) hp.isIdempotentElem.eq
    simpa using this
  have horth : ⟪p x, (1 - p) x⟫_ℂ = 0 := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
      hsa x (p x), hid, hsa x x, sub_self]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (p x) ((1 - p) x) horth
  have hx : p x + (1 - p) x = x := by simp
  rw [hx] at h
  rw [sq, sq, sq]; exact h

lemma norm_proj_le {p : H →L[ℂ] H} (hp : IsStarProjection p) (x : H) : ‖p x‖ ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by linarith [proj_pythag hp x, sq_nonneg ‖(1 - p) x‖])

lemma norm_one_sub_proj_le {p : H →L[ℂ] H} (hp : IsStarProjection p) (x : H) :
    ‖(1 - p) x‖ ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by linarith [proj_pythag hp x, sq_nonneg ‖p x‖])

lemma hsSq_proj_split {ι : Type*} (b : HilbertBasis ι ℂ H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (Z : H →L[ℂ] H) :
    hsSq b Z = hsSq b (p * Z) + hsSq b ((1 - p) * Z) := by
  unfold hsSq
  rw [← ENNReal.tsum_add]
  refine tsum_congr (fun i => ?_)
  rw [← ofReal_sq_norm, ← ofReal_sq_norm, ← ofReal_sq_norm,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  exact proj_pythag hp (Z (b i))

lemma hsSq_conj {ι : Type*} (b : HilbertBasis ι ℂ H) {C x : H →L[ℂ] H} (hC : 0 ≤ C)
    (hx : IsSelfAdjoint x) : hsSq b (x * CFC.sqrt C) = tauD b (x * C * x) := by
  have hW : IsSelfAdjoint (CFC.sqrt C) := (CFC.sqrt_nonneg C).isSelfAdjoint
  rw [← hsSq_star, star_mul, hW.star_eq, hx.star_eq, ← tauD_star_mul, star_mul, hW.star_eq,
    hx.star_eq]
  conv_rhs => rw [← CFC.sqrt_mul_sqrt_self C hC]
  simp only [mul_assoc]

open QChernoff.Trace in
lemma supportProj_mul_self (B : H →L[ℂ] H) : supportProj B * B = B := by
  ext x
  rw [ContinuousLinearMap.mul_apply]
  unfold supportProj
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)

open QChernoff.Trace in
lemma mul_supportProj_self {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) : B * supportProj B = B := by
  have h := congrArg star (supportProj_mul_self B)
  rwa [star_mul, hB.star_eq, (isStarProjection_supportProj B).isSelfAdjoint.star_eq] at h

/-- Endpoint chain: `tau A <= ||p sqrt A||_HS^2 + tau P` when `A <= B + P` and `B p = B`. -/
theorem endpoint {ι : Type*} (b : HilbertBasis ι ℂ H) {A B P p : H →L[ℂ] H} (hA : 0 ≤ A)
    (hP : 0 ≤ P) (hABP : A ≤ B + P) (hp : IsStarProjection p) (hBp : B * p = B) :
    tauD b A ≤ hsSq b (p * CFC.sqrt A) + tauD b P := by
  have hR : IsSelfAdjoint (1 - p) :=
    (show IsSelfAdjoint (1 : H →L[ℂ] H) from star_one _).sub hp.isSelfAdjoint
  have hBR : B * (1 - p) = 0 := by rw [mul_sub, mul_one, hBp, sub_self]
  have h4 : (1 - p) * (B + P) * (1 - p) = (1 - p) * P * (1 - p) := by
    rw [mul_add, add_mul, mul_assoc (1 - p) B, hBR, mul_zero, zero_add]
  calc tauD b A = hsSq b (p * CFC.sqrt A) + hsSq b ((1 - p) * CFC.sqrt A) := by
        rw [tauD_eq_hsSq b hA]; exact hsSq_proj_split b hp _
    _ = hsSq b (p * CFC.sqrt A) + tauD b ((1 - p) * A * (1 - p)) := by rw [hsSq_conj b hA hR]
    _ ≤ hsSq b (p * CFC.sqrt A) + tauD b ((1 - p) * (B + P) * (1 - p)) := by
        gcongr; exact tauD_mono b (conj_le' hR hABP)
    _ = hsSq b (p * CFC.sqrt A) + tauD b ((1 - p) * P * (1 - p)) := by rw [h4]
    _ ≤ hsSq b (p * CFC.sqrt A) + tauD b P := by
        gcongr
        rw [← hsSq_conj b hP hR, tauD_eq_hsSq b hP]
        exact hsSq_le_of_norm_le b _ _ (fun x => norm_one_sub_proj_le hp x)

lemma inner_eq_ofReal_re {C : H →L[ℂ] H} (hC : IsSelfAdjoint C) (x : H) :
    ⟪x, C x⟫_ℂ = ((RCLike.re ⟪x, C x⟫_ℂ : ℝ) : ℂ) := by
  have h1 : (starRingEnd ℂ) ⟪x, C x⟫_ℂ = ⟪x, C x⟫_ℂ := by
    rw [inner_conj_symm]; exact hC.isSymmetric x x
  exact (Complex.conj_eq_iff_re.mp h1).symm

lemma hasSum_diag_star_mul {ι : Type*} (b : HilbertBasis ι ℂ H) (Z : H →L[ℂ] H)
    (hZ : hsSq b Z ≠ ⊤) :
    HasSum (fun i => ⟪b i, (star Z * Z) (b i)⟫_ℂ) (((hsSq b Z).toReal : ℝ) : ℂ) := by
  have hsa : IsSelfAdjoint (star Z * Z) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg Z)
  have hf : ∀ i, ⟪b i, (star Z * Z) (b i)⟫_ℂ =
      (((ENNReal.ofReal (‖Z (b i)‖ ^ 2)).toReal : ℝ) : ℂ) := by
    intro i
    rw [inner_eq_ofReal_re hsa, re_inner_star_mul, ENNReal.toReal_ofReal (by positivity)]
  simp_rw [hf]
  rw [Complex.hasSum_ofReal]
  have heq : hsSq b Z = ∑' i, ENNReal.ofReal (‖Z (b i)‖ ^ 2) := by
    unfold hsSq; simp_rw [ofReal_sq_norm]
  have hZ' : ∑' i, ENNReal.ofReal (‖Z (b i)‖ ^ 2) ≠ ⊤ := by rw [← heq]; exact hZ
  rw [heq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact (ENNReal.summable_toReal hZ').hasSum

/-- Endpoint trace: `Tr_b(A p) = ||p sqrt A||_HS^2` (complex HasSum). -/
lemma trace_endpoint {ι : Type*} (b : HilbertBasis ι ℂ H) {A p : H →L[ℂ] H} (hA : 0 ≤ A)
    (hAfin : tauD b A ≠ ⊤) (hp : IsStarProjection p) :
    HasSum (fun i => ⟪b i, (A * p) (b i)⟫_ℂ) (((hsSq b (p * CFC.sqrt A)).toReal : ℝ) : ℂ) := by
  have hW : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hWfin : hsSq b (CFC.sqrt A) ≠ ⊤ := by rwa [← tauD_eq_hsSq b hA]
  have hpW : hsSq b (p * CFC.sqrt A) ≠ ⊤ :=
    ne_top_of_le_ne_top hWfin (hsSq_le_of_norm_le b _ _ (fun x => norm_proj_le hp x))
  have hU : hsSq b (ContinuousLinearMap.adjoint (CFC.sqrt A)) ≠ ⊤ := by
    rwa [← ContinuousLinearMap.star_eq_adjoint, hsSq_star]
  have hV : hsSq b (CFC.sqrt A * p) ≠ ⊤ := by
    have : CFC.sqrt A * p = star (p * CFC.sqrt A) := by
      rw [star_mul, hW.star_eq, hp.isSelfAdjoint.star_eq]
    rwa [this, hsSq_star]
  obtain ⟨h1, -⟩ := trace_swap b b (CFC.sqrt A) (CFC.sqrt A * p) hU hV
  have hUV : CFC.sqrt A * (CFC.sqrt A * p) = A * p := by
    rw [← mul_assoc, CFC.sqrt_mul_sqrt_self A hA]
  have hVU : CFC.sqrt A * p * CFC.sqrt A = star (p * CFC.sqrt A) * (p * CFC.sqrt A) := by
    rw [star_mul, hW.star_eq, hp.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc (CFC.sqrt A) p p,
      hp.isIdempotentElem.eq]
  rw [hUV, hVU, (hasSum_diag_star_mul b _ hpW).tsum_eq] at h1
  exact h1

/-- Finiteness of `tau(Y^{q/2} X^p Y^{q/2})` for `p + q = 1`. -/
lemma tauD_sandwich_ne_top {ι : Type*} (b : HilbertBasis ι ℂ H) {X Y : H →L[ℂ] H} (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hXf : tauD b X ≠ ⊤) (hYf : tauD b Y ≠ ⊤) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (hpq : p + q = 1) : tauD b (Y ^ (q / 2) * X ^ p * Y ^ (q / 2)) ≠ ⊤ := by
  have hC : 0 ≤ X + Y := add_nonneg hX hY
  have hCf : tauD b (X + Y) ≠ ⊤ := by
    rw [tauD_add b hX hY]; exact ENNReal.add_ne_top.mpr ⟨hXf, hYf⟩
  have hy : IsSelfAdjoint (Y ^ (q / 2)) := CFC.rpow_nonneg.isSelfAdjoint
  rcases hp.eq_or_lt with h0 | hp'
  · subst h0
    have hq1 : q = 1 := by linarith
    subst hq1
    rw [CFC.rpow_zero X hX, mul_one, ← rpow_half_sq one_pos, CFC.rpow_one Y hY]
    exact hYf
  · have hXC : X ^ p ≤ (X + Y) ^ p :=
      CFC.rpow_le_rpow ⟨hp, by linarith⟩ (le_add_of_nonneg_right hY)
    have hYC : Y ^ q ≤ (X + Y) ^ q :=
      CFC.rpow_le_rpow ⟨hq.le, by linarith⟩ (le_add_of_nonneg_left hX)
    have hc : IsSelfAdjoint ((X + Y) ^ (p / 2)) := CFC.rpow_nonneg.isSelfAdjoint
    refine ne_top_of_le_ne_top hCf ?_
    calc tauD b (Y ^ (q / 2) * X ^ p * Y ^ (q / 2))
        ≤ tauD b (Y ^ (q / 2) * (X + Y) ^ p * Y ^ (q / 2)) := tauD_mono b (conj_le' hy hXC)
      _ = tauD b (Y ^ (q / 2) * ((X + Y) ^ (p / 2) * (X + Y) ^ (p / 2)) * Y ^ (q / 2)) := by
          rw [← rpow_half_sq hp']
      _ = tauD b ((X + Y) ^ (p / 2) * (Y ^ (q / 2) * Y ^ (q / 2)) * (X + Y) ^ (p / 2)) :=
          tauD_conj_swap b hy hc
      _ = tauD b ((X + Y) ^ (p / 2) * Y ^ q * (X + Y) ^ (p / 2)) := by rw [← rpow_half_sq hq]
      _ ≤ tauD b ((X + Y) ^ (p / 2) * (X + Y) ^ q * (X + Y) ^ (p / 2)) :=
          tauD_mono b (conj_le' hc hYC)
      _ = tauD b (X + Y) := by rw [← rpow_sandwich hC hp' hq hpq]

open QAlgorithms.Papers.Independent.Next46.P02 in
/-- LHS: if `tau A <= r + tau (A-B)^+` then `Tr[A + B - |A - B|]/2 <= r`. -/
theorem lhs_le {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAtr : IsModulusTraceClass A)
    {r : ℝ} (hr : 0 ≤ r)
    (hch : tauD (referenceBasis (F := ℂ) (H := H)) A ≤
      ENNReal.ofReal r + tauD (referenceBasis (F := ℂ) (H := H)) (A - B)⁺) :
    basisOperatorTrace (A + B - CFC.abs (A - B)) / 2 ≤ (r : ℂ) := by
  set b := referenceBasis (F := ℂ) (H := H)
  have hX : IsSelfAdjoint (A - B) :=
    (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  set P := (A - B)⁺ with hPdef
  have hP : 0 ≤ P := CFC.posPart_nonneg _
  have hT : A + B - CFC.abs (A - B) = (A - P) + (A - P) := by
    have h := CFC.abs_add_self (A - B) hX
    rw [two_smul] at h
    calc A + B - CFC.abs (A - B) = A + A - (CFC.abs (A - B) + (A - B)) := by abel
      _ = A + A - (P + P) := by rw [h]
      _ = (A - P) + (A - P) := by abel
  have hdiag : ∀ i, basisDiagonal b ((A - P) + (A - P)) i = 2 * basisDiagonal b (A - P) i := by
    intro i; unfold basisDiagonal; rw [ContinuousLinearMap.add_apply, inner_add_right, two_mul]
  have hL : basisOperatorTrace (A + B - CFC.abs (A - B)) / 2 = ∑' i, basisDiagonal b (A - P) i := by
    show (∑' i, basisDiagonal b (A + B - CFC.abs (A - B)) i) / 2 = _
    rw [hT]; simp_rw [hdiag]; rw [tsum_mul_left]; ring
  rw [hL]
  by_cases hs : Summable (fun i => basisDiagonal b (A - P) i)
  · have hre : ∀ {C : H →L[ℂ] H}, IsSelfAdjoint C → ∀ i,
        basisDiagonal b C i = ((RCLike.re (basisDiagonal b C i) : ℝ) : ℂ) :=
      fun hC i => inner_eq_ofReal_re hC (b i)
    have hAs : Summable (fun i => RCLike.re (basisDiagonal b A i)) := by
      have := hAtr; unfold IsModulusTraceClass at this; rw [modulus_of_nonneg hA] at this; exact this
    have hAc : Summable (fun i => basisDiagonal b A i) := by
      have : (fun i => basisDiagonal b A i) =
          fun i => ((RCLike.re (basisDiagonal b A i) : ℝ) : ℂ) :=
        funext (hre (IsSelfAdjoint.of_nonneg hA))
      rw [this]; exact Complex.summable_ofReal.mpr hAs
    have hdP : ∀ i, basisDiagonal b P i = basisDiagonal b A i - basisDiagonal b (A - P) i := by
      intro i; unfold basisDiagonal; rw [ContinuousLinearMap.sub_apply, inner_sub_right]; ring
    have hPc : Summable (fun i => basisDiagonal b P i) := by
      simp_rw [hdP]; exact hAc.sub hs
    have hPs : Summable (fun i => RCLike.re (basisDiagonal b P i)) :=
      (Complex.reCLM.summable hPc :)
    have htA : tauD b A = ENNReal.ofReal (∑' i, RCLike.re (basisDiagonal b A i)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun i => re_inner_nonneg hA _) hAs).symm
    have htP : tauD b P = ENNReal.ofReal (∑' i, RCLike.re (basisDiagonal b P i)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun i => re_inner_nonneg hP _) hPs).symm
    have hPnn : 0 ≤ ∑' i, RCLike.re (basisDiagonal b P i) :=
      tsum_nonneg (fun i => re_inner_nonneg hP _)
    rw [htA, htP, ← ENNReal.ofReal_add hr hPnn,
      ENNReal.ofReal_le_ofReal_iff (add_nonneg hr hPnn)] at hch
    have hsum : ∑' i, basisDiagonal b (A - P) i =
        ∑' i, basisDiagonal b A i - ∑' i, basisDiagonal b P i := by
      rw [← hAc.tsum_sub hPc]; congr 1; funext i; rw [hdP]; ring
    rw [hsum, Complex.le_def]
    constructor
    · rw [Complex.sub_re, Complex.re_tsum hAc, Complex.re_tsum hPc, Complex.ofReal_re]
      have e1 : ∑' i, (basisDiagonal b A i).re = ∑' i, RCLike.re (basisDiagonal b A i) := rfl
      have e2 : ∑' i, (basisDiagonal b P i).re = ∑' i, RCLike.re (basisDiagonal b P i) := rfl
      rw [e1, e2]; linarith
    · have h0 : ∀ {C : H →L[ℂ] H}, IsSelfAdjoint C → ∀ i, (basisDiagonal b C i).im = 0 :=
        fun hC i => by rw [hre hC i]; exact Complex.ofReal_im _
      rw [Complex.sub_im, Complex.im_tsum hAc, Complex.im_tsum hPc, Complex.ofReal_im]
      simp [h0 (IsSelfAdjoint.of_nonneg hA), h0 (IsSelfAdjoint.of_nonneg hP)]
  · rw [tsum_eq_zero_of_not_summable hs]
    exact Complex.zero_le_real.mpr hr

/-! Stage 9: interior identification and assembly. -/

lemma rpow_add_nonneg {a : H →L[ℂ] H} (ha : 0 ≤ a) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    a ^ (x + y) = a ^ x * a ^ y := by
  rcases hy.eq_or_lt with h | h
  · subst h; rw [add_zero, CFC.rpow_zero a ha, mul_one]
  · exact rpow_add_pos hx h

lemma rpow_mul_self_nonneg {a : H →L[ℂ] H} (ha : 0 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    a ^ y * a ^ y = a ^ (2 * y) := by
  rcases hy.eq_or_lt with h | h
  · subst h; rw [CFC.rpow_zero a ha, mul_one, mul_zero, CFC.rpow_zero a ha]
  · rw [rpow_half_sq (a := a) (show (0:ℝ) < 2 * y by linarith), show 2 * y / 2 = y by ring]

lemma hsSq_rpow_half {ι : Type*} (b : HilbertBasis ι ℂ H) {C : H →L[ℂ] H} (hC : 0 ≤ C) :
    hsSq b (C ^ ((1:ℝ) / 2)) = tauD b C := by
  rw [← tauD_star_mul, (CFC.rpow_nonneg : 0 ≤ C ^ ((1:ℝ) / 2)).isSelfAdjoint.star_eq,
    ← rpow_half_sq one_pos, CFC.rpow_one C hC]

lemma exists_hs_factor {ι : Type*} (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hAf : tauD b A ≠ ⊤) (hBf : tauD b B ≠ ⊤) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t = 1) : ∃ U V : H →L[ℂ] H, U * V = A ^ s * B ^ t ∧
      hsSq b (ContinuousLinearMap.adjoint U) ≠ ⊤ ∧ hsSq b V ≠ ⊤ := by
  by_cases h2 : (1:ℝ) / 2 ≤ s
  · refine ⟨A ^ ((1:ℝ) / 2), A ^ (s - 1 / 2) * B ^ t, ?_, ?_, ?_⟩
    · rw [← mul_assoc, ← rpow_add_nonneg hA (x := (1:ℝ) / 2) (y := s - 1 / 2) (by norm_num)
        (by linarith), show (1:ℝ) / 2 + (s - 1 / 2) = s by ring]
    · rw [← ContinuousLinearMap.star_eq_adjoint, hsSq_star, hsSq_rpow_half b hA]; exact hAf
    · rw [← tauD_star_mul, star_mul, (CFC.rpow_nonneg : 0 ≤ B ^ t).isSelfAdjoint.star_eq,
        (CFC.rpow_nonneg : 0 ≤ A ^ (s - 1 / 2)).isSelfAdjoint.star_eq, mul_assoc,
        ← mul_assoc (A ^ (s - 1 / 2)), rpow_mul_self_nonneg hA (y := s - 1 / 2) (by linarith),
        ← mul_assoc]
      have := tauD_sandwich_ne_top b hA hB hAf hBf (p := 2 * (s - 1 / 2)) (q := 2 * t)
        (by linarith) (by linarith) (by linarith)
      rwa [show 2 * t / 2 = t by ring] at this
  · replace h2 : s < 1 / 2 := lt_of_not_ge h2
    refine ⟨A ^ s * B ^ (t - 1 / 2), B ^ ((1:ℝ) / 2), ?_, ?_, ?_⟩
    · rw [mul_assoc, ← rpow_add_pos (x := t - 1 / 2) (y := (1:ℝ) / 2) (by linarith) (by norm_num),
        show t - 1 / 2 + (1:ℝ) / 2 = t by ring]
    · rw [← ContinuousLinearMap.star_eq_adjoint, ← tauD_star_mul, star_star, star_mul,
        (CFC.rpow_nonneg : 0 ≤ B ^ (t - 1 / 2)).isSelfAdjoint.star_eq,
        (CFC.rpow_nonneg : 0 ≤ A ^ s).isSelfAdjoint.star_eq, mul_assoc,
        ← mul_assoc (B ^ (t - 1 / 2)), rpow_mul_self_nonneg hB (y := t - 1 / 2) (by linarith),
        ← mul_assoc]
      have := tauD_sandwich_ne_top b hB hA hBf hAf (p := 2 * (t - 1 / 2)) (q := 2 * s)
        (by linarith) (by linarith) (by linarith)
      rwa [show 2 * s / 2 = s by ring] at this
    · rw [hsSq_rpow_half b hB]; exact hBf

/-- Interior: `Tr_b(A^s B^t) = tau(A^{s/2} B^t A^{s/2})` (complex HasSum), `s,t > 0`. -/
theorem trace_interior {ι : Type*} (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hAf : tauD b A ≠ ⊤) (hBf : tauD b B ≠ ⊤) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t = 1) :
    HasSum (fun i => ⟪b i, (A ^ s * B ^ t) (b i)⟫_ℂ)
      (((tauD b (A ^ (s / 2) * B ^ t * A ^ (s / 2))).toReal : ℝ) : ℂ) := by
  obtain ⟨U, V, hUV, hU, hV⟩ := exists_hs_factor b hA hB hAf hBf hs ht hst
  have hc : IsCompactOperator A := by
    have h := hAf
    rw [eq_star_sqrt hA, tauD_star_mul] at h
    have hc := (isCompactOperator_of_hs _ _ h).clm_comp (star (CFC.sqrt A))
    rw [eq_star_sqrt hA]
    exact hc
  obtain ⟨κ, e, hev⟩ := exists_eigen_hilbertBasis (IsSelfAdjoint.of_nonneg hA) hc
  have hUe : hsSq e (ContinuousLinearMap.adjoint U) ≠ ⊤ := by rwa [hsSq_basis e b]
  have hVe : hsSq e V ≠ ⊤ := by rwa [hsSq_basis e b]
  have h1 := (trace_swap b e U V hU hV).1
  have h2 := (trace_swap e e U V hUe hVe).1
  rw [hUV] at h1 h2
  obtain ⟨Z, hZdef⟩ : ∃ Z : H →L[ℂ] H, Z = B ^ (t / 2) * A ^ (s / 2) := ⟨_, rfl⟩
  have ha : IsSelfAdjoint (A ^ (s / 2)) := CFC.rpow_nonneg.isSelfAdjoint
  have hg : IsSelfAdjoint (B ^ (t / 2)) := CFC.rpow_nonneg.isSelfAdjoint
  have hM : A ^ (s / 2) * B ^ t * A ^ (s / 2) = star Z * Z := by
    rw [hZdef, star_mul, ha.star_eq, hg.star_eq, rpow_half_sq ht]
    simp only [mul_assoc]
  have hMnn : 0 ≤ A ^ (s / 2) * B ^ t * A ^ (s / 2) := conj_nonneg' ha CFC.rpow_nonneg
  have hMf : tauD b (A ^ (s / 2) * B ^ t * A ^ (s / 2)) ≠ ⊤ :=
    tauD_sandwich_ne_top b hB hA hBf hAf ht.le hs (by linarith)
  have hZe : hsSq e Z ≠ ⊤ := by
    rw [← tauD_star_mul, ← hM, tauD_basis e b hMnn]; exact hMf
  have h3 := hasSum_diag_star_mul e Z hZe
  have hAsa : IsSelfAdjoint (A ^ s) := CFC.rpow_nonneg.isSelfAdjoint
  have hsym : ∀ x y : H, ⟪(A ^ s) x, y⟫_ℂ = ⟪x, (A ^ s) y⟫_ℂ := fun x y => hAsa.isSymmetric x y
  have hsyma : ∀ x y : H, ⟪(A ^ (s / 2)) x, y⟫_ℂ = ⟪x, (A ^ (s / 2)) y⟫_ℂ :=
    fun x y => ha.isSymmetric x y
  have hterm : ∀ k, ⟪e k, (A ^ s * B ^ t) (e k)⟫_ℂ = ⟪e k, (star Z * Z) (e k)⟫_ℂ := by
    intro k
    rw [← hM]
    obtain ⟨μ, hμ⟩ := hev k
    obtain ⟨c, hc⟩ := rpow_apply_eigen hA hμ (s / 2)
    have hee : ⟪e k, e k⟫_ℂ = 1 := by
      classical
      simpa using orthonormal_iff_ite.mp e.orthonormal k k
    have hcr : (starRingEnd ℂ) c = c := by
      have h1 := inner_eq_ofReal_re ha (e k)
      rw [hc, inner_smul_right, hee, mul_one] at h1
      rw [h1]; exact Complex.conj_ofReal _
    have hAs_e : (A ^ s) (e k) = (c * c) • e k := by
      rw [rpow_half_sq hs, ContinuousLinearMap.mul_apply, hc, map_smul, hc, smul_smul]
    have lhs : ⟪e k, (A ^ s * B ^ t) (e k)⟫_ℂ =
        (starRingEnd ℂ) (c * c) * ⟪e k, (B ^ t) (e k)⟫_ℂ := by
      rw [ContinuousLinearMap.mul_apply, ← hsym, hAs_e, inner_smul_left]
    have rhs : ⟪e k, (A ^ (s / 2) * B ^ t * A ^ (s / 2)) (e k)⟫_ℂ =
        (starRingEnd ℂ) c * (c * ⟪e k, (B ^ t) (e k)⟫_ℂ) := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hc, map_smul, ← hsyma, hc,
        inner_smul_left, inner_smul_right]
    rw [lhs, rhs, map_mul, hcr]; ring
  have h3' : HasSum (fun k => ⟪e k, (A ^ s * B ^ t) (e k)⟫_ℂ)
      (((hsSq e Z).toReal : ℝ) : ℂ) := by
    simp_rw [hterm]; exact h3
  have hval := h2.unique h3'
  rw [hval] at h1
  rw [hM, tauD_basis b e (star_mul_self_nonneg Z), tauD_star_mul]
  exact h1

lemma le_add_posPart {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B) : A ≤ B + (A - B)⁺ := by
  have hX : IsSelfAdjoint (A - B) :=
    (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  have h := CFC.posPart_sub_negPart (A - B) hX
  have hN : 0 ≤ (A - B)⁻ := CFC.negPart_nonneg _
  set P := (A - B)⁺
  set N := (A - B)⁻
  have e : B + P - A = N := by
    have : B + P - A = N + ((P - N) - (A - B)) := by abel
    rw [this, h, sub_self, add_zero]
  rw [← sub_nonneg, e]; exact hN

lemma abs_sub_comm' (A B : H →L[ℂ] H) : CFC.abs (A - B) = CFC.abs (B - A) := by
  rw [show B - A = -(A - B) by abel, CFC.abs_neg]

lemma trace_endpoint' {ι : Type*} (b : HilbertBasis ι ℂ H) {A p : H →L[ℂ] H} (hA : 0 ≤ A)
    (hAfin : tauD b A ≠ ⊤) (hp : IsStarProjection p) :
    HasSum (fun i => ⟪b i, (p * A) (b i)⟫_ℂ) (((hsSq b (p * CFC.sqrt A)).toReal : ℝ) : ℂ) := by
  have h := Complex.hasSum_conj'.mpr (trace_endpoint b hA hAfin hp)
  rw [Complex.conj_ofReal] at h
  have hsA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ :=
    fun x y => (IsSelfAdjoint.of_nonneg hA).isSymmetric x y
  have hsp : ∀ x y : H, ⟪p x, y⟫_ℂ = ⟪x, p y⟫_ℂ := fun x y => hp.isSelfAdjoint.isSymmetric x y
  convert h using 2 with i
  rw [inner_conj_symm, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hsA, hsp]

open QAlgorithms.Papers.Independent.Next46.P02 QChernoff.Trace in
theorem endpoint_case {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAtr : IsModulusTraceClass A) :
    basisOperatorTrace (A + B - CFC.abs (A - B)) / 2 ≤ basisOperatorTrace (A * supportProj B) ∧
    basisOperatorTrace (supportProj B * A) = basisOperatorTrace (A * supportProj B) := by
  have hAf := tauD_ref_ne_top hA hAtr
  have hp := isStarProjection_supportProj B
  have h1 := trace_endpoint (referenceBasis (F := ℂ) (H := H)) hA hAf hp
  have h2 := trace_endpoint' (referenceBasis (F := ℂ) (H := H)) hA hAf hp
  have e1 : basisOperatorTrace (A * supportProj B) =
      (((hsSq (referenceBasis (F := ℂ) (H := H)) (supportProj B * CFC.sqrt A)).toReal : ℝ) : ℂ) :=
    h1.tsum_eq
  have e2 : basisOperatorTrace (supportProj B * A) =
      (((hsSq (referenceBasis (F := ℂ) (H := H)) (supportProj B * CFC.sqrt A)).toReal : ℝ) : ℂ) :=
    h2.tsum_eq
  refine ⟨?_, by rw [e1, e2]⟩
  rw [e1]
  refine lhs_le hA hB hAtr ENNReal.toReal_nonneg ?_
  have hfin : hsSq (referenceBasis (F := ℂ) (H := H)) (supportProj B * CFC.sqrt A) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rwa [← tauD_eq_hsSq _ hA])
      (hsSq_le_of_norm_le _ _ _ (fun x => norm_proj_le hp x))
  rw [ENNReal.ofReal_toReal hfin]
  exact endpoint _ hA (CFC.posPart_nonneg _) (le_add_posPart hA hB) hp
    (mul_supportProj_self (IsSelfAdjoint.of_nonneg hB))

open QAlgorithms.Papers.Independent.Next46.P02 QChernoff.Trace in
theorem main_thm {A B : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAtr : IsModulusTraceClass A) (hBtr : IsModulusTraceClass B)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    basisOperatorTrace (A + B - CFC.abs (A - B)) / 2 ≤
      basisOperatorTrace (qPow A s * qPow B (1 - s)) := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have e : qPow A 0 * qPow B (1 - 0) = supportProj A * B := by
      rw [qPow, qPow, if_pos rfl, if_neg (by norm_num : ¬ ((1:ℝ) - 0 = 0)), sub_zero,
        CFC.rpow_one B hB]
    rw [e]
    obtain ⟨h1, h2⟩ := endpoint_case hB hA hBtr
    have hsym : A + B - CFC.abs (A - B) = B + A - CFC.abs (B - A) := by
      rw [abs_sub_comm' A B, add_comm A B]
    rw [hsym, h2]; exact h1
  rcases hs1.eq_or_lt with h1 | hlt
  · subst h1
    have e : qPow A 1 * qPow B (1 - 1) = A * supportProj B := by
      rw [qPow, qPow, if_neg (one_ne_zero : (1:ℝ) ≠ 0), sub_self, if_pos rfl, CFC.rpow_one A hA]
    rw [e]; exact (endpoint_case hA hB hAtr).1
  · have e : qPow A s * qPow B (1 - s) = A ^ s * B ^ (1 - s) := by
      rw [qPow, qPow, if_neg hpos.ne', if_neg (sub_ne_zero.mpr hlt.ne')]
    rw [e]
    have hAf := tauD_ref_ne_top hA hAtr
    have hBf := tauD_ref_ne_top hB hBtr
    have ht : 0 < 1 - s := by linarith
    have hst : s + (1 - s) = 1 := by ring
    have hI := trace_interior _ hA hB hAf hBf hpos ht hst
    have eR : basisOperatorTrace (A ^ s * B ^ (1 - s)) =
        (((tauD (referenceBasis (F := ℂ) (H := H))
          (A ^ (s / 2) * B ^ (1 - s) * A ^ (s / 2))).toReal : ℝ) : ℂ) := hI.tsum_eq
    rw [eR]
    refine lhs_le hA hB hAtr ENNReal.toReal_nonneg ?_
    rw [ENNReal.ofReal_toReal (tauD_sandwich_ne_top _ hB hA hBf hAf ht.le hpos (by ring))]
    exact chain _ hA hB (CFC.posPart_nonneg _) (le_add_posPart hA hB) hBf hpos ht hst

end QCT

open QAlgorithms.Papers.Independent.Next46.P02 QChernoff.Trace ComplexOrder in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAtr : IsModulusTraceClass A) (hBtr : IsModulusTraceClass B)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    basisOperatorTrace (A + B - CFC.abs (A - B)) / 2 ≤
      basisOperatorTrace (qPow A s * qPow B (1 - s)) := by
  exact QCT.main_thm hA hB hAtr hBtr s hs0 hs1
