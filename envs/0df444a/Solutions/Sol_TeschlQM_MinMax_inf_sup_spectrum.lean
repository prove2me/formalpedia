-- Prove2me | solution 1 for TeschlQM.MinMax.inf_sup_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T11:58:13.277031+00:00
-- url     : https://prove2.me/submissions/4375813b-3dc8-46fe-bf32-7a34dd535cf0

import Mathlib
import Definitions.Def_TeschlQM_MinMax_spectrum

open scoped InnerProductSpace

namespace TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For self-adjoint `A`, the adjoint agrees with `A` on the domain. -/
lemma sa_adjoint_apply {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (x : A.adjoint.domain)
    (hx : (x : H) ∈ A.domain) : A.adjoint x = A ⟨x, hx⟩ := by
  have h := LinearPMap.isSelfAdjoint_def.mp hA
  obtain ⟨_, h2⟩ := LinearPMap.ext_iff.mp h
  exact @h2 (x : H) x.2 hx

lemma sa_domain {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : A.adjoint.domain = A.domain := by
  rw [LinearPMap.isSelfAdjoint_def.mp hA]

/-- Symmetry of a self-adjoint operator. -/
lemma sa_symm {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (x y : A.domain) :
    ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have hx : (x : H) ∈ A.adjoint.domain := by rw [sa_domain hA]; exact x.2
  have := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain ⟨x, hx⟩ y
  rw [sa_adjoint_apply hA ⟨x, hx⟩ x.2] at this
  simpa using this

/-- Adjoint criterion: if `⟪A x, y⟫ = ⟪x, v⟫` for all `x` in the domain then `y ∈ 𝔇(A)` and
`A y = v`. -/
lemma sa_mem_of_inner {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (y v : H)
    (h : ∀ x : A.domain, ⟪A x, y⟫_ℂ = ⟪(x : H), v⟫_ℂ) :
    ∃ hy : y ∈ A.domain, A ⟨y, hy⟩ = v := by
  have hd := hA.dense_domain
  have hy : y ∈ A.adjoint.domain := by
    rw [LinearPMap.mem_adjoint_domain_iff]
    have : ((innerₛₗ ℂ) y ∘ₗ A.toFun) = (innerₛₗ ℂ v) ∘ₗ A.domain.subtype := by
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, innerₛₗ_apply_apply,
        Submodule.coe_subtype]
      rw [← inner_conj_symm]
      erw [h x, inner_conj_symm]
    rw [this]
    exact (continuous_const.inner continuous_id).comp continuous_subtype_val
  have hy' : y ∈ A.domain := by rw [← sa_domain hA]; exact hy
  refine ⟨hy', ?_⟩
  rw [← sa_adjoint_apply hA ⟨y, hy⟩ hy']
  apply LinearPMap.adjoint_apply_eq hd
  intro x
  rw [← inner_conj_symm, ← h x, inner_conj_symm]

/-- Quadratic form is real. -/
lemma sa_inner_self_im {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (x : A.domain) :
    (⟪(x : H), A x⟫_ℂ).im = 0 := by
  have := sa_symm hA x x
  rw [← inner_conj_symm] at this
  exact Complex.conj_eq_iff_im.mp this

/-- If `A - z` and `A - conj z` are bounded below, then `z` is in the resolvent set. -/
lemma sa_resolvent_of_bdd_below {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (h1 : ∀ ψ : A.domain, δ * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (h2 : ∀ ψ : A.domain, δ * ‖(ψ : H)‖ ≤ ‖A ψ - (starRingEnd ℂ z) • (ψ : H)‖) :
    z ∈ resolventSet A := by
  have hsymm := sa_symm hA
  have hmem := sa_mem_of_inner hA
  set T : A.domain →ₗ[ℂ] H := A.toFun - z • A.domain.subtype with hT
  have hTapp : ∀ ψ : A.domain, T ψ = A ψ - z • (ψ : H) := fun ψ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ψ hψ
    have := h1 ψ
    rw [← hTapp, hψ, norm_zero] at this
    have : ‖(ψ : H)‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (ψ : H)]) (norm_nonneg _)
    exact Subtype.ext (by simpa using this)
  have hclosed : IsClosed ((LinearMap.range T : Submodule ℂ H) : Set H) := by
    apply IsSeqClosed.isClosed
    intro φs φ hφs hlim
    choose ψs hψs using hφs
    have hcauchy : CauchySeq (fun n => (ψs n : H)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hc := hlim.cauchySeq
      rw [Metric.cauchySeq_iff] at hc
      obtain ⟨N, hN⟩ := hc (δ * ε) (by positivity)
      refine ⟨N, fun m hm n hn => ?_⟩
      have := hN m hm n hn
      rw [dist_eq_norm] at this ⊢
      have hb := h1 (ψs m - ψs n)
      have : T (ψs m - ψs n) = φs m - φs n := by rw [map_sub, hψs, hψs]
      rw [← hTapp, this] at hb
      push_cast at hb
      by_contra hcon
      push_neg at hcon
      nlinarith
    obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hAψ : Filter.Tendsto (fun n => A (ψs n)) Filter.atTop (nhds (φ + z • ψ)) := by
      have : (fun n => A (ψs n)) = fun n => φs n + z • (ψs n : H) := by
        funext n; rw [← hψs n, hTapp]; abel
      rw [this]
      exact hlim.add (hψ.const_smul z)
    obtain ⟨hψd, hAψ'⟩ := hmem ψ (φ + z • ψ) (by
      intro x
      have e1 : Filter.Tendsto (fun n => ⟪A x, (ψs n : H)⟫_ℂ) Filter.atTop (nhds ⟪A x, ψ⟫_ℂ) :=
        (continuous_const.inner continuous_id).continuousAt.tendsto.comp hψ
      have e2 : Filter.Tendsto (fun n => ⟪(x : H), A (ψs n)⟫_ℂ) Filter.atTop
          (nhds ⟪(x : H), φ + z • ψ⟫_ℂ) :=
        (continuous_const.inner continuous_id).continuousAt.tendsto.comp hAψ
      have : (fun n => ⟪A x, (ψs n : H)⟫_ℂ) = fun n => ⟪(x : H), A (ψs n)⟫_ℂ := by
        funext n; exact hsymm x (ψs n)
      rw [this] at e1
      exact tendsto_nhds_unique e1 e2)
    refine ⟨⟨ψ, hψd⟩, ?_⟩
    rw [hTapp]
    simp only [hAψ']
    abel
  have hsurj : LinearMap.range T = ⊤ := by
    haveI : CompleteSpace (LinearMap.range T) := hclosed.completeSpace_coe
    rw [← Submodule.orthogonal_eq_bot_iff]
    rw [Submodule.eq_bot_iff]
    intro φ hφ
    rw [Submodule.mem_orthogonal] at hφ
    obtain ⟨hφd, hAφ⟩ := hmem φ ((starRingEnd ℂ z) • φ) (by
      intro x
      have := hφ (T x) ⟨x, rfl⟩
      rw [hTapp, inner_sub_left, inner_smul_left, sub_eq_zero] at this
      rw [this, inner_smul_right])
    have := h2 ⟨φ, hφd⟩
    simp only [hAφ, sub_self, norm_zero] at this
    have : ‖φ‖ = 0 := le_antisymm (by nlinarith [norm_nonneg φ]) (norm_nonneg _)
    simpa using this
  have hbij : Function.Bijective T := ⟨hinj, LinearMap.range_eq_top.mp hsurj⟩
  set e := LinearEquiv.ofBijective T hbij
  let R0 : H →ₗ[ℂ] H := A.domain.subtype ∘ₗ (e.symm : H →ₗ[ℂ] A.domain)
  have hR0 : ∀ φ, ‖R0 φ‖ ≤ δ⁻¹ * ‖φ‖ := by
    intro φ
    have := h1 (e.symm φ)
    have he : A (e.symm φ) - z • ((e.symm φ : A.domain) : H) = φ := by
      rw [← hTapp]; exact e.apply_symm_apply φ
    rw [he] at this
    show ‖((e.symm φ : A.domain) : H)‖ ≤ δ⁻¹ * ‖φ‖
    rw [le_inv_mul_iff₀ hδ]; exact this
  refine ⟨R0.mkContinuous δ⁻¹ hR0, ?_, ?_⟩
  · intro ψ
    show ((e.symm (A ψ - z • (ψ : H)) : A.domain) : H) = ψ
    rw [← hTapp]
    exact congrArg Subtype.val (e.symm_apply_apply ψ)
  · intro φ
    refine ⟨(e.symm φ).2, ?_⟩
    rw [← hTapp]
    exact e.apply_symm_apply φ

/-- `‖(A - w) ψ‖ ≥ |Im w| ‖ψ‖`. -/
lemma sa_im_bound {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (w : ℂ) (ψ : A.domain) :
    |w.im| * ‖(ψ : H)‖ ≤ ‖A ψ - w • (ψ : H)‖ := by
  have him := sa_inner_self_im hA ψ
  have h1 : (⟪(ψ : H), A ψ - w • (ψ : H)⟫_ℂ).im = - w.im * ‖(ψ : H)‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [him]
    norm_cast
    ring
  have h2 : |(⟪(ψ : H), A ψ - w • (ψ : H)⟫_ℂ).im| ≤ ‖(ψ : H)‖ * ‖A ψ - w • (ψ : H)‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [h1, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ‖(ψ : H)‖)] at h2
  rcases eq_or_lt_of_le (norm_nonneg (ψ : H)) with h0 | h0
  · rw [← h0]; simp
  · nlinarith

/-- Non-real points are in the resolvent set. -/
lemma sa_resolvent_of_im_ne {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    z ∈ resolventSet A := by
  refine sa_resolvent_of_bdd_below hA z |z.im| (abs_pos.mpr hz) (sa_im_bound hA z) ?_
  intro ψ
  have := sa_im_bound hA ((starRingEnd ℂ) z) ψ
  simpa using this

/-- Points of the spectrum are real. -/
lemma sa_spectrum_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ) (hz : z ∈ spectrum A) :
    (z.re : ℂ) = z := by
  by_contra h
  apply hz
  apply sa_resolvent_of_im_ne hA
  intro h'
  exact h (Complex.ext (by simp) (by simp [h']))

open scoped ComplexOrder in
lemma cfc_quad_nonneg (R : H →L[ℂ] H) [IsStarNormal R] (c d : ℂ)
    (hpos : ∀ w ∈ _root_.spectrum ℂ R, 0 ≤ star (1 + c * w) * (1 + d * w)) (φ : H) :
    0 ≤ (⟪(1 + c • R) φ, (1 + d • R) φ⟫_ℂ).re := by
  have hK : ∀ e : ℂ, (1 + e • R) = cfc (fun w : ℂ => 1 + e * w) R := by
    intro e
    rw [cfc_add R (fun _ => (1:ℂ)) (fun w => e * w), cfc_const_one ℂ R,
      cfc_const_mul e (fun w => w) R, cfc_id' ℂ R]
  have hM : star (1 + c • R) * (1 + d • R) =
      cfc (fun w : ℂ => star (1 + c * w) * (1 + d * w)) R := by
    rw [hK c, hK d, ← cfc_star (fun w : ℂ => 1 + c * w) R,
      ← cfc_mul (fun w : ℂ => star (1 + c * w)) (fun w : ℂ => 1 + d * w) R]
  have h0 : 0 ≤ star (1 + c • R) * (1 + d • R) := by
    rw [hM]; exact cfc_nonneg hpos
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at h0
  have := h0.re_inner_nonneg_right φ
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right] at this
  exact this

/-- The resolvent at `i` has the resolvent at `-i` as adjoint. -/
lemma resolvent_adjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (R R' : H →L[ℂ] H)
    (hRd : ∀ φ, R φ ∈ A.domain)
    (hRe : ∀ φ, A ⟨R φ, hRd φ⟩ - Complex.I • R φ = φ)
    (hRd' : ∀ φ, R' φ ∈ A.domain)
    (hRe' : ∀ φ, A ⟨R' φ, hRd' φ⟩ - (-Complex.I) • R' φ = φ) :
    ContinuousLinearMap.adjoint R = R' := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hs := sa_symm hA ⟨R' x, hRd' x⟩ ⟨R y, hRd y⟩
  calc ⟪R' x, y⟫_ℂ = ⟪R' x, A ⟨R y, hRd y⟩ - Complex.I • R y⟫_ℂ := by rw [hRe y]
    _ = ⟪A ⟨R' x, hRd' x⟩ - (-Complex.I) • R' x, R y⟫_ℂ := by
        rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left]
        simp only at hs
        rw [hs]
        simp
    _ = ⟪x, R y⟫_ℂ := by rw [hRe' x]

omit [CompleteSpace H] in
/-- Resolvent identity: `R - R' = 2i R R'`, for resolvents at `i` and `-i`. -/
lemma resolvent_identity {A : H →ₗ.[ℂ] H} (R R' : H →L[ℂ] H)
    (hR1 : ∀ ψ : A.domain, R (A ψ - Complex.I • (ψ : H)) = ψ)
    (hRd' : ∀ φ, R' φ ∈ A.domain)
    (hRe' : ∀ φ, A ⟨R' φ, hRd' φ⟩ - (-Complex.I) • R' φ = φ) (φ : H) :
    R φ - R' φ = (2 * Complex.I) • R (R' φ) := by
  have h1 := hR1 ⟨R' φ, hRd' φ⟩
  have h2 : φ = (A ⟨R' φ, hRd' φ⟩ - Complex.I • R' φ) + (2 * Complex.I) • R' φ := by
    conv_lhs => rw [← hRe' φ]
    module
  have h3 : R φ = R ((A ⟨R' φ, hRd' φ⟩ - Complex.I • R' φ) + (2 * Complex.I) • R' φ) :=
    congrArg R h2
  rw [h3, map_add, map_smul]
  simp only at h1
  rw [h1]
  abel

/-- Spectral mapping for the resolvent at `i`. -/
lemma resolvent_spectrum {A : H →ₗ.[ℂ] H} (R : H →L[ℂ] H)
    (hR1 : ∀ ψ : A.domain, R (A ψ - Complex.I • (ψ : H)) = ψ)
    (hRd : ∀ φ, R φ ∈ A.domain)
    (hRe : ∀ φ, A ⟨R φ, hRd φ⟩ - Complex.I • R φ = φ)
    (w : ℂ) (hw : w ∈ _root_.spectrum ℂ R) (hw0 : w ≠ 0) :
    Complex.I + w⁻¹ ∈ spectrum A := by
  intro hx
  obtain ⟨S, hS1, hS2⟩ := hx
  choose hSd hSe using hS2
  apply (_root_.spectrum.mem_iff).mp hw
  set U : H →L[ℂ] H := w⁻¹ • (1 + w⁻¹ • S) with hU
  have e1 : (algebraMap ℂ (H →L[ℂ] H) w - R) * U = 1 := by
    ext φ
    have hs := hSe φ
    have h3 : φ + w⁻¹ • S φ = A ⟨S φ, hSd φ⟩ - Complex.I • S φ := by
      linear_combination (norm := module) -hs
    have h4 := hR1 ⟨S φ, hSd φ⟩
    simp only at h4
    simp only [hU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, Algebra.algebraMap_eq_smul_one]
    rw [h3, map_smul, h4, smul_smul, mul_inv_cancel₀ hw0, one_smul]
    linear_combination (norm := module) hs
  have e2 : U * (algebraMap ℂ (H →L[ℂ] H) w - R) = 1 := by
    ext φ
    have hu := hRe φ
    have h5 : w • φ - R φ = w • (A ⟨R φ, hRd φ⟩ - (Complex.I + w⁻¹) • R φ) := by
      rw [smul_sub, smul_smul, mul_add, mul_inv_cancel₀ hw0]
      linear_combination (norm := module) (-w) • hu
    have h6 := hS1 ⟨R φ, hRd φ⟩
    simp only at h6
    simp only [hU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, Algebra.algebraMap_eq_smul_one]
    rw [h5, map_smul, h6, ← h5, smul_smul, inv_mul_cancel₀ hw0, one_smul]
    rw [smul_add, smul_sub, smul_smul, inv_mul_cancel₀ hw0, one_smul]
    abel
  exact ⟨⟨_, U, e1, e2⟩, rfl⟩

open scoped ComplexOrder in
/-- Key positivity: if `(x - a)(x - b) ≥ 0` on the real spectrum then
`Re ⟪(A - a)ψ, (A - b)ψ⟫ ≥ 0`. -/
lemma sa_quad_nonneg {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (a b : ℝ)
    (hab : ∀ x : ℝ, (x : ℂ) ∈ spectrum A → 0 ≤ (x - a) * (x - b)) (ψ : A.domain) :
    0 ≤ (⟪A ψ - (a : ℂ) • (ψ : H), A ψ - (b : ℂ) • (ψ : H)⟫_ℂ).re := by
  obtain ⟨R, hR1, hR2⟩ := sa_resolvent_of_im_ne hA Complex.I (by simp)
  obtain ⟨R', hR1', hR2'⟩ := sa_resolvent_of_im_ne hA (-Complex.I) (by simp)
  choose hRd hRe using hR2
  choose hRd' hRe' using hR2'
  have hadj := resolvent_adjoint hA R R' hRd hRe hRd' hRe'
  have hnormal : IsStarNormal R := by
    refine ⟨?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, hadj]
    show R' * R = R * R'
    ext φ
    have e1 := resolvent_identity R R' hR1 hRd' hRe' φ
    have e2 : R φ - R' φ = (2 * Complex.I) • R' (R φ) := by
      have h1 := hR1' ⟨R φ, hRd φ⟩
      have h2 : φ = (A ⟨R φ, hRd φ⟩ - (-Complex.I) • R φ) - (2 * Complex.I) • R φ := by
        linear_combination (norm := module) -(hRe φ)
      have h3 : R' φ = R' ((A ⟨R φ, hRd φ⟩ - (-Complex.I) • R φ) - (2 * Complex.I) • R φ) :=
        congrArg R' h2
      rw [h3, map_sub, map_smul]
      simp only at h1
      rw [h1]
      abel
    have : (2 * Complex.I) • R' (R φ) = (2 * Complex.I) • R (R' φ) := by rw [← e1, ← e2]
    have h2I : (2 * Complex.I) ≠ 0 := by simp
    simpa using smul_right_injective H h2I this
  set φ : H := A ψ - Complex.I • (ψ : H) with hφ
  have hK : ∀ c : ℝ, (1 + (Complex.I - c) • R) φ = A ψ - (c : ℂ) • (ψ : H) := by
    intro c
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, hφ, hR1 ψ]
    module
  rw [← hK a, ← hK b]
  apply cfc_quad_nonneg
  intro w hw
  by_cases hw0 : w = 0
  · subst hw0; simp only [mul_zero, add_zero, star_one, mul_one]; exact zero_le_one
  have hx := resolvent_spectrum R hR1 hRd hRe w hw hw0
  have hreal := sa_spectrum_real hA _ hx
  set r := (Complex.I + w⁻¹).re with hr
  have hr' : (r : ℂ) = Complex.I + w⁻¹ := hreal
  have hab' := hab r (by rw [hr']; exact hx)
  have hwinv : w⁻¹ = (r : ℂ) - Complex.I := by rw [hr']; ring
  have hfac : ∀ c : ℝ, 1 + (Complex.I - c) * w = w * ((r : ℂ) - c) := by
    intro c
    have : (1 : ℂ) = w * w⁻¹ := (mul_inv_cancel₀ hw0).symm
    rw [this, hwinv]
    ring
  rw [hfac a, hfac b]
  have : star (w * ((r : ℂ) - a)) * (w * ((r : ℂ) - b)) =
      ((Complex.normSq w * ((r - a) * (r - b)) : ℝ) : ℂ) := by
    rw [star_mul', Complex.star_def]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sub, Complex.conj_ofReal]
    ring
  rw [this]
  exact_mod_cast mul_nonneg (Complex.normSq_nonneg w) hab'

end TeschlQM.MinMax.Core

namespace TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Expansion of `Re ⟪(A - a)ψ, (A - b)ψ⟫`. -/
lemma quad_expand {A : H →ₗ.[ℂ] H} (a b : ℝ) (ψ : A.domain) :
    (⟪A ψ - (a : ℂ) • (ψ : H), A ψ - (b : ℂ) • (ψ : H)⟫_ℂ).re =
      (‖A ψ‖ ^ 2 - a * (⟪(ψ : H), A ψ⟫_ℂ).re) - b * ((⟪(ψ : H), A ψ⟫_ℂ).re - a * ‖(ψ : H)‖ ^ 2) := by
  have h1 : (⟪A ψ, (ψ : H)⟫_ℂ).re = (⟪(ψ : H), A ψ⟫_ℂ).re := by
    rw [← inner_conj_symm (A ψ) (ψ : H), Complex.conj_re]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, h1]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp [sq]

/-- If the real spectrum lies in `[m, ∞)`, then `⟨ψ, Aψ⟩ ≥ m ‖ψ‖²`. -/
lemma form_ge_of_spectrum_ge {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (m : ℝ)
    (hm : ∀ x : ℝ, (x : ℂ) ∈ spectrum A → m ≤ x) (ψ : A.domain) :
    m * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re := by
  by_contra hcon
  push_neg at hcon
  set q := (⟪(ψ : H), A ψ⟫_ℂ).re
  set η := m * ‖(ψ : H)‖ ^ 2 - q with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set C := ‖A ψ‖ ^ 2 - m * q
  set b : ℝ := min m (-(|C| + 1) / η)
  have hb := sa_quad_nonneg hA m b (by
    intro x hx
    have := hm x hx
    have : b ≤ m := min_le_left _ _
    nlinarith) ψ
  rw [quad_expand] at hb
  have hb2 : b ≤ -(|C| + 1) / η := min_le_right _ _
  have : b * η ≤ -(|C| + 1) := by rwa [le_div_iff₀ hηpos] at hb2
  have : C - b * (q - m * ‖(ψ : H)‖ ^ 2) = C + b * η := by rw [hη]; ring
  have hC := le_abs_self C
  linarith

/-- If the real spectrum lies in `(-∞, M]`, then `⟨ψ, Aψ⟩ ≤ M ‖ψ‖²`. -/
lemma form_le_of_spectrum_le {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (M : ℝ)
    (hM : ∀ x : ℝ, (x : ℂ) ∈ spectrum A → x ≤ M) (ψ : A.domain) :
    (⟪(ψ : H), A ψ⟫_ℂ).re ≤ M * ‖(ψ : H)‖ ^ 2 := by
  by_contra hcon
  push_neg at hcon
  set q := (⟪(ψ : H), A ψ⟫_ℂ).re
  set η := q - M * ‖(ψ : H)‖ ^ 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set C := ‖A ψ‖ ^ 2 - M * q
  set b : ℝ := max M ((|C| + 1) / η)
  have hb := sa_quad_nonneg hA M b (by
    intro x hx
    have := hM x hx
    have : M ≤ b := le_max_left _ _
    nlinarith) ψ
  rw [quad_expand] at hb
  have hb2 : (|C| + 1) / η ≤ b := le_max_right _ _
  have : |C| + 1 ≤ b * η := by rwa [div_le_iff₀ hηpos] at hb2
  have hC := le_abs_self C
  linarith

omit [CompleteSpace H] in
/-- Lower bound on `‖(A - x)ψ‖` from a lower bound on `|Re ⟨ψ, (A - x)ψ⟩|`. -/
lemma bdd_of_inner {A : H →ₗ.[ℂ] H} (x δ : ℝ) (ψ : A.domain)
    (h : δ * ‖(ψ : H)‖ ^ 2 ≤ |(⟪(ψ : H), A ψ - (x : ℂ) • (ψ : H)⟫_ℂ).re|) :
    δ * ‖(ψ : H)‖ ≤ ‖A ψ - (x : ℂ) • (ψ : H)‖ := by
  have h2 : |(⟪(ψ : H), A ψ - (x : ℂ) • (ψ : H)⟫_ℂ).re| ≤
      ‖(ψ : H)‖ * ‖A ψ - (x : ℂ) • (ψ : H)‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (ψ : H)) with h0 | h0
  · rw [← h0]; simp
  · nlinarith

omit [CompleteSpace H] in
lemma inner_sub_re {A : H →ₗ.[ℂ] H} (x : ℝ) (ψ : A.domain) :
    (⟪(ψ : H), A ψ - (x : ℂ) • (ψ : H)⟫_ℂ).re =
      (⟪(ψ : H), A ψ⟫_ℂ).re - x * ‖(ψ : H)‖ ^ 2 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [sq]

/-- A real point below a lower form bound is in the resolvent set. -/
lemma resolvent_of_form_ge {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (c x : ℝ) (hx : x < c)
    (hc : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) :
    (x : ℂ) ∈ resolventSet A := by
  have hb : ∀ ψ : A.domain, (c - x) * ‖(ψ : H)‖ ≤ ‖A ψ - (x : ℂ) • (ψ : H)‖ := by
    intro ψ
    apply bdd_of_inner
    rw [inner_sub_re]
    have := hc ψ
    rw [abs_of_nonneg (by nlinarith [sq_nonneg ‖(ψ : H)‖])]
    linarith
  exact sa_resolvent_of_bdd_below hA x (c - x) (by linarith) hb (by simpa using hb)

/-- A real point above an upper form bound is in the resolvent set. -/
lemma resolvent_of_form_le {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (c x : ℝ) (hx : c < x)
    (hc : ∀ ψ : A.domain, (⟪(ψ : H), A ψ⟫_ℂ).re ≤ c * ‖(ψ : H)‖ ^ 2) :
    (x : ℂ) ∈ resolventSet A := by
  have hb : ∀ ψ : A.domain, (x - c) * ‖(ψ : H)‖ ≤ ‖A ψ - (x : ℂ) • (ψ : H)‖ := by
    intro ψ
    apply bdd_of_inner
    rw [inner_sub_re]
    have := hc ψ
    rw [abs_of_nonpos (by nlinarith [sq_nonneg ‖(ψ : H)‖])]
    linarith
  exact sa_resolvent_of_bdd_below hA x (x - c) (by linarith) hb (by simpa using hb)

omit [CompleteSpace H] in
/-- Scaling of the quadratic form. -/
lemma form_smul {A : H →ₗ.[ℂ] H} (t : ℝ) (ψ : A.domain) :
    (⟪(((t : ℂ) • ψ : A.domain) : H), A ((t : ℂ) • ψ)⟫_ℂ).re = t ^ 2 * (⟪(ψ : H), A ψ⟫_ℂ).re := by
  rw [LinearPMap.map_smul]
  simp only [Submodule.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

omit [CompleteSpace H] in
/-- Normalization: a bound on unit vectors extends to all vectors. -/
lemma form_ge_of_unit {A : H →ₗ.[ℂ] H} (c : ℝ)
    (hc : ∀ ψ : A.domain, ‖(ψ : H)‖ = 1 → c ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) (ψ : A.domain) :
    c * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re := by
  rcases eq_or_lt_of_le (norm_nonneg (ψ : H)) with h0 | h0
  · have : (ψ : H) = 0 := norm_eq_zero.mp h0.symm
    rw [← h0, this]; simp
  · set t : ℝ := ‖(ψ : H)‖⁻¹
    have hu : ‖(((t : ℂ) • ψ : A.domain) : H)‖ = 1 := by
      rw [Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr h0), inv_mul_cancel₀ h0.ne']
    have := hc _ hu
    rw [form_smul] at this
    have ht : t ^ 2 * ‖(ψ : H)‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ h0.ne', one_pow]
    have hpos : 0 < ‖(ψ : H)‖ ^ 2 := by positivity
    calc c * ‖(ψ : H)‖ ^ 2 ≤ t ^ 2 * (⟪(ψ : H), A ψ⟫_ℂ).re * ‖(ψ : H)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this hpos.le
      _ = (⟪(ψ : H), A ψ⟫_ℂ).re := by
          rw [mul_comm (t ^ 2), mul_assoc, ht, mul_one]

omit [CompleteSpace H] in
lemma form_le_of_unit {A : H →ₗ.[ℂ] H} (c : ℝ)
    (hc : ∀ ψ : A.domain, ‖(ψ : H)‖ = 1 → (⟪(ψ : H), A ψ⟫_ℂ).re ≤ c) (ψ : A.domain) :
    (⟪(ψ : H), A ψ⟫_ℂ).re ≤ c * ‖(ψ : H)‖ ^ 2 := by
  rcases eq_or_lt_of_le (norm_nonneg (ψ : H)) with h0 | h0
  · have : (ψ : H) = 0 := norm_eq_zero.mp h0.symm
    rw [← h0, this]; simp
  · set t : ℝ := ‖(ψ : H)‖⁻¹
    have hu : ‖(((t : ℂ) • ψ : A.domain) : H)‖ = 1 := by
      rw [Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr h0), inv_mul_cancel₀ h0.ne']
    have := hc _ hu
    rw [form_smul] at this
    have ht : t ^ 2 * ‖(ψ : H)‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ h0.ne', one_pow]
    have hpos : 0 < ‖(ψ : H)‖ ^ 2 := by positivity
    calc (⟪(ψ : H), A ψ⟫_ℂ).re = t ^ 2 * (⟪(ψ : H), A ψ⟫_ℂ).re * ‖(ψ : H)‖ ^ 2 := by
          rw [mul_comm (t ^ 2), mul_assoc, ht, mul_one]
      _ ≤ c * ‖(ψ : H)‖ ^ 2 := mul_le_mul_of_nonneg_right this hpos.le

end TeschlQM.MinMax.Core

open TeschlQM.MinMax TeschlQM.MinMax.Core

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ spectrum A}) =
        ⨅ (ψ : A.domain) (_ : ‖(ψ : H)‖ = 1), ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal) ∧
      sSup ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ spectrum A}) =
        ⨆ (ψ : A.domain) (_ : ‖(ψ : H)‖ = 1), ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal) := by
  constructor
  · apply le_antisymm
    · refine le_iInf₂ fun ψ hψ => ?_
      by_contra hcon
      push_neg at hcon
      obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
      have hspec : ∀ x : ℝ, (x : ℂ) ∈ spectrum A → m ≤ x := by
        intro x hx
        have : sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ spectrum A}) ≤ (x : EReal) :=
          sInf_le ⟨x, hx, rfl⟩
        exact_mod_cast (hm2.trans_le this).le
      have := form_ge_of_spectrum_ge hA m hspec ψ
      rw [hψ, one_pow, mul_one] at this
      exact absurd (EReal.coe_lt_coe_iff.mp hm1) (not_lt.mpr this)
    · refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
      have hunit : ∀ ψ : A.domain, ‖(ψ : H)‖ = 1 → c ≤ (⟪(ψ : H), A ψ⟫_ℂ).re := by
        intro ψ hψ
        have : (⨅ (ψ : A.domain) (_ : ‖(ψ : H)‖ = 1), ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal)) ≤
            ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal) := iInf₂_le ψ hψ
        exact_mod_cast (hc2.trans_le this).le
      exact hx (resolvent_of_form_ge hA c x (EReal.coe_lt_coe_iff.mp hc1)
        (form_ge_of_unit c hunit))
  · apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
      have hunit : ∀ ψ : A.domain, ‖(ψ : H)‖ = 1 → (⟪(ψ : H), A ψ⟫_ℂ).re ≤ c := by
        intro ψ hψ
        have : ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal) ≤
            (⨆ (ψ : A.domain) (_ : ‖(ψ : H)‖ = 1), ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal)) :=
          le_iSup₂ (f := fun (ψ : A.domain) (_ : ‖(ψ : H)‖ = 1) =>
            ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal)) ψ hψ
        exact_mod_cast (this.trans_lt hc1).le
      exact hx (resolvent_of_form_le hA c x (EReal.coe_lt_coe_iff.mp hc2)
        (form_le_of_unit c hunit))
    · refine iSup₂_le fun ψ hψ => ?_
      by_contra hcon
      push_neg at hcon
      obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
      have hspec : ∀ x : ℝ, (x : ℂ) ∈ spectrum A → x ≤ m := by
        intro x hx
        have : (x : EReal) ≤ sSup ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ spectrum A}) :=
          le_sSup ⟨x, hx, rfl⟩
        exact_mod_cast (this.trans_lt hm1).le
      have := form_le_of_spectrum_le hA m hspec ψ
      rw [hψ, one_pow, mul_one] at this
      exact absurd (EReal.coe_lt_coe_iff.mp hm2) (not_lt.mpr this)
