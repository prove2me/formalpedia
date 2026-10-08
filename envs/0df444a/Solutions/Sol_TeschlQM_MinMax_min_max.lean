-- Prove2me | solution 1 for TeschlQM.MinMax.min_max
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T13:04:20.123381+00:00
-- url     : https://prove2.me/submissions/e15139f9-18ac-4b4d-8921-3851113e1abf

import Mathlib
import Definitions.Def_TeschlQM_MinMax_spectrum
import Definitions.Def_TeschlQM_MinMax_eigenspace
import Definitions.Def_TeschlQM_MinMax_eigenvalueSeq
import Definitions.Def_TeschlQM_MinMax_minMaxSet

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

namespace TeschlQM.MinMax.MM

open TeschlQM.MinMax TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

/-- The resolvent `(A - i)⁻¹`. -/
noncomputable def res (hA : IsSelfAdjoint A) : H →L[ℂ] H :=
  (sa_resolvent_of_im_ne hA Complex.I (by simp)).choose

lemma res_left (hA : IsSelfAdjoint A) (ψ : A.domain) :
    res hA (A ψ - Complex.I • (ψ : H)) = ψ :=
  (sa_resolvent_of_im_ne hA Complex.I (by simp)).choose_spec.1 ψ

lemma res_mem (hA : IsSelfAdjoint A) (φ : H) : res hA φ ∈ A.domain :=
  ((sa_resolvent_of_im_ne hA Complex.I (by simp)).choose_spec.2 φ).1

lemma res_right (hA : IsSelfAdjoint A) (φ : H) :
    A ⟨res hA φ, res_mem hA φ⟩ - Complex.I • res hA φ = φ :=
  ((sa_resolvent_of_im_ne hA Complex.I (by simp)).choose_spec.2 φ).2

lemma res_injective (hA : IsSelfAdjoint A) : Function.Injective (res hA) := by
  intro x y h
  rw [← res_right hA x, ← res_right hA y]
  congr 1
  · congr 2
  · rw [h]

lemma res_normal (hA : IsSelfAdjoint A) : IsStarNormal (res hA) := by
  obtain ⟨R', hR1', hR2'⟩ := sa_resolvent_of_im_ne hA (-Complex.I) (by simp)
  choose hRd' hRe' using hR2'
  set R := res hA
  have hR1 := res_left hA
  have hRd := res_mem hA
  have hRe := res_right hA
  have hadj := resolvent_adjoint hA R R' hRd hRe hRd' hRe'
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

/-- The real number attached to a nonzero spectral point `w` of the resolvent. -/
noncomputable def xr (w : ℂ) : ℝ := (w⁻¹).re

/-- Spectral mapping, forward direction. -/
lemma res_spec_fwd (hA : IsSelfAdjoint A) (w : ℂ) (hw : w ∈ _root_.spectrum ℂ (res hA))
    (hw0 : w ≠ 0) : ((xr w : ℝ) : ℂ) ∈ spectrum A ∧ w⁻¹ = (xr w : ℂ) - Complex.I := by
  have hx := resolvent_spectrum (res hA) (res_left hA) (res_mem hA) (res_right hA) w hw hw0
  have hreal := sa_spectrum_real hA _ hx
  have hre : (Complex.I + w⁻¹).re = xr w := by simp [xr]
  rw [hre] at hreal
  refine ⟨by rw [hreal]; exact hx, ?_⟩
  rw [hreal]; ring

/-- Spectral mapping, backward direction. -/
lemma res_spec_back (hA : IsSelfAdjoint A) (z : ℂ) (hz : z ∈ spectrum A) (hzi : z ≠ Complex.I) :
    (z - Complex.I)⁻¹ ∈ _root_.spectrum ℂ (res hA) := by
  have hzi' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hzi
  set w := (z - Complex.I)⁻¹ with hw
  have hw0 : w ≠ 0 := inv_ne_zero hzi'
  have hwz : w * (z - Complex.I) = 1 := inv_mul_cancel₀ hzi'
  set R := res hA
  by_contra hns
  rw [_root_.spectrum.mem_iff, not_not] at hns
  obtain ⟨u, hu⟩ := hns
  have hcomm : Commute R (u : H →L[ℂ] H) := by
    rw [hu]
    exact (show Commute R (algebraMap ℂ _ w) from (Algebra.commutes w R).symm).sub_right
      (Commute.refl R)
  have hcomm' : Commute R (↑u⁻¹ : H →L[ℂ] H) := hcomm.units_inv_right
  set U : H →L[ℂ] H := ↑u⁻¹
  have hUB : ∀ φ, U ((algebraMap ℂ (H →L[ℂ] H) w - R) φ) = φ := by
    intro φ
    rw [← hu, ← ContinuousLinearMap.mul_apply, Units.inv_mul]; rfl
  have hBU : ∀ φ, (algebraMap ℂ (H →L[ℂ] H) w - R) (U φ) = φ := by
    intro φ
    rw [← hu, ← ContinuousLinearMap.mul_apply, Units.mul_inv]; rfl
  have hRU : ∀ φ, R (U φ) = U (R φ) := by
    intro φ
    rw [← ContinuousLinearMap.mul_apply, hcomm'.eq]; rfl
  apply hz
  refine ⟨w • (R * U), ?_, ?_⟩
  · intro ψ
    have h1 := res_left hA ψ
    have key : (algebraMap ℂ (H →L[ℂ] H) w - R) (ψ : H) =
        w • R (A ψ - z • (ψ : H)) := by
      have : A ψ - z • (ψ : H) = (A ψ - Complex.I • (ψ : H)) - (z - Complex.I) • (ψ : H) := by
        module
      rw [this, map_sub, map_smul, h1]
      simp only [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      rw [smul_sub, smul_smul, hwz, one_smul]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
    rw [hRU, ← map_smul, ← key, hUB]
  · intro φ
    refine ⟨?_, ?_⟩
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
      exact A.domain.smul_mem _ (res_mem hA _)
    · have h2 := res_right hA (U φ)
      have e : (⟨(w • (R * U)) φ, A.domain.smul_mem w (res_mem hA (U φ))⟩ : A.domain) =
          w • ⟨R (U φ), res_mem hA (U φ)⟩ := rfl
      have hB := hBU φ
      simp only [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at hB
      rw [e, show A (w • (⟨R (U φ), res_mem hA (U φ)⟩ : A.domain)) =
          w • A ⟨R (U φ), res_mem hA (U φ)⟩ from A.toFun.map_smul _ _]
      have h3 : A ⟨R (U φ), res_mem hA (U φ)⟩ = U φ + Complex.I • R (U φ) := by
        exact sub_eq_iff_eq_add.mp h2
      rw [h3]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
      have h4 : z • w • R (U φ) = (1 + w * Complex.I) • R (U φ) := by
        rw [smul_smul]; congr 1; linear_combination hwz
      rw [h4]
      linear_combination (norm := module) hB

end TeschlQM.MinMax.MM

namespace TeschlQM.MinMax.MM

open TeschlQM.MinMax TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

omit [CompleteSpace H] in
lemma mem_eigenspace_iff (z : ℂ) (v : H) :
    v ∈ eigenspace A z ↔ ∃ hv : v ∈ A.domain, A ⟨v, hv⟩ = z • v := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.coe_subtype] at hx
    simpa [sub_eq_zero] using hx
  · rintro ⟨hv, h⟩
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.coe_subtype]
    rw [sub_eq_zero]
    exact h

lemma eigen_of_res (hA : IsSelfAdjoint A) (v : H) (w0 : ℂ) (hw0 : w0 ≠ 0)
    (hv : res hA v = w0 • v) : v ∈ eigenspace A (Complex.I + w0⁻¹) := by
  have hv' : v = res hA (w0⁻¹ • v) := by
    rw [map_smul, hv, smul_smul, inv_mul_cancel₀ hw0, one_smul]
  rw [mem_eigenspace_iff]
  refine ⟨by rw [hv']; exact res_mem hA _, ?_⟩
  have e : (⟨v, by rw [hv']; exact res_mem hA _⟩ : A.domain) =
      ⟨res hA (w0⁻¹ • v), res_mem hA _⟩ := Subtype.ext hv'
  rw [e]
  have h2 := sub_eq_iff_eq_add.mp (res_right hA (w0⁻¹ • v))
  rw [h2, ← hv']
  module

lemma res_cfc (hA : IsSelfAdjoint A) (K : ℂ → ℂ)
    (hK : ContinuousOn K (_root_.spectrum ℂ (res hA))) :
    res hA * cfc K (res hA) = cfc (fun w => w * K w) (res hA) := by
  haveI := res_normal hA
  rw [cfc_mul (fun w => w) K (res hA) continuousOn_id hK, cfc_id' ℂ (res hA)]

lemma inner_cfc_cfc (hA : IsSelfAdjoint A) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (_root_.spectrum ℂ (res hA)))
    (hg : ContinuousOn g (_root_.spectrum ℂ (res hA))) (u : H) :
    ⟪cfc f (res hA) u, cfc g (res hA) u⟫_ℂ =
      ⟪u, cfc (fun w => star (f w) * g w) (res hA) u⟫_ℂ := by
  haveI := res_normal hA
  rw [cfc_mul (fun w => star (f w)) g (res hA) hf.star hg, cfc_star,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- The quadratic form on vectors of the form `R (K(R) u)`. -/
lemma qf_formula (hA : IsSelfAdjoint A) (K : ℂ → ℂ)
    (hK : ContinuousOn K (_root_.spectrum ℂ (res hA))) (c : ℝ) (u : H) :
    ⟪res hA (cfc K (res hA) u), A ⟨res hA (cfc K (res hA) u), res_mem hA _⟩ -
        (c : ℂ) • res hA (cfc K (res hA) u)⟫_ℂ =
      ⟪u, cfc (fun w => star (w * K w) * ((1 + (Complex.I - c) * w) * K w)) (res hA) u⟫_ℂ := by
  haveI := res_normal hA
  set y := cfc K (res hA) u with hy
  have h2 := sub_eq_iff_eq_add.mp (res_right hA y)
  have e1 : A ⟨res hA y, res_mem hA y⟩ - (c : ℂ) • res hA y =
      cfc (fun w => (1 + (Complex.I - c) * w) * K w) (res hA) u := by
    have hcont : ContinuousOn (fun w : ℂ => w * K w) (_root_.spectrum ℂ (res hA)) :=
      continuousOn_id.mul hK
    rw [cfc_congr (g := fun w => K w + (Complex.I - c) * (w * K w)) (fun w _ => by ring),
      cfc_add (a := res hA) K (fun w => (Complex.I - c) * (w * K w)) hK
        (continuousOn_const.mul hcont),
      cfc_const_mul (Complex.I - (c : ℂ)) (fun w => w * K w) (res hA) hcont, ← res_cfc hA K hK]
    rw [h2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, hy]
    module
  have e2 : res hA y = cfc (fun w => w * K w) (res hA) u := by
    rw [← res_cfc hA K hK]; rfl
  rw [e1, e2]
  exact inner_cfc_cfc hA _ _ (continuousOn_id.mul hK)
    (((continuousOn_const.add (continuousOn_const.mul continuousOn_id))).mul hK) u

lemma star_mul_factor (hA : IsSelfAdjoint A) (w : ℂ) (hw : w ∈ _root_.spectrum ℂ (res hA))
    (hw0 : w ≠ 0) (c : ℝ) :
    star w * (1 + (Complex.I - c) * w) = ((Complex.normSq w * (xr w - c) : ℝ) : ℂ) := by
  have hinv := (res_spec_fwd hA w hw hw0).2
  have hconj : star w = (Complex.normSq w : ℂ) * w⁻¹ := by
    rw [Complex.inv_def, Complex.star_def]
    have : (Complex.normSq w : ℂ) ≠ 0 := by exact_mod_cast Complex.normSq_pos.mpr hw0 |>.ne'
    rw [Complex.ofReal_inv, mul_left_comm, mul_inv_cancel₀ this, mul_one]
  rw [hconj]
  have : (Complex.normSq w : ℂ) * w⁻¹ * (1 + (Complex.I - c) * w) =
      (Complex.normSq w : ℂ) * (w⁻¹ + (Complex.I - c) * (w⁻¹ * w)) := by ring
  rw [this, inv_mul_cancel₀ hw0, hinv]
  push_cast
  ring

open scoped ComplexOrder in
lemma re_inner_cfc_nonneg (hA : IsSelfAdjoint A) (f : ℂ → ℂ)
    (hf : ∀ w ∈ _root_.spectrum ℂ (res hA), 0 ≤ f w) (u : H) :
    0 ≤ (⟪u, cfc f (res hA) u⟫_ℂ).re := by
  haveI := res_normal hA
  have h0 : 0 ≤ cfc f (res hA) := cfc_nonneg hf
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at h0
  exact h0.re_inner_nonneg_right u

open scoped ComplexOrder in
lemma re_inner_cfc_nonpos (hA : IsSelfAdjoint A) (f : ℂ → ℂ)
    (hf : ∀ w ∈ _root_.spectrum ℂ (res hA), f w ≤ 0) (u : H) :
    (⟪u, cfc f (res hA) u⟫_ℂ).re ≤ 0 := by
  haveI := res_normal hA
  have h := re_inner_cfc_nonneg hA (fun w => - f w) (fun w hw => neg_nonneg.mpr (hf w hw)) u
  rw [cfc_neg, ContinuousLinearMap.neg_apply, inner_neg_right, Complex.neg_re] at h
  linarith

lemma qf_fun_eq (hA : IsSelfAdjoint A) (K : ℂ → ℂ) (c : ℝ) (w : ℂ)
    (hw : w ∈ _root_.spectrum ℂ (res hA)) :
    star (w * K w) * ((1 + (Complex.I - c) * w) * K w) =
      ((if w = 0 then 0 else Complex.normSq (K w) * Complex.normSq w * (xr w - c) : ℝ) : ℂ) := by
  by_cases hw0 : w = 0
  · subst hw0; simp
  rw [if_neg hw0]
  have := star_mul_factor hA w hw hw0 c
  have e : star (w * K w) * ((1 + (Complex.I - c) * w) * K w) =
      (star (K w) * K w) * (star w * (1 + (Complex.I - c) * w)) := by
    rw [star_mul']; ring
  rw [e, this, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  push_cast
  ring

open scoped ComplexOrder in
/-- Lower bound for the quadratic form on `R (K(R) u)`. -/
lemma qf_ge (hA : IsSelfAdjoint A) (K : ℂ → ℂ)
    (hK : ContinuousOn K (_root_.spectrum ℂ (res hA))) (c : ℝ)
    (h : ∀ w ∈ _root_.spectrum ℂ (res hA), w ≠ 0 → K w ≠ 0 → c ≤ xr w) (u : H) :
    0 ≤ (⟪res hA (cfc K (res hA) u), A ⟨res hA (cfc K (res hA) u), res_mem hA _⟩ -
        (c : ℂ) • res hA (cfc K (res hA) u)⟫_ℂ).re := by
  rw [qf_formula hA K hK c u]
  apply re_inner_cfc_nonneg hA
  intro w hw
  rw [qf_fun_eq hA K c w hw]
  apply Complex.zero_le_real.mpr
  split_ifs with hw0
  · rfl
  · by_cases hK0 : K w = 0
    · simp [hK0]
    · have := h w hw hw0 hK0
      have := Complex.normSq_nonneg (K w)
      have := Complex.normSq_nonneg w
      have : 0 ≤ xr w - c := by linarith
      positivity

open scoped ComplexOrder in
/-- Upper bound for the quadratic form on `R (K(R) u)`. -/
lemma qf_le (hA : IsSelfAdjoint A) (K : ℂ → ℂ)
    (hK : ContinuousOn K (_root_.spectrum ℂ (res hA))) (c : ℝ)
    (h : ∀ w ∈ _root_.spectrum ℂ (res hA), w ≠ 0 → K w ≠ 0 → xr w ≤ c) (u : H) :
    (⟪res hA (cfc K (res hA) u), A ⟨res hA (cfc K (res hA) u), res_mem hA _⟩ -
        (c : ℂ) • res hA (cfc K (res hA) u)⟫_ℂ).re ≤ 0 := by
  rw [qf_formula hA K hK c u]
  apply re_inner_cfc_nonpos hA
  intro w hw
  rw [qf_fun_eq hA K c w hw]
  rw [← Complex.ofReal_zero, Complex.real_le_real]
  split_ifs with hw0
  · rfl
  · by_cases hK0 : K w = 0
    · simp [hK0]
    · have := h w hw hw0 hK0
      have := Complex.normSq_nonneg (K w)
      have := Complex.normSq_nonneg w
      have : 0 ≤ c - xr w := by linarith
      nlinarith [mul_nonneg (mul_nonneg (Complex.normSq_nonneg (K w))
        (Complex.normSq_nonneg w)) this]

end TeschlQM.MinMax.MM

namespace TeschlQM.MinMax.MM

open TeschlQM.MinMax TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

lemma xr_large (hA : IsSelfAdjoint A) (w : ℂ) (hw : w ∈ _root_.spectrum ℂ (res hA))
    (hw0 : w ≠ 0) : ‖w‖⁻¹ - 1 ≤ |xr w| := by
  have hinv := (res_spec_fwd hA w hw hw0).2
  have h : ‖w⁻¹‖ ≤ |xr w| + 1 := by
    rw [hinv]
    calc ‖(xr w : ℂ) - Complex.I‖ ≤ ‖(xr w : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ = |xr w| + 1 := by simp
  rw [norm_inv] at h
  linarith

lemma small_imp_large (hA : IsSelfAdjoint A) (M : ℝ) :
    ∃ δ > 0, ∀ w ∈ _root_.spectrum ℂ (res hA), w ≠ 0 → ‖w‖ < δ → M < |xr w| := by
  have hM2 : (0 : ℝ) < |M| + 2 := by positivity
  refine ⟨(|M| + 2)⁻¹, inv_pos.mpr hM2, ?_⟩
  intro w hw hw0 hlt
  have h1 := xr_large hA w hw hw0
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have h2 : |M| + 2 < ‖w‖⁻¹ := (lt_inv_comm₀ hpos hM2).mp hlt
  linarith [le_abs_self M]

lemma eventually_small (S : Set ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ w in nhdsWithin (0 : ℂ) S, w ∈ S ∧ ‖w‖ < δ := by
  have h1 : ∀ᶠ w in nhdsWithin (0 : ℂ) S, w ∈ S := self_mem_nhdsWithin
  have h2 : ∀ᶠ w in nhdsWithin (0 : ℂ) S, ‖w‖ < δ := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have := Metric.ball_mem_nhds (0 : ℂ) hδ
    filter_upwards [this] with w hw
    simpa using hw
  filter_upwards [h1, h2] with w a b
  exact ⟨a, b⟩

lemma contOn_of_eventually (S : Set ℂ) (F : ℂ → ℂ)
    (h : ∀ w0 ∈ S, ∀ᶠ w in nhdsWithin w0 S, F w = F w0) : ContinuousOn F S :=
  fun w0 hw0 => continuousWithinAt_const.congr_of_eventuallyEq (h w0 hw0) rfl

lemma xr_contAt {w0 : ℂ} (hw0 : w0 ≠ 0) : ContinuousAt xr w0 :=
  Complex.continuous_re.continuousAt.comp (continuousAt_inv₀ hw0)

lemma eventually_ne_zero {w0 : ℂ} (hw0 : w0 ≠ 0) (S : Set ℂ) :
    ∀ᶠ w in nhdsWithin w0 S, w ≠ 0 :=
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds hw0)

/-- The indicator of the spectral point of `R` corresponding to `l`. -/
noncomputable def chi (l : ℝ) (w : ℂ) : ℂ := if w ≠ 0 ∧ xr w = l then 1 else 0

/-- `l` is isolated among the real points of the spectrum. -/
def IsoPt (A : H →ₗ.[ℂ] H) (l : ℝ) : Prop :=
  ∃ ε > 0, ∀ μ : ℝ, (μ : ℂ) ∈ spectrum A → |μ - l| < ε → μ = l

lemma chi_cont (hA : IsSelfAdjoint A) (l : ℝ) (hl : IsoPt A l) :
    ContinuousOn (chi l) (_root_.spectrum ℂ (res hA)) := by
  apply contOn_of_eventually
  intro w0 hw0
  by_cases h0 : w0 = 0
  · subst h0
    obtain ⟨δ, hδ, hδ'⟩ := small_imp_large hA |l|
    filter_upwards [eventually_small _ δ hδ] with w ⟨hw, hwδ⟩
    simp only [chi]
    rw [if_neg, if_neg]
    · simp
    · rintro ⟨hw0, hx⟩
      have := hδ' w hw hw0 hwδ
      rw [hx] at this
      exact lt_irrefl _ this
  · by_cases hx : xr w0 = l
    · obtain ⟨ε, hε, hε'⟩ := hl
      have hball : ∀ᶠ w in nhdsWithin w0 (_root_.spectrum ℂ (res hA)), |xr w - l| < ε := by
        apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
        have := (xr_contAt h0).eventually (Metric.ball_mem_nhds (xr w0) hε)
        filter_upwards [this] with w hw
        rw [← hx]
        simpa [Real.dist_eq] using hw
      filter_upwards [self_mem_nhdsWithin, eventually_ne_zero h0 _, hball] with w hw hw0' hwε
      have hσ := (res_spec_fwd hA w hw hw0').1
      have := hε' _ hσ hwε
      simp only [chi]
      rw [if_pos ⟨hw0', this⟩, if_pos ⟨h0, hx⟩]
    · have hne : ∀ᶠ w in nhdsWithin w0 (_root_.spectrum ℂ (res hA)), xr w ≠ l := by
        apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
        exact (xr_contAt h0).eventually (isOpen_ne.mem_nhds hx)
      filter_upwards [hne] with w hw
      simp only [chi]
      rw [if_neg (fun h => hw h.2), if_neg (fun h => hx h.2)]

lemma xr_wl (l : ℝ) : xr (((l : ℂ) - Complex.I)⁻¹) = l := by simp [xr]

lemma wl_ne (l : ℝ) : ((l : ℂ) - Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma chi_range (hA : IsSelfAdjoint A) (l : ℝ) (hl : IsoPt A l) (u : H) :
    cfc (chi l) (res hA) u ∈ eigenspace A (l : ℂ) := by
  haveI := res_normal hA
  set wl : ℂ := ((l : ℂ) - Complex.I)⁻¹ with hwl
  have hwl0 : wl ≠ 0 := inv_ne_zero (wl_ne l)
  have hc := chi_cont hA l hl
  have key : res hA * cfc (chi l) (res hA) = wl • cfc (chi l) (res hA) := by
    rw [res_cfc hA _ hc, ← cfc_const_mul wl (chi l) (res hA) hc]
    apply cfc_congr
    intro w hw
    simp only [chi]
    split_ifs with h
    · obtain ⟨hw0, hx⟩ := h
      have hinv := (res_spec_fwd hA w hw hw0).2
      rw [hx] at hinv
      have : w = wl := by rw [hwl, ← hinv, inv_inv]
      rw [this]
    · simp
  have hv : res hA (cfc (chi l) (res hA) u) = wl • cfc (chi l) (res hA) u := by
    have := congrArg (fun T => T u) key
    simpa using this
  have := eigen_of_res hA _ wl hwl0 hv
  have e : Complex.I + wl⁻¹ = (l : ℂ) := by rw [hwl, inv_inv]; ring
  rwa [e] at this

lemma chi_ne_zero (hA : IsSelfAdjoint A) (l : ℝ) (hl : IsoPt A l)
    (hσ : (l : ℂ) ∈ spectrum A) : ∃ u, cfc (chi l) (res hA) u ≠ 0 := by
  haveI := res_normal hA
  by_contra hcon
  push_neg at hcon
  have h0 : cfc (chi l) (res hA) = cfc (0 : ℂ → ℂ) (res hA) := by
    rw [cfc_zero]
    ext u
    simpa using hcon u
  have heq := eqOn_of_cfc_eq_cfc h0 (chi_cont hA l hl) continuous_zero.continuousOn
  have hne : (l : ℂ) ≠ Complex.I := fun h => wl_ne l (by rw [h, sub_self])
  have hwl := res_spec_back hA (l : ℂ) hσ hne
  have := heq hwl
  simp only [chi, Pi.zero_apply] at this
  rw [if_pos ⟨inv_ne_zero (wl_ne l), xr_wl l⟩] at this
  exact one_ne_zero this

lemma chi_proj (hA : IsSelfAdjoint A) (l : ℝ) (hl : IsoPt A l) :
    star (cfc (chi l) (res hA)) * cfc (chi l) (res hA) = cfc (chi l) (res hA) := by
  haveI := res_normal hA
  have hc := chi_cont hA l hl
  rw [← cfc_star, ← cfc_mul _ _ _ hc.star hc]
  apply cfc_congr
  intro w _
  simp only [chi]
  split_ifs <;> simp

lemma chi_apply_eq_zero (hA : IsSelfAdjoint A) (l : ℝ) (hl : IsoPt A l) (φ : H)
    (h : ⟪φ, cfc (chi l) (res hA) φ⟫_ℂ = 0) : cfc (chi l) (res hA) φ = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
    ← ContinuousLinearMap.star_eq_adjoint, chi_proj hA l hl, h]

lemma cfc_res_comm (hA : IsSelfAdjoint A) (K : ℂ → ℂ) (x : H) :
    cfc K (res hA) (res hA x) = res hA (cfc K (res hA) x) := by
  haveI := res_normal hA
  have := cfc_commute_cfc K (fun w => w) (res hA)
  rw [cfc_id' ℂ (res hA)] at this
  have := congrArg (fun T => T x) this.eq
  simpa using this

/-- Lift of a real function to the spectrum of the resolvent. -/
noncomputable def lift (b : ℝ → ℝ) (w : ℂ) : ℂ := if w = 0 then 0 else ((b (xr w) : ℝ) : ℂ)

lemma contOn_of_vanish (hA : IsSelfAdjoint A) (F : ℂ → ℂ) (hF : ∀ w, w ≠ 0 → ContinuousAt F w)
    (h0 : ∃ δ > 0, ∀ w ∈ _root_.spectrum ℂ (res hA), ‖w‖ < δ → F w = F 0) :
    ContinuousOn F (_root_.spectrum ℂ (res hA)) := by
  intro w hw
  by_cases hw0 : w = 0
  · subst hw0
    obtain ⟨δ, hδ, hδ'⟩ := h0
    apply continuousWithinAt_const.congr_of_eventuallyEq _ rfl
    filter_upwards [eventually_small _ δ hδ] with w ⟨a, b⟩
    exact hδ' w a b
  · exact (hF w hw0).continuousWithinAt

lemma lift_vanish (hA : IsSelfAdjoint A) (b : ℝ → ℝ) (M : ℝ) (hM : ∀ x, M ≤ |x| → b x = 0) :
    ∃ δ > 0, ∀ w ∈ _root_.spectrum ℂ (res hA), ‖w‖ < δ → lift b w = 0 := by
  obtain ⟨δ, hδ, hδ'⟩ := small_imp_large hA M
  refine ⟨δ, hδ, fun w hw hwδ => ?_⟩
  simp only [lift]
  split_ifs with h
  · rfl
  · rw [hM _ (hδ' w hw h hwδ).le]; simp

lemma lift_contAt (b : ℝ → ℝ) (hb : Continuous b) {w0 : ℂ} (hw0 : w0 ≠ 0) :
    ContinuousAt (lift b) w0 := by
  have hc : ContinuousAt (fun w => ((b (xr w) : ℝ) : ℂ)) w0 :=
    Complex.continuous_ofReal.continuousAt.comp (hb.continuousAt.comp (xr_contAt hw0))
  apply hc.congr
  filter_upwards [isOpen_ne.mem_nhds hw0] with w hw
  simp [lift, hw]

lemma lift_cont (hA : IsSelfAdjoint A) (b : ℝ → ℝ) (hb : Continuous b) (M : ℝ)
    (hM : ∀ x, M ≤ |x| → b x = 0) : ContinuousOn (lift b) (_root_.spectrum ℂ (res hA)) := by
  apply contOn_of_vanish hA _ (fun w hw => lift_contAt b hb hw)
  obtain ⟨δ, hδ, hδ'⟩ := lift_vanish hA b M hM
  exact ⟨δ, hδ, fun w hw hwδ => by rw [hδ' w hw hwδ]; simp [lift]⟩

lemma liftK_cont (hA : IsSelfAdjoint A) (b : ℝ → ℝ) (hb : Continuous b) (M : ℝ)
    (hM : ∀ x, M ≤ |x| → b x = 0) :
    ContinuousOn (fun w => lift b w * w⁻¹) (_root_.spectrum ℂ (res hA)) := by
  apply contOn_of_vanish hA _ (fun w hw => (lift_contAt b hb hw).mul (continuousAt_inv₀ hw))
  obtain ⟨δ, hδ, hδ'⟩ := lift_vanish hA b M hM
  exact ⟨δ, hδ, fun w hw hwδ => by
    show lift b w * w⁻¹ = lift b 0 * (0 : ℂ)⁻¹
    rw [hδ' w hw hwδ]; simp [lift]⟩

lemma cfc_lift (hA : IsSelfAdjoint A) (b : ℝ → ℝ) (hb : Continuous b) (M : ℝ)
    (hM : ∀ x, M ≤ |x| → b x = 0) :
    cfc (lift b) (res hA) = res hA * cfc (fun w => lift b w * w⁻¹) (res hA) := by
  rw [res_cfc hA _ (liftK_cont hA b hb M hM)]
  apply cfc_congr
  intro w _
  by_cases h : w = 0
  · simp [lift, h]
  · simp only
    field_simp

lemma lift_mul (b c : ℝ → ℝ) (w : ℂ) :
    lift b w * lift c w = lift (fun x => b x * c x) w := by
  simp only [lift]
  split_ifs <;> push_cast <;> ring

lemma lift_wl (b : ℝ → ℝ) (l : ℝ) : lift b (((l : ℂ) - Complex.I)⁻¹) = b l := by
  simp only [lift, inv_eq_zero, wl_ne l, if_false, xr_wl]

/-- Vectors in the range of `b(A)` (for `b` supported in `(-∞, s]`) have form `≤ s`. -/
lemma lift_qf_le (hA : IsSelfAdjoint A) (b : ℝ → ℝ) (hb : Continuous b) (M : ℝ)
    (hM : ∀ x, M ≤ |x| → b x = 0) (s : ℝ) (hbs : ∀ x, b x ≠ 0 → x ≤ s) (u : H) :
    ∃ hv : cfc (lift b) (res hA) u ∈ A.domain,
      (⟪cfc (lift b) (res hA) u, A ⟨_, hv⟩⟫_ℂ).re ≤ s * ‖cfc (lift b) (res hA) u‖ ^ 2 := by
  set K := fun w => lift b w * w⁻¹ with hK
  have hKc : ContinuousOn K (_root_.spectrum ℂ (res hA)) := liftK_cont hA b hb M hM
  have e : cfc (lift b) (res hA) u = res hA (cfc K (res hA) u) := by
    rw [cfc_lift hA b hb M hM]; rfl
  have hq := qf_le hA K hKc s (by
    intro w _ hw0 hKw
    apply hbs
    intro hb0
    apply hKw
    simp [hK, lift, hw0, hb0]) u
  refine ⟨by rw [e]; exact res_mem hA _, ?_⟩
  have e2 : (⟨cfc (lift b) (res hA) u, by rw [e]; exact res_mem hA _⟩ : A.domain) =
      ⟨res hA (cfc K (res hA) u), res_mem hA _⟩ := Subtype.ext e
  rw [e2, e]
  have hn : ∀ x : H, ((s : ℂ) * ⟪x, x⟫_ℂ).re = s * ‖x‖ ^ 2 := by
    intro x; rw [Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]; norm_cast
  rw [inner_sub_right, inner_smul_right, Complex.sub_re, hn] at hq
  linarith

end TeschlQM.MinMax.MM

namespace TeschlQM.MinMax.MM

open TeschlQM.MinMax TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

omit [CompleteSpace H] in
lemma eigenspace_le_domain (z : ℂ) : eigenspace A z ≤ A.domain := by
  rintro v ⟨x, _, rfl⟩
  exact x.2

lemma eigenspaceBelow_le_domain (x : ℝ) : eigenspaceBelow A x ≤ A.domain :=
  iSup₂_le fun _ _ => eigenspace_le_domain _

lemma eigenspace_le_below {μ x : ℝ} (h1 : (μ : EReal) < infEssSpectrum A) (h2 : μ ≤ x) :
    eigenspace A (μ : ℂ) ≤ eigenspaceBelow A x :=
  le_iSup₂_of_le (f := fun (μ : ℝ) (_ : (μ : EReal) < infEssSpectrum A ∧ μ ≤ x) =>
    eigenspace A (μ : ℂ)) μ ⟨h1, h2⟩ le_rfl

lemma eig_orth (hA : IsSelfAdjoint A) {μ ν : ℝ} (hne : μ ≠ ν) {u v : H}
    (hu : u ∈ eigenspace A μ) (hv : v ∈ eigenspace A ν) : ⟪u, v⟫_ℂ = 0 := by
  obtain ⟨hu', hAu⟩ := (mem_eigenspace_iff _ _).mp hu
  obtain ⟨hv', hAv⟩ := (mem_eigenspace_iff _ _).mp hv
  have h := sa_symm hA ⟨u, hu'⟩ ⟨v, hv'⟩
  rw [hAu, hAv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have : ((μ : ℂ) - ν) * ⟪u, v⟫_ℂ = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (by exact_mod_cast sub_eq_zero.mp h1) hne
  · exact h1

omit [CompleteSpace H] in
lemma mem_orth_span {m : ℕ} (ψ : Fin m → H) (w : H) (h : ∀ j, ⟪ψ j, w⟫_ℂ = 0) :
    w ∈ (Submodule.span ℂ (Set.range ψ))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

omit [CompleteSpace H] in
/-- Dimension count: a subspace of dimension `≥ n` on which the form is `≤ s` gives a test
vector in every `U(ψ₁,…,ψ_{n-1})`. -/
lemma inf_le_of_subspace {n : ℕ} (ψ : Fin (n - 1) → H) (hn : 1 ≤ n) (W : Submodule ℂ H)
    (hWd : W ≤ A.domain) (hrank : (n : Cardinal) ≤ Module.rank ℂ W) (s : ℝ)
    (hq : ∀ w (hw : w ∈ A.domain), w ∈ W → (⟪w, A ⟨w, hw⟩⟫_ℂ).re ≤ s * ‖w‖ ^ 2) :
    ⨅ φ ∈ minMaxSet A ψ, (((⟪(φ : H), A φ⟫_ℂ).re : ℝ) : EReal) ≤ s := by
  let T : W →ₗ[ℂ] (Fin (n - 1) → ℂ) :=
    { toFun := fun w j => ⟪ψ j, (w : H)⟫_ℂ
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro c x; ext j; simp }
  have hker : ∃ w : W, w ≠ 0 ∧ T w = 0 := by
    by_contra hcon
    push_neg at hcon
    have hinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      by_contra h
      exact hcon x h hx
    have := LinearMap.lift_rank_le_of_injective T hinj
    rw [rank_fin_fun, Cardinal.lift_natCast, Cardinal.lift_uzero] at this
    have h2 := hrank.trans this
    norm_cast at h2
    omega
  obtain ⟨⟨w, hwW⟩, hw0, hTw⟩ := hker
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hwd : w ∈ A.domain := hWd hwW
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0'
  set c : ℂ := ((‖w‖⁻¹ : ℝ) : ℂ) with hc
  let φ : A.domain := c • ⟨w, hwd⟩
  have hφU : φ ∈ minMaxSet A ψ := by
    refine ⟨?_, ?_⟩
    · show ‖c • w‖ = 1
      rw [norm_smul, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
        inv_mul_cancel₀ hnorm.ne']
    · show c • w ∈ _
      apply Submodule.smul_mem
      apply mem_orth_span
      intro j
      exact congrFun hTw j
  have hφq : (⟪(φ : H), A φ⟫_ℂ).re ≤ s := by
    have e : A φ = c • A ⟨w, hwd⟩ := A.toFun.map_smul c ⟨w, hwd⟩
    show (⟪c • w, A φ⟫_ℂ).re ≤ s
    rw [e, inner_smul_left, inner_smul_right, hc, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    have := hq w hwd hwW
    have hpos : 0 ≤ ‖w‖⁻¹ * ‖w‖⁻¹ := by positivity
    calc ‖w‖⁻¹ * ‖w‖⁻¹ * (⟪w, A ⟨w, hwd⟩⟫_ℂ).re ≤ ‖w‖⁻¹ * ‖w‖⁻¹ * (s * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = s := by field_simp
  calc _ ≤ (((⟪(φ : H), A φ⟫_ℂ).re : ℝ) : EReal) := iInf₂_le φ hφU
    _ ≤ s := EReal.coe_le_coe_iff.mpr hφq

/-- Transport of `qf_ge` to an arbitrary element of the domain. -/
lemma qf_ge' (hA : IsSelfAdjoint A) (K : ℂ → ℂ)
    (hK : ContinuousOn K (_root_.spectrum ℂ (res hA))) (c : ℝ)
    (h : ∀ w ∈ _root_.spectrum ℂ (res hA), w ≠ 0 → K w ≠ 0 → c ≤ xr w) (u : H)
    (φ : A.domain) (hφ : (φ : H) = res hA (cfc K (res hA) u)) :
    c * ‖(φ : H)‖ ^ 2 ≤ (⟪(φ : H), A φ⟫_ℂ).re := by
  obtain ⟨φ, hφd⟩ := φ
  simp only at hφ
  subst hφ
  have := qf_ge hA K hK c h u
  have hn : ∀ x : H, ((c : ℂ) * ⟪x, x⟫_ℂ).re = c * ‖x‖ ^ 2 := by
    intro x; rw [Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]; norm_cast
  rw [inner_sub_right, inner_smul_right, Complex.sub_re, hn] at this
  simp only
  linarith

/-- Points of the spectrum below `inf σ_ess` are in the discrete spectrum. -/
lemma discrete_of_lt (l : ℝ) (hl : (l : ℂ) ∈ spectrum A) (hlt : (l : EReal) < infEssSpectrum A) :
    (l : ℂ) ∈ discreteSpectrum A := by
  by_contra hd
  have hess : (l : ℂ) ∈ essentialSpectrum A := ⟨hl, hd⟩
  have : infEssSpectrum A ≤ (l : EReal) := sInf_le ⟨l, hess, rfl⟩
  exact absurd hlt (not_lt.mpr this)

lemma isoPt_of_discrete (l : ℝ) (hl : (l : ℂ) ∈ discreteSpectrum A) : IsoPt A l := by
  obtain ⟨_, _, ⟨ε, hε, h⟩, _⟩ := hl
  refine ⟨ε, hε, fun μ hμ hμl => ?_⟩
  have := h (μ : ℂ) hμ (by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hμl)
  exact_mod_cast this

lemma discrete_of_isoPt (hA : IsSelfAdjoint A) (l : ℝ) (hl : (l : ℂ) ∈ spectrum A)
    (hiso : IsoPt A l) (hne : eigenspace A (l : ℂ) ≠ ⊥)
    (hfin : FiniteDimensional ℂ (eigenspace A (l : ℂ))) : (l : ℂ) ∈ discreteSpectrum A := by
  obtain ⟨ε, hε, h⟩ := hiso
  refine ⟨hl, hne, ⟨ε, hε, fun w hw hwl => ?_⟩, hfin⟩
  have hre := sa_spectrum_real hA w hw
  rw [← hre] at hw hwl ⊢
  have := h w.re hw (by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hwl; exact hwl)
  rw [this]

end TeschlQM.MinMax.MM

namespace TeschlQM.MinMax.MM

open TeschlQM.MinMax TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

omit [CompleteSpace H] in
lemma inner_sum_orth {ι : Type*} (s : Finset ι) (f : ι → H) (c : ι → ℂ)
    (horth : ∀ i j, i ≠ j → ⟪f i, f j⟫_ℂ = 0) :
    ⟪∑ i ∈ s, f i, ∑ j ∈ s, c j • f j⟫_ℂ = ∑ i ∈ s, c i * ((‖f i‖ : ℂ) ^ 2) := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single_of_mem i hi]
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K]; rfl
  · intro j _ hji
    rw [inner_smul_right, horth i j (Ne.symm hji), mul_zero]

/-- The form is `≤ x` on the span of the eigenvectors with eigenvalues `≤ x`. -/
lemma below_form (hA : IsSelfAdjoint A) (x : ℝ) (w : H) (hw : w ∈ A.domain)
    (hwV : w ∈ eigenspaceBelow A x) : (⟪w, A ⟨w, hw⟩⟫_ℂ).re ≤ x * ‖w‖ ^ 2 := by
  have hV : eigenspaceBelow A x = ⨆ i : {μ : ℝ // (μ : EReal) < infEssSpectrum A ∧ μ ≤ x},
      eigenspace A ((i : ℝ) : ℂ) := by
    rw [eigenspaceBelow, iSup_subtype']
  rw [hV, Submodule.mem_iSup_iff_exists_finsupp] at hwV
  obtain ⟨f, hf, rfl⟩ := hwV
  have hfd : ∀ i, f i ∈ A.domain := fun i => eigenspace_le_domain _ (hf i)
  have hAf : ∀ i, A ⟨f i, hfd i⟩ = (((i : ℝ) : ℂ)) • f i := fun i => by
    obtain ⟨_, h2⟩ := (mem_eigenspace_iff _ _).mp (hf i)
    exact h2
  have horth : ∀ i j, i ≠ j → ⟪f i, f j⟫_ℂ = 0 := fun i j hij =>
    eig_orth hA (fun h => hij (Subtype.ext h)) (hf i) (hf j)
  set g := fun i => (⟨f i, hfd i⟩ : A.domain) with hg
  have hsum : (f.sum fun _ xi => xi) = ((∑ i ∈ f.support, g i : A.domain) : H) := by
    rw [Finsupp.sum, Submodule.coe_sum]
  have hsub : (⟨f.sum fun _ xi => xi, hw⟩ : A.domain) = ∑ i ∈ f.support, g i :=
    Subtype.ext hsum
  have hAsum : A (∑ i ∈ f.support, g i) = ∑ i ∈ f.support, (((i : ℝ) : ℂ)) • f i := by
    rw [show A (∑ i ∈ f.support, g i) = ∑ i ∈ f.support, A (g i) from map_sum A.toFun _ _]
    exact Finset.sum_congr rfl fun i _ => hAf i
  rw [hsub, hAsum, hsum, Submodule.coe_sum]
  have e1 := inner_sum_orth f.support (fun i => f i) (fun i => (((i : ℝ) : ℂ))) horth
  have e2 := inner_sum_orth f.support (fun i => f i) (fun _ => (1 : ℂ)) horth
  simp only [one_smul, one_mul] at e2
  rw [e1]
  have hn : ‖∑ i ∈ f.support, f i‖ ^ 2 = ∑ i ∈ f.support, ‖f i‖ ^ 2 := by
    have := congrArg Complex.re e2
    rw [inner_self_eq_norm_sq_to_K] at this
    have h1 : (((‖∑ i ∈ f.support, f i‖ : ℝ) : ℂ) ^ 2).re = ‖∑ i ∈ f.support, f i‖ ^ 2 := by
      norm_cast
    have h2 : (∑ i ∈ f.support, ((‖f i‖ : ℝ) : ℂ) ^ 2).re = ∑ i ∈ f.support, ‖f i‖ ^ 2 := by
      norm_cast
    exact h1.symm.trans (this.trans h2)
  show _ ≤ x * ‖∑ i ∈ f.support, f i‖ ^ 2
  rw [hn]
  have h3 : (∑ i ∈ f.support, (((i : ℝ) : ℂ)) * ((‖f i‖ : ℝ) : ℂ) ^ 2).re =
      ∑ i ∈ f.support, (i : ℝ) * ‖f i‖ ^ 2 := by
    norm_cast
  try simp only at h3 ⊢
  rw [h3, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right i.2.2 (sq_nonneg _)

/-- Upper bound from eigenvalues below `x`. -/
lemma upper_a (hA : IsSelfAdjoint A) {n : ℕ} (ψ : Fin (n - 1) → H) (hn : 1 ≤ n) (x : ℝ)
    (hrank : (n : Cardinal) ≤ Module.rank ℂ (eigenspaceBelow A x)) :
    ⨅ φ ∈ minMaxSet A ψ, (((⟪(φ : H), A φ⟫_ℂ).re : ℝ) : EReal) ≤ x :=
  inf_le_of_subspace ψ hn _ (eigenspaceBelow_le_domain x) hrank x
    (fun w hw hwV => below_form hA x w hw hwV)

omit [CompleteSpace H] in
lemma rank_ge_of_not_fin (W : Submodule ℂ H) (h : ¬ FiniteDimensional ℂ W) (n : ℕ) :
    (n : Cardinal) ≤ Module.rank ℂ W := by
  have : ¬ Module.rank ℂ W < Cardinal.aleph0 := fun h' => h (Module.rank_lt_aleph0_iff.mp h')
  exact (Cardinal.nat_lt_aleph0 n).le.trans (not_lt.mp this)

omit [CompleteSpace H] in
lemma upper_iso_inf {n : ℕ} (ψ : Fin (n - 1) → H) (hn : 1 ≤ n) (l : ℝ)
    (hfin : ¬ FiniteDimensional ℂ (eigenspace A (l : ℂ))) (s : ℝ) (hls : l < s) :
    ⨅ φ ∈ minMaxSet A ψ, (((⟪(φ : H), A φ⟫_ℂ).re : ℝ) : EReal) ≤ s := by
  refine inf_le_of_subspace ψ hn _ (eigenspace_le_domain _) (rank_ge_of_not_fin _ hfin n) s ?_
  intro w hw hwE
  obtain ⟨_, hAw⟩ := (mem_eigenspace_iff _ _).mp hwE
  have e : A ⟨w, hw⟩ = (l : ℂ) • w := hAw
  rw [e, inner_smul_right, inner_self_eq_norm_sq_to_K]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hls.le (sq_nonneg ‖w‖))
  norm_cast
  rw [Complex.re_ofReal_mul]
  first | rfl | simp

lemma not_iso_infinite (l : ℝ) (hiso : ¬ IsoPt A l) (ε : ℝ) (hε : 0 < ε) :
    {μ : ℝ | (μ : ℂ) ∈ spectrum A ∧ |μ - l| < ε}.Infinite := by
  simp only [IsoPt, not_exists, not_and, not_forall] at hiso
  set S' := {μ : ℝ | ((μ : ℂ) ∈ spectrum A ∧ |μ - l| < ε) ∧ μ ≠ l}
  have himg : ((fun μ => |μ - l|⁻¹) '' S').Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    have hr : 0 < min ε (|a| + 1)⁻¹ := lt_min hε (by positivity)
    obtain ⟨μ, hμ, hμl, hne⟩ := hiso _ hr
    have hpos : 0 < |μ - l| := abs_pos.mpr (sub_ne_zero.mpr hne)
    refine ⟨|μ - l|⁻¹, ⟨μ, ⟨⟨hμ, lt_of_lt_of_le hμl (min_le_left _ _)⟩, hne⟩, rfl⟩, ?_⟩
    have h1 : |μ - l| < (|a| + 1)⁻¹ := lt_of_lt_of_le hμl (min_le_right _ _)
    have h2 : |a| + 1 < |μ - l|⁻¹ := (lt_inv_comm₀ hpos (by positivity)).mp h1
    linarith [le_abs_self a]
  exact (himg.of_image _).mono (fun μ hμ => hμ.1)

lemma lift_ne_zero (hA : IsSelfAdjoint A) (b : ℝ → ℝ) (hb : Continuous b) (M : ℝ)
    (hM : ∀ x, M ≤ |x| → b x = 0) (μ : ℝ) (hμ : (μ : ℂ) ∈ spectrum A) (hbμ : b μ ≠ 0) :
    ∃ u, cfc (lift b) (res hA) u ≠ 0 := by
  haveI := res_normal hA
  by_contra hcon
  push_neg at hcon
  have h0 : cfc (lift b) (res hA) = cfc (0 : ℂ → ℂ) (res hA) := by
    rw [cfc_zero]
    ext u
    simpa using hcon u
  have heq := eqOn_of_cfc_eq_cfc h0 (lift_cont hA b hb M hM) continuous_zero.continuousOn
  have hne : (μ : ℂ) ≠ Complex.I := fun h => wl_ne μ (by rw [h, sub_self])
  have := heq (res_spec_back hA (μ : ℂ) hμ hne)
  rw [lift_wl, Pi.zero_apply] at this
  exact hbμ (by exact_mod_cast this)

lemma cfc_lift_comp (hA : IsSelfAdjoint A) (b c : ℝ → ℝ) (hb : Continuous b) (M : ℝ)
    (hM : ∀ x, M ≤ |x| → b x = 0) (hc : Continuous c) (N : ℝ)
    (hN : ∀ x, N ≤ |x| → c x = 0) (u : H) :
    cfc (lift b) (res hA) (cfc (lift c) (res hA) u) =
      cfc (lift (fun x => b x * c x)) (res hA) u := by
  haveI := res_normal hA
  rw [← ContinuousLinearMap.mul_apply, ← cfc_mul _ _ _ (lift_cont hA b hb M hM)
    (lift_cont hA c hc N hN)]
  congr 2
  ext w
  exact lift_mul b c w

lemma lift_zero_fun : lift (fun _ => (0 : ℝ)) = 0 := by
  ext w
  simp [lift]

lemma upper_noniso (hA : IsSelfAdjoint A) {n : ℕ} (ψ : Fin (n - 1) → H) (hn : 1 ≤ n) (l : ℝ)
    (hiso : ¬ IsoPt A l) (s : ℝ) (hls : l < s) :
    ⨅ φ ∈ minMaxSet A ψ, (((⟪(φ : H), A φ⟫_ℂ).re : ℝ) : EReal) ≤ s := by
  haveI := res_normal hA
  set ε := min 1 (s - l) with hεdef
  have hε : 0 < ε := lt_min one_pos (by linarith)
  obtain ⟨T, hT, hTc⟩ := (not_iso_infinite l hiso ε hε).exists_subset_card_eq n
  set μ : Fin n → ℝ := fun i => T.orderEmbOfFin hTc i with hμdef
  have hμmem : ∀ i, (μ i : ℂ) ∈ spectrum A ∧ |μ i - l| < ε :=
    fun i => hT (T.orderEmbOfFin_mem hTc i)
  have hμinj : Function.Injective μ := (T.orderEmbOfFin hTc).injective
  obtain ⟨δ, hδ, hsep⟩ : ∃ δ > 0, ∀ i j, i ≠ j → 2 * δ ≤ |μ i - μ j| := by
    haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
    obtain ⟨p, hp⟩ := Finite.exists_min
      (fun p : Fin n × Fin n => if p.1 = p.2 then (1 : ℝ) else |μ p.1 - μ p.2|)
    have hpos : ∀ q : Fin n × Fin n,
        0 < (if q.1 = q.2 then (1 : ℝ) else |μ q.1 - μ q.2|) := by
      intro q
      split_ifs with h
      · exact one_pos
      · exact abs_pos.mpr (sub_ne_zero.mpr (fun h' => h (hμinj h')))
    refine ⟨(if p.1 = p.2 then (1 : ℝ) else |μ p.1 - μ p.2|) / 2, by linarith [hpos p], ?_⟩
    intro i j hij
    have := hp (i, j)
    simp only [if_neg hij] at this
    linarith
  set b : ℝ → ℝ := fun x => max 0 (min (x - (l - 1)) (s - x)) with hbdef
  set bk : Fin n → ℝ → ℝ := fun k x => max 0 (δ - |x - μ k|) with hbkdef
  have hbc : Continuous b := by
    simp only [hbdef]; fun_prop
  have hbM : ∀ x, (|l| + |s| + 1) ≤ |x| → b x = 0 := by
    intro x hx
    simp only [hbdef]
    apply max_eq_left
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx
      have : s - x ≤ 0 := by linarith [le_abs_self s, abs_nonneg l]
      exact (min_le_right _ _).trans this
    · rw [abs_of_neg h0] at hx
      have : x - (l - 1) ≤ 0 := by linarith [neg_abs_le l, abs_nonneg s]
      exact (min_le_left _ _).trans this
  have hbs : ∀ x, b x ≠ 0 → x ≤ s := by
    intro x hx
    by_contra hxs
    push_neg at hxs
    apply hx
    simp only [hbdef]
    apply max_eq_left
    exact (min_le_right _ _).trans (by linarith)
  have hbkc : ∀ k, Continuous (bk k) := by
    intro k; simp only [hbkdef]; fun_prop
  have hbkM : ∀ k x, (|μ k| + δ) ≤ |x| → bk k x = 0 := by
    intro k x hx
    simp only [hbkdef]
    apply max_eq_left
    have : |x| - |μ k| ≤ |x - μ k| := abs_sub_abs_le_abs_sub x (μ k)
    linarith
  have hdisj : ∀ j k, j ≠ k → ∀ x, bk j x * bk k x = 0 := by
    intro j k hjk x
    simp only [hbkdef]
    by_contra hne
    rcases mul_ne_zero_iff.mp hne with ⟨h1, h2⟩
    have h1' : |x - μ j| < δ := by
      by_contra h; push_neg at h; exact h1 (max_eq_left (by linarith))
    have h2' : |x - μ k| < δ := by
      by_contra h; push_neg at h; exact h2 (max_eq_left (by linarith))
    have := hsep j k hjk
    have : |μ j - μ k| ≤ |x - μ j| + |x - μ k| := by
      calc |μ j - μ k| = |(x - μ k) - (x - μ j)| := by ring_nf
        _ ≤ |x - μ k| + |x - μ j| := abs_sub _ _
        _ = _ := add_comm _ _
    linarith
  have hbpos : ∀ k, b (μ k) ≠ 0 := by
    intro k
    have h := (hμmem k).2
    have h1 : |μ k - l| < 1 := lt_of_lt_of_le h (min_le_left _ _)
    have h2 : |μ k - l| < s - l := lt_of_lt_of_le h (min_le_right _ _)
    rw [abs_lt] at h1 h2
    simp only [hbdef]
    apply ne_of_gt
    apply lt_max_of_lt_right
    exact lt_min (by linarith) (by linarith)
  have hgM : ∀ k x, (|μ k| + δ) ≤ |x| → b x * bk k x ^ 2 = 0 := by
    intro k x hx; rw [hbkM k x hx]; ring
  have hex : ∀ k, ∃ u, cfc (lift (fun x => b x * bk k x ^ 2)) (res hA) u ≠ 0 := by
    intro k
    refine lift_ne_zero hA _ (hbc.mul ((hbkc k).pow 2)) _ (hgM k) (μ k) (hμmem k).1 ?_
    have : bk k (μ k) = δ := by simp [hbkdef, hδ.le]
    rw [this]
    exact mul_ne_zero (hbpos k) (pow_ne_zero 2 hδ.ne')
  choose u hu using hex
  set v : Fin n → H := fun k => cfc (lift b) (res hA) (cfc (lift (bk k)) (res hA) (u k)) with hvdef
  have hv_apply : ∀ j k, cfc (lift (bk j)) (res hA) (v k) =
      cfc (lift (fun x => bk j x * (b x * bk k x))) (res hA) (u k) := by
    intro j k
    simp only [hvdef]
    rw [cfc_lift_comp hA b (bk k) hbc _ hbM (hbkc k) _ (hbkM k),
      cfc_lift_comp hA (bk j) (fun x => b x * bk k x) (hbkc j) _ (hbkM j) (hbc.mul (hbkc k)) _
        (fun x hx => by (try simp only); rw [hbkM k x hx, mul_zero])]
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun y => cfc (lift (bk j)) (res hA) y) hg
    try simp only at this
    rw [map_sum, map_zero] at this
    simp_rw [map_smul, hv_apply] at this
    rw [Finset.sum_eq_single j] at this
    · have e : (fun x => bk j x * (b x * bk j x)) = fun x => b x * bk j x ^ 2 := by
        ext x; ring
      rw [e] at this
      exact (smul_eq_zero.mp this).resolve_right (hu j)
    · intro k _ hkj
      have e : (fun x => bk j x * (b x * bk k x)) = fun _ => 0 := by
        ext x
        calc bk j x * (b x * bk k x) = b x * (bk j x * bk k x) := by ring
          _ = 0 := by rw [hdisj j k (Ne.symm hkj) x, mul_zero]
      rw [e, lift_zero_fun, cfc_zero]
      simp
    · simp
  set W := Submodule.span ℂ (Set.range v)
  have hWrange : W ≤ LinearMap.range (cfc (lift b) (res hA)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩
  have hrank : (n : Cardinal) ≤ Module.rank ℂ W := by
    rw [rank_span hli]
    have h := Cardinal.mk_range_eq_of_injective hli.injective
    simp only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] at h
    rw [h]
  refine inf_le_of_subspace ψ hn W ?_ hrank s ?_
  · intro w hw
    obtain ⟨u', rfl⟩ := hWrange hw
    exact (lift_qf_le hA b hbc _ hbM s hbs u').1
  · intro w hw hwW
    obtain ⟨u', rfl⟩ := hWrange hwW
    exact (lift_qf_le hA b hbc _ hbM s hbs u').2

/-- Upper bound from a point of the essential spectrum. -/
lemma upper_b (hA : IsSelfAdjoint A) {n : ℕ} (ψ : Fin (n - 1) → H) (hn : 1 ≤ n) (l : ℝ)
    (hl : (l : ℂ) ∈ essentialSpectrum A) (s : ℝ) (hls : l < s) :
    ⨅ φ ∈ minMaxSet A ψ, (((⟪(φ : H), A φ⟫_ℂ).re : ℝ) : EReal) ≤ s := by
  have hlσ : (l : ℂ) ∈ spectrum A := hl.1
  by_cases hiso : IsoPt A l
  · by_cases hfin : FiniteDimensional ℂ (eigenspace A (l : ℂ))
    · by_cases hne : eigenspace A (l : ℂ) = ⊥
      · exfalso
        obtain ⟨u, hu⟩ := chi_ne_zero hA l hiso hlσ
        have := chi_range hA l hiso u
        rw [hne, Submodule.mem_bot] at this
        exact hu this
      · exact absurd (discrete_of_isoPt hA l hlσ hiso hne hfin) hl.2
    · exact upper_iso_inf ψ hn l hfin s hls
  · exact upper_noniso hA ψ hn l hiso s hls

end TeschlQM.MinMax.MM

namespace TeschlQM.MinMax.MM

open TeschlQM.MinMax TeschlQM.MinMax.Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

/-- Lower bound: below `E_n` the form is bounded below on a suitable `U(ψ)`. -/
lemma lower (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) (hS : (t : EReal) < infEssSpectrum A)
    (hr : ¬ (n : Cardinal) ≤ Module.rank ℂ (eigenspaceBelow A t)) :
    ∃ ψ : Fin (n - 1) → H, ∀ φ ∈ minMaxSet A ψ, t ≤ (⟪(φ : H), A φ⟫_ℂ).re := by
  haveI := res_normal hA
  set V := eigenspaceBelow A t with hVdef
  have hrlt : Module.rank ℂ V < n := not_le.mp hr
  haveI hVfin : FiniteDimensional ℂ V :=
    Module.rank_lt_aleph0_iff.mp (hrlt.trans (Cardinal.nat_lt_aleph0 n))
  set F := {x : ℝ | (x : ℂ) ∈ spectrum A ∧ x ≤ t} with hFdef
  have hFlt : ∀ x ∈ F, (x : EReal) < infEssSpectrum A := fun x hx =>
    lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hx.2) hS
  have hFdisc : ∀ x ∈ F, (x : ℂ) ∈ discreteSpectrum A := fun x hx =>
    discrete_of_lt x hx.1 (hFlt x hx)
  have hFiso : ∀ x ∈ F, IsoPt A x := fun x hx => isoPt_of_discrete x (hFdisc x hx)
  have hFle : ∀ x ∈ F, eigenspace A (x : ℂ) ≤ V := fun x hx =>
    eigenspace_le_below (hFlt x hx) hx.2
  have hFfin : F.Finite := by
    have : ∀ x : F, ∃ e ∈ eigenspace A ((x : ℝ) : ℂ), e ≠ 0 := fun x =>
      Submodule.exists_mem_ne_zero_of_ne_bot (hFdisc x x.2).2.1
    choose e he he0 using this
    let e' : F → V := fun x => ⟨e x, hFle x x.2 (he x)⟩
    have hli : LinearIndependent ℂ e' := by
      apply LinearIndependent.of_comp V.subtype
      apply linearIndependent_of_ne_zero_of_inner_eq_zero
      · intro x
        simpa [e'] using he0 x
      · intro x y hxy
        exact eig_orth hA (fun h => hxy (Subtype.ext h)) (he x) (he y)
    haveI := hli.finite
    exact Set.toFinite F
  set Fs := hFfin.toFinset with hFsdef
  have hchic : ∀ x ∈ Fs, ContinuousOn (chi x) (_root_.spectrum ℂ (res hA)) := fun x hx =>
    chi_cont hA x (hFiso x (hFfin.mem_toFinset.mp hx))
  have hsumc : ContinuousOn (∑ x ∈ Fs, chi x) (_root_.spectrum ℂ (res hA)) := by
    rw [Finset.sum_fn]
    exact continuousOn_finset_sum _ hchic
  set k : ℂ → ℂ := fun w => (fun _ => (1 : ℂ)) w - (∑ x ∈ Fs, chi x) w with hkdef
  have hkc : ContinuousOn k (_root_.spectrum ℂ (res hA)) := continuousOn_const.sub hsumc
  have hkcfc : cfc k (res hA) = 1 - ∑ x ∈ Fs, cfc (chi x) (res hA) := by
    rw [hkdef, cfc_sub (fun _ => (1 : ℂ)) (∑ x ∈ Fs, chi x) (res hA) continuousOn_const hsumc,
      cfc_const_one ℂ (res hA), cfc_sum (fun x => chi x) (res hA) Fs hchic]
  -- the test vectors
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank ℂ V = d := ⟨_, rfl⟩
  have hdn : d ≤ n - 1 := by
    have h1 : (Module.finrank ℂ V : Cardinal) = Module.rank ℂ V := Module.finrank_eq_rank ℂ V
    rw [← h1, hd] at hrlt
    norm_cast at hrlt
    omega
  let bas := Module.finBasisOfFinrankEq ℂ V hd
  let ψ : Fin (n - 1) → H := fun j => if h : (j : ℕ) < d then (bas ⟨j, h⟩ : H) else 0
  refine ⟨ψ, fun φ hφ => ?_⟩
  have hVspan : ∀ v ∈ V, ⟪v, (φ : H)⟫_ℂ = 0 := by
    intro v hv
    have h1 : (⟨v, hv⟩ : V) ∈ Submodule.span ℂ (Set.range bas) := by
      rw [bas.span_eq]; trivial
    have h2 : v ∈ Submodule.span ℂ (V.subtype '' Set.range bas) := by
      rw [Submodule.span_image]
      exact ⟨_, h1, rfl⟩
    have h3 : v ∈ Submodule.span ℂ (Set.range ψ) := by
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨⟨i, lt_of_lt_of_le i.2 hdn⟩, ?_⟩
      simp [ψ, i.2]
    exact (Submodule.mem_orthogonal _ _).mp hφ.2 v h3
  set χ : H := A φ - Complex.I • (φ : H) with hχ
  have hφχ : res hA χ = φ := res_left hA φ
  have hchi0 : ∀ x ∈ Fs, cfc (chi x) (res hA) χ = 0 := by
    intro x hx
    have hxF := hFfin.mem_toFinset.mp hx
    have h1 : cfc (chi x) (res hA) φ = 0 := by
      apply chi_apply_eq_zero hA x (hFiso x hxF) φ
      have := hVspan _ (hFle x hxF (chi_range hA x (hFiso x hxF) φ))
      rw [← inner_conj_symm, this, map_zero]
    apply res_injective hA
    rw [← cfc_res_comm, hφχ, h1, map_zero]
  have hkχ : cfc k (res hA) χ = χ := by
    rw [hkcfc, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.sum_apply, Finset.sum_eq_zero hchi0, sub_zero]
  have hφeq : (φ : H) = res hA (cfc k (res hA) χ) := by rw [hkχ, hφχ]
  have hq := qf_ge' hA k hkc t (by
    intro w hw hw0 hk
    by_contra hlt
    push_neg at hlt
    have hx : xr w ∈ F := ⟨(res_spec_fwd hA w hw hw0).1, hlt.le⟩
    have hxs : xr w ∈ Fs := hFfin.mem_toFinset.mpr hx
    apply hk
    simp only [hkdef, Finset.sum_apply]
    rw [Finset.sum_eq_single (xr w)]
    · simp [chi, hw0]
    · intro y _ hy
      simp only [chi]
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hy h.symm
    · intro h
      exact absurd hxs h) χ φ hφeq
  rw [hφ.1] at hq
  linarith

end TeschlQM.MinMax.MM

open TeschlQM.MinMax TeschlQM.MinMax.MM in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (n : ℕ) (hn : 1 ≤ n) :
    eigenvalueSeq A n =
      ⨆ ψ : Fin (n - 1) → H, ⨅ φ ∈ minMaxSet A ψ, ((⟪(φ : H), A φ⟫_ℂ).re : EReal) := by
  apply le_antisymm
  · rw [← EReal.ge_of_forall_gt_iff_ge]
    intro t ht
    have hS : (t : EReal) < infEssSpectrum A :=
      lt_of_lt_of_le ht (sInf_le (Or.inr rfl))
    have hr : ¬ (n : Cardinal) ≤ Module.rank ℂ (eigenspaceBelow A t) := by
      intro h
      have : eigenvalueSeq A n ≤ (t : EReal) := sInf_le (Or.inl ⟨t, rfl, hS, h⟩)
      exact absurd this (not_le.mpr ht)
    obtain ⟨ψ, hψ⟩ := lower hA n t hS hr
    calc (t : EReal) ≤ ⨅ φ ∈ minMaxSet A ψ, ((⟪(φ : H), A φ⟫_ℂ).re : EReal) :=
          le_iInf₂ fun φ hφ => EReal.coe_le_coe_iff.mpr (hψ φ hφ)
      _ ≤ _ := le_iSup (fun ψ : Fin (n - 1) → H =>
          ⨅ φ ∈ minMaxSet A ψ, ((⟪(φ : H), A φ⟫_ℂ).re : EReal)) ψ
  · apply iSup_le
    intro ψ
    rw [← EReal.le_of_forall_lt_iff_le]
    intro s hs
    obtain ⟨y, hy, hys⟩ := sInf_lt_iff.mp hs
    rcases hy with ⟨x, rfl, _, hrank⟩ | hy
    · exact (upper_a hA ψ hn x hrank).trans (EReal.coe_le_coe_iff.mpr (EReal.coe_lt_coe_iff.mp hys).le)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy] at hys
      obtain ⟨z, ⟨l, hl, rfl⟩, hls⟩ := sInf_lt_iff.mp hys
      exact upper_b hA ψ hn l hl s (EReal.coe_lt_coe_iff.mp hls)
