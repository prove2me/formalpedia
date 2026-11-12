-- Prove2me | solution 1 for TeschlQM.OneParticle.relativelyCompact_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T10:46:00.825492+00:00
-- url     : https://prove2.me/submissions/aea04b17-93af-43d6-987d-271974303bf8

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_OneParticle_IsBoundedBelow

set_option autoImplicit false

open scoped InnerProductSpace LinearPMap

namespace RCP

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- P1: the domain of `A` is contained in the domain of a relatively compact `K`. -/
theorem dom_le (A K : H →ₗ.[ℂ] H) (hrc : TeschlQM.Shared.IsRelativelyCompact K A) :
    A.domain ≤ K.domain := by
  obtain ⟨z, R, hR, C, _, hKC⟩ := hrc
  intro ψ hψ
  have h : R (A ⟨ψ, hψ⟩ - z • ψ) = ψ := hR.2 ⟨ψ, hψ⟩
  obtain ⟨hmem, _⟩ := hKC (A ⟨ψ, hψ⟩ - z • ψ)
  rw [h] at hmem
  exact hmem

/-- P1: the resolvent maps onto the domain. -/
theorem resolvent_mem {A : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H}
    (hR : TeschlQM.Shared.IsResolventAt A z R) (φ : H) : R φ ∈ A.domain :=
  (hR.1 φ).1

theorem domain_add (A K : H →ₗ.[ℂ] H) (hrc : TeschlQM.Shared.IsRelativelyCompact K A) :
    (A + K).domain = A.domain := by
  rw [LinearPMap.add_domain]
  exact inf_eq_left.mpr (dom_le A K hrc)

variable [CompleteSpace H]

/-- A self-adjoint operator is symmetric. -/
theorem symm_of_selfAdjoint (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    ∀ x y : A.domain, ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have hA' : A† = A := hA
  have hle : A ≤ A† := by rw [hA']
  intro x y
  have hx : (x : H) ∈ A†.domain := hle.1 x.2
  have h1 : A x = A† ⟨x, hx⟩ := hle.2 (x := x) (y := ⟨x, hx⟩) rfl
  rw [h1]
  exact LinearPMap.adjoint_isFormalAdjoint hA.dense_domain ⟨x, hx⟩ y

/-- P2: a densely defined symmetric operator `T` such that `T - l` is onto for one real `l`
is self-adjoint. -/
theorem selfAdjoint_of_symm_surj (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : ∀ x y : T.domain, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ) (l : ℝ)
    (hsurj : ∀ φ : H, ∃ ψ : T.domain, T ψ - (l : ℂ) • (ψ : H) = φ) : IsSelfAdjoint T := by
  have hle : T ≤ T† := LinearPMap.IsFormalAdjoint.le_adjoint hd hs
  have hdom : T†.domain ≤ T.domain := by
    intro y hy
    obtain ⟨ψ, hψ⟩ := hsurj (T† ⟨y, hy⟩ - (l : ℂ) • y)
    have hψ' : (ψ : H) ∈ T†.domain := hle.1 ψ.2
    have h1 : T ψ = T† ⟨ψ, hψ'⟩ := hle.2 (x := ψ) (y := ⟨ψ, hψ'⟩) rfl
    set w : T†.domain := ⟨y, hy⟩ - ⟨ψ, hψ'⟩ with hw
    have hwv : (w : H) = y - ψ := rfl
    have hTw : T† w = (l : ℂ) • (w : H) := by
      rw [hw, LinearPMap.map_sub, ← h1, hwv, smul_sub]
      have h2 : T ψ - T† ⟨y, hy⟩ = (l : ℂ) • (ψ : H) - (l : ℂ) • y :=
        sub_eq_sub_iff_sub_eq_sub.mp hψ
      rw [← neg_sub (T ψ), h2, neg_sub]
    have horth : ∀ x : T.domain, ⟪(w : H), T x - (l : ℂ) • (x : H)⟫_ℂ = 0 := by
      intro x
      have hfa := LinearPMap.adjoint_isFormalAdjoint hd w x
      rw [inner_sub_right, ← hfa, hTw, inner_smul_left, inner_smul_right]
      simp
    obtain ⟨x, hx⟩ := hsurj (w : H)
    have h0 := horth x
    rw [hx, inner_self_eq_zero] at h0
    have hyψ : y = ψ := by
      have : y - ψ = 0 := by rw [← hwv]; exact h0
      exact sub_eq_zero.mp this
    rw [hyψ]
    exact ψ.2
  have heq : T = T† := LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)
  exact heq.symm

/-- P5 (surjectivity half of Kato-Rellich): if `R = R_A(l)` and `K R = C'` with `‖C'‖ < 1`,
then `A + K - l` is onto. -/
theorem add_sub_surj (A K : H →ₗ.[ℂ] H) (l : ℂ) (R C' : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A l R)
    (hKC : ∀ φ : H, ∃ h : R φ ∈ K.domain, K ⟨R φ, h⟩ = C' φ) (hn : ‖C'‖ < 1) :
    ∀ φ : H, ∃ ψ : (A + K).domain, (A + K) ψ - l • (ψ : H) = φ := by
  intro φ
  have hn' : ‖-C'‖ < 1 := by rwa [norm_neg]
  set U := Units.oneSub (-C') hn'
  set u : H := ((U⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) φ with hu
  have key : u + C' u = φ := by
    have h := congrArg (fun T : H →L[ℂ] H => T φ) (Units.mul_inv U)
    simp only [U, Units.val_oneSub, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.neg_apply, sub_neg_eq_add] at h
    rw [hu]
    exact h
  obtain ⟨hA, hAeq⟩ := hR.1 u
  obtain ⟨hK, hKeq⟩ := hKC u
  refine ⟨⟨R u, ⟨hA, hK⟩⟩, ?_⟩
  have hadd : (A + K) ⟨R u, ⟨hA, hK⟩⟩ = A ⟨R u, hA⟩ + K ⟨R u, hK⟩ := LinearPMap.add_apply A K _
  rw [hadd, hKeq]
  calc A ⟨R u, hA⟩ + C' u - l • R u = (A ⟨R u, hA⟩ - l • R u) + C' u := by abel
    _ = φ := by rw [hAeq, key]

/-- P3a: `(γ - l)‖ψ‖ ≤ ‖(A - l)ψ‖` for `A ≥ γ`, `l < γ`. -/
theorem lower_bound (A : H →ₗ.[ℂ] H) (γ : ℝ)
    (hγ : ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) (l : ℝ) :
    ∀ ψ : A.domain, (γ - l) * ‖(ψ : H)‖ ≤ ‖A ψ - (l : ℂ) • (ψ : H)‖ := by
  intro ψ
  have hl1 : ⟪(ψ : H), (l : ℂ) • (ψ : H)⟫_ℂ = ((l * ‖(ψ : H)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_mul, Complex.ofReal_pow]
    rfl
  have h1 : (⟪(ψ : H), A ψ - (l : ℂ) • (ψ : H)⟫_ℂ).re
      = (⟪(ψ : H), A ψ⟫_ℂ).re - l * ‖(ψ : H)‖ ^ 2 := by
    rw [inner_sub_right, hl1, Complex.sub_re, Complex.ofReal_re]
  have h2 : (⟪(ψ : H), A ψ - (l : ℂ) • (ψ : H)⟫_ℂ).re
      ≤ ‖(ψ : H)‖ * ‖A ψ - (l : ℂ) • (ψ : H)‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h3 : ‖(ψ : H)‖ * ((γ - l) * ‖(ψ : H)‖) ≤ ‖(ψ : H)‖ * ‖A ψ - (l : ℂ) • (ψ : H)‖ := by
    have := hγ ψ
    nlinarith
  rcases (norm_nonneg (ψ : H)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · exact le_of_mul_le_mul_left h3 hpos


/-- P3b: for self-adjoint `A ≥ γ` and real `l < γ`, `A - l` maps `𝔇(A)` onto `ℌ`. -/
theorem surj_below (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (γ : ℝ)
    (hγ : ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) (l : ℝ) (hl : l < γ) :
    ∀ φ : H, ∃ ψ : A.domain, A ψ - (l : ℂ) • (ψ : H) = φ := by
  have hgl : 0 < γ - l := sub_pos.mpr hl
  let L : A.domain →ₗ[ℂ] H := A.toFun - (l : ℂ) • A.domain.subtype
  have hL : ∀ ψ : A.domain, L ψ = A ψ - (l : ℂ) • (ψ : H) := fun ψ => rfl
  have hlb := lower_bound A γ hγ l
  -- closed range
  have hclosed : IsClosed (LinearMap.range L : Set H) := by
    rw [← closure_subset_iff_isClosed]
    intro φ hφ
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hφ
    choose ψ hψ using fun n => LinearMap.mem_range.mp (hu n)
    have hc : CauchySeq (fun n => (ψ n : H)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ((γ - l) * ε) (mul_pos hgl hε)
      refine ⟨N, fun m hm n hn => ?_⟩
      have hd := hN m hm n hn
      rw [dist_eq_norm] at hd ⊢
      have hb := hlb (ψ m - ψ n)
      have he : A (ψ m - ψ n) - (l : ℂ) • ((ψ m - ψ n : A.domain) : H) = u m - u n := by
        rw [← hψ m, ← hψ n, ← hL, map_sub]
      rw [he, Submodule.coe_sub] at hb
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
    have hAψ : Filter.Tendsto (fun n => A (ψ n)) Filter.atTop (nhds (φ + (l : ℂ) • x)) := by
      have h1 : (fun n => A (ψ n)) = fun n => u n + (l : ℂ) • (ψ n : H) := by
        funext n; rw [← hψ n, hL]; abel
      rw [h1]
      exact hlim.add (hx.const_smul _)
    have hmem : (x, φ + (l : ℂ) • x) ∈ (A.graph : Set (H × H)) :=
      hA.isClosed.mem_of_tendsto (hx.prodMk_nhds hAψ)
        (Filter.Eventually.of_forall fun n => LinearPMap.mem_graph A (ψ n))
    obtain ⟨y, hy⟩ := (LinearPMap.mem_graph_iff A).mp hmem
    simp only [Prod.mk.injEq] at hy
    refine ⟨y, ?_⟩
    rw [hL, hy.2, hy.1]
    abel
  -- dense range
  have hdense : (LinearMap.range L).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hperp : ∀ x : A.domain, ⟪A x - (l : ℂ) • (x : H), y⟫_ℂ = 0 := fun x =>
      hy _ ⟨x, rfl⟩
    have hw : ∀ x : A.domain, ⟪(l : ℂ) • y, (x : H)⟫_ℂ = ⟪y, A x⟫_ℂ := by
      intro x
      have h0 := hperp x
      rw [inner_sub_left, sub_eq_zero, inner_smul_left] at h0
      rw [inner_smul_left, ← inner_conj_symm y (A x), h0, ← inner_conj_symm]
      simp
    have hyd : y ∈ A†.domain := LinearPMap.mem_adjoint_domain_of_exists y ⟨_, hw⟩
    have hAy : A† ⟨y, hyd⟩ = (l : ℂ) • y :=
      LinearPMap.adjoint_apply_eq hA.dense_domain ⟨y, hyd⟩ hw
    have hA' : A† = A := hA
    have hle : A† ≤ A := by rw [hA']
    have hyA : y ∈ A.domain := hle.1 hyd
    have hAy' : A ⟨y, hyA⟩ = (l : ℂ) • y := by
      rw [← hAy]; exact (hle.2 (x := ⟨y, hyd⟩) (y := ⟨y, hyA⟩) rfl).symm
    have hb := hγ ⟨y, hyA⟩
    have hre : (⟪y, A ⟨y, hyA⟩⟫_ℂ).re = l * ‖y‖ ^ 2 := by
      rw [hAy', inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    simp only at hb
    rw [hre] at hb
    have : ‖y‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
    exact norm_eq_zero.mp this
  have htop : LinearMap.range L = ⊤ := by
    rw [← hdense]
    exact (IsClosed.submodule_topologicalClosure_eq hclosed).symm
  intro φ
  have hφ : φ ∈ LinearMap.range L := by rw [htop]; trivial
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp hφ
  exact ⟨ψ, hψ⟩

theorem symmSA_p3 (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    ∀ x y : A.domain, ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have hA' : A† = A := hA
  have hle : A ≤ A† := by rw [hA']
  intro x y
  have hx : (x : H) ∈ A†.domain := hle.1 x.2
  have h1 : A x = A† ⟨x, hx⟩ := hle.2 (x := x) (y := ⟨x, hx⟩) rfl
  rw [h1]
  exact LinearPMap.adjoint_isFormalAdjoint hA.dense_domain ⟨x, hx⟩ y

/-- P3c: the resolvent `R_A(l)` exists for real `l < γ`, has norm `≤ (γ - l)⁻¹` and is
symmetric. -/
theorem resolvent_below (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (γ : ℝ)
    (hγ : ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) (l : ℝ) (hl : l < γ) :
    ∃ R : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt A (l : ℂ) R ∧ ‖R‖ ≤ (γ - l)⁻¹ ∧
      ∀ x y : H, ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ := by
  have hgl : 0 < γ - l := sub_pos.mpr hl
  have hlb := lower_bound A γ hγ l
  let L : A.domain →ₗ[ℂ] H := A.toFun - (l : ℂ) • A.domain.subtype
  have hL : ∀ ψ : A.domain, L ψ = A ψ - (l : ℂ) • (ψ : H) := fun ψ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ψ hψ
    rw [LinearMap.mem_ker, hL] at hψ
    have hb := hlb ψ
    rw [hψ, norm_zero] at hb
    have h0 : ‖(ψ : H)‖ = 0 := by nlinarith [norm_nonneg (ψ : H)]
    exact Subtype.ext (by simpa using h0)
  have hsurj : Function.Surjective L := fun φ => surj_below A hA γ hγ l hl φ
  let e : A.domain ≃ₗ[ℂ] H := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have he : ∀ ψ, e ψ = L ψ := fun ψ => rfl
  let Rl : H →ₗ[ℂ] H := A.domain.subtype.comp e.symm.toLinearMap
  have hRl : ∀ φ, Rl φ = (e.symm φ : H) := fun φ => rfl
  have hbound : ∀ φ, ‖Rl φ‖ ≤ (γ - l)⁻¹ * ‖φ‖ := by
    intro φ
    have hb := hlb (e.symm φ)
    rw [← hL, ← he, LinearEquiv.apply_symm_apply] at hb
    rw [hRl, inv_mul_eq_div, le_div_iff₀ hgl]
    linarith
  refine ⟨Rl.mkContinuous (γ - l)⁻¹ hbound, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro φ
    refine ⟨(e.symm φ).2, ?_⟩
    have h1 := e.apply_symm_apply φ
    rw [he, hL] at h1
    exact h1
  · intro ψ
    show ((e.symm (A ψ - (l : ℂ) • (ψ : H))) : H) = ψ
    rw [← hL, ← he, LinearEquiv.symm_apply_apply]
  · exact LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr hgl.le) _
  · intro x y
    show ⟪((e.symm x : A.domain) : H), y⟫_ℂ = ⟪x, ((e.symm y : A.domain) : H)⟫_ℂ
    have hx := e.apply_symm_apply x
    have hy := e.apply_symm_apply y
    rw [he, hL] at hx hy
    conv_lhs => rw [← hy]
    conv_rhs => rw [← hx]
    rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
      symmSA_p3 A hA (e.symm x) (e.symm y)]
    simp

/-- P4a: a uniformly bounded operator that is small on a finite subset of a dense set is small
on a totally bounded set. -/
theorem unif_small (S D : Set H) (hS : TotallyBounded S) (hD : Dense D) (M : ℝ) (hM0 : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) : ∃ t : Finset H, (∀ y ∈ t, y ∈ D) ∧
      ∀ T : H →L[ℂ] H, ‖T‖ ≤ M → (∀ y ∈ t, ‖T y‖ ≤ ε / 2) → ∀ x ∈ S, ‖T x‖ ≤ ε := by
  classical
  set δ : ℝ := ε / (4 * (M + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨c, -, hcfin, hcov⟩ := Metric.finite_approx_of_totallyBounded hS δ hδpos
  have hch : ∀ x : H, ∃ y ∈ D, dist x y < δ := fun x => hD.exists_dist_lt x hδpos
  choose! d hdD hdd using hch
  refine ⟨hcfin.toFinset.image d, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact hdD x
  · intro T hT hy x hx
    obtain ⟨c0, hc0, hxc⟩ := Set.mem_iUnion₂.1 (hcov hx)
    have hdy : ‖T (d c0)‖ ≤ ε / 2 :=
      hy _ (Finset.mem_image.2 ⟨c0, hcfin.mem_toFinset.2 hc0, rfl⟩)
    have h1 : ‖x - d c0‖ < 2 * δ := by
      have h0 := hdd c0
      rw [Metric.mem_ball, dist_eq_norm] at hxc
      rw [dist_eq_norm] at h0
      calc ‖x - d c0‖ = ‖(x - c0) + (c0 - d c0)‖ := by congr 1; abel
        _ ≤ ‖x - c0‖ + ‖c0 - d c0‖ := norm_add_le _ _
        _ < 2 * δ := by linarith
    have h2 : ‖T (x - d c0)‖ ≤ M * (2 * δ) :=
      (T.le_opNorm _).trans (mul_le_mul hT h1.le (norm_nonneg _) hM0)
    have h3 : M * (2 * δ) ≤ ε / 2 := by
      have hM1 : 0 < M + 1 := by linarith
      have : M * (2 * δ) = ε / 2 * (M / (M + 1)) := by
        rw [hδ]; field_simp; ring
      rw [this]
      exact mul_le_of_le_one_right (by linarith) ((div_le_one hM1).2 (by linarith))
    calc ‖T x‖ = ‖T (x - d c0) + T (d c0)‖ := by rw [← map_add, sub_add_cancel]
      _ ≤ ‖T (x - d c0)‖ + ‖T (d c0)‖ := norm_add_le _ _
      _ ≤ ε := by linarith

/-- P4b: `⟨φ + c R φ, x⟩ = ⟨φ, x + c̄ R x⟩` for symmetric `R`. -/
theorem inner_S_T (Rl : H →L[ℂ] H) (hsym : ∀ x y : H, ⟪Rl x, y⟫_ℂ = ⟪x, Rl y⟫_ℂ) (c : ℂ)
    (φ x : H) : ⟪φ + c • Rl φ, x⟫_ℂ = ⟪φ, x + (starRingEnd ℂ c) • Rl x⟫_ℂ := by
  rw [inner_add_left, inner_smul_left, hsym, inner_add_right, inner_smul_right]

/-- P4c: on `𝔇(A)`, `x + (l - w) R_l x = R_l (A x - w x)`. -/
theorem T_on_dom (A : H →ₗ.[ℂ] H) (l w : ℂ) (Rl : H →L[ℂ] H)
    (hRl : TeschlQM.Shared.IsResolventAt A l Rl) (y : A.domain) :
    (y : H) + (l - w) • Rl y = Rl (A y - w • (y : H)) := by
  have : A y - w • (y : H) = (A y - l • (y : H)) + (l - w) • (y : H) := by
    rw [sub_smul]; abel
  rw [this, map_add, map_smul, hRl.2 y]

/-- P4d: `‖1 + c R‖ ≤ 1 + ‖c‖ ‖R‖`. -/
theorem norm_one_add_smul (Rl : H →L[ℂ] H) (c : ℂ) :
    ‖(1 + c • Rl : H →L[ℂ] H)‖ ≤ 1 + ‖c‖ * ‖Rl‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply]
  calc ‖x + c • Rl x‖ ≤ ‖x‖ + ‖c‖ * (‖Rl‖ * ‖x‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (Rl.le_opNorm x) (norm_nonneg _)
    _ = (1 + ‖c‖ * ‖Rl‖) * ‖x‖ := by ring

/-- P4e: the coefficient bound `‖c‖ ‖R_l‖ ≤ 1 + |γ| + ‖z‖` for `c = l - w`, `‖w‖ = ‖z‖`,
`l ≤ min (γ - 1) 0`. -/
theorem coeff_bound (γ l : ℝ) (w : ℂ) (r : ℝ) (hl1 : l ≤ γ - 1) (hl0 : l ≤ 0)
    (hr : r ≤ (γ - l)⁻¹) : ‖((l : ℂ) - w)‖ * r ≤ 1 + |γ| + ‖w‖ := by
  have hgl : 1 ≤ γ - l := by linarith
  have hgl0 : 0 < γ - l := by linarith
  have hn : ‖((l : ℂ) - w)‖ ≤ (γ - l) + (|γ| + ‖w‖) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hl0]
    have := neg_abs_le γ
    linarith
  have hr' : r ≤ 1 := hr.trans (inv_le_one_of_one_le₀ hgl)
  rcases le_or_gt r 0 with hr0 | hr0
  · have : ‖((l : ℂ) - w)‖ * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr0
    have := abs_nonneg γ; have := norm_nonneg w; linarith
  · calc ‖((l : ℂ) - w)‖ * r ≤ ((γ - l) + (|γ| + ‖w‖)) * (γ - l)⁻¹ :=
          mul_le_mul hn hr hr0.le (by positivity)
      _ = 1 + (|γ| + ‖w‖) * (γ - l)⁻¹ := by field_simp
      _ ≤ 1 + (|γ| + ‖w‖) * 1 := by
          gcongr
          exact inv_le_one_of_one_le₀ hgl
      _ = 1 + |γ| + ‖w‖ := by ring

/-- P4 (Teschl L6.22): `‖K R_A(l)‖ = ‖C (1 + (l - z) R_A(l))‖ ≤ ε` for all real `l` far enough
below the lower bound `γ`. -/
theorem relCompact_small (A : H →ₗ.[ℂ] H) (hdense : Dense (A.domain : Set H)) (γ : ℝ) (z : ℂ)
    (C : H →L[ℂ] H) (hC : IsCompactOperator C) (ε : ℝ) (hε : 0 < ε) :
    ∃ l0 : ℝ, l0 < γ ∧ ∀ l : ℝ, l ≤ l0 → ∀ Rl : H →L[ℂ] H,
      TeschlQM.Shared.IsResolventAt A (l : ℂ) Rl → ‖Rl‖ ≤ (γ - l)⁻¹ →
      (∀ x y : H, ⟪Rl x, y⟫_ℂ = ⟪x, Rl y⟫_ℂ) →
      ‖C.comp (1 + ((l : ℂ) - z) • Rl)‖ ≤ ε := by
  classical
  set M : ℝ := 2 + |γ| + ‖z‖ with hM
  have hM0 : 0 ≤ M := by positivity
  set K0 : Set H := (ContinuousLinearMap.adjoint C) '' closure (C '' Metric.closedBall 0 M)
    with hK0def
  have hK0 : TotallyBounded K0 :=
    ((hC.isCompact_closure_image_closedBall M).image
      (ContinuousLinearMap.adjoint C).continuous).totallyBounded
  have hε2 : 0 < ε ^ 2 := by positivity
  obtain ⟨t, htD, ht⟩ := unif_small K0 (A.domain : Set H) hK0 hdense M hM0 (ε ^ 2) hε2
  set f : H → ℝ := fun y =>
    if h : y ∈ A.domain then ‖A ⟨y, h⟩ - (starRingEnd ℂ z) • y‖ else 0 with hfdef
  set N : ℝ := ∑ y ∈ t, f y with hNdef
  have hf0 : ∀ y, 0 ≤ f y := by intro y; simp only [f]; split_ifs <;> positivity
  have hfN : ∀ y ∈ t, f y ≤ N := fun y hy => Finset.single_le_sum (fun y _ => hf0 y) hy
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun y _ => hf0 y)
  refine ⟨min (min (γ - 1) 0) (γ - 2 * N / ε ^ 2 - 1), ?_, ?_⟩
  · have := min_le_left (min (γ - 1) 0) (γ - 2 * N / ε ^ 2 - 1)
    have := min_le_left (γ - 1) 0
    linarith
  intro l hl Rl hRl hRn hsym
  have hl1 : l ≤ γ - 1 := hl.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hl0 : l ≤ 0 := hl.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hl2 : l ≤ γ - 2 * N / ε ^ 2 - 1 := hl.trans (min_le_right _ _)
  have hgl : 0 < γ - l := by linarith
  have hSn : ‖(1 + ((l : ℂ) - z) • Rl : H →L[ℂ] H)‖ ≤ M := by
    refine (norm_one_add_smul Rl _).trans ?_
    have := coeff_bound γ l z ‖Rl‖ hl1 hl0 hRn
    linarith
  have hTn : ‖(1 + ((l : ℂ) - starRingEnd ℂ z) • Rl : H →L[ℂ] H)‖ ≤ M := by
    refine (norm_one_add_smul Rl _).trans ?_
    have := coeff_bound γ l (starRingEnd ℂ z) ‖Rl‖ hl1 hl0 hRn
    rw [show ‖(starRingEnd ℂ) z‖ = ‖z‖ from RCLike.norm_conj z] at this
    linarith
  have hsmall : ∀ y ∈ t,
      ‖(1 + ((l : ℂ) - starRingEnd ℂ z) • Rl : H →L[ℂ] H) y‖ ≤ ε ^ 2 / 2 := by
    intro y hy
    have hyD : y ∈ A.domain := htD y hy
    have e1 : (1 + ((l : ℂ) - starRingEnd ℂ z) • Rl : H →L[ℂ] H) y
        = Rl (A ⟨y, hyD⟩ - (starRingEnd ℂ z) • y) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply]
      exact T_on_dom A l (starRingEnd ℂ z) Rl hRl ⟨y, hyD⟩
    have hfy : f y = ‖A ⟨y, hyD⟩ - (starRingEnd ℂ z) • y‖ := by simp only [f, dif_pos hyD]
    rw [e1]
    calc ‖Rl (A ⟨y, hyD⟩ - (starRingEnd ℂ z) • y)‖ ≤ ‖Rl‖ * f y := by
          rw [hfy]; exact Rl.le_opNorm _
      _ ≤ (γ - l)⁻¹ * N := mul_le_mul hRn (hfN y hy) (hf0 y) (by positivity)
      _ ≤ ε ^ 2 / 2 := by
        rw [inv_mul_le_iff₀ hgl]
        have h4 : 2 * N / ε ^ 2 ≤ γ - l - 1 := by linarith
        rw [div_le_iff₀ hε2] at h4
        nlinarith
  have hT := ht _ hTn hsmall
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hε.le fun φ hφ => ?_
  obtain ⟨u, hu⟩ : ∃ u : H, u = φ + ((l : ℂ) - z) • Rl φ := ⟨_, rfl⟩
  have hCu : (C.comp (1 + ((l : ℂ) - z) • Rl)) φ = C u := by
    rw [hu]; simp
  have hun : ‖u‖ ≤ M := by
    have h := (1 + ((l : ℂ) - z) • Rl : H →L[ℂ] H).le_opNorm φ
    rw [hφ, mul_one] at h
    have e : (1 + ((l : ℂ) - z) • Rl : H →L[ℂ] H) φ = u := by rw [hu]; simp
    rw [e] at h; exact h.trans hSn
  obtain ⟨x, hxd⟩ : ∃ x : H, x = ContinuousLinearMap.adjoint C (C u) := ⟨_, rfl⟩
  have hx : x ∈ K0 := ⟨C u, subset_closure ⟨u, by simpa using hun, rfl⟩, hxd.symm⟩
  have hTx := hT x hx
  have e1 : ⟪C u, C u⟫_ℂ = ⟪u, x⟫_ℂ := by rw [hxd, ContinuousLinearMap.adjoint_inner_right]
  have e2 : ⟪u, x⟫_ℂ = ⟪φ, (1 + ((l : ℂ) - starRingEnd ℂ z) • Rl : H →L[ℂ] H) x⟫_ℂ := by
    rw [hu, inner_S_T Rl hsym, map_sub, Complex.conj_ofReal]; simp
  have e3 : ‖C u‖ ^ 2 = (⟪C u, C u⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) (C u)).symm
  have key : ‖C u‖ ^ 2 ≤ ε ^ 2 := by
    rw [e3, e1, e2]
    refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [hφ, one_mul]; exact hTx
  rw [hCu]
  nlinarith [norm_nonneg (C u)]


/-- P5a: `K ψ = C (A ψ - z ψ)` on `𝔇(A)`. -/
theorem K_on_dom (A K : H →ₗ.[ℂ] H) (z : ℂ) (R C : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R)
    (hKC : ∀ φ : H, ∃ h : R φ ∈ K.domain, K ⟨R φ, h⟩ = C φ) (ψ : A.domain) :
    ∃ h : (ψ : H) ∈ K.domain, K ⟨ψ, h⟩ = C (A ψ - z • (ψ : H)) := by
  obtain ⟨hmem, hK⟩ := hKC (A ψ - z • (ψ : H))
  have e : R (A ψ - z • (ψ : H)) = ψ := hR.2 ψ
  have hψ : (ψ : H) ∈ K.domain := e ▸ hmem
  refine ⟨hψ, ?_⟩
  have : (⟨ψ, hψ⟩ : K.domain) = ⟨R (A ψ - z • (ψ : H)), hmem⟩ := Subtype.ext e.symm
  rw [this, hK]

/-- P5b: `K R_A(l) = C (1 + (l - z) R_A(l))`. -/
theorem KR_eq (A K : H →ₗ.[ℂ] H) (z : ℂ) (R C : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R)
    (hKC : ∀ φ : H, ∃ h : R φ ∈ K.domain, K ⟨R φ, h⟩ = C φ) (l : ℂ) (Rl : H →L[ℂ] H)
    (hRl : TeschlQM.Shared.IsResolventAt A l Rl) :
    ∀ φ : H, ∃ h : Rl φ ∈ K.domain, K ⟨Rl φ, h⟩ = (C.comp (1 + (l - z) • Rl)) φ := by
  intro φ
  obtain ⟨hD, hA⟩ := hRl.1 φ
  obtain ⟨hK, e⟩ := K_on_dom A K z R C hR hKC ⟨Rl φ, hD⟩
  refine ⟨hK, ?_⟩
  rw [e]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply]
  congr 1
  calc A ⟨Rl φ, hD⟩ - z • Rl φ = (A ⟨Rl φ, hD⟩ - l • Rl φ) + (l - z) • Rl φ := by
        rw [sub_smul]; abel
    _ = φ + (l - z) • Rl φ := by rw [hA]

/-- P5c: `A + K` is symmetric. -/
theorem add_symm (A K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hK : ∀ x y : K.domain, ⟪K x, (y : H)⟫_ℂ = ⟪(x : H), K y⟫_ℂ) :
    ∀ x y : (A + K).domain, ⟪(A + K) x, (y : H)⟫_ℂ = ⟪(x : H), (A + K) y⟫_ℂ := by
  intro x y
  have ex : (A + K) x = A ⟨x, x.2.1⟩ + K ⟨x, x.2.2⟩ := LinearPMap.add_apply A K x
  have ey : (A + K) y = A ⟨y, y.2.1⟩ + K ⟨y, y.2.2⟩ := LinearPMap.add_apply A K y
  rw [ex, ey, inner_add_left, inner_add_right]
  have h1 := symm_of_selfAdjoint A hA ⟨x, x.2.1⟩ ⟨y, y.2.1⟩
  have h2 := hK ⟨x, x.2.2⟩ ⟨y, y.2.2⟩
  simp only at h1 h2
  rw [h1, h2]

/-- P5 (Kato-Rellich, self-adjointness half): `𝔇(A + K) = 𝔇(A)`, `A + K` is self-adjoint, and
`A + K - l` is onto for all real `l ≤ l0`. -/
theorem kato_rellich_sa (A K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (γ : ℝ)
    (hγ : ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re)
    (hK : ∀ x y : K.domain, ⟪K x, (y : H)⟫_ℂ = ⟪(x : H), K y⟫_ℂ)
    (hrc : TeschlQM.Shared.IsRelativelyCompact K A) :
    (A + K).domain = A.domain ∧ IsSelfAdjoint (A + K) ∧ ∃ l0 : ℝ, l0 < γ ∧ ∀ l : ℝ, l ≤ l0 →
      ∀ φ : H, ∃ ψ : (A + K).domain, (A + K) ψ - (l : ℂ) • (ψ : H) = φ := by
  have hdom := domain_add A K hrc
  obtain ⟨z, R, hR, C, hC, hKC⟩ := hrc
  obtain ⟨l0, hl0, hsmall⟩ := relCompact_small A hA.dense_domain γ z C hC (1 / 2) (by norm_num)
  have hsurj : ∀ l : ℝ, l ≤ l0 →
      ∀ φ : H, ∃ ψ : (A + K).domain, (A + K) ψ - (l : ℂ) • (ψ : H) = φ := by
    intro l hl
    obtain ⟨Rl, hRl, hRn, hsym⟩ := resolvent_below A hA γ hγ l (by linarith)
    exact add_sub_surj A K l Rl _ hRl (KR_eq A K z R C hR hKC l Rl hRl)
      (lt_of_le_of_lt (hsmall l hl Rl hRl hRn hsym) (by norm_num))
  have hd : Dense ((A + K).domain : Set H) := by rw [hdom]; exact hA.dense_domain
  exact ⟨hdom, selfAdjoint_of_symm_surj (A + K) hd (add_symm A K hA hK) l0 (hsurj l0 le_rfl),
    l0, hl0, hsurj⟩


/-- P6a: the resolvent identity `R_a - R_b = (a - b) R_a R_b`. -/
theorem resolvent_identity (X : H →ₗ.[ℂ] H) (a b : ℂ) (Ra Rb : H →L[ℂ] H)
    (ha : TeschlQM.Shared.IsResolventAt X a Ra) (hb : TeschlQM.Shared.IsResolventAt X b Rb)
    (φ : H) : Ra φ - Rb φ = (a - b) • Ra (Rb φ) := by
  obtain ⟨hD, hX⟩ := hb.1 φ
  have e := ha.2 ⟨Rb φ, hD⟩
  have h1 : X ⟨Rb φ, hD⟩ - a • Rb φ = φ - (a - b) • Rb φ := by
    calc X ⟨Rb φ, hD⟩ - a • Rb φ = (X ⟨Rb φ, hD⟩ - b • Rb φ) - (a - b) • Rb φ := by
          rw [sub_smul]; abel
      _ = φ - (a - b) • Rb φ := by rw [hX]
  simp only at e
  rw [h1, map_sub, map_smul] at e
  calc Ra φ - Rb φ = Ra φ - (Ra φ - (a - b) • Ra (Rb φ)) := by rw [e]
    _ = (a - b) • Ra (Rb φ) := by abel

/-- P6b: if `‖K R_A(l)‖ < 1` then `l ∈ ρ(A + K)`, with `R_{A+K}(l) = R_A(l) (1 + K R_A(l))⁻¹`. -/
theorem resolvent_T (A K : H →ₗ.[ℂ] H) (z : ℂ) (R C : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R)
    (hKC : ∀ φ : H, ∃ h : R φ ∈ K.domain, K ⟨R φ, h⟩ = C φ) (l : ℂ) (Rl : H →L[ℂ] H)
    (hRl : TeschlQM.Shared.IsResolventAt A l Rl) (hn : ‖C.comp (1 + (l - z) • Rl)‖ < 1) :
    ∃ S : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt (A + K) l S := by
  set C' : H →L[ℂ] H := C.comp (1 + (l - z) • Rl) with hC'
  have hn' : ‖-C'‖ < 1 := by rwa [norm_neg]
  set U := Units.oneSub (-C') hn' with hUdef
  have hU : ((U : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = 1 + C' := by
    rw [hUdef, Units.val_oneSub, sub_neg_eq_add]
  obtain ⟨W, hW1, hW2⟩ : ∃ W : H →L[ℂ] H, (∀ φ, W φ + C' (W φ) = φ) ∧ (∀ v, W (v + C' v) = v) := by
    refine ⟨((U⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H), fun φ => ?_, fun v => ?_⟩
    · have h := congrArg (fun T : H →L[ℂ] H => T φ) (Units.mul_inv U)
      simp only [hU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.one_apply] at h
      exact h
    · have h := congrArg (fun T : H →L[ℂ] H => T v) (Units.inv_mul U)
      simp only [hU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.one_apply] at h
      exact h
  have hKR := KR_eq A K z R C hR hKC l Rl hRl
  refine ⟨Rl.comp W, fun φ => ?_, fun ψ => ?_⟩
  · obtain ⟨hD, hA⟩ := hRl.1 (W φ)
    obtain ⟨hK, hKe⟩ := hKR (W φ)
    have hmem : (Rl.comp W) φ ∈ (A + K).domain := ⟨hD, hK⟩
    refine ⟨hmem, ?_⟩
    have ex : (A + K) ⟨(Rl.comp W) φ, hmem⟩ = A ⟨Rl (W φ), hD⟩ + K ⟨Rl (W φ), hK⟩ :=
      LinearPMap.add_apply A K ⟨(Rl.comp W) φ, hmem⟩
    rw [ex, hKe]
    simp only [ContinuousLinearMap.comp_apply] at hA ⊢
    calc A ⟨Rl (W φ), hD⟩ + C' (W φ) - l • Rl (W φ)
        = (A ⟨Rl (W φ), hD⟩ - l • Rl (W φ)) + C' (W φ) := by abel
      _ = φ := by rw [hA, hW1]
  · have hψA : (ψ : H) ∈ A.domain := ψ.2.1
    have hψK : (ψ : H) ∈ K.domain := ψ.2.2
    set v : H := A ⟨ψ, hψA⟩ - l • (ψ : H) with hv
    have hRv : Rl v = ψ := hRl.2 ⟨ψ, hψA⟩
    obtain ⟨hK2, hKe2⟩ := hKR v
    have hKψ : K ⟨ψ, hψK⟩ = C' v := by
      rw [← hKe2]
      have : (⟨ψ, hψK⟩ : K.domain) = ⟨Rl v, hK2⟩ := Subtype.ext hRv.symm
      rw [this]
    have ex : (A + K) ψ = A ⟨ψ, hψA⟩ + K ⟨ψ, hψK⟩ := LinearPMap.add_apply A K ψ
    have e2 : (A + K) ψ - l • (ψ : H) = v + C' v := by
      rw [ex, hKψ, hv]; abel
    simp only [ContinuousLinearMap.comp_apply]
    rw [e2, hW2, hRv]


/-- P6c: the resolvent at a real point of a symmetric operator is symmetric. -/
theorem resolvent_symm (X : H →ₗ.[ℂ] H)
    (hs : ∀ x y : X.domain, ⟪X x, (y : H)⟫_ℂ = ⟪(x : H), X y⟫_ℂ) (l : ℝ) (S : H →L[ℂ] H)
    (hS : TeschlQM.Shared.IsResolventAt X (l : ℂ) S) : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ := by
  intro x y
  obtain ⟨hx, ex⟩ := hS.1 x
  obtain ⟨hy, ey⟩ := hS.1 y
  calc ⟪S x, y⟫_ℂ = ⟪S x, X ⟨S y, hy⟩ - (l : ℂ) • S y⟫_ℂ := by rw [ey]
    _ = ⟪S x, X ⟨S y, hy⟩⟫_ℂ - (l : ℂ) * ⟪S x, S y⟫_ℂ := by
        rw [inner_sub_right, inner_smul_right]
    _ = ⟪X ⟨S x, hx⟩, S y⟫_ℂ - (l : ℂ) * ⟪S x, S y⟫_ℂ := by
        rw [hs ⟨S x, hx⟩ ⟨S y, hy⟩]
    _ = ⟪X ⟨S x, hx⟩ - (l : ℂ) • S x, S y⟫_ℂ := by
        rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal]
    _ = ⟪x, S y⟫_ℂ := by rw [ex]

/-- P8a: if `a ≠ b` are both in `ρ(X)` then `(b - a)⁻¹ - R_X(a)` is invertible. -/
theorem isUnit_of_resolvent (X : H →ₗ.[ℂ] H) (a b : ℂ) (hab : a ≠ b) (Ra Rb : H →L[ℂ] H)
    (ha : TeschlQM.Shared.IsResolventAt X a Ra) (hb : TeschlQM.Shared.IsResolventAt X b Rb) :
    IsUnit (algebraMap ℂ (H →L[ℂ] H) ((b - a)⁻¹) - Ra) := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  set c : ℂ := (b - a)⁻¹ with hc
  have hcb : c * (b - a) = 1 := inv_mul_cancel₀ hba
  have hbc : (b - a) * c = 1 := mul_inv_cancel₀ hba
  have k1 : ∀ φ, (b - a) • Ra (Rb φ) = Rb φ - Ra φ := by
    intro φ
    have e := resolvent_identity X a b Ra Rb ha hb φ
    rw [show b - a = -(a - b) by ring, neg_smul, ← e]; abel
  have k2 : ∀ φ, (b - a) • Rb (Ra φ) = Rb φ - Ra φ := fun φ =>
    (resolvent_identity X b a Rb Ra hb ha φ).symm
  have hal : ∀ φ, algebraMap ℂ (H →L[ℂ] H) c φ = c • φ := by
    intro φ; simp [Algebra.algebraMap_eq_smul_one]
  refine ⟨⟨algebraMap ℂ (H →L[ℂ] H) c - Ra, (b - a) • (1 + (b - a) • Rb), ?_, ?_⟩, rfl⟩
  · ext φ
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, hal]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply]
    rw [smul_smul c, hcb, one_smul, map_smul, map_add, map_smul, k1]
    have h3 : Ra φ + (Rb φ - Ra φ) = Rb φ := by abel
    rw [h3]; abel
  · ext φ
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, hal]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply]
    rw [map_sub, map_smul, smul_sub, k2, smul_smul (b - a) c, hbc, one_smul]
    have h3 : c • φ - Ra φ + (Rb φ - (Rb φ - Ra φ)) = c • φ := by abel
    rw [h3, smul_smul, hbc, one_smul]

/-- P6d: a self-adjoint bounded operator with `s - S` invertible for all `s < 0` is positive. -/
theorem nonneg_of_resolvent (S : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hspec : ∀ s : ℝ, s < 0 → IsUnit (algebraMap ℝ (H →L[ℂ] H) s - S)) :
    ∀ φ : H, 0 ≤ (⟪S φ, φ⟫_ℂ).re := by
  have h0 : 0 ≤ S := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) S hS).2
    (fun x hx => le_of_not_gt (fun hneg => (spectrum.mem_iff.1 hx) (hspec x hneg)))
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive S).1 h0
  exact fun φ => hp.re_inner_nonneg_left φ

/-- P6 (Kato-Rellich, lower bound): `A + K` is bounded below, and `l ∈ ρ(A + K)` for all real
`l ≤ l0`. -/
theorem kato_rellich_bdd (A K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (γ : ℝ)
    (hγ : ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re)
    (hK : ∀ x y : K.domain, ⟪K x, (y : H)⟫_ℂ = ⟪(x : H), K y⟫_ℂ)
    (hrc : TeschlQM.Shared.IsRelativelyCompact K A) :
    TeschlQM.OneParticle.IsBoundedBelow (A + K) ∧ ∃ l0 : ℝ, ∀ l : ℝ, l ≤ l0 →
      ∃ S : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt (A + K) (l : ℂ) S := by
  obtain ⟨z, R, hR, C, hC, hKC⟩ := hrc
  obtain ⟨l0, hl0, hsmall⟩ := relCompact_small A hA.dense_domain γ z C hC (1 / 2) (by norm_num)
  have hres : ∀ l : ℝ, l ≤ l0 →
      ∃ S : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt (A + K) (l : ℂ) S := by
    intro l hl
    obtain ⟨Rl, hRl, hRn, hsym⟩ := resolvent_below A hA γ hγ l (by linarith)
    exact resolvent_T A K z R C hR hKC l Rl hRl
      (lt_of_le_of_lt (hsmall l hl Rl hRl hRn hsym) (by norm_num))
  refine ⟨?_, l0, hres⟩
  obtain ⟨S, hS⟩ := hres l0 le_rfl
  have hSs := resolvent_symm (A + K) (add_symm A K hA hK) l0 S hS
  have hSa : IsSelfAdjoint S :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (fun x y => hSs x y)
  have hspec : ∀ s : ℝ, s < 0 → IsUnit (algebraMap ℝ (H →L[ℂ] H) s - S) := by
    intro s hs
    set b : ℝ := l0 + s⁻¹ with hbdef
    have hsi : s⁻¹ < 0 := inv_lt_zero.2 hs
    have hb : b ≤ l0 := by linarith
    obtain ⟨Sb, hSb⟩ := hres b hb
    have hne : (l0 : ℂ) ≠ (b : ℂ) := by
      intro h
      have := Complex.ofReal_injective h
      linarith
    have hu := isUnit_of_resolvent (A + K) (l0 : ℂ) (b : ℂ) hne S Sb hS hSb
    have e : ((b : ℂ) - (l0 : ℂ))⁻¹ = (s : ℂ) := by
      rw [hbdef]; push_cast; rw [add_sub_cancel_left, inv_inv]
    rw [e] at hu
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (H →L[ℂ] H) s, Complex.coe_algebraMap]
    exact hu
  have hpos := nonneg_of_resolvent S hSa hspec
  refine ⟨l0, fun ψ => ?_⟩
  have e := hS.2 ψ
  have hp := hpos ((A + K) ψ - (l0 : ℂ) • (ψ : H))
  rw [e, inner_sub_right, Complex.sub_re] at hp
  have hl : (⟪(ψ : H), (l0 : ℂ) • (ψ : H)⟫_ℂ).re = l0 * ‖(ψ : H)‖ ^ 2 := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.re_ofReal_mul]
    norm_cast
  linarith



/-- `S - μ` is bounded below off a finite-dimensional subspace. -/
def FredAt (S : H →L[ℂ] H) (μ : ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧
    ∀ φ : H, φ ∈ Vᗮ → ε * ‖φ‖ ≤ ‖S φ - μ • φ‖

/-- B1: a compact operator is small off a finite-dimensional subspace. -/
theorem compact_small (C : H →L[ℂ] H) (hC : IsCompactOperator C) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ ∀ φ : H, φ ∈ Wᗮ → ‖C φ‖ ≤ δ * ‖φ‖ := by
  have hK : IsCompact (closure (C '' Metric.closedBall 0 1)) :=
    hC.isCompact_closure_image_closedBall 1
  obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded δ hδ
  refine ⟨Submodule.span ℂ (ContinuousLinearMap.adjoint C '' t),
    FiniteDimensional.span_of_finite ℂ (htf.image _), ?_⟩
  intro φ hφ
  by_cases h0 : φ = 0
  · simp [h0]
  have hn : 0 < ‖φ‖ := norm_pos_iff.2 h0
  set u : H := ((‖φ‖⁻¹ : ℝ) : ℂ) • φ with hu
  have hu1 : u ∈ Metric.closedBall (0 : H) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
  have huW : u ∈ (Submodule.span ℂ (ContinuousLinearMap.adjoint C '' t))ᗮ :=
    Submodule.smul_mem _ _ hφ
  have hmem : C u ∈ ⋃ y ∈ t, Metric.ball y δ := hcov (subset_closure ⟨u, hu1, rfl⟩)
  simp only [Set.mem_iUnion, Metric.mem_ball] at hmem
  obtain ⟨y, hyt, hy⟩ := hmem
  have horth : ⟪C u, y⟫_ℂ = 0 := by
    have h1 : ⟪ContinuousLinearMap.adjoint C y, u⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_image_of_mem _ hyt)) huW
    rw [ContinuousLinearMap.adjoint_inner_left] at h1
    rw [← inner_conj_symm, h1, map_zero]
  have hCu : ‖C u‖ ≤ δ := by
    have h2 : ‖C u‖ ^ 2 ≤ ‖C u‖ * ‖C u - y‖ := by
      have e : (⟪C u, C u - y⟫_ℂ).re = ‖C u‖ ^ 2 := by
        rw [inner_sub_right, horth, sub_zero]
        exact inner_self_eq_norm_sq (𝕜 := ℂ) (C u)
      rw [← e]
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
    rw [← dist_eq_norm] at h2
    by_cases hz : ‖C u‖ = 0
    · rw [hz]; exact hδ.le
    · have hp : 0 < ‖C u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have : ‖C u‖ ≤ dist (C u) y := by nlinarith
      linarith
  have hφu : φ = ((‖φ‖ : ℝ) : ℂ) • u := by
    rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  rw [hφu, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have hu' : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn),
      inv_mul_cancel₀ hn.ne']
  rw [hu', mul_one, mul_comm]
  exact mul_le_mul_of_nonneg_right hCu hn.le

/-- B1': `FredAt` is stable under compact perturbations. -/
theorem fred_add_compact (S C : H →L[ℂ] H) (hC : IsCompactOperator C) (μ : ℂ)
    (h : FredAt S μ) : FredAt (S + C) μ := by
  obtain ⟨ε, hε, V, hV, hS⟩ := h
  obtain ⟨W, hW, hCW⟩ := compact_small C hC (ε / 2) (by linarith)
  refine ⟨ε / 2, by linarith, V ⊔ W, Submodule.finiteDimensional_sup V W, ?_⟩
  intro φ hφ
  have hφV : φ ∈ Vᗮ := Submodule.orthogonal_le le_sup_left hφ
  have hφW : φ ∈ Wᗮ := Submodule.orthogonal_le le_sup_right hφ
  have h1 := hS φ hφV
  have h2 := hCW φ hφW
  have h3 : ‖S φ - μ • φ‖ ≤ ‖(S + C) φ - μ • φ‖ + ‖C φ‖ := by
    have : S φ - μ • φ = ((S + C) φ - μ • φ) - C φ := by
      simp; abel
    rw [this]; exact norm_sub_le _ _
  linarith

/-- Finite-dimensional bound: a subspace meeting `Vᗮ` trivially has dimension at most `dim V`. -/
theorem dim_le (M V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (h : ∀ x ∈ M, x ∈ Vᗮ → x = 0) :
    FiniteDimensional ℂ M ∧ Module.finrank ℂ M ≤ Module.finrank ℂ V := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  set L : M →ₗ[ℂ] V := (V.orthogonalProjectionOnto : H →L[ℂ] V).toLinearMap ∘ₗ M.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have : (x : H) ∈ Vᗮ := by
      rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
      exact hx
    exact Subtype.ext (h x x.2 this)
  haveI : FiniteDimensional ℂ M := Module.Finite.of_injective L hinj
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hinj⟩

/-- B2-T1: outside the spectrum, `S - μ` is bounded below. -/
theorem fred_of_not_spec (S : H →L[ℂ] H) (μ : ℂ) (h : μ ∉ spectrum ℂ S) : FredAt S μ := by
  have h' : IsUnit (algebraMap ℂ (H →L[ℂ] H) μ - S) :=
    not_not.1 (fun hc => h (spectrum.mem_iff.2 hc))
  obtain ⟨U, hU⟩ := h'
  set c := ‖(↑U⁻¹ : H →L[ℂ] H)‖ with hcdef
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨1 / (c + 1), by positivity, ⊥, inferInstance, ?_⟩
  intro φ _
  have e : (↑U⁻¹ : H →L[ℂ] H) (μ • φ - S φ) = φ := by
    have : ((↑U⁻¹ : H →L[ℂ] H) * ↑U) φ = φ := by rw [Units.inv_mul]; rfl
    rw [hU] at this
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have h1 : ‖φ‖ ≤ c * ‖S φ - μ • φ‖ := by
    calc ‖φ‖ = ‖(↑U⁻¹ : H →L[ℂ] H) (μ • φ - S φ)‖ := by rw [e]
      _ ≤ c * ‖μ • φ - S φ‖ := ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [norm_sub_rev]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg φ, norm_nonneg (S φ - μ • φ)]

/-- `(S - m) cfc G S = cfc ((t - m) G) S`, pointwise. -/
theorem cfc_lin (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (m : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (x : H) :
    S (cfc G S x) - (m : ℂ) • cfc G S x = cfc (fun t => (t - m) * G t) S x := by
  rw [cfc_mul (fun t => t - m) G S (by fun_prop) hG.continuousOn,
    cfc_sub (fun t => t) (fun _ => m) S, cfc_id' ℝ S, cfc_const m S]
  simp [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]

/-- B2-T3(b): a "spectral window" subspace of width `ε/2` around `m` has dimension `≤ dim V`. -/
theorem window_dim (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (m : ℝ) (ε : ℝ) (hε : 0 < ε)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (hV : ∀ φ : H, φ ∈ Vᗮ → ε * ‖φ‖ ≤ ‖S φ - (m : ℂ) • φ‖)
    (G : ℝ → ℝ) (hG : Continuous G) (hGb : ∀ t, |(t - m) * G t| ≤ ε / 2)
    (M : Submodule ℂ H) (hM : ∀ x ∈ M, cfc G S x = x) :
    FiniteDimensional ℂ M ∧ Module.finrank ℂ M ≤ Module.finrank ℂ V := by
  apply dim_le M V
  intro x hxM hxV
  have h1 := hV x hxV
  have e := cfc_lin S hS m G hG x
  rw [hM x hxM] at e
  have h2 : ‖S x - (m : ℂ) • x‖ ≤ ε / 2 * ‖x‖ := by
    rw [e]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact norm_cfc_le (by linarith) (fun t _ => by rw [Real.norm_eq_abs]; exact hGb t)
  have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.1 this

/-- The plateau function: `1` on `|t - m| ≤ ε/4`, `0` for `|t - m| ≥ ε/2`. -/
noncomputable def plateau (m ε : ℝ) (t : ℝ) : ℝ := max 0 (min 1 (2 - 4 * |t - m| / ε))

/-- A tent of radius `r` at `w`. -/
noncomputable def tent (w r : ℝ) (t : ℝ) : ℝ := max 0 (1 - |t - w| / r)

theorem plateau_cont (m ε : ℝ) : Continuous (plateau m ε) := by
  unfold plateau; fun_prop

theorem tent_cont (w r : ℝ) : Continuous (tent w r) := by
  unfold tent; fun_prop

theorem plateau_bound (m ε : ℝ) (hε : 0 < ε) (t : ℝ) : |(t - m) * plateau m ε t| ≤ ε / 2 := by
  unfold plateau
  rw [abs_mul]
  by_cases h : |t - m| < ε / 2
  · have h0 : 0 ≤ max 0 (min 1 (2 - 4 * |t - m| / ε)) := le_max_left _ _
    have h1 : max 0 (min 1 (2 - 4 * |t - m| / ε)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    rw [abs_of_nonneg h0]
    nlinarith [abs_nonneg (t - m)]
  · have : 2 - 4 * |t - m| / ε ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hε]; linarith
    have : max 0 (min 1 (2 - 4 * |t - m| / ε)) = 0 :=
      max_eq_left ((min_le_right _ _).trans this)
    rw [this]; simp; linarith

theorem tent_eq_zero {w r t : ℝ} (hr : 0 < r) (h : r ≤ |t - w|) : tent w r t = 0 := by
  unfold tent
  apply max_eq_left
  rw [sub_nonpos, le_div_iff₀ hr]; linarith

theorem tent_self (w r : ℝ) (hr : 0 < r) : tent w r w = 1 := by
  unfold tent; simp

/-- B2-T3(c): a finite set of spectral points within `ε/4` of `m` has at most `dim V` elements. -/
theorem card_le (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (m : ℝ) (ε : ℝ) (hε : 0 < ε)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (hV : ∀ φ : H, φ ∈ Vᗮ → ε * ‖φ‖ ≤ ‖S φ - (m : ℂ) • φ‖)
    (F : Finset ℝ) (hF : ∀ w ∈ F, w ∈ spectrum ℝ S ∧ |w - m| < ε / 4) :
    F.card ≤ Module.finrank ℂ V := by
  classical
  -- a common tent radius
  have hev : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ p ∈ F ×ˢ F,
      (p.1 ≠ p.2 → 2 * r ≤ |p.1 - p.2|) ∧ r ≤ ε / 4 - |p.1 - m| := by
    rw [Filter.eventually_all_finset]
    intro p hp
    rw [Finset.mem_product] at hp
    have hpos : 0 < ε / 4 - |p.1 - m| := by linarith [(hF p.1 hp.1).2]
    refine Filter.Eventually.and ?_ ?_
    · by_cases hne : p.1 = p.2
      · exact Filter.Eventually.of_forall (fun _ h => absurd hne h)
      · have hd : 0 < |p.1 - p.2| / 2 := by
          have : 0 < |p.1 - p.2| := abs_pos.2 (sub_ne_zero.2 hne)
          linarith
        filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hd)] with r hr _
        linarith
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hpos)] with r hr
      exact hr.le
  obtain ⟨r, hr, hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0 : (0 : ℝ) < r := hrpos
  set G := plateau m ε with hGdef
  -- G * tent = tent
  have hGt : ∀ w ∈ F, ∀ t, G t * tent w r t = tent w r t := by
    intro w hw t
    by_cases ht : |t - w| < r
    · have hwm := (hr (w, w) (Finset.mem_product.2 ⟨hw, hw⟩)).2
      simp only at hwm
      have htm : |t - m| ≤ ε / 4 := by
        have := abs_sub_le t w m
        linarith
      have : G t = 1 := by
        rw [hGdef]; unfold plateau
        have : 1 ≤ 2 - 4 * |t - m| / ε := by
          rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hε]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      rw [this, one_mul]
    · rw [tent_eq_zero hr0 (not_lt.1 ht), mul_zero]
  -- disjoint tents
  have hdis : ∀ w ∈ F, ∀ w' ∈ F, w ≠ w' → ∀ t, tent w r t * tent w' r t = 0 := by
    intro w hw w' hw' hne t
    have hsep := (hr (w, w') (Finset.mem_product.2 ⟨hw, hw'⟩)).1 hne
    simp only at hsep
    by_cases ht : |t - w| < r
    · have : r ≤ |t - w'| := by
        by_contra hc
        push Not at hc
        have := abs_sub_le w t w'
        rw [abs_sub_comm w t] at this
        linarith
      rw [tent_eq_zero hr0 this, mul_zero]
    · rw [tent_eq_zero hr0 (not_lt.1 ht), zero_mul]
  -- nonzero vectors in the range of each tent
  have hne : ∀ w ∈ F, ∃ η : H, cfc (tent w r) S η ≠ 0 := by
    intro w hw
    by_contra hc
    push Not at hc
    have h0 : cfc (tent w r) S = 0 := ContinuousLinearMap.ext hc
    have := norm_apply_le_norm_cfc (tent w r) S (hF w hw).1 (tent_cont w r).continuousOn hS
    rw [h0, tent_self w r hr0, norm_zero] at this
    norm_num at this
  choose! η hη using hne
  set v : F → H := fun w => cfc (tent w r) S (η w) with hv
  have hv0 : ∀ w : F, v w ≠ 0 := fun w => hη w w.2
  have hvG : ∀ w : F, cfc G S (v w) = v w := by
    intro w
    rw [hv]
    show (cfc G S * cfc (tent (w : ℝ) r) S) (η w) = _
    rw [← cfc_mul G (tent (w : ℝ) r) S (plateau_cont m ε).continuousOn
      (tent_cont _ r).continuousOn]
    congr 2
    funext t
    exact hGt w w.2 t
  have hvo : Pairwise fun i j : F => ⟪v i, v j⟫_ℂ = 0 := by
    intro i j hij
    have hij' : (i : ℝ) ≠ j := fun h => hij (Subtype.ext h)
    have hsa : IsSelfAdjoint (cfc (tent (i : ℝ) r) S) := cfc_predicate _ _
    rw [hv]
    simp only
    rw [← ContinuousLinearMap.adjoint_inner_right (cfc (tent (i : ℝ) r) S),
      ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
    show ⟪η i, (cfc (tent (i : ℝ) r) S * cfc (tent (j : ℝ) r) S) (η j)⟫_ℂ = 0
    rw [← cfc_mul _ _ S (tent_cont _ r).continuousOn (tent_cont _ r).continuousOn]
    have : (fun t => tent (i : ℝ) r t * tent (j : ℝ) r t) = fun _ => 0 := by
      funext t; exact hdis i i.2 j j.2 hij' t
    rw [this, cfc_const_zero]
    simp
  have hli : LinearIndependent ℂ v := linearIndependent_of_ne_zero_of_inner_eq_zero hv0 hvo
  set M : Submodule ℂ H := LinearMap.ker (((cfc G S : H →L[ℂ] H) : H →ₗ[ℂ] H) - LinearMap.id) with hMdef
  have hMmem : ∀ x ∈ M, cfc G S x = x := by
    intro x hx
    rw [hMdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
    exact hx
  obtain ⟨hMf, hMr⟩ := window_dim S hS m ε hε V hV G (plateau_cont m ε)
    (plateau_bound m ε hε) M hMmem
  have hvM : ∀ w : F, v w ∈ M := by
    intro w
    rw [hMdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact hvG w
  set v' : F → M := fun w => ⟨v w, hvM w⟩
  have hli' : LinearIndependent ℂ v' := by
    apply LinearIndependent.of_comp M.subtype
    exact hli
  have := hli'.fintype_card_le_finrank
  rw [Fintype.card_coe] at this
  exact this.trans hMr

/-- The eigenspace of a bounded operator. -/
def eig (S : H →L[ℂ] H) (μ : ℂ) : Submodule ℂ H :=
  LinearMap.ker ((S : H →ₗ[ℂ] H) - μ • LinearMap.id)

theorem mem_eig {S : H →L[ℂ] H} {μ : ℂ} {φ : H} : φ ∈ eig S μ ↔ S φ = μ • φ := by
  rw [eig, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  rfl

/-- B2-T3: `FredAt` at a spectral point forces a discrete eigenvalue. -/
theorem of_fred (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (μ : ℂ) (h : FredAt S μ)
    (hμ : μ ∈ spectrum ℂ S) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ spectrum ℂ S, ‖w - μ‖ < δ → w = μ) ∧ eig S μ ≠ ⊥ ∧
      FiniteDimensional ℂ (eig S μ) := by
  classical
  obtain ⟨ε, hε, V, hV, hfred⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m : ℝ, μ = m := ⟨μ.re, hS.mem_spectrum_eq_re hμ⟩
  have hreal : ∀ w ∈ spectrum ℂ S, w = (w.re : ℂ) := fun w hw => hS.mem_spectrum_eq_re hw
  have hRe : ∀ w ∈ spectrum ℂ S, w.re ∈ spectrum ℝ S := by
    intro w hw
    apply spectrum.of_algebraMap_mem ℂ
    have e : (algebraMap ℝ ℂ) w.re = w := by
      rw [Complex.coe_algebraMap]; exact (hreal w hw).symm
    rw [e]; exact hw
  -- finiteness of the spectrum near m
  set P : Set ℝ := {w | w ∈ spectrum ℝ S ∧ |w - m| < ε / 4} with hPdef
  have hPfin : P.Finite := by
    by_contra hinf
    obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (Module.finrank ℂ V + 1)
    have := card_le S hS m ε hε V hfred F (fun w hw => hFsub hw)
    omega
  set T := hPfin.toFinset.erase m with hTdef
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ w ∈ T, δ ≤ |w - m| := by
    rw [Filter.eventually_all_finset]
    intro w hw
    have hpos : 0 < |w - m| := abs_pos.2 (sub_ne_zero.2 (Finset.ne_of_mem_erase hw))
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hpos)] with δ hδ
    exact hδ.le
  have hev2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < ε / 4 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by linarith))
  obtain ⟨δ, ⟨hδT, hδε⟩, hδpos⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδpos
  have hiso : ∀ w ∈ spectrum ℂ S, ‖w - (m : ℂ)‖ < δ → w = m := by
    intro w hw hwd
    have e := hreal w hw
    have hn : ‖w - (m : ℂ)‖ = |w.re - m| := by
      rw [e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    rw [hn] at hwd
    by_contra hne
    have hre : w.re ≠ m := fun h' => hne (by rw [e, h'])
    have hP : w.re ∈ P := ⟨hRe w hw, by linarith⟩
    have hT : w.re ∈ T := Finset.mem_erase.2 ⟨hre, hPfin.mem_toFinset.2 hP⟩
    have := hδT w.re hT
    linarith
  refine ⟨⟨δ, hδ0, hiso⟩, ?_, ?_⟩
  · -- an eigenvector from the tent at `m`
    have hmS : m ∈ spectrum ℝ S := by
      have := hRe _ hμ
      simpa using this
    have hne : ∃ η : H, cfc (tent m δ) S η ≠ 0 := by
      by_contra hc
      push Not at hc
      have h0 : cfc (tent m δ) S = 0 := ContinuousLinearMap.ext hc
      have := norm_apply_le_norm_cfc (tent m δ) S hmS (tent_cont m δ).continuousOn hS
      rw [h0, tent_self m δ hδ0, norm_zero] at this
      norm_num at this
    obtain ⟨η, hη⟩ := hne
    have hzero : cfc (fun t => (t - m) * tent m δ t) S = 0 := by
      rw [← cfc_const_zero (R := ℝ) (a := S)]
      apply cfc_congr
      intro t ht
      by_cases htm : t = m
      · simp [htm]
      · have htC : (t : ℂ) ∈ spectrum ℂ S := by
          have := spectrum.algebraMap_mem ℂ ht
          simpa using this
        have : δ ≤ |t - m| := by
          by_contra hc
          push Not at hc
          have := hiso _ htC (by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hc)
          exact htm (Complex.ofReal_injective this)
        simp [tent_eq_zero hδ0 this]
    have e := cfc_lin S hS m (tent m δ) (tent_cont m δ) η
    rw [hzero, ContinuousLinearMap.zero_apply, sub_eq_zero] at e
    rw [Submodule.ne_bot_iff]
    exact ⟨cfc (tent m δ) S η, mem_eig.2 e, hη⟩
  · haveI := hV
    refine (dim_le (eig S m) V ?_).1
    intro x hx hxV
    have h1 := hfred x hxV
    rw [mem_eig.1 hx, sub_self, norm_zero] at h1
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.1 this

/-- B2-T2: at an isolated eigenvalue of finite multiplicity, `FredAt` holds. -/
theorem fred_of_discrete (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ S) (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ w ∈ spectrum ℂ S, ‖w - μ‖ < δ → w = μ) (hfin : FiniteDimensional ℂ (eig S μ)) :
    FredAt S μ := by
  obtain ⟨m, rfl⟩ : ∃ m : ℝ, μ = m := ⟨μ.re, hS.mem_spectrum_eq_re hμ⟩
  have hfar : ∀ t ∈ spectrum ℝ S, t ≠ m → δ ≤ |t - m| := by
    intro t ht htm
    have htC : (t : ℂ) ∈ spectrum ℂ S := by
      have := spectrum.algebraMap_mem ℂ ht
      simpa using this
    by_contra hc
    push Not at hc
    have := hiso _ htC (by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hc)
    exact htm (Complex.ofReal_injective this)
  set Q := cfc (tent m δ) S with hQdef
  have hden : ∀ t : ℝ, max ((t - m) ^ 2) (δ ^ 2) ≠ 0 := fun t =>
    (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'
  set g : ℝ → ℝ := fun t => (t - m) * (max ((t - m) ^ 2) (δ ^ 2))⁻¹ with hgdef
  have hgc : Continuous g :=
    (continuous_id.sub continuous_const).mul
      ((by fun_prop : Continuous fun t : ℝ => max ((t - m) ^ 2) (δ ^ 2)).inv₀ hden)
  have hlin : cfc (fun t : ℝ => t - m) S = S - algebraMap ℝ (H →L[ℂ] H) m := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => m) S, cfc_id' ℝ S, cfc_const m S]
  have hkey : cfc g S * cfc (fun t : ℝ => t - m) S = 1 - Q := by
    rw [← cfc_mul g (fun t : ℝ => t - m) S hgc.continuousOn (by fun_prop), hQdef,
      ← cfc_const_one (R := ℝ) (a := S),
      ← cfc_sub (fun _ : ℝ => (1 : ℝ)) (tent m δ) S (by fun_prop) (tent_cont m δ).continuousOn]
    apply cfc_congr
    intro t ht
    by_cases htm : t = m
    · simp [hgdef, htm, tent_self m δ hδ]
    · have h1 := hfar t ht htm
      have h2 : δ ^ 2 ≤ (t - m) ^ 2 := by
        rw [← sq_abs (t - m)]; exact pow_le_pow_left₀ hδ.le h1 2
      have hne : (t - m) ≠ 0 := sub_ne_zero.2 htm
      simp only [hgdef]
      rw [max_eq_left h2, tent_eq_zero hδ h1, sub_zero]
      field_simp
  have hQeig : ∀ η : H, Q η ∈ eig S m := by
    intro η
    have hzero : cfc (fun t => (t - m) * tent m δ t) S = 0 := by
      rw [← cfc_const_zero (R := ℝ) (a := S)]
      apply cfc_congr
      intro t ht
      by_cases htm : t = m
      · simp [htm]
      · simp [tent_eq_zero hδ (hfar t ht htm)]
    have e := cfc_lin S hS m (tent m δ) (tent_cont m δ) η
    rw [hzero, ContinuousLinearMap.zero_apply, sub_eq_zero] at e
    exact mem_eig.2 e
  have hsa : IsSelfAdjoint Q := cfc_predicate _ _
  set c := ‖cfc g S‖ with hcdef
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨1 / (c + 1), by positivity, eig S m, hfin, ?_⟩
  intro φ hφ
  have hQφ : Q φ = 0 := by
    have : ⟪Q φ, Q φ⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right Q, ← ContinuousLinearMap.star_eq_adjoint,
        hsa.star_eq]
      exact Submodule.inner_left_of_mem_orthogonal (hQeig (Q φ)) hφ
    exact inner_self_eq_zero.1 this
  have e : cfc g S (S φ - (m : ℂ) • φ) = φ := by
    have h1 : (cfc g S * cfc (fun t : ℝ => t - m) S) φ = φ - Q φ := by
      rw [hkey]; simp
    rw [hQφ, sub_zero, ContinuousLinearMap.mul_apply, hlin] at h1
    have h2 : (S - algebraMap ℝ (H →L[ℂ] H) m) φ = S φ - (m : ℂ) • φ := by
      simp [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
    rw [h2] at h1
    exact h1
  have h1 : ‖φ‖ ≤ c * ‖S φ - (m : ℂ) • φ‖ := by
    calc ‖φ‖ = ‖cfc g S (S φ - (m : ℂ) • φ)‖ := by rw [e]
      _ ≤ c * ‖S φ - (m : ℂ) • φ‖ := ContinuousLinearMap.le_opNorm _ _
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg φ, norm_nonneg (S φ - (m : ℂ) • φ)]



/-- P7: cores transfer along an `A`-bounded perturbation `T = A + C (A - z)` with `T` closed. -/
theorem core_transfer (A T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (hdom : T.domain = A.domain)
    (C : H →L[ℂ] H) (z : ℂ)
    (hTA : ∀ (x : H) (h1 : x ∈ T.domain) (h2 : x ∈ A.domain),
      T ⟨x, h1⟩ = A ⟨x, h2⟩ + C (A ⟨x, h2⟩ - z • x))
    (S : Submodule ℂ H) (hS : A.HasCore S) : T.HasCore S := by
  have hle : S ≤ T.domain := hdom ▸ hS.le_domain
  refine ⟨hle, ?_⟩
  set f := T.domRestrict S with hfdef
  have hfT : f ≤ T := LinearPMap.domRestrict_le
  have hf : f.IsClosable := hT.isClosable.leIsClosable hfT
  apply LinearPMap.eq_of_eq_graph
  rw [← hf.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hfT) hT
  · intro p hp
    rw [LinearPMap.mem_graph_iff] at hp
    obtain ⟨y, hy1, hy2⟩ := hp
    have hyA : (y : H) ∈ A.domain := hdom ▸ y.2
    set g := A.domRestrict S with hgdef
    have hmem : ((y : H), A ⟨y, hyA⟩) ∈ (g.graph.topologicalClosure : Set (H × H)) := by
      by_cases hg : g.IsClosable
      · rw [hg.graph_closure_eq_closure_graph, hS.closure_eq]
        exact LinearPMap.mem_graph A ⟨y, hyA⟩
      · have e : g = A := (LinearPMap.closure_def' hg).symm.trans hS.closure_eq
        apply Submodule.le_topologicalClosure
        rw [e]
        exact LinearPMap.mem_graph A ⟨y, hyA⟩
    set Φ : H × H →L[ℂ] H × H := (ContinuousLinearMap.fst ℂ H H).prod
      (ContinuousLinearMap.snd ℂ H H + C.comp (ContinuousLinearMap.snd ℂ H H -
        z • ContinuousLinearMap.fst ℂ H H)) with hΦ
    have hΦapp : ∀ q : H × H, Φ q = (q.1, q.2 + C (q.2 - z • q.1)) := by
      intro q; simp [hΦ]
    have hmaps : Set.MapsTo Φ (g.graph : Set (H × H)) (f.graph : Set (H × H)) := by
      intro q hq
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hq
      obtain ⟨x, hx1, hx2⟩ := hq
      have hxS : (x : H) ∈ S := x.2.1
      have hxA : (x : H) ∈ A.domain := x.2.2
      have hxT : (x : H) ∈ T.domain := hle hxS
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      refine ⟨⟨x, hxS, hxT⟩, ?_, ?_⟩
      · rw [hΦapp]; exact hx1
      · rw [hΦapp]
        have h1 : f ⟨x, hxS, hxT⟩ = T ⟨x, hxT⟩ := LinearPMap.domRestrict_apply rfl
        have h2 : g x = A ⟨x, hxA⟩ := LinearPMap.domRestrict_apply rfl
        rw [h1, hTA x hxT hxA, ← hx1, ← hx2, h2]
    have := map_mem_closure Φ.continuous (by
      rw [← Submodule.topologicalClosure_coe]; exact hmem) hmaps
    rw [← Submodule.topologicalClosure_coe] at this
    have hp : Φ ((y : H), A ⟨y, hyA⟩) = p := by
      rw [hΦapp]
      ext
      · exact hy1
      · simp only
        rw [← hy2, hTA y y.2 hyA]
    rw [← hp]
    exact this


/-! ## P8: essential spectrum through the resolvent (Moebius transfer) -/

/-- An inverse of `ν - R` (with `ν = (w - l)⁻¹`, `R = R_X(l)`) yields a resolvent of `X` at `w`. -/
theorem resolvent_of_inv (X : H →ₗ.[ℂ] H) (l w : ℂ) (R V : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hwν : (w - l) * (w - l)⁻¹ = 1)
    (h1 : ∀ x, (w - l)⁻¹ • V x - R (V x) = x) (h2 : ∀ x, V ((w - l)⁻¹ • x - R x) = x) :
    TeschlQM.Shared.IsResolventAt X w (R.comp ((w - l)⁻¹ • V)) := by
  have hcomm : ∀ x, R (V x) = V (R x) := by
    intro x
    have e : (w - l)⁻¹ • R (V x) - R (R (V x)) = R x := by
      conv_rhs => rw [← h1 x]
      rw [map_sub, map_smul]
    calc R (V x) = V ((w - l)⁻¹ • R (V x) - R (R (V x))) := (h2 _).symm
      _ = V (R x) := by rw [e]
  refine ⟨fun φ => ?_, fun ψ => ?_⟩
  · obtain ⟨hd, he⟩ := hR.1 ((w - l)⁻¹ • V φ)
    refine ⟨hd, ?_⟩
    show X ⟨R ((w - l)⁻¹ • V φ), hd⟩ - w • R ((w - l)⁻¹ • V φ) = φ
    have hX : X ⟨R ((w - l)⁻¹ • V φ), hd⟩ = (w - l)⁻¹ • V φ + l • R ((w - l)⁻¹ • V φ) :=
      eq_add_of_sub_eq he
    have key : l • ((w - l)⁻¹ • R (V φ)) - w • ((w - l)⁻¹ • R (V φ)) = - R (V φ) := by
      rw [smul_smul, smul_smul, ← sub_smul,
        show l * (w - l)⁻¹ - w * (w - l)⁻¹ = -((w - l) * (w - l)⁻¹) by ring, hwν, neg_one_smul]
    rw [hX, map_smul, add_sub_assoc, key, ← sub_eq_add_neg]
    exact h1 φ
  · have e2 : R (X ψ - l • (ψ : H)) = ψ := hR.2 ψ
    have hu : R (X ψ - w • (ψ : H)) = (w - l) • ((w - l)⁻¹ • (ψ : H) - R ψ) := by
      have : X ψ - w • (ψ : H) = (X ψ - l • (ψ : H)) - (w - l) • (ψ : H) := by
        rw [sub_smul]; abel
      rw [this, map_sub, e2, map_smul, smul_sub, smul_smul, hwν, one_smul]
    show R ((w - l)⁻¹ • V (X ψ - w • (ψ : H))) = ψ
    rw [map_smul, hcomm, hu, map_smul, h2, smul_smul, mul_comm, hwν, one_smul]

/-- `ν - R` invertible gives a resolvent at `w`. -/
theorem resolvent_of_unit (X : H →ₗ.[ℂ] H) (l w : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hw : w ≠ l)
    (hu : IsUnit (algebraMap ℂ (H →L[ℂ] H) ((w - l)⁻¹) - R)) :
    ∃ S : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt X w S := by
  obtain ⟨U, hU⟩ := hu
  have hwν : (w - l) * (w - l)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.2 hw)
  refine ⟨_, resolvent_of_inv X l w R (↑U⁻¹ : H →L[ℂ] H) hR hwν (fun x => ?_) (fun x => ?_)⟩
  · have := congrArg (fun T : H →L[ℂ] H => T x) U.mul_inv
    simpa [hU, Algebra.algebraMap_eq_smul_one] using this
  · have := congrArg (fun T : H →L[ℂ] H => T x) U.inv_mul
    simpa [hU, Algebra.algebraMap_eq_smul_one] using this

/-- Spectral mapping for the resolvent: `w ∈ σ(X) ↔ (w - l)⁻¹ ∈ σ(R_X(l))`. -/
theorem spec_iff (X : H →ₗ.[ℂ] H) (l w : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hw : w ≠ l) :
    w ∈ TeschlQM.Shared.spectrum X ↔ (w - l)⁻¹ ∈ spectrum ℂ R := by
  unfold TeschlQM.Shared.spectrum
  rw [Set.mem_compl_iff, spectrum.mem_iff]
  constructor
  · intro hs hu
    exact hs (by exact resolvent_of_unit X l w R hR hw hu)
  · intro hn hres
    obtain ⟨Rw, hRw⟩ := hres
    exact hn (isUnit_of_resolvent X l w (Ne.symm hw) R Rw hR hRw)

theorem mem_eigenspace {X : H →ₗ.[ℂ] H} {μ : ℂ} {φ : H} :
    φ ∈ TeschlQM.OneParticle.eigenspace X μ ↔ ∃ h : φ ∈ X.domain, X ⟨φ, h⟩ = μ • φ := by
  unfold TeschlQM.OneParticle.eigenspace
  constructor
  · rintro ⟨⟨ψ, hψd⟩, hψ, rfl⟩
    refine ⟨hψd, ?_⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hψ
    simpa [sub_eq_zero] using hψ
  · rintro ⟨h, hX⟩
    refine ⟨⟨φ, h⟩, ?_, rfl⟩
    simp [hX]

/-- Eigenvectors of `X` at `μ` are eigenvectors of `R_X(l)` at `(μ - l)⁻¹`. -/
theorem eig_iff (X : H →ₗ.[ℂ] H) (l μ : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hμ : μ ≠ l) (φ : H) :
    φ ∈ TeschlQM.OneParticle.eigenspace X μ ↔ R φ = (μ - l)⁻¹ • φ := by
  have hc : μ - l ≠ 0 := sub_ne_zero.2 hμ
  rw [mem_eigenspace]
  constructor
  · rintro ⟨h, hX⟩
    have e2 : R (X ⟨φ, h⟩ - l • φ) = φ := hR.2 ⟨φ, h⟩
    rw [hX, ← sub_smul, map_smul] at e2
    calc R φ = (μ - l)⁻¹ • ((μ - l) • R φ) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (μ - l)⁻¹ • φ := by rw [e2]
  · intro hRφ
    obtain ⟨hd, he⟩ := hR.1 φ
    have hφ : φ = (μ - l) • R φ := by rw [hRφ, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hdφ : φ ∈ X.domain := by rw [hφ]; exact X.domain.smul_mem _ hd
    refine ⟨hdφ, ?_⟩
    have e : (⟨φ, hdφ⟩ : X.domain) = (μ - l) • (⟨R φ, hd⟩ : X.domain) := Subtype.ext hφ
    have hX : X ⟨R φ, hd⟩ = φ + l • R φ := eq_add_of_sub_eq he
    rw [e, LinearPMap.map_smul, hX, hRφ, smul_add, smul_smul, smul_smul, ← add_smul]
    congr 1
    have hmi : (μ - l) * (μ - l)⁻¹ = 1 := mul_inv_cancel₀ hc
    linear_combination l * hmi

theorem eig_eq (X : H →ₗ.[ℂ] H) (l μ : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hμ : μ ≠ l) :
    TeschlQM.OneParticle.eigenspace X μ = eig R ((μ - l)⁻¹) :=
  Submodule.ext fun φ => (eig_iff X l μ R hR hμ φ).trans mem_eig.symm

theorem not_spec_at (X : H →ₗ.[ℂ] H) (l : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) : l ∉ TeschlQM.Shared.spectrum X := by
  unfold TeschlQM.Shared.spectrum
  rw [Set.mem_compl_iff, not_not]
  exact (⟨R, hR⟩ : ∃ S : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt X l S)

theorem not_ess_at (X : H →ₗ.[ℂ] H) (l : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) :
    l ∉ TeschlQM.OneParticle.essentialSpectrum X := fun h => not_spec_at X l R hR h.1

/-- P8: for `μ ≠ l`, `μ ∈ σ_ess(X)` iff `R_X(l) - (μ - l)⁻¹` is not Fredholm-like. -/
theorem ess_iff (X : H →ₗ.[ℂ] H) (l : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hRs : IsSelfAdjoint R) (μ : ℂ) (hμ : μ ≠ l) :
    μ ∈ TeschlQM.OneParticle.essentialSpectrum X ↔ ¬ FredAt R ((μ - l)⁻¹) := by
  have hc : μ - l ≠ 0 := sub_ne_zero.2 hμ
  have heq := eig_eq X l μ R hR hμ
  unfold TeschlQM.OneParticle.essentialSpectrum TeschlQM.OneParticle.discreteSpectrum
  constructor
  · rintro ⟨hs, hnd⟩ hF
    have hνs := (spec_iff X l μ R hR hμ).1 hs
    obtain ⟨⟨δ, hδ, hiso⟩, hne, hfin⟩ := of_fred R hRs _ hF hνs
    apply hnd
    rw [Set.mem_setOf_eq]
    refine ⟨hs, by rw [heq]; exact hne, ?_, by rw [heq]; exact hfin⟩
    have hcont : ContinuousAt (fun w : ℂ => (w - l)⁻¹) μ :=
      (continuousAt_id.sub continuousAt_const).inv₀ hc
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hcont δ hδ
    refine ⟨η, hη, fun w hw hwμ => ?_⟩
    have hwl : w ≠ l := fun h => not_spec_at X l R hR (h ▸ hw)
    have hws := (spec_iff X l w R hR hwl).1 hw
    have hd : dist ((w - l)⁻¹) ((μ - l)⁻¹) < δ := hηc (by rw [dist_eq_norm]; exact hwμ)
    rw [dist_eq_norm] at hd
    have := hiso _ hws hd
    exact sub_left_inj.1 (inv_inj.1 this)
  · intro hnF
    have hs : μ ∈ TeschlQM.Shared.spectrum X := by
      by_contra hs
      exact hnF (fred_of_not_spec R _ (fun h => hs ((spec_iff X l μ R hR hμ).2 h)))
    refine ⟨hs, ?_⟩
    rintro ⟨-, -, ⟨ε, hε, hiso⟩, hfin⟩
    have hνs := (spec_iff X l μ R hR hμ).1 hs
    have hν0 : (μ - l)⁻¹ ≠ 0 := inv_ne_zero hc
    have hcont : ContinuousAt (fun v : ℂ => l + v⁻¹) ((μ - l)⁻¹) :=
      continuousAt_const.add (continuousAt_id.inv₀ hν0)
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hcont ε hε
    have hpos : 0 < ‖(μ - l)⁻¹‖ := norm_pos_iff.2 hν0
    apply hnF
    refine fred_of_discrete R hRs _ hνs (min η ‖(μ - l)⁻¹‖) (lt_min hη hpos) ?_
      (by rw [← heq]; exact hfin)
    intro v hv hvd
    have hv0 : v ≠ 0 := by
      rintro rfl
      have := lt_of_lt_of_le hvd (min_le_right _ _)
      simp at this
    have hwl : l + v⁻¹ ≠ l := by simpa using inv_ne_zero hv0
    have hvs : l + v⁻¹ ∈ TeschlQM.Shared.spectrum X := by
      rw [spec_iff X l _ R hR hwl, add_sub_cancel_left, inv_inv]; exact hv
    have hd : dist (l + v⁻¹) (l + ((μ - l)⁻¹)⁻¹) < ε :=
      hηc (by rw [dist_eq_norm]; exact lt_of_lt_of_le hvd (min_le_left _ _))
    rw [inv_inv, add_sub_cancel, dist_eq_norm] at hd
    have h1 := hiso _ hvs hd
    have h2 : v⁻¹ = μ - l := by rw [← h1]; ring
    rw [← h2, inv_inv]

/-! ## P11: the resolvent difference is compact -/

theorem diff_compact (A K : H →ₗ.[ℂ] H) (z : ℂ) (R C : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R) (hC : IsCompactOperator C)
    (hKC : ∀ φ : H, ∃ h : R φ ∈ K.domain, K ⟨R φ, h⟩ = C φ) (l : ℂ) (Rl S : H →L[ℂ] H)
    (hRl : TeschlQM.Shared.IsResolventAt A l Rl)
    (hS : TeschlQM.Shared.IsResolventAt (A + K) l S) :
    IsCompactOperator (Rl - S) := by
  have e : Rl - S = S.comp (C.comp (1 + (l - z) • Rl)) := by
    ext φ
    obtain ⟨hk, hK⟩ := KR_eq A K z R C hR hKC l Rl hRl φ
    obtain ⟨hd, he⟩ := hRl.1 φ
    have h2 : S ((A + K) ⟨Rl φ, ⟨hd, hk⟩⟩ - l • Rl φ) = Rl φ := hS.2 ⟨Rl φ, ⟨hd, hk⟩⟩
    have hsum : (A + K) ⟨Rl φ, ⟨hd, hk⟩⟩ = A ⟨Rl φ, hd⟩ + K ⟨Rl φ, hk⟩ :=
      LinearPMap.add_apply A K _
    rw [hsum, hK, add_sub_right_comm, he, map_add] at h2
    show Rl φ - S φ = S ((C.comp (1 + (l - z) • Rl)) φ)
    rw [← h2]; abel
  rw [e]
  exact (hC.comp_clm _).clm_comp S

end RCP

open TeschlQM.OneParticle InnerProductSpace in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hAbdd : IsBoundedBelow A)
    (hK : ∀ x y : K.domain, ⟪K x, (y : H)⟫_ℂ = ⟪(x : H), K y⟫_ℂ)
    (hrc : TeschlQM.Shared.IsRelativelyCompact K A) :
    (A + K).domain = A.domain ∧ IsSelfAdjoint (A + K) ∧ IsBoundedBelow (A + K) ∧
      essentialSpectrum (A + K) = essentialSpectrum A ∧
      ∀ S : Submodule ℂ H, A.HasCore S → (A + K).HasCore S := by
  obtain ⟨γ, hγ⟩ := hAbdd
  obtain ⟨hdom, hsa, -⟩ := RCP.kato_rellich_sa A K hA γ hγ hK hrc
  obtain ⟨hbdd, l0, hl0⟩ := RCP.kato_rellich_bdd A K hA γ hγ hK hrc
  obtain ⟨z, R, hR, C, hC, hKC⟩ := hrc
  refine ⟨hdom, hsa, hbdd, ?_, ?_⟩
  · have hl1 : min l0 (γ - 1) < γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨RA, hRA, -, hRAs⟩ := RCP.resolvent_below A hA γ hγ (min l0 (γ - 1)) hl1
    obtain ⟨RT, hRT⟩ := hl0 (min l0 (γ - 1)) (min_le_left _ _)
    have hRTs := RCP.resolvent_symm (A + K) (RCP.symm_of_selfAdjoint _ hsa) _ RT hRT
    have sa1 : IsSelfAdjoint RA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hRAs
    have sa2 : IsSelfAdjoint RT := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hRTs
    have hcmp := RCP.diff_compact A K z R C hR hC hKC _ RA RT hRA hRT
    ext μ
    by_cases hμ : μ = ((min l0 (γ - 1) : ℝ) : ℂ)
    · rw [hμ]
      exact iff_of_false (RCP.not_ess_at (A + K) _ RT hRT) (RCP.not_ess_at A _ RA hRA)
    · rw [RCP.ess_iff (A + K) _ RT hRT sa2 μ hμ, RCP.ess_iff A _ RA hRA sa1 μ hμ]
      apply not_congr
      constructor
      · intro h
        have := RCP.fred_add_compact RT (RA - RT) hcmp _ h
        rwa [add_sub_cancel] at this
      · intro h
        have := RCP.fred_add_compact RA (-(RA - RT)) hcmp.neg _ h
        rwa [neg_sub, add_sub_cancel] at this
  · intro S hS
    refine RCP.core_transfer A (A + K) hsa.isClosed hdom C z ?_ S hS
    intro x h1 h2
    obtain ⟨hk, hkx⟩ := RCP.K_on_dom A K z R C hR hKC ⟨x, h2⟩
    have hkx' : K ⟨x, hk⟩ = C (A ⟨x, h2⟩ - z • x) := hkx
    have hsum : (A + K) ⟨x, h1⟩ = A ⟨x, h2⟩ + K ⟨x, hk⟩ := LinearPMap.add_apply A K _
    rw [hsum, hkx']
