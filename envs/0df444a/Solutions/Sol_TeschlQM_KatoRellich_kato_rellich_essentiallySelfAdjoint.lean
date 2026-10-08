-- Prove2me | solution 1 for TeschlQM.KatoRellich.kato_rellich_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:08:02.371041+00:00
-- url     : https://prove2.me/submissions/d40e5c2c-450e-47d1-8432-b3bd3ab9d0bc

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_KatoRellich_resolvent
import Definitions.Def_TeschlQM_KatoRellich_compCLM
import Definitions.Def_TeschlQM_KatoRellich_opNorm
import Definitions.Def_TeschlQM_Shared_IsEssentiallySelfAdjoint

open scoped InnerProductSpace ComplexConjugate ENNReal NNReal
open LinearPMap Filter Topology

namespace TeschlQM.KatoRellich.Aux



section Basic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma inner_sym_im {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) (ψ : T.domain) :
    (⟪(ψ : H), T ψ⟫_ℂ).im = 0 := by
  have h := hT.2 ψ ψ
  have h2 : conj ⟪(ψ : H), T ψ⟫_ℂ = ⟪T ψ, (ψ : H)⟫_ℂ := inner_conj_symm _ _
  rw [← h] at h2
  exact Complex.conj_eq_iff_im.mp h2

lemma norm_sub_smul_sq {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) (z : ℂ)
    (ψ : T.domain) :
    ‖T ψ - z • (ψ : H)‖ ^ 2 =
      ‖T ψ‖ ^ 2 - 2 * z.re * (⟪(ψ : H), T ψ⟫_ℂ).re + ‖z‖ ^ 2 * ‖(ψ : H)‖ ^ 2 := by
  have him := inner_sym_im hT ψ
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  have h1 : ⟪T ψ, (ψ : H)⟫_ℂ = conj ⟪(ψ : H), T ψ⟫_ℂ := (inner_conj_symm _ _).symm
  have h2 : RCLike.re (z * ⟪T ψ, (ψ : H)⟫_ℂ) = z.re * (⟪(ψ : H), T ψ⟫_ℂ).re := by
    show (z * ⟪T ψ, (ψ : H)⟫_ℂ).re = _
    rw [Complex.mul_re, h1, Complex.conj_re, Complex.conj_im, him]; ring
  rw [h2, mul_pow]
  ring

/-- The shifted operator `T - z` as a linear map on the domain. -/
noncomputable def shift (T : H →ₗ.[ℂ] H) (z : ℂ) : T.domain →ₗ[ℂ] H :=
  T.toFun - z • T.domain.subtype

lemma shift_apply (T : H →ₗ.[ℂ] H) (z : ℂ) (ψ : T.domain) :
    shift T z ψ = T ψ - z • (ψ : H) := by
  simp [shift]

end Basic

section Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded-below, surjective shift of `T` has a bounded inverse, i.e. `z` is a resolvent
point. -/
lemma exists_resolventAt (T : H →ₗ.[ℂ] H) (z : ℂ) (c : ℝ) (hc : 0 < c)
    (hlb : ∀ ψ : T.domain, c * ‖(ψ : H)‖ ≤ ‖T ψ - z • (ψ : H)‖)
    (hsurj : ∀ φ : H, ∃ ψ : T.domain, T ψ - z • (ψ : H) = φ) :
    ∃ R : H →L[ℂ] H, TeschlQM.KatoRellich.IsResolventAt T z R ∧ ∀ φ, c * ‖R φ‖ ≤ ‖φ‖ := by
  have hinj : Function.Injective (shift T z) := by
    rw [injective_iff_map_eq_zero]
    intro ψ hψ
    have h := hlb ψ
    rw [← shift_apply, hψ, norm_zero] at h
    have h0 : ‖(ψ : H)‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖(ψ : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith [mul_pos hc hpos]
    exact Subtype.ext (norm_eq_zero.mp h0)
  have hbij : Function.Bijective (shift T z) :=
    ⟨hinj, fun φ => by
      obtain ⟨ψ, h⟩ := hsurj φ
      exact ⟨ψ, by rw [shift_apply]; exact h⟩⟩
  let e := LinearEquiv.ofBijective (shift T z) hbij
  let R0 : H →ₗ[ℂ] H := T.domain.subtype ∘ₗ e.symm.toLinearMap
  have hR0 : ∀ φ, ‖R0 φ‖ ≤ 1 / c * ‖φ‖ := by
    intro φ
    have h1 := hlb (e.symm φ)
    have h2 : shift T z (e.symm φ) = φ := e.apply_symm_apply φ
    rw [← shift_apply, h2] at h1
    show ‖((e.symm φ : T.domain) : H)‖ ≤ _
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  refine ⟨LinearMap.mkContinuous R0 (1 / c) hR0, ⟨?_, ?_⟩, ?_⟩
  · intro φ
    refine ⟨(e.symm φ).2, ?_⟩
    have h2 : shift T z (e.symm φ) = φ := e.apply_symm_apply φ
    rw [shift_apply] at h2
    exact h2
  · intro ψ
    have h2 : e.symm (shift T z ψ) = ψ := e.symm_apply_apply ψ
    show ((e.symm (T ψ - z • (ψ : H)) : T.domain) : H) = ψ
    rw [← shift_apply, h2]
  · intro φ
    have := hR0 φ
    show c * ‖R0 φ‖ ≤ ‖φ‖
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hc] at this
    linarith

/-- Self-adjoint operators: a pair `(w, u)` with `⟪u, x⟫ = ⟪w, T x⟫` lies in the graph. -/
lemma graph_of_selfAdjoint {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) (w u : H)
    (h : ∀ x : T.domain, ⟪u, (x : H)⟫_ℂ = ⟪w, T x⟫_ℂ) :
    ∃ y : T.domain, (y : H) = w ∧ T y = u := by
  have hd := hT.dense_domain
  have hw : w ∈ T†.domain := mem_adjoint_domain_of_exists w ⟨u, h⟩
  have hT' : T† = T := hT
  have hu : T† ⟨w, hw⟩ = u := adjoint_apply_eq hd ⟨w, hw⟩ h
  have hmem : (w, u) ∈ T†.graph := (LinearPMap.mem_graph_iff _).2 ⟨⟨w, hw⟩, rfl, hu⟩
  rw [hT'] at hmem
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hmem
  exact ⟨y, hy1, hy2⟩

/-- A self-adjoint operator whose shifts by `z` and `conj z` are bounded below is surjective
after the shift. -/
lemma surj_of_selfAdjoint {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) (z : ℂ) {c : ℝ} (hc : 0 < c)
    (hlb : ∀ ψ : T.domain, c * ‖(ψ : H)‖ ≤ ‖T ψ - z • (ψ : H)‖)
    (hlb' : ∀ ψ : T.domain, c * ‖(ψ : H)‖ ≤ ‖T ψ - (conj z) • (ψ : H)‖) :
    ∀ φ : H, ∃ ψ : T.domain, T ψ - z • (ψ : H) = φ := by
  set K : Submodule ℂ H := LinearMap.range (shift T z) with hK
  have hclosed : IsClosed (K : Set H) := by
    rw [← isSeqClosed_iff_isClosed]
    intro φs φ hφs hlim
    choose ψs hψs using fun n => LinearMap.mem_range.mp (hφs n)
    have hcauchy : CauchySeq (fun n => (ψs n : H)) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq (c * ε) (mul_pos hc hε)
      refine ⟨N, fun n hn => ?_⟩
      have h1 := hN n hn
      have h2 := hlb (ψs n - ψs N)
      rw [← shift_apply, _root_.map_sub, hψs, hψs, ← dist_eq_norm] at h2
      rw [dist_eq_norm]
      have : (↑(ψs n - ψs N) : H) = (ψs n : H) - ψs N := rfl
      rw [this] at h2
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_left hcon hc.le
      linarith
    obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hT1 : Filter.Tendsto (fun n => (ψs n : H)) Filter.atTop (nhds ψ) := hψ
    have hT2 : Filter.Tendsto (fun n => T (ψs n)) Filter.atTop (nhds (φ + z • ψ)) := by
      have : ∀ n, T (ψs n) = φs n + z • (ψs n : H) := by
        intro n
        have := hψs n
        rw [shift_apply] at this
        rw [← this]; abel
      simp_rw [this]
      exact hlim.add (hT1.const_smul z)
    have hgraph : IsClosed (T.graph : Set (H × H)) := hT.isClosed
    have hmem : (ψ, φ + z • ψ) ∈ (T.graph : Set (H × H)) := by
      refine hgraph.mem_of_tendsto (hT1.prodMk_nhds hT2) (Filter.Eventually.of_forall fun n => ?_)
      exact LinearPMap.mem_graph _ _
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hmem
    refine ⟨y, ?_⟩
    rw [shift_apply, hy2, hy1]
    simp
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have h : ∀ x : T.domain, ⟪(conj z) • w, (x : H)⟫_ℂ = ⟪w, T x⟫_ℂ := by
      intro x
      have h0 := hw (shift T z x) (LinearMap.mem_range_self _ _)
      rw [shift_apply, inner_sub_left, inner_smul_left] at h0
      have h1 : ⟪T x, w⟫_ℂ = conj z * ⟪(x : H), w⟫_ℂ := sub_eq_zero.mp h0
      have h2 := congrArg conj h1
      rw [inner_conj_symm, map_mul, inner_conj_symm, Complex.conj_conj] at h2
      rw [inner_smul_left, Complex.conj_conj, h2]
    obtain ⟨y, hy1, hy2⟩ := graph_of_selfAdjoint hT w ((conj z) • w) h
    have h3 := hlb' y
    have h4 : T y - (conj z) • (y : H) = 0 := by rw [hy2, hy1]; simp
    rw [h4, norm_zero] at h3
    have h0 : ‖(y : H)‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖(y : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith [mul_pos hc hpos]
    rw [← hy1]
    exact norm_eq_zero.mp h0
  have : CompleteSpace K := hclosed.completeSpace_coe
  have hK : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  intro φ
  have : φ ∈ K := by rw [hK]; trivial
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp this
  exact ⟨ψ, by rw [← shift_apply]; exact hψ⟩


/-- A symmetric operator whose shifts by `z` and `conj z` are surjective is self-adjoint. -/
lemma isSelfAdjoint_of_surj {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) (z : ℂ)
    (h1 : ∀ φ : H, ∃ ψ : T.domain, T ψ - z • (ψ : H) = φ)
    (h2 : ∀ φ : H, ∃ ψ : T.domain, T ψ - (conj z) • (ψ : H) = φ) : IsSelfAdjoint T := by
  have hd := hT.1
  have hfa : T.IsFormalAdjoint T := fun x y => (hT.2 x y).symm
  have hle : T ≤ T† := hfa.le_adjoint hd
  have hform := adjoint_isFormalAdjoint hd
  have hdom : ∀ y ∈ T†.domain, y ∈ T.domain := by
    intro y hy
    obtain ⟨x, hx⟩ := h1 (T† ⟨y, hy⟩ - z • y)
    have hx' : (x : H) ∈ T†.domain := hle.1 x.2
    have hw : y - (x : H) ∈ T†.domain := Submodule.sub_mem _ hy hx'
    have hTx : T† ⟨(x : H), hx'⟩ = T x := (hle.2 rfl).symm
    have hTw : T† ⟨y - (x : H), hw⟩ = z • (y - (x : H)) := by
      have e1 : (⟨y - (x : H), hw⟩ : T†.domain) = ⟨y, hy⟩ - ⟨(x : H), hx'⟩ := rfl
      rw [e1, LinearPMap.map_sub, hTx, smul_sub]
      have hx2 : T x = T† ⟨y, hy⟩ - z • y + z • (x : H) := by rw [← hx]; abel
      rw [hx2]; abel
    have hperp : ∀ ψ : T.domain, ⟪y - (x : H), T ψ - (conj z) • (ψ : H)⟫_ℂ = 0 := by
      intro ψ
      have h3 := hform ⟨y - (x : H), hw⟩ ψ
      rw [hTw, inner_smul_left] at h3
      rw [inner_sub_right, inner_smul_right]
      linear_combination (-1 : ℂ) * h3
    obtain ⟨ψ, hψ⟩ := h2 (y - (x : H))
    have h4 := hperp ψ
    rw [hψ, inner_self_eq_zero, sub_eq_zero] at h4
    rw [h4]; exact x.2
  exact isSelfAdjoint_def.mpr
    (eq_of_le_of_domain_eq hle (le_antisymm hle.1 (fun y hy => hdom y hy))).symm

/-- A self-adjoint operator is symmetric. -/
lemma isSymmetric_of_selfAdjoint {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) :
    TeschlQM.Shared.IsSymmetric T := by
  have hd := hT.dense_domain
  have hT' : T† = T := hT
  have hle : T ≤ T† := le_of_eq hT'.symm
  have hform := adjoint_isFormalAdjoint hd
  refine ⟨hd, fun φ ψ => ?_⟩
  have hφ : (φ : H) ∈ T†.domain := hle.1 φ.2
  have h1 := hform ⟨(φ : H), hφ⟩ ψ
  have h2 : T† ⟨(φ : H), hφ⟩ = T φ := (hle.2 rfl).symm
  rw [h2] at h1
  exact h1.symm

end Resolvent

section Estimates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma le_of_sq_eq_add {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2 + c ^ 2) :
    b ≤ a := by
  by_contra hlt
  push Not at hlt
  nlinarith [mul_self_lt_mul_self ha hlt, sq_nonneg c]

/-- Estimates for the shift by a purely imaginary number. -/
lemma norm_le_imag {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) (s : ℝ)
    (ψ : T.domain) :
    ‖T ψ‖ ≤ ‖T ψ - ((s : ℂ) * Complex.I) • (ψ : H)‖ ∧
      |s| * ‖(ψ : H)‖ ≤ ‖T ψ - ((s : ℂ) * Complex.I) • (ψ : H)‖ := by
  have h := norm_sub_smul_sq hT ((s : ℂ) * Complex.I) ψ
  have hre : ((s : ℂ) * Complex.I).re = 0 := by simp
  have hn : ‖(s : ℂ) * Complex.I‖ = |s| := by simp
  rw [hre, hn] at h
  have h' : ‖T ψ - ((s : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 =
      ‖T ψ‖ ^ 2 + (|s| * ‖(ψ : H)‖) ^ 2 := by rw [h]; ring
  have h'' : ‖T ψ - ((s : ℂ) * Complex.I) • (ψ : H)‖ ^ 2 =
      (|s| * ‖(ψ : H)‖) ^ 2 + ‖T ψ‖ ^ 2 := by rw [h']; ring
  exact ⟨le_of_sq_eq_add (norm_nonneg _) (norm_nonneg _) h',
    le_of_sq_eq_add (norm_nonneg _) (by positivity) h''⟩

/-- Estimates for the shift by a negative real number, for `T` bounded below by `γ`. -/
lemma norm_le_real {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) {γ : ℝ}
    (hγ : TeschlQM.Shared.IsBoundedBelowBy T γ) (t : ℝ) (ht0 : 0 ≤ t) (ht : -2 * γ ≤ t)
    (htγ : 0 < t + γ) (ψ : T.domain) :
    ‖T ψ‖ ≤ ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ ∧
      (t + γ) * ‖(ψ : H)‖ ≤ ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ := by
  have hq := hγ ψ
  have h := norm_sub_smul_sq hT (-(t : ℂ)) ψ
  have hre : (-(t : ℂ)).re = -t := by simp
  have hn : ‖-(t : ℂ)‖ = |t| := by simp
  rw [hre, hn, abs_of_nonneg ht0] at h
  have hv : ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ ^ 2 =
      ‖T ψ‖ ^ 2 + 2 * t * (⟪(ψ : H), T ψ⟫_ℂ).re + t ^ 2 * ‖(ψ : H)‖ ^ 2 := by
    rw [h]; ring
  constructor
  · by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (norm_nonneg _) hlt
    nlinarith [mul_nonneg ht0 (show 0 ≤ t + 2 * γ by linarith) , sq_nonneg ‖(ψ : H)‖,
      mul_nonneg (mul_nonneg ht0 (show 0 ≤ t + 2 * γ by linarith)) (sq_nonneg ‖(ψ : H)‖)]
  · by_cases hψ : ‖(ψ : H)‖ = 0
    · rw [hψ]; simp
    · have hpos : 0 < ‖(ψ : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hψ)
      -- Cauchy-Schwarz for `⟪ψ, (T + t) ψ⟫`
      have hcs : (⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ).re ≤
          ‖(ψ : H)‖ * ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ := by
        calc (⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ).re
            ≤ ‖⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ‖ := Complex.re_le_norm _
          _ ≤ ‖(ψ : H)‖ * ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ := norm_inner_le_norm _ _
      have hre2 : (⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ).re =
          (⟪(ψ : H), T ψ⟫_ℂ).re + t * ‖(ψ : H)‖ ^ 2 := by
        have hii : ⟪(ψ : H), (ψ : H)⟫_ℂ = ((‖(ψ : H)‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
        have hcast : (-(t : ℂ)) * ((‖(ψ : H)‖ : ℝ) : ℂ) ^ 2 = ((-t * ‖(ψ : H)‖ ^ 2 : ℝ) : ℂ) := by
          push_cast; ring
        rw [inner_sub_right, inner_smul_right, hii, hcast, Complex.sub_re, Complex.ofReal_re]
        ring
      rw [hre2] at hcs
      by_contra hlt
      push Not at hlt
      nlinarith [mul_pos hpos (sub_pos.mpr hlt)]

end Estimates


section Resolvents

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sa_resolventAt_imag {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) {s : ℝ} (hs : s ≠ 0) :
    ∃ R, IsResolventAt T ((s : ℂ) * Complex.I) R := by
  have hsym := isSymmetric_of_selfAdjoint hT
  have hc : 0 < |s| := abs_pos.mpr hs
  have hconj : conj ((s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hsurj := surj_of_selfAdjoint hT ((s : ℂ) * Complex.I) hc
    (fun ψ => (norm_le_imag hsym s ψ).2)
    (fun ψ => by
      rw [hconj]
      have := (norm_le_imag hsym (-s) ψ).2
      rwa [abs_neg] at this)
  obtain ⟨R, hR, -⟩ := exists_resolventAt T ((s : ℂ) * Complex.I) |s| hc
    (fun ψ => (norm_le_imag hsym s ψ).2) hsurj
  exact ⟨R, hR⟩

lemma sa_resolventAt_real {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) {γ : ℝ}
    (hγ : TeschlQM.Shared.IsBoundedBelowBy T γ) {t : ℝ} (ht0 : 0 ≤ t) (ht : -2 * γ ≤ t)
    (htγ : 0 < t + γ) : ∃ R, IsResolventAt T (-(t : ℂ)) R := by
  have hsym := isSymmetric_of_selfAdjoint hT
  have hconj : conj (-(t : ℂ)) = -(t : ℂ) := by simp [Complex.conj_ofReal]
  have hsurj := surj_of_selfAdjoint hT (-(t : ℂ)) htγ
    (fun ψ => (norm_le_real hsym hγ t ht0 ht htγ ψ).2)
    (fun ψ => by
      rw [hconj]
      exact (norm_le_real hsym hγ t ht0 ht htγ ψ).2)
  obtain ⟨R, hR, -⟩ := exists_resolventAt T (-(t : ℂ)) (t + γ) htγ
    (fun ψ => (norm_le_real hsym hγ t ht0 ht htγ ψ).2) hsurj
  exact ⟨R, hR⟩

end Resolvents

section OpNorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma opNorm_le_of_bound (T : H →ₗ.[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : T.domain, ‖T φ‖ ≤ C * ‖(φ : H)‖) : opNorm T ≤ ENNReal.ofReal C := by
  unfold opNorm
  refine iSup_le fun φ => ENNReal.div_le_of_le_mul ?_
  have h1 : (‖T φ‖₊ : ℝ≥0) ≤ C.toNNReal * ‖(φ : H)‖₊ := by
    rw [← NNReal.coe_le_coe]
    simpa [Real.coe_toNNReal C hC] using h φ
  calc (‖T φ‖₊ : ℝ≥0∞) ≤ ((C.toNNReal * ‖(φ : H)‖₊ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast h1
    _ = ENNReal.ofReal C * (‖(φ : H)‖₊ : ℝ≥0∞) := by
      rw [ENNReal.coe_mul]; rfl

lemma norm_le_of_opNorm_ne_top (T : H →ₗ.[ℂ] H) (hT : opNorm T ≠ ⊤) (φ : T.domain) :
    ‖T φ‖ ≤ (opNorm T).toReal * ‖(φ : H)‖ := by
  have h1 : (‖T φ‖₊ : ℝ≥0∞) / (‖(φ : H)‖₊ : ℝ≥0∞) ≤ opNorm T :=
    le_iSup (fun φ : T.domain => (‖T φ‖₊ : ℝ≥0∞) / (‖(φ : H)‖₊ : ℝ≥0∞)) φ
  by_cases hφ : ‖(φ : H)‖₊ = 0
  · have : φ = 0 := Subtype.ext (by simpa using hφ)
    subst this
    simp
  · have hne : (‖(φ : H)‖₊ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hφ
    rw [ENNReal.div_le_iff hne ENNReal.coe_ne_top] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hT ENNReal.coe_ne_top) h1
    rw [ENNReal.toReal_mul] at h2
    simpa using h2

end OpNorm

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma isResolventAt_resolvent {A : H →ₗ.[ℂ] H} {z : ℂ} (h : ∃ R : H →L[ℂ] H, IsResolventAt A z R) :
    IsResolventAt A z (resolvent A z) := by
  unfold resolvent
  rw [dif_pos h]
  exact h.choose_spec

/-- The two estimates relating `‖B R_A(z)‖` and the `A`-bound. -/
lemma resolvent_estimates {A B : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H} (hR : IsResolventAt A z R)
    {c : ℝ} (hc : 0 < c)
    (h1 : ∀ ψ : A.domain, ‖A ψ‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (h2 : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (hAB : A.domain ≤ B.domain) :
    (∀ a b : ℝ, IsRelativelyBoundedWith A B a b →
        opNorm (compCLM B R) ≤ ENNReal.ofReal (a + b / c)) ∧
      relativeBound A B ≤ opNorm (compCLM B R) := by
  constructor
  · intro a b hab
    obtain ⟨-, ha, hb, hbound⟩ := hab
    refine opNorm_le_of_bound _ (by positivity) ?_
    intro φ
    have hφ : R (φ : H) ∈ B.domain := φ.2
    obtain ⟨hRA, hRφ⟩ := hR.1 (φ : H)
    have hb' := hbound (R (φ : H)) hRA hφ
    have e1 : ‖A ⟨R (φ : H), hRA⟩‖ ≤ ‖(φ : H)‖ := by
      have := h1 ⟨R (φ : H), hRA⟩
      rwa [hRφ] at this
    have e2 : c * ‖R (φ : H)‖ ≤ ‖(φ : H)‖ := by
      have := h2 ⟨R (φ : H), hRA⟩
      rwa [show A ⟨R (φ : H), hRA⟩ - z • R (φ : H) = (φ : H) from hRφ] at this
    have e3 : ‖R (φ : H)‖ ≤ ‖(φ : H)‖ / c := by rw [le_div_iff₀ hc]; linarith
    show ‖B ⟨R (φ : H), hφ⟩‖ ≤ (a + b / c) * ‖(φ : H)‖
    calc ‖B ⟨R (φ : H), hφ⟩‖ ≤ a * ‖A ⟨R (φ : H), hRA⟩‖ + b * ‖R (φ : H)‖ := hb'
      _ ≤ a * ‖(φ : H)‖ + b * (‖(φ : H)‖ / c) := by gcongr
      _ = (a + b / c) * ‖(φ : H)‖ := by ring
  · by_cases htop : opNorm (compCLM B R) = ⊤
    · rw [htop]; exact le_top
    · set κ : ℝ := (opNorm (compCLM B R)).toReal with hκ
      have hκ0 : 0 ≤ κ := ENNReal.toReal_nonneg
      have hrel : IsRelativelyBoundedWith A B κ (‖z‖ * κ) := by
        refine ⟨hAB, hκ0, by positivity, ?_⟩
        intro ψ hA hB
        have hmem : (A ⟨ψ, hA⟩ - z • ψ) ∈ (compCLM B R).domain := by
          show R (A ⟨ψ, hA⟩ - z • ψ) ∈ B.domain
          rw [hR.2 ⟨ψ, hA⟩]; exact hB
        have h3 := norm_le_of_opNorm_ne_top (compCLM B R) htop ⟨_, hmem⟩
        have h4 : (compCLM B R) ⟨_, hmem⟩ = B ⟨ψ, hB⟩ := by
          show B ⟨R (A ⟨ψ, hA⟩ - z • ψ), _⟩ = B ⟨ψ, hB⟩
          congr 1
          exact Subtype.ext (hR.2 ⟨ψ, hA⟩)
        rw [h4] at h3
        calc ‖B ⟨ψ, hB⟩‖ ≤ κ * ‖A ⟨ψ, hA⟩ - z • ψ‖ := h3
          _ ≤ κ * (‖A ⟨ψ, hA⟩‖ + ‖z‖ * ‖ψ‖) := by
            gcongr
            calc ‖A ⟨ψ, hA⟩ - z • ψ‖ ≤ ‖A ⟨ψ, hA⟩‖ + ‖z • ψ‖ := norm_sub_le _ _
              _ = _ := by rw [norm_smul]
          _ = κ * ‖A ⟨ψ, hA⟩‖ + ‖z‖ * κ * ‖ψ‖ := by ring
      calc relativeBound A B ≤ ENNReal.ofReal κ :=
            iInf₂_le κ ⟨‖z‖ * κ, hrel⟩
        _ = opNorm (compCLM B R) := ENNReal.ofReal_toReal htop

end General


section Limit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma tendsto_of_family {A B : H →ₗ.[ℂ] H} (hB : IsRelativelyBounded A B) (z : ℝ → ℂ)
    (c : ℝ → ℝ) (hc : Tendsto c atTop atTop)
    (hev : ∀ᶠ t in atTop, 0 < c t ∧ (∃ R : H →L[ℂ] H, IsResolventAt A (z t) R) ∧
      (∀ ψ : A.domain, ‖A ψ‖ ≤ ‖A ψ - z t • (ψ : H)‖) ∧
      (∀ ψ : A.domain, c t * ‖(ψ : H)‖ ≤ ‖A ψ - z t • (ψ : H)‖)) :
    Tendsto (fun t => opNorm (compCLM B (resolvent A (z t)))) atTop
      (𝓝 (relativeBound A B)) := by
  have hAB : A.domain ≤ B.domain := by obtain ⟨a, b, h⟩ := hB; exact h.1
  have hest : ∀ᶠ t in atTop, (∀ a b : ℝ, IsRelativelyBoundedWith A B a b →
      opNorm (compCLM B (resolvent A (z t))) ≤ ENNReal.ofReal (a + b / c t)) ∧
      relativeBound A B ≤ opNorm (compCLM B (resolvent A (z t))) := by
    filter_upwards [hev] with t ⟨hct, hex, h1, h2⟩
    exact resolvent_estimates (isResolventAt_resolvent hex) hct h1 h2 hAB
  rw [tendsto_order]
  constructor
  · intro u hu
    filter_upwards [hest] with t ht
    exact lt_of_lt_of_le hu ht.2
  · intro u hu
    have hu' : relativeBound A B < u := hu
    unfold relativeBound at hu'
    rw [iInf_lt_iff] at hu'
    obtain ⟨a, hu'⟩ := hu'
    rw [iInf_lt_iff] at hu'
    obtain ⟨⟨b, hab⟩, hau⟩ := hu'
    obtain ⟨r, hr0, har, hru⟩ := ENNReal.lt_iff_exists_real_btwn.mp hau
    have har' : a < r ∧ 0 < r := (ENNReal.ofReal_lt_ofReal_iff').mp har
    have hlim : Tendsto (fun t => a + b / c t) atTop (𝓝 (a + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hc)
    have hlt : ∀ᶠ t in atTop, a + b / c t < r :=
      hlim.eventually_lt_const (by linarith [har'.1])
    filter_upwards [hest, hlt] with t ht hlt'
    calc opNorm (compCLM B (resolvent A (z t))) ≤ ENNReal.ofReal (a + b / c t) :=
          ht.1 a b hab
      _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff har'.2).mpr hlt'
      _ < u := hru

end Limit



section Closure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A symmetric operator is closable. -/
lemma isClosable_of_symmetric {B : H →ₗ.[ℂ] H} (hB : TeschlQM.Shared.IsSymmetric B) :
    B.IsClosable := by
  have hd := hB.1
  have hfa : B.IsFormalAdjoint B := fun x y => (hB.2 x y).symm
  exact (adjoint_isClosed hd).isClosable.leIsClosable (hfa.le_adjoint hd)

/-- Every point of the graph of the closure is a limit of points of the graph. -/
lemma exists_approx {T : H →ₗ.[ℂ] H} (hT : T.IsClosable) (ψ : T.closure.domain) :
    ∃ x : ℕ → T.domain, Tendsto (fun n => (x n : H)) atTop (𝓝 (ψ : H)) ∧
      Tendsto (fun n => T (x n)) atTop (𝓝 (T.closure ψ)) := by
  have hmem : ((ψ : H), T.closure ψ) ∈ closure (T.graph : Set (H × H)) := by
    have := T.closure.mem_graph ψ
    rw [← hT.graph_closure_eq_closure_graph] at this
    exact this
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hp' : ∀ n, ∃ y : T.domain, ((y : H), T y) = p n :=
    fun n => (LinearPMap.mem_graph_iff' _).mp (hp n)
  choose x hx using hp'
  refine ⟨x, ?_, ?_⟩
  · have := hlim.fst_nhds
    refine this.congr (fun n => ?_)
    rw [← hx n]
  · have := hlim.snd_nhds
    refine this.congr (fun n => ?_)
    rw [← hx n]

/-- A graph limit of points of `T` lies in the graph of the closure. -/
lemma mem_closure_domain_of_tendsto {T : H →ₗ.[ℂ] H} (hT : T.IsClosable) (x : ℕ → T.domain)
    {ψ y : H} (h1 : Tendsto (fun n => (x n : H)) atTop (𝓝 ψ))
    (h2 : Tendsto (fun n => T (x n)) atTop (𝓝 y)) :
    ∃ h : ψ ∈ T.closure.domain, T.closure ⟨ψ, h⟩ = y := by
  have hmem : (ψ, y) ∈ closure (T.graph : Set (H × H)) :=
    mem_closure_of_tendsto (h1.prodMk_nhds h2)
      (Eventually.of_forall fun n => T.mem_graph (x n))
  have : (ψ, y) ∈ T.closure.graph := by
    rw [← hT.graph_closure_eq_closure_graph]; exact hmem
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).mp this
  subst hz1
  exact ⟨z.2, hz2⟩

lemma cauchy_of_dominated {u v w : ℕ → H} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : CauchySeq u) (hv : CauchySeq v)
    (h : ∀ n m, ‖w n - w m‖ ≤ a * ‖u n - u m‖ + b * ‖v n - v m‖) : CauchySeq w := by
  rw [Metric.cauchySeq_iff] at hu hv ⊢
  intro ε hε
  have hδ : 0 < ε / (2 * (a + b + 1)) := by positivity
  obtain ⟨N1, h1⟩ := hu _ hδ
  obtain ⟨N2, h2⟩ := hv _ hδ
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have e1 := h1 m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
  have e2 := h2 m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm] at e1 e2 ⊢
  have e3 := h m n
  have e4 : a * ‖u m - u n‖ ≤ a * (ε / (2 * (a + b + 1))) := mul_le_mul_of_nonneg_left e1.le ha
  have e5 : b * ‖v m - v n‖ ≤ b * (ε / (2 * (a + b + 1))) := mul_le_mul_of_nonneg_left e2.le hb
  have e6 : (a + b) * (ε / (2 * (a + b + 1))) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

end Closure

section ApproxPair

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If `B` is `A` bounded then every point of `𝔇(Ā)` is a simultaneous graph limit for `A` and
`B`, and lies in `𝔇(B̄)`. -/
lemma approx_pair {A B : H →ₗ.[ℂ] H} (hA : A.IsClosable) (hB : B.IsClosable) {a b : ℝ}
    (hrel : IsRelativelyBoundedWith A B a b) (ψ : A.closure.domain) :
    ∃ h : (ψ : H) ∈ B.closure.domain, ∃ x : ℕ → A.domain,
      Tendsto (fun n => (x n : H)) atTop (𝓝 (ψ : H)) ∧
      Tendsto (fun n => A (x n)) atTop (𝓝 (A.closure ψ)) ∧
      Tendsto (fun n => B ⟨(x n : H), hrel.1 (x n).2⟩) atTop (𝓝 (B.closure ⟨ψ, h⟩)) := by
  obtain ⟨x, hx1, hx2⟩ := exists_approx hA ψ
  have hcauchy : CauchySeq (fun n => B ⟨(x n : H), hrel.1 (x n).2⟩) := by
    refine cauchy_of_dominated (u := fun n => A (x n)) (v := fun n => (x n : H)) hrel.2.1
      hrel.2.2.1 hx2.cauchySeq hx1.cauchySeq (fun n m => ?_)
    have hsub : B ⟨(x n : H), hrel.1 (x n).2⟩ - B ⟨(x m : H), hrel.1 (x m).2⟩ =
        B ⟨((x n - x m : A.domain) : H), hrel.1 (x n - x m).2⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    have hsubA : A (x n) - A (x m) = A (x n - x m) := (LinearPMap.map_sub A _ _).symm
    show ‖B ⟨(x n : H), hrel.1 (x n).2⟩ - B ⟨(x m : H), hrel.1 (x m).2⟩‖ ≤
      a * ‖A (x n) - A (x m)‖ + b * ‖(x n : H) - (x m : H)‖
    rw [hsub, hsubA]
    exact hrel.2.2.2 ((x n - x m : A.domain) : H) (x n - x m).2 (hrel.1 (x n - x m).2)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  obtain ⟨h, hval⟩ := mem_closure_domain_of_tendsto hB (fun n => ⟨(x n : H), hrel.1 (x n).2⟩)
    hx1 hy
  refine ⟨h, x, hx1, hx2, ?_⟩
  rw [hval]; exact hy

/-- `B̄` is `Ā` bounded with the same constants. -/
lemma closure_relBounded {A B : H →ₗ.[ℂ] H} (hA : A.IsClosable) (hB : B.IsClosable) {a b : ℝ}
    (hrel : IsRelativelyBoundedWith A B a b) :
    IsRelativelyBoundedWith A.closure B.closure a b := by
  refine ⟨fun ψ hψ => (approx_pair hA hB hrel ⟨ψ, hψ⟩).1, hrel.2.1, hrel.2.2.1, ?_⟩
  intro ψ hψA hψB
  obtain ⟨h, x, h1, h2, h3⟩ := approx_pair hA hB hrel ⟨ψ, hψA⟩
  have hle : ∀ n, ‖B ⟨(x n : H), hrel.1 (x n).2⟩‖ ≤ a * ‖A (x n)‖ + b * ‖(x n : H)‖ :=
    fun n => hrel.2.2.2 (x n : H) (x n).2 (hrel.1 (x n).2)
  have := le_of_tendsto_of_tendsto' h3.norm
    ((h2.norm.const_mul a).add (h1.norm.const_mul b)) hle
  exact this

/-- If `B` is symmetric then `B̄` is symmetric on `𝔇(Ā)`. -/
lemma closure_symm {A B : H →ₗ.[ℂ] H} (hA : A.IsClosable) (hB : B.IsClosable) {a b : ℝ}
    (hrel : IsRelativelyBoundedWith A B a b)
    (hsym : ∀ φ ψ : B.domain, ⟪(φ : H), B ψ⟫_ℂ = ⟪B φ, (ψ : H)⟫_ℂ)
    (φ ψ : A.closure.domain) (hφ : (φ : H) ∈ B.closure.domain) (hψ : (ψ : H) ∈ B.closure.domain) :
    ⟪(φ : H), B.closure ⟨ψ, hψ⟩⟫_ℂ = ⟪B.closure ⟨φ, hφ⟩, (ψ : H)⟫_ℂ := by
  obtain ⟨h, x, h1, h2, h3⟩ := approx_pair hA hB hrel φ
  obtain ⟨h', y, k1, k2, k3⟩ := approx_pair hA hB hrel ψ
  have e1 : Tendsto (fun n => ⟪(x n : H), B ⟨(y n : H), hrel.1 (y n).2⟩⟫_ℂ) atTop
      (𝓝 ⟪(φ : H), B.closure ⟨ψ, h'⟩⟫_ℂ) := h1.inner k3
  have e2 : Tendsto (fun n => ⟪B ⟨(x n : H), hrel.1 (x n).2⟩, (y n : H)⟫_ℂ) atTop
      (𝓝 ⟪B.closure ⟨φ, h⟩, (ψ : H)⟫_ℂ) := h3.inner k1
  have e3 : ∀ n, ⟪(x n : H), B ⟨(y n : H), hrel.1 (y n).2⟩⟫_ℂ =
      ⟪B ⟨(x n : H), hrel.1 (x n).2⟩, (y n : H)⟫_ℂ :=
    fun n => hsym ⟨(x n : H), hrel.1 (x n).2⟩ ⟨(y n : H), hrel.1 (y n).2⟩
  simp_rw [e3] at e1
  exact tendsto_nhds_unique e1 e2

end ApproxPair


section Sum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma closed_mem {A : H →ₗ.[ℂ] H} (hA : A.IsClosed) (x : ℕ → A.domain) {ψ u : H}
    (h1 : Tendsto (fun n => (x n : H)) atTop (𝓝 ψ))
    (h2 : Tendsto (fun n => A (x n)) atTop (𝓝 u)) :
    ∃ h : ψ ∈ A.domain, A ⟨ψ, h⟩ = u := by
  have hmem : (ψ, u) ∈ (A.graph : Set (H × H)) :=
    hA.mem_of_tendsto (h1.prodMk_nhds h2) (Eventually.of_forall fun n => A.mem_graph (x n))
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).mp hmem
  subst hz1
  exact ⟨z.2, hz2⟩

lemma mem_sum_domain {A B : H →ₗ.[ℂ] H} (hAB : A.domain ≤ B.domain) {ψ : H}
    (h : ψ ∈ A.domain) : ψ ∈ (A + B).domain :=
  Submodule.mem_inf.mpr ⟨h, hAB h⟩

lemma sum_domain_eq {A B : H →ₗ.[ℂ] H} (hAB : A.domain ≤ B.domain) :
    (A + B).domain = A.domain := inf_eq_left.mpr hAB

lemma sum_apply' {A B : H →ₗ.[ℂ] H} (ψ : (A + B).domain) :
    (A + B) ψ = A ⟨ψ, ψ.2.1⟩ + B ⟨ψ, ψ.2.2⟩ := rfl

/-- Graph-norm equivalence: `(1 - a) ‖A w‖ ≤ ‖(A + B) w‖ + b ‖w‖`. -/
lemma norm_A_le_sum {A B : H →ₗ.[ℂ] H} {a b : ℝ} (hrel : IsRelativelyBoundedWith A B a b)
    (w : A.domain) :
    (1 - a) * ‖A w‖ ≤ ‖(A + B) ⟨(w : H), mem_sum_domain hrel.1 w.2⟩‖ + b * ‖(w : H)‖ := by
  have h1 := hrel.2.2.2 (w : H) w.2 (hrel.1 w.2)
  have h2 : (A + B) ⟨(w : H), mem_sum_domain hrel.1 w.2⟩ = A w + B ⟨(w : H), hrel.1 w.2⟩ := rfl
  have h3 : ‖A w‖ ≤ ‖A w + B ⟨(w : H), hrel.1 w.2⟩‖ + ‖B ⟨(w : H), hrel.1 w.2⟩‖ := by
    have := norm_sub_le (A w + B ⟨(w : H), hrel.1 w.2⟩) (B ⟨(w : H), hrel.1 w.2⟩)
    simpa using this
  rw [h2]
  linarith

/-- If `A` is closed and `B` is `A`-bounded with `A`-bound `< 1`, then `A + B` is closed. -/
lemma sum_isClosed {A B : H →ₗ.[ℂ] H} (hA : A.IsClosed) {a b : ℝ}
    (hrel : IsRelativelyBoundedWith A B a b) (ha1 : a < 1) : (A + B).IsClosed := by
  unfold LinearPMap.IsClosed
  rw [← isSeqClosed_iff_isClosed]
  intro p q hp hlim
  have hp' : ∀ n, ∃ y : (A + B).domain, ((y : H), (A + B) y) = p n :=
    fun n => (LinearPMap.mem_graph_iff' _).mp (hp n)
  choose x hx using hp'
  have hx1 : Tendsto (fun n => (x n : H)) atTop (𝓝 q.1) :=
    hlim.fst_nhds.congr (fun n => by rw [← hx n])
  have hx2 : Tendsto (fun n => (A + B) (x n)) atTop (𝓝 q.2) :=
    hlim.snd_nhds.congr (fun n => by rw [← hx n])
  set xa : ℕ → A.domain := fun n => ⟨(x n : H), (x n).2.1⟩ with hxa
  have h1a : 0 < 1 - a := by linarith
  -- the sequence `A (xa n)` is Cauchy
  have hcauchy : CauchySeq (fun n => A (xa n)) := by
    refine cauchy_of_dominated (u := fun n => (A + B) (x n)) (v := fun n => (x n : H))
      (a := 1 / (1 - a)) (b := b / (1 - a)) (by positivity) (div_nonneg hrel.2.2.1 h1a.le)
      hx2.cauchySeq hx1.cauchySeq (fun n m => ?_)
    have hsub : A (xa n) - A (xa m) = A (xa n - xa m) := (LinearPMap.map_sub A _ _).symm
    have hsub2 : (A + B) (x n) - (A + B) (x m) =
        (A + B) ⟨((xa n - xa m : A.domain) : H), mem_sum_domain hrel.1 (xa n - xa m).2⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [hsub, hsub2]
    have := norm_A_le_sum hrel (xa n - xa m)
    have e : ‖A (xa n - xa m)‖ ≤ (‖(A + B) ⟨((xa n - xa m : A.domain) : H),
        mem_sum_domain hrel.1 (xa n - xa m).2⟩‖ + b * ‖((xa n - xa m : A.domain) : H)‖) /
          (1 - a) := by
      rw [le_div_iff₀ h1a]; linarith
    show ‖A (xa n - xa m)‖ ≤ 1 / (1 - a) * ‖(A + B) ⟨((xa n - xa m : A.domain) : H),
        mem_sum_domain hrel.1 (xa n - xa m).2⟩‖ + b / (1 - a) * ‖((xa n - xa m : A.domain) : H)‖
    calc ‖A (xa n - xa m)‖ ≤ _ := e
      _ = _ := by ring
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  obtain ⟨hmem, hval⟩ := closed_mem hA xa hx1 hu
  -- `B (xa n) → B ψ`
  have hB : Tendsto (fun n => B ⟨(x n : H), hrel.1 (xa n).2⟩) atTop (𝓝 (B ⟨q.1, hrel.1 hmem⟩)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hA' : Tendsto (fun n => ‖A (xa n) - A ⟨q.1, hmem⟩‖) atTop (𝓝 0) := by
      rw [← tendsto_iff_norm_sub_tendsto_zero]
      rw [hval]; exact hu
    have hx' : Tendsto (fun n => ‖(x n : H) - q.1‖) atTop (𝓝 0) := by
      rw [← tendsto_iff_norm_sub_tendsto_zero]; exact hx1
    have hup : Tendsto (fun n => a * ‖A (xa n) - A ⟨q.1, hmem⟩‖ + b * ‖(x n : H) - q.1‖) atTop
        (𝓝 (a * 0 + b * 0)) := (hA'.const_mul a).add (hx'.const_mul b)
    rw [mul_zero, mul_zero, add_zero] at hup
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hup
    have hsub : B ⟨(x n : H), hrel.1 (xa n).2⟩ - B ⟨q.1, hrel.1 hmem⟩ =
        B ⟨((xa n : H) - q.1 : H), Submodule.sub_mem _ (hrel.1 (xa n).2) (hrel.1 hmem)⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    have hsubA : A (xa n) - A ⟨q.1, hmem⟩ =
        A ⟨((xa n : H) - q.1 : H), Submodule.sub_mem _ (xa n).2 hmem⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [hsub, hsubA]
    exact hrel.2.2.2 _ _ _
  have hS : Tendsto (fun n => (A + B) (x n)) atTop (𝓝 (A ⟨q.1, hmem⟩ + B ⟨q.1, hrel.1 hmem⟩)) := by
    have : Tendsto (fun n => A (xa n) + B ⟨(x n : H), hrel.1 (xa n).2⟩) atTop
        (𝓝 (A ⟨q.1, hmem⟩ + B ⟨q.1, hrel.1 hmem⟩)) := by
      have hu' : Tendsto (fun n => A (xa n)) atTop (𝓝 (A ⟨q.1, hmem⟩)) := by
        rw [hval]; exact hu
      exact hu'.add hB
    exact this
  have hq2 : q.2 = A ⟨q.1, hmem⟩ + B ⟨q.1, hrel.1 hmem⟩ := tendsto_nhds_unique hx2 hS
  refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨q.1, mem_sum_domain hrel.1 hmem⟩, rfl, ?_⟩
  rw [hq2]; rfl

end Sum


section Neumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The elementary bound `‖B R φ‖ ≤ (a + b/c) ‖φ‖`. -/
lemma bound_BR {A B : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H} (hR : IsResolventAt A z R) {c : ℝ}
    (hc : 0 < c) (h1 : ∀ ψ : A.domain, ‖A ψ‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (h2 : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖) {a b : ℝ}
    (hrel : IsRelativelyBoundedWith A B a b) (φ : H) :
    ‖B ⟨R φ, hrel.1 (hR.1 φ).fst⟩‖ ≤ (a + b / c) * ‖φ‖ := by
  have ha := hrel.2.1
  have hb := hrel.2.2.1
  obtain ⟨hRA, hRφ⟩ := hR.1 φ
  have hb' := hrel.2.2.2 (R φ) hRA (hrel.1 hRA)
  have e1 : ‖A ⟨R φ, hRA⟩‖ ≤ ‖φ‖ := by
    have := h1 ⟨R φ, hRA⟩
    rwa [hRφ] at this
  have e2 : c * ‖R φ‖ ≤ ‖φ‖ := by
    have := h2 ⟨R φ, hRA⟩
    rwa [show A ⟨R φ, hRA⟩ - z • R φ = φ from hRφ] at this
  have e3 : ‖R φ‖ ≤ ‖φ‖ / c := by rw [le_div_iff₀ hc]; linarith
  calc ‖B ⟨R φ, hrel.1 hRA⟩‖ ≤ a * ‖A ⟨R φ, hRA⟩‖ + b * ‖R φ‖ := hb'
    _ ≤ a * ‖φ‖ + b * (‖φ‖ / c) := by gcongr
    _ = (a + b / c) * ‖φ‖ := by ring

/-- Neumann series: `(A + B) - z` is surjective if `‖B R_A(z)‖ ≤ κ < 1`. -/
lemma surj_neumann {A B : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H} (hR : IsResolventAt A z R)
    (hAB : A.domain ≤ B.domain) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hbd : ∀ φ : H, ‖B ⟨R φ, hAB (hR.1 φ).fst⟩‖ ≤ κ * ‖φ‖) :
    ∀ φ : H, ∃ ψ : (A + B).domain, (A + B) ψ - z • (ψ : H) = φ := by
  let f : H →ₗ[ℂ] H := B.toFun ∘ₗ
    (LinearMap.codRestrict B.domain (R : H →ₗ[ℂ] H) (fun φ => hAB (hR.1 φ).fst))
  let Q : H →L[ℂ] H := f.mkContinuous κ (fun φ => hbd φ)
  have hQ : ‖Q‖ ≤ κ := LinearMap.mkContinuous_norm_le _ hκ0 _
  have hu : IsUnit (1 - (-Q)) :=
    isUnit_one_sub_of_norm_lt_one (by rw [norm_neg]; exact lt_of_le_of_lt hQ hκ)
  obtain ⟨N, hN⟩ := hu.exists_right_inv
  intro φ
  have h3 : (1 - -Q) (N φ) = φ := by
    have := congrArg (fun T : H →L[ℂ] H => T φ) hN
    simpa using this
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.one_apply, sub_neg_eq_add] at h3
  obtain ⟨hmem, hres⟩ := hR.1 (N φ)
  refine ⟨⟨R (N φ), mem_sum_domain hAB hmem⟩, ?_⟩
  show A ⟨R (N φ), hmem⟩ + B ⟨R (N φ), hAB hmem⟩ - z • R (N φ) = φ
  have hQN : Q (N φ) = B ⟨R (N φ), hAB hmem⟩ := rfl
  calc A ⟨R (N φ), hmem⟩ + B ⟨R (N φ), hAB hmem⟩ - z • R (N φ)
      = (A ⟨R (N φ), hmem⟩ - z • R (N φ)) + B ⟨R (N φ), hAB hmem⟩ := by abel
    _ = N φ + Q (N φ) := by rw [hres, hQN]
    _ = φ := h3

/-- The sum of a symmetric operator and a symmetric relatively bounded one. -/
lemma sum_isSymmetric {A B : H →ₗ.[ℂ] H} (hAsym : TeschlQM.Shared.IsSymmetric A)
    (hAB : A.domain ≤ B.domain)
    (hBsym : ∀ φ ψ : A.domain, ⟪(φ : H), B ⟨ψ, hAB ψ.2⟩⟫_ℂ = ⟪B ⟨φ, hAB φ.2⟩, (ψ : H)⟫_ℂ) :
    TeschlQM.Shared.IsSymmetric (A + B) := by
  refine ⟨?_, fun φ ψ => ?_⟩
  · show Dense ((A + B).domain : Set H)
    rw [sum_domain_eq hAB]; exact hAsym.1
  · rw [sum_apply', sum_apply', inner_add_right, inner_add_left]
    have h1 := hAsym.2 ⟨φ, φ.2.1⟩ ⟨ψ, ψ.2.1⟩
    have h2 := hBsym ⟨φ, φ.2.1⟩ ⟨ψ, ψ.2.1⟩
    rw [h1]
    exact congrArg _ h2

end Neumann


section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma closure_eq_of_closed {S : H →ₗ.[ℂ] H} (hS : S.IsClosed) : S.closure = S := by
  have h := hS.isClosable.graph_closure_eq_closure_graph
  rw [hS.submodule_topologicalClosure_eq] at h
  exact (LinearPMap.eq_of_eq_graph h).symm

/-- `A` essentially self-adjoint is closable. -/
lemma isClosable_of_esa {A : H →ₗ.[ℂ] H} (hA : TeschlQM.Shared.IsEssentiallySelfAdjoint A) :
    A.IsClosable := by
  by_contra h
  have hA' : IsSelfAdjoint A.closure := hA
  rw [closure_def' h] at hA'
  exact h hA'.isClosed.isClosable

/-- From `relativeBound A B < 1` extract constants `a < 1`, `b`. -/
lemma exists_constants {A B : H →ₗ.[ℂ] H} (h : relativeBound A B < 1) :
    ∃ a b : ℝ, a < 1 ∧ IsRelativelyBoundedWith A B a b := by
  unfold relativeBound at h
  rw [iInf_lt_iff] at h
  obtain ⟨a, h⟩ := h
  rw [iInf_lt_iff] at h
  obtain ⟨⟨b, hab⟩, h⟩ := h
  exact ⟨a, b, ENNReal.ofReal_lt_one.mp h, hab⟩

/-- Kato-Rellich for self-adjoint `A` and a symmetric `A`-bounded `B` with `a < 1`. -/
lemma sum_isSelfAdjoint {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {a b : ℝ} (ha1 : a < 1)
    (hrel : IsRelativelyBoundedWith A B a b)
    (hBsym : ∀ φ ψ : A.domain,
      ⟪(φ : H), B ⟨ψ, hrel.1 ψ.2⟩⟫_ℂ = ⟪B ⟨φ, hrel.1 φ.2⟩, (ψ : H)⟫_ℂ) :
    IsSelfAdjoint (A + B) := by
  have hAsym := isSymmetric_of_selfAdjoint hA
  have hSsym := sum_isSymmetric hAsym hrel.1 hBsym
  have h1a : 0 < 1 - a := by linarith
  set s : ℝ := b / (1 - a) + 1 with hs
  have hb0 : 0 ≤ b / (1 - a) := div_nonneg hrel.2.2.1 h1a.le
  have hs0 : 0 < s := by linarith
  have hκ : a + b / s < 1 := by
    have e : (1 - a) * (b / (1 - a) + 1) = b + (1 - a) := by field_simp
    have : b / s < 1 - a := by
      rw [div_lt_iff₀ hs0]
      calc b < b + (1 - a) := by linarith
        _ = (1 - a) * s := by rw [hs, e]
    linarith
  have hκ0 : 0 ≤ a + b / s := by
    have := hrel.2.1
    have := div_nonneg hrel.2.2.1 hs0.le
    linarith
  have hconj : conj ((s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  -- surjectivity of `S - i s`
  have surj1 : ∀ φ : H, ∃ ψ : (A + B).domain,
      (A + B) ψ - ((s : ℂ) * Complex.I) • (ψ : H) = φ := by
    obtain ⟨R, hR⟩ := sa_resolventAt_imag hA hs0.ne'
    refine surj_neumann hR hrel.1 hκ0 hκ (fun φ => ?_)
    have := bound_BR hR hs0 (fun ψ => (norm_le_imag hAsym s ψ).1)
      (fun ψ => by have := (norm_le_imag hAsym s ψ).2; rwa [abs_of_pos hs0] at this) hrel φ
    exact this
  have surj2 : ∀ φ : H, ∃ ψ : (A + B).domain,
      (A + B) ψ - ((-s : ℝ) * Complex.I : ℂ) • (ψ : H) = φ := by
    obtain ⟨R, hR⟩ := sa_resolventAt_imag hA (neg_ne_zero.mpr hs0.ne')
    refine surj_neumann hR hrel.1 hκ0 hκ (fun φ => ?_)
    have := bound_BR hR hs0 (fun ψ => (norm_le_imag hAsym (-s) ψ).1)
      (fun ψ => by
        have := (norm_le_imag hAsym (-s) ψ).2
        rwa [abs_neg, abs_of_pos hs0] at this) hrel φ
    exact this
  refine isSelfAdjoint_of_surj hSsym ((s : ℂ) * Complex.I) surj1 ?_
  rw [hconj]
  exact surj2

end Core


section Core2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma le_mk {f g : H →ₗ.[ℂ] H} (h1 : f.domain ≤ g.domain)
    (h2 : ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄, (x : H) = y → f x = g y) : f ≤ g :=
  ⟨h1, h2⟩

/-- The structural part of the essentially self-adjoint Kato-Rellich theorem. -/
theorem esa_core (A B : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsEssentiallySelfAdjoint A)
    (hB : TeschlQM.Shared.IsSymmetric B) (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ TeschlQM.Shared.IsEssentiallySelfAdjoint (A + B) ∧
      A.closure.domain ≤ B.closure.domain ∧ (A + B).closure = A.closure + B.closure := by
  obtain ⟨a, b, ha1, hrel⟩ := exists_constants hbound
  have hAcl := isClosable_of_esa hA
  have hBcl := isClosable_of_symmetric hB
  have hrel' := closure_relBounded hAcl hBcl hrel
  have hAsa : IsSelfAdjoint A.closure := hA
  have hsym' : ∀ φ ψ : A.closure.domain, ⟪(φ : H), B.closure ⟨ψ, hrel'.1 ψ.2⟩⟫_ℂ =
      ⟪B.closure ⟨φ, hrel'.1 φ.2⟩, (ψ : H)⟫_ℂ :=
    fun φ ψ => closure_symm hAcl hBcl hrel hB.2 φ ψ _ _
  have hSsa := sum_isSelfAdjoint hAsa ha1 hrel' hsym'
  have hSclosed := sum_isClosed hAsa.isClosed hrel' ha1
  have hle1 : A + B ≤ A.closure + B.closure := by
    refine le_mk ?_ ?_
    · intro x hx
      exact Submodule.mem_inf.mpr ⟨A.le_closure.1 hx.1, B.le_closure.1 hx.2⟩
    · intro x y hxy
      have e1 := A.le_closure.2 (x := ⟨(x : H), x.2.1⟩) (y := ⟨(y : H), y.2.1⟩) hxy
      have e2 := B.le_closure.2 (x := ⟨(x : H), x.2.2⟩) (y := ⟨(y : H), y.2.2⟩) hxy
      show A ⟨x, x.2.1⟩ + B ⟨x, x.2.2⟩ = A.closure ⟨y, y.2.1⟩ + B.closure ⟨y, y.2.2⟩
      rw [e1, e2]
  have hABcl : (A + B).IsClosable := hSclosed.isClosable.leIsClosable hle1
  have hval : ∀ (ψ : H) (hψ : ψ ∈ (A.closure + B.closure).domain),
      ∃ hmem : ψ ∈ (A + B).closure.domain, (A + B).closure ⟨ψ, hmem⟩ =
        A.closure ⟨ψ, hψ.1⟩ + B.closure ⟨ψ, hψ.2⟩ := by
    intro ψ hψ
    obtain ⟨h, x, h1, h2, h3⟩ := approx_pair hAcl hBcl hrel ⟨ψ, hψ.1⟩
    have h4 : Tendsto (fun n => (A + B) (⟨(x n : H), mem_sum_domain hrel.1 (x n).2⟩ :
        (A + B).domain)) atTop (𝓝 (A.closure ⟨ψ, hψ.1⟩ + B.closure ⟨ψ, h⟩)) := h2.add h3
    exact mem_closure_domain_of_tendsto hABcl
      (fun n => ⟨(x n : H), mem_sum_domain hrel.1 (x n).2⟩) h1 h4
  have hle2 : A.closure + B.closure ≤ (A + B).closure := by
    refine le_mk ?_ ?_
    · intro ψ hψ
      exact (hval ψ hψ).1
    · intro x y hxy
      obtain ⟨hmem, hv⟩ := hval (x : H) x.2
      have : y = ⟨(x : H), hmem⟩ := Subtype.ext hxy.symm
      rw [this, hv]; rfl
  have hle3 : (A + B).closure ≤ A.closure + B.closure := by
    have := hSclosed.isClosable.closure_mono hle1
    rwa [closure_eq_of_closed hSclosed] at this
  have heq : (A + B).closure = A.closure + B.closure :=
    eq_of_le_of_domain_eq hle3 (le_antisymm hle3.1 hle2.1)
  refine ⟨sum_domain_eq hrel.1, ?_, hrel'.1, heq⟩
  show IsSelfAdjoint (A + B).closure
  rw [heq]; exact hSsa

end Core2


section LowerBound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Lower bound for the shift by a real number, valid whenever `t + γ > 0`. -/
lemma lb_real {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) {γ : ℝ}
    (hγ : TeschlQM.Shared.IsBoundedBelowBy T γ) (t : ℝ) (htγ : 0 < t + γ) (ψ : T.domain) :
    (t + γ) * ‖(ψ : H)‖ ≤ ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ := by
  have hq := hγ ψ
  by_cases hψ : ‖(ψ : H)‖ = 0
  · rw [hψ]; simp
  · have hpos : 0 < ‖(ψ : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hψ)
    have hcs : (⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ).re ≤
        ‖(ψ : H)‖ * ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ := by
      calc (⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ).re
          ≤ ‖⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ‖ := Complex.re_le_norm _
        _ ≤ ‖(ψ : H)‖ * ‖T ψ - (-(t : ℂ)) • (ψ : H)‖ := norm_inner_le_norm _ _
    have hre2 : (⟪(ψ : H), T ψ - (-(t : ℂ)) • (ψ : H)⟫_ℂ).re =
        (⟪(ψ : H), T ψ⟫_ℂ).re + t * ‖(ψ : H)‖ ^ 2 := by
      have hii : ⟪(ψ : H), (ψ : H)⟫_ℂ = ((‖(ψ : H)‖ : ℝ) : ℂ) ^ 2 :=
        inner_self_eq_norm_sq_to_K _
      have hcast : (-(t : ℂ)) * ((‖(ψ : H)‖ : ℝ) : ℂ) ^ 2 =
          ((-t * ‖(ψ : H)‖ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [inner_sub_right, inner_smul_right, hii, hcast, Complex.sub_re, Complex.ofReal_re]
      ring
    rw [hre2] at hcs
    by_contra hlt
    push Not at hlt
    nlinarith [mul_pos hpos (sub_pos.mpr hlt)]

/-- The key quadratic estimate (spectral: `x² ≤ (γ/(x+l))² ...`), elementary version. -/
lemma sq_est {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) {γ : ℝ}
    (hγ : TeschlQM.Shared.IsBoundedBelowBy T γ) {l : ℝ} (hd : 0 < l + γ)
    (hdle : l + γ ≤ |γ|) (hγl : γ * l ≤ 0) (ψ : T.domain) :
    (l + γ) ^ 2 * ‖T ψ‖ ^ 2 ≤ γ ^ 2 * ‖T ψ - (-(l : ℂ)) • (ψ : H)‖ ^ 2 := by
  have hq := hγ ψ
  have hv := norm_sub_smul_sq hT (-(l : ℂ)) ψ
  have hD := norm_sub_smul_sq hT (γ : ℂ) ψ
  have hre1 : (-(l : ℂ)).re = -l := by simp
  have hn1 : ‖-(l : ℂ)‖ = |l| := by simp
  have hre2 : (γ : ℂ).re = γ := by simp
  have hn2 : ‖(γ : ℂ)‖ = |γ| := by simp
  rw [hre1, hn1, sq_abs] at hv
  rw [hre2, hn2, sq_abs] at hD
  have hsq : (l + γ) ^ 2 ≤ γ ^ 2 := by
    have : l + γ ≤ |γ| := hdle
    nlinarith [sq_abs γ, abs_nonneg γ]
  have h1 : 0 ≤ (γ ^ 2 - (l + γ) ^ 2) * ‖T ψ - (γ : ℂ) • (ψ : H)‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ (-(γ * l)) * (l + γ) * ((⟪(ψ : H), T ψ⟫_ℂ).re - γ * ‖(ψ : H)‖ ^ 2) :=
    mul_nonneg (mul_nonneg (by linarith) hd.le) (by linarith)
  rw [hv]
  rw [hD] at h1
  nlinarith [h1, h2]

lemma norm_le_M {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) {γ : ℝ}
    (hγ : TeschlQM.Shared.IsBoundedBelowBy T γ) {l : ℝ} (hd : 0 < l + γ) (ψ : T.domain) :
    ‖T ψ‖ ≤ max 1 (|γ| / (l + γ)) * ‖T ψ - (-(l : ℂ)) • (ψ : H)‖ := by
  set v := ‖T ψ - (-(l : ℂ)) • (ψ : H)‖ with hv
  have hv0 : 0 ≤ v := norm_nonneg _
  by_cases hP : l + γ ≤ |γ| ∧ γ * l ≤ 0
  · have h := sq_est hT hγ hd hP.1 hP.2 ψ
    have h1 : (l + γ) * ‖T ψ‖ ≤ |γ| * v := by
      by_contra hlt
      push Not at hlt
      have := mul_self_lt_mul_self (by positivity) hlt
      nlinarith [sq_abs γ]
    have h2 : ‖T ψ‖ ≤ |γ| / (l + γ) * v := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]; linarith
    exact le_trans h2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hv0)
  · -- here `0 ≤ l` and `-2γ ≤ l`
    have hl : 0 ≤ l ∧ -2 * γ ≤ l := by
      by_cases h1 : l + γ ≤ |γ|
      · have h2 : 0 < γ * l := by
          by_contra h2; exact hP ⟨h1, not_lt.mp h2⟩
        rcases lt_trichotomy γ 0 with hγ0 | hγ0 | hγ0
        · have : l < 0 := by nlinarith
          linarith
        · rw [hγ0] at h2; simp at h2
        · have : 0 < l := by nlinarith
          constructor <;> linarith
      · push Not at h1
        rcases le_total 0 γ with hγ0 | hγ0
        · rw [abs_of_nonneg hγ0] at h1
          constructor <;> linarith
        · rw [abs_of_nonpos hγ0] at h1
          constructor <;> linarith
    have h3 : ‖T ψ‖ ≤ v := by
      have := lb_real hT hγ l hd ψ
      by_contra hlt
      push Not at hlt
      have hv2 := norm_sub_smul_sq hT (-(l : ℂ)) ψ
      have hre1 : (-(l : ℂ)).re = -l := by simp
      have hn1 : ‖-(l : ℂ)‖ = |l| := by simp
      rw [hre1, hn1, abs_of_nonneg hl.1] at hv2
      have hq := hγ ψ
      have := mul_self_lt_mul_self (norm_nonneg _) hlt
      nlinarith [mul_nonneg hl.1 (show 0 ≤ l + 2 * γ by linarith) , sq_nonneg ‖(ψ : H)‖,
        mul_nonneg (mul_nonneg hl.1 (show 0 ≤ l + 2 * γ by linarith)) (sq_nonneg ‖(ψ : H)‖)]
    exact le_trans h3 (by
      calc v = 1 * v := (one_mul v).symm
        _ ≤ max 1 (|γ| / (l + γ)) * v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)

end LowerBound


section LB2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sa_resolventAt_real' {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) {γ : ℝ}
    (hγ : TeschlQM.Shared.IsBoundedBelowBy T γ) {t : ℝ} (htγ : 0 < t + γ) :
    ∃ R, IsResolventAt T (-(t : ℂ)) R := by
  have hsym := isSymmetric_of_selfAdjoint hT
  have hconj : conj (-(t : ℂ)) = -(t : ℂ) := by simp [Complex.conj_ofReal]
  have hsurj := surj_of_selfAdjoint hT (-(t : ℂ)) htγ
    (fun ψ => lb_real hsym hγ t htγ ψ)
    (fun ψ => by
      rw [hconj]
      exact lb_real hsym hγ t htγ ψ)
  obtain ⟨R, hR, -⟩ := exists_resolventAt T (-(t : ℂ)) (t + γ) htγ
    (fun ψ => lb_real hsym hγ t htγ ψ) hsurj
  exact ⟨R, hR⟩

lemma bound_BR_M {A B : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H} (hR : IsResolventAt A z R) {c : ℝ}
    (hc : 0 < c) {M : ℝ} (h1 : ∀ ψ : A.domain, ‖A ψ‖ ≤ M * ‖A ψ - z • (ψ : H)‖)
    (h2 : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖) {a b : ℝ}
    (hrel : IsRelativelyBoundedWith A B a b) (φ : H) :
    ‖B ⟨R φ, hrel.1 (hR.1 φ).fst⟩‖ ≤ (a * M + b / c) * ‖φ‖ := by
  have ha := hrel.2.1
  have hb := hrel.2.2.1
  obtain ⟨hRA, hRφ⟩ := hR.1 φ
  have hb' := hrel.2.2.2 (R φ) hRA (hrel.1 hRA)
  have e1 : ‖A ⟨R φ, hRA⟩‖ ≤ M * ‖φ‖ := by
    have := h1 ⟨R φ, hRA⟩
    rwa [hRφ] at this
  have e2 : c * ‖R φ‖ ≤ ‖φ‖ := by
    have := h2 ⟨R φ, hRA⟩
    rwa [show A ⟨R φ, hRA⟩ - z • R φ = φ from hRφ] at this
  have e3 : ‖R φ‖ ≤ ‖φ‖ / c := by rw [le_div_iff₀ hc]; linarith
  calc ‖B ⟨R φ, hrel.1 hRA⟩‖ ≤ a * ‖A ⟨R φ, hRA⟩‖ + b * ‖R φ‖ := hb'
    _ ≤ a * (M * ‖φ‖) + b * (‖φ‖ / c) := by gcongr
    _ = (a * M + b / c) * ‖φ‖ := by ring

lemma kappa_lt_one {a b γ l : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hl : max (a * |γ| + b) (b / (1 - a)) < l + γ) :
    a * max 1 (|γ| / (l + γ)) + b / (l + γ) < 1 := by
  have h1a : 0 < 1 - a := by linarith
  have hdp : a * |γ| + b < l + γ := lt_of_le_of_lt (le_max_left _ _) hl
  have hdq : b / (1 - a) < l + γ := lt_of_le_of_lt (le_max_right _ _) hl
  have hd : 0 < l + γ := lt_of_le_of_lt (by positivity) hdp
  rcases le_total 1 (|γ| / (l + γ)) with h | h
  · rw [max_eq_right h]
    have : (a * |γ| + b) / (l + γ) < 1 := by rw [div_lt_one hd]; exact hdp
    calc a * (|γ| / (l + γ)) + b / (l + γ) = (a * |γ| + b) / (l + γ) := by ring
      _ < 1 := this
  · rw [max_eq_left h]
    have : b / (l + γ) < 1 - a := by
      rw [div_lt_iff₀ hd]
      rw [div_lt_iff₀ h1a] at hdq
      linarith
    linarith

lemma surj_shift_real {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {γ a b : ℝ}
    (hγ : TeschlQM.Shared.IsBoundedBelowBy A γ) (ha1 : a < 1)
    (hrel : IsRelativelyBoundedWith A B a b) {l : ℝ}
    (hl : max (a * |γ| + b) (b / (1 - a)) < l + γ) :
    ∀ φ : H, ∃ ψ : (A + B).domain, (A + B) ψ - (-(l : ℂ)) • (ψ : H) = φ := by
  have hdp : a * |γ| + b < l + γ := lt_of_le_of_lt (le_max_left _ _) hl
  have hd : 0 < l + γ := lt_of_le_of_lt (by have := hrel.2.1; have := hrel.2.2.1; positivity) hdp
  have hAsym := isSymmetric_of_selfAdjoint hA
  obtain ⟨R, hR⟩ := sa_resolventAt_real' hA hγ hd
  have hκ := kappa_lt_one hrel.2.1 ha1 hrel.2.2.1 hl
  have hκ0 : 0 ≤ a * max 1 (|γ| / (l + γ)) + b / (l + γ) := by
    have := hrel.2.1; have := hrel.2.2.1
    have : 0 ≤ max 1 (|γ| / (l + γ)) := le_trans zero_le_one (le_max_left _ _)
    positivity
  exact surj_neumann hR hrel.1 hκ0 hκ (fun φ =>
    bound_BR_M hR hd (fun ψ => norm_le_M hAsym hγ hd ψ) (fun ψ => lb_real hAsym hγ l hd ψ) hrel φ)

lemma closure_boundedBelow {A : H →ₗ.[ℂ] H} (hA : A.IsClosable) {γ : ℝ}
    (h : TeschlQM.Shared.IsBoundedBelowBy A γ) :
    TeschlQM.Shared.IsBoundedBelowBy A.closure γ := by
  intro ψ
  obtain ⟨x, h1, h2⟩ := exists_approx hA ψ
  have e1 : Tendsto (fun n => γ * ‖(x n : H)‖ ^ 2) atTop (𝓝 (γ * ‖(ψ : H)‖ ^ 2)) :=
    ((h1.norm).pow 2).const_mul γ
  have e2 : Tendsto (fun n => (⟪(x n : H), A (x n)⟫_ℂ).re) atTop
      (𝓝 (⟪(ψ : H), A.closure ψ⟫_ℂ).re) :=
    (Complex.continuous_re.tendsto _).comp (h1.inner h2)
  exact le_of_tendsto_of_tendsto' e1 e2 (fun n => h (x n))

end LB2


section KL

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Symmetry identity for the real shift of a symmetric operator. -/
lemma sym_shift {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) (l : ℝ)
    (ψ η : T.domain) :
    ⟪(ψ : H), T η - (-(l : ℂ)) • (η : H)⟫_ℂ = ⟪T ψ - (-(l : ℂ)) • (ψ : H), (η : H)⟫_ℂ := by
  rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left, hT.2 ψ η]
  simp [Complex.conj_ofReal]

lemma re_inner_shift {T : H →ₗ.[ℂ] H} (l : ℝ) (ψ : T.domain) :
    (⟪(ψ : H), T ψ - (-(l : ℂ)) • (ψ : H)⟫_ℂ).re =
      (⟪(ψ : H), T ψ⟫_ℂ).re + l * ‖(ψ : H)‖ ^ 2 := by
  have hii : ⟪(ψ : H), (ψ : H)⟫_ℂ = ((‖(ψ : H)‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have hcast : (-(l : ℂ)) * ((‖(ψ : H)‖ : ℝ) : ℂ) ^ 2 = ((-l * ‖(ψ : H)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [inner_sub_right, inner_smul_right, hii, hcast, Complex.sub_re, Complex.ofReal_re]
  ring

/-- If `T` is symmetric and `T + l` is surjective, then `T + l` has a bounded self-adjoint
inverse. -/
lemma exists_inverse_CLM {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) {l : ℝ}
    (hsurj : ∀ φ : H, ∃ ψ : T.domain, T ψ - (-(l : ℂ)) • (ψ : H) = φ) :
    ∃ Q : H →L[ℂ] H, (∀ φ, ∃ h : Q φ ∈ T.domain, T ⟨Q φ, h⟩ - (-(l : ℂ)) • Q φ = φ) ∧
      (∀ ψ : T.domain, Q (T ψ - (-(l : ℂ)) • (ψ : H)) = ψ) ∧ IsSelfAdjoint Q := by
  have hinj : Function.Injective (shift T (-(l : ℂ))) := by
    rw [injective_iff_map_eq_zero]
    intro ψ hψ
    rw [shift_apply] at hψ
    obtain ⟨η, hη⟩ := hsurj (ψ : H)
    have h1 := sym_shift hT l ψ η
    rw [hη, hψ, inner_zero_left] at h1
    have : ⟪(ψ : H), (ψ : H)⟫_ℂ = 0 := h1
    exact Subtype.ext (inner_self_eq_zero.mp this)
  have hbij : Function.Bijective (shift T (-(l : ℂ))) :=
    ⟨hinj, fun φ => by
      obtain ⟨ψ, h⟩ := hsurj φ
      exact ⟨ψ, by rw [shift_apply]; exact h⟩⟩
  let e := LinearEquiv.ofBijective (shift T (-(l : ℂ))) hbij
  let Q0 : H →ₗ[ℂ] H := T.domain.subtype ∘ₗ e.symm.toLinearMap
  have hsymm : LinearMap.IsSymmetric Q0 := by
    intro x y
    have h1 := sym_shift hT l (e.symm x) (e.symm y)
    have hx : shift T (-(l : ℂ)) (e.symm x) = x := e.apply_symm_apply x
    have hy : shift T (-(l : ℂ)) (e.symm y) = y := e.apply_symm_apply y
    rw [shift_apply] at hx hy
    rw [hx, hy] at h1
    exact h1
  have hcont : Continuous Q0 := hsymm.continuous
  let Q : H →L[ℂ] H := { toLinearMap := Q0, cont := hcont }
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro φ
    refine ⟨(e.symm φ).2, ?_⟩
    have h2 : shift T (-(l : ℂ)) (e.symm φ) = φ := e.apply_symm_apply φ
    rw [shift_apply] at h2
    exact h2
  · intro ψ
    have h2 : e.symm (shift T (-(l : ℂ)) ψ) = ψ := e.symm_apply_apply ψ
    show ((e.symm (T ψ - (-(l : ℂ)) • (ψ : H)) : T.domain) : H) = ψ
    rw [← shift_apply, h2]
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hsymm


/-- Resolvent identity for the inverses of two shifts. -/
lemma inverse_RI {T : H →ₗ.[ℂ] H} {l μ : ℝ} {Q Qμ : H →L[ℂ] H}
    (hQ2 : ∀ ψ : T.domain, Q (T ψ - (-(l : ℂ)) • (ψ : H)) = ψ)
    (hμ1 : ∀ φ, ∃ h : Qμ φ ∈ T.domain, T ⟨Qμ φ, h⟩ - (-(μ : ℂ)) • Qμ φ = φ) (φ : H) :
    Q φ - Qμ φ = ((μ - l : ℝ) : ℂ) • Q (Qμ φ) := by
  obtain ⟨h, hres⟩ := hμ1 φ
  have e : T ⟨Qμ φ, h⟩ - (-(l : ℂ)) • (Qμ φ) = φ - ((μ - l : ℝ) : ℂ) • (Qμ φ) := by
    have : T ⟨Qμ φ, h⟩ = φ + (-(μ : ℂ)) • Qμ φ := sub_eq_iff_eq_add.mp hres
    rw [this]; push_cast; module
  have h3 := hQ2 ⟨Qμ φ, h⟩
  have h4 : Q (T ⟨Qμ φ, h⟩ - (-(l : ℂ)) • ((⟨Qμ φ, h⟩ : T.domain) : H)) = Qμ φ := h3
  rw [show (T ⟨Qμ φ, h⟩ - (-(l : ℂ)) • ((⟨Qμ φ, h⟩ : T.domain) : H)) =
    φ - ((μ - l : ℝ) : ℂ) • (Qμ φ) from e, _root_.map_sub, _root_.map_smul] at h4
  simpa using (congrArg (fun v => Q φ - v) h4).symm

lemma inverse_nonneg {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) {l0 : ℝ}
    (hsurj : ∀ l : ℝ, l0 < l → ∀ φ : H, ∃ ψ : T.domain, T ψ - (-(l : ℂ)) • (ψ : H) = φ)
    {l : ℝ} (hl : l0 < l) {Q : H →L[ℂ] H}
    (hQ1 : ∀ φ, ∃ h : Q φ ∈ T.domain, T ⟨Q φ, h⟩ - (-(l : ℂ)) • Q φ = φ)
    (hQ2 : ∀ ψ : T.domain, Q (T ψ - (-(l : ℂ)) • (ψ : H)) = ψ) (hQsa : IsSelfAdjoint Q) :
    0 ≤ Q := by
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) Q hQsa]
  intro x hx
  by_contra hx0
  push Not at hx0
  rw [spectrum.mem_iff] at hx
  apply hx
  have hx1 : x ≠ 0 := hx0.ne
  set μ : ℝ := l - 1 / x with hμdef
  have hμ : l0 < μ := by
    have : 0 < -(1 / x) := by
      have : 1 / x < 0 := by rw [one_div]; exact inv_lt_zero.mpr hx0
      linarith
    linarith
  obtain ⟨Qμ, hμ1, hμ2, -⟩ := exists_inverse_CLM hT (hsurj μ hμ)
  have hRI := inverse_RI hQ2 hμ1
  have ha : (x : ℂ) ≠ 0 := by exact_mod_cast hx1
  have hfapp : ∀ v : H, (algebraMap ℝ (H →L[ℂ] H) x - Q) v = (x : ℂ) • v - Q v := by
    intro v
    simp [Algebra.algebraMap_eq_smul_one]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro φ hφ
    rw [hfapp] at hφ
    have hQφ : Q φ = (x : ℂ) • φ := (sub_eq_zero.mp hφ).symm
    obtain ⟨hmem, hres⟩ := hQ1 φ
    have h1 : T ⟨Q φ, hmem⟩ = φ - (l : ℂ) • Q φ := by
      rw [sub_eq_iff_eq_add.mp hres]; module
    have hzero : T ⟨Q φ, hmem⟩ - (-(μ : ℂ)) • Q φ = 0 := by
      rw [h1, hμdef, hQφ]
      push_cast
      match_scalars <;> field_simp <;> ring
    have h5 : Qμ (T ⟨Q φ, hmem⟩ - (-(μ : ℂ)) • Q φ) = Q φ := hμ2 ⟨Q φ, hmem⟩
    rw [hzero, _root_.map_zero] at h5
    have : (x : ℂ) • φ = 0 := by rw [← hQφ]; exact h5.symm
    exact (smul_eq_zero.mp this).resolve_left ha
  · intro φ
    refine ⟨(x : ℂ)⁻¹ • φ + ((x : ℂ)⁻¹) ^ 2 • Qμ φ, ?_⟩
    rw [hfapp, _root_.map_add, _root_.map_smul, _root_.map_smul]
    have h1 := hRI φ
    have hμl : ((μ - l : ℝ) : ℂ) = -(x : ℂ)⁻¹ := by
      rw [hμdef]; push_cast; ring
    rw [hμl] at h1
    have hW : Q (Qμ φ) = -(x : ℂ) • (Q φ - Qμ φ) := by
      rw [h1]
      match_scalars <;> field_simp
    rw [hW]
    match_scalars <;> field_simp <;> ring

theorem re_inner_ge_of_surj {T : H →ₗ.[ℂ] H} (hT : TeschlQM.Shared.IsSymmetric T) {l0 : ℝ}
    (hsurj : ∀ l : ℝ, l0 < l → ∀ φ : H, ∃ ψ : T.domain, T ψ - (-(l : ℂ)) • (ψ : H) = φ)
    (ψ : T.domain) : -l0 * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), T ψ⟫_ℂ).re := by
  have key : ∀ l : ℝ, l0 < l → 0 ≤ (⟪(ψ : H), T ψ⟫_ℂ).re + l * ‖(ψ : H)‖ ^ 2 := by
    intro l hl
    obtain ⟨Q, hQ1, hQ2, hQsa⟩ := exists_inverse_CLM hT (hsurj l hl)
    have hpos := inverse_nonneg hT hsurj hl hQ1 hQ2 hQsa
    have hP : Q.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive Q).mp hpos
    have h1 := hP.re_inner_nonneg_left (T ψ - (-(l : ℂ)) • (ψ : H))
    rw [hQ2 ψ] at h1
    have h2 : 0 ≤ (⟪(ψ : H), T ψ - (-(l : ℂ)) • (ψ : H)⟫_ℂ).re := h1
    rw [re_inner_shift] at h2
    exact h2
  by_contra hlt
  push Not at hlt
  set p := (⟪(ψ : H), T ψ⟫_ℂ).re
  set n := ‖(ψ : H)‖ ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  set δ := -(p + l0 * n) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hpos2 : 0 < δ / (2 * (n + 1)) := by positivity
  have := key (l0 + δ / (2 * (n + 1))) (by linarith)
  have h2 : δ / (2 * (n + 1)) * n ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  nlinarith

end KL


section Final

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sum_le_closure_sum (A B : H →ₗ.[ℂ] H) : A + B ≤ A.closure + B.closure := by
  refine le_mk ?_ ?_
  · intro x hx
    exact Submodule.mem_inf.mpr ⟨A.le_closure.1 hx.1, B.le_closure.1 hx.2⟩
  · intro x y hxy
    have e1 := A.le_closure.2 (x := ⟨(x : H), x.2.1⟩) (y := ⟨(y : H), y.2.1⟩) hxy
    have e2 := B.le_closure.2 (x := ⟨(x : H), x.2.2⟩) (y := ⟨(y : H), y.2.2⟩) hxy
    show A ⟨x, x.2.1⟩ + B ⟨x, x.2.2⟩ = A.closure ⟨y, y.2.1⟩ + B.closure ⟨y, y.2.2⟩
    rw [e1, e2]

/-- The full essentially self-adjoint Kato-Rellich theorem (Teschl, Theorem 6.4). -/
theorem esa_final (A B : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsEssentiallySelfAdjoint A)
    (hB : TeschlQM.Shared.IsSymmetric B) (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ TeschlQM.Shared.IsEssentiallySelfAdjoint (A + B) ∧
      A.closure.domain ≤ B.closure.domain ∧ (A + B).closure = A.closure + B.closure ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b →
        TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B)
          (γ - max (a * |γ| + b) (b / (1 - a))) := by
  obtain ⟨h1, h2, h3, h4⟩ := esa_core A B hA hB hbound
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro γ a b ha1 hrel hγ
  have hAcl := isClosable_of_esa hA
  have hBcl := isClosable_of_symmetric hB
  have hrel' := closure_relBounded hAcl hBcl hrel
  have hAsa : IsSelfAdjoint A.closure := hA
  have hγ' := closure_boundedBelow hAcl hγ
  have hSsa : IsSelfAdjoint (A.closure + B.closure) := by
    have : IsSelfAdjoint (A + B).closure := h2
    rwa [h4] at this
  have hSsym := isSymmetric_of_selfAdjoint hSsa
  have hsurj : ∀ l : ℝ, (max (a * |γ| + b) (b / (1 - a)) - γ) < l →
      ∀ φ : H, ∃ ψ : (A.closure + B.closure).domain,
        (A.closure + B.closure) ψ - (-(l : ℂ)) • (ψ : H) = φ := by
    intro l hl φ
    exact surj_shift_real hAsa hγ' ha1 hrel' (by linarith) φ
  intro x
  have hx : (x : H) ∈ (A.closure + B.closure).domain := sum_le_closure_sum A B |>.1 x.2
  have hval : (A + B) x = (A.closure + B.closure) ⟨(x : H), hx⟩ :=
    (sum_le_closure_sum A B).2 rfl
  have := re_inner_ge_of_surj hSsym hsurj ⟨(x : H), hx⟩
  rw [hval]
  have e : γ - max (a * |γ| + b) (b / (1 - a)) = -(max (a * |γ| + b) (b / (1 - a)) - γ) := by
    ring
  rw [e]
  exact this

end Final

end TeschlQM.KatoRellich.Aux

open TeschlQM.KatoRellich in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsEssentiallySelfAdjoint A)
    (hB : TeschlQM.Shared.IsSymmetric B) (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ TeschlQM.Shared.IsEssentiallySelfAdjoint (A + B) ∧
      A.closure.domain ≤ B.closure.domain ∧ (A + B).closure = A.closure + B.closure ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b →
        TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B)
          (γ - max (a * |γ| + b) (b / (1 - a))) :=
  TeschlQM.KatoRellich.Aux.esa_final A B hA hB hbound
