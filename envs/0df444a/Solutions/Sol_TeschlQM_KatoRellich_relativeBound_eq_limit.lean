-- Prove2me | solution 1 for TeschlQM.KatoRellich.relativeBound_eq_limit
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:30:30.075346+00:00
-- url     : https://prove2.me/submissions/fda812e9-e027-4269-b18d-984a73a24d08

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_KatoRellich_resolvent
import Definitions.Def_TeschlQM_KatoRellich_compCLM
import Definitions.Def_TeschlQM_KatoRellich_opNorm

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

end TeschlQM.KatoRellich.Aux

namespace TeschlQM.KatoRellich.Aux

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

section Main

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem relativeBound_eq_limit_main (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hB : IsRelativelyBounded A B) :
    Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A ((t : ℂ) * Complex.I)))) atTop
        (𝓝 (relativeBound A B)) ∧
      Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A (-((t : ℂ) * Complex.I))))) atTop
        (𝓝 (relativeBound A B)) ∧
      ∀ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy A γ →
        Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A (-(t : ℂ))))) atTop
          (𝓝 (relativeBound A B)) := by
  have hsym := isSymmetric_of_selfAdjoint hA
  refine ⟨?_, ?_, ?_⟩
  · refine tendsto_of_family hB (fun t => (t : ℂ) * Complex.I) (fun t => t) tendsto_id ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    refine ⟨ht, sa_resolventAt_imag hA ht.ne', fun ψ => (norm_le_imag hsym t ψ).1, fun ψ => ?_⟩
    have := (norm_le_imag hsym t ψ).2
    rwa [abs_of_pos ht] at this
  · refine tendsto_of_family hB (fun t => -((t : ℂ) * Complex.I)) (fun t => t) tendsto_id ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hz : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    refine ⟨ht, ?_, ?_, ?_⟩
    · rw [hz]; exact sa_resolventAt_imag hA (neg_ne_zero.mpr ht.ne')
    · intro ψ
      rw [hz]; exact (norm_le_imag hsym (-t) ψ).1
    · intro ψ
      rw [hz]
      have := (norm_le_imag hsym (-t) ψ).2
      rwa [abs_neg, abs_of_pos ht] at this
  · intro γ hγ
    refine tendsto_of_family hB (fun t => -(t : ℂ)) (fun t => t + γ)
      (tendsto_atTop_add_const_right _ _ tendsto_id) ?_
    filter_upwards [eventually_ge_atTop (2 * |γ| + 1)] with t ht
    have h1 : -|γ| ≤ γ := neg_abs_le γ
    have h2 : γ ≤ |γ| := le_abs_self γ
    have h3 : 0 ≤ |γ| := abs_nonneg γ
    have ht0 : 0 ≤ t := by linarith
    have ht1 : -2 * γ ≤ t := by linarith
    have ht2 : 0 < t + γ := by linarith
    exact ⟨ht2, sa_resolventAt_real hA hγ ht0 ht1 ht2,
      fun ψ => (norm_le_real hsym hγ t ht0 ht1 ht2 ψ).1,
      fun ψ => (norm_le_real hsym hγ t ht0 ht1 ht2 ψ).2⟩

end Main

end TeschlQM.KatoRellich.Aux

open TeschlQM.KatoRellich Filter Topology Complex in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsRelativelyBounded A B) :
    Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A ((t : ℂ) * I)))) atTop
        (𝓝 (relativeBound A B)) ∧
      Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A (-((t : ℂ) * I))))) atTop
        (𝓝 (relativeBound A B)) ∧
      ∀ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy A γ →
        Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A (-(t : ℂ))))) atTop
          (𝓝 (relativeBound A B)) :=
  TeschlQM.KatoRellich.Aux.relativeBound_eq_limit_main A B hA hB
