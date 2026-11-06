-- Prove2me | solution 1 for SunNLSDP.Equiv.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:11:21.775162+00:00
-- url     : https://prove2.me/submissions/5434692c-311c-44d1-8380-fd16b87d5c3e

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDPProp8Aux

open SunNLSDP.Equiv Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A normal vector is nonpositive on the contingent cone. -/
theorem tangent_inner_nonpos (D : Set E) (G Γ T : E)
    (hΓ : Γ ∈ RobinsonSR.Reduction.normalCone D G) (hT : T ∈ tangentCone D G) : ⟪Γ, T⟫ ≤ 0 := by
  obtain ⟨t, htpos, ht0, hlim⟩ := hT
  have hne : D.Nonempty := ⟨G, hΓ.1⟩
  have key : ∀ k, ⟪Γ, T⟫ ≤ ‖Γ‖ * (infDist (G + t k • T) D / t k + t k) := by
    intro k
    have htk := htpos k
    obtain ⟨c, hc, hdc⟩ := (infDist_lt_iff hne).1
      (lt_add_of_pos_right (infDist (G + t k • T) D) (pow_pos htk 2))
    have h1 : ⟪Γ, c - G⟫ ≤ 0 := hΓ.2 c hc
    have h2 : ⟪Γ, G + t k • T - c⟫ ≤ ‖Γ‖ * dist (G + t k • T) c := by
      rw [dist_eq_norm]; exact real_inner_le_norm _ _
    have h3 : ⟪Γ, c - G⟫ + ⟪Γ, G + t k • T - c⟫ = t k * ⟪Γ, T⟫ := by
      rw [← inner_add_right, ← inner_smul_right]; congr 1; abel
    have h4 : t k * ⟪Γ, T⟫ ≤ ‖Γ‖ * (infDist (G + t k • T) D + t k ^ 2) := by
      have := mul_le_mul_of_nonneg_left hdc.le (norm_nonneg Γ)
      linarith
    have h5 : ‖Γ‖ * (infDist (G + t k • T) D / t k + t k) =
        ‖Γ‖ * (infDist (G + t k • T) D + t k ^ 2) / t k := by
      field_simp
    rw [h5, le_div_iff₀ htk]
    linarith
  have hT2 : Tendsto (fun k => ‖Γ‖ * (infDist (G + t k • T) D / t k + t k)) atTop
      (𝓝 (‖Γ‖ * (0 + 0))) := (hlim.add ht0).const_mul _
  simp only [add_zero, mul_zero] at hT2
  exact ge_of_tendsto' hT2 key

/-- weighted infDist bound -/
theorem infDist_le_comb (D : Set E) (hne : D.Nonempty) (x z1 z2 : E) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (H : ∀ c1 ∈ D, ∀ c2 ∈ D, ∃ c ∈ D, dist x c ≤ a * dist z1 c1 + b * dist z2 c2) :
    infDist x D ≤ a * infDist z1 D + b * infDist z2 D := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set δ := ε / (a + b + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨c1, hc1, hd1⟩ := (infDist_lt_iff hne).1 (lt_add_of_pos_right (infDist z1 D) hδ)
  obtain ⟨c2, hc2, hd2⟩ := (infDist_lt_iff hne).1 (lt_add_of_pos_right (infDist z2 D) hδ)
  obtain ⟨c, hc, hdc⟩ := H c1 hc1 c2 hc2
  have e1 : infDist x D ≤ dist x c := infDist_le_dist_of_mem hc
  have e2 : a * dist z1 c1 ≤ a * (infDist z1 D + δ) := mul_le_mul_of_nonneg_left hd1.le ha
  have e3 : b * dist z2 c2 ≤ b * (infDist z2 D + δ) := mul_le_mul_of_nonneg_left hd2.le hb
  have e4 : (a + b) * δ < ε := by
    have : (a + b + 1) * δ = ε := by
      simp only [δ]; field_simp
    nlinarith
  nlinarith

variable (D : Set E) (hDc : Convex ℝ D) (y : E) (hy : y ∈ D)
include hDc hy

theorem infDist_mono (T : E) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    infDist (y + s • T) D ≤ (s / t) * infDist (y + t • T) D := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have := infDist_le_comb D ⟨y, hy⟩ (y + s • T) (y + t • T) (y + t • T) (s / t) 0
    (div_nonneg hs.le ht.le) le_rfl (fun c1 hc1 _ _ => ?_)
  · simpa using this
  refine ⟨y + (s / t) • (c1 - y), hDc.add_smul_sub_mem hy hc1
    ⟨div_nonneg hs.le ht.le, (div_le_one ht).2 hst⟩, ?_⟩
  rw [dist_eq_norm, dist_eq_norm, zero_mul, add_zero]
  have : y + s • T - (y + (s / t) • (c1 - y)) = (s / t) • (y + t • T - c1) := by
    simp only [smul_sub, smul_add, smul_smul, div_mul_cancel₀ s ht.ne']
    abel
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs.le ht.le)]

theorem tangent_iff (T : E) : T ∈ tangentCone D y ↔
    ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s ≤ δ → infDist (y + s • T) D / s ≤ ε := by
  constructor
  · rintro ⟨t, htpos, ht0, hlim⟩ ε hε
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    refine ⟨t k, htpos k, fun s hs hst => ?_⟩
    have hm := infDist_mono D hDc y hy T s (t k) hs hst
    rw [div_le_iff₀ hs]
    have htk := htpos k
    have e1 : s / t k * infDist (y + t k • T) D = s * (infDist (y + t k • T) D / t k) := by
      field_simp
    rw [e1] at hm
    nlinarith
  · intro H
    refine ⟨fun k : ℕ => 1 / ((k : ℝ) + 1), fun k => by positivity,
      tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k =>
      lt_of_lt_of_le ha (div_nonneg infDist_nonneg (by positivity)), fun a ha => ?_⟩
    obtain ⟨δ, hδ, hH⟩ := H (a / 2) (by linarith)
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)] with k hk
    have := hH _ (by positivity) hk.le
    linarith

theorem tangent_zero : (0 : E) ∈ tangentCone D y := by
  rw [tangent_iff D hDc y hy]
  intro ε hε
  refine ⟨1, one_pos, fun s hs _ => ?_⟩
  simp [infDist_zero_of_mem hy, hε.le]

theorem tangent_add (T1 T2 : E) (h1 : T1 ∈ tangentCone D y) (h2 : T2 ∈ tangentCone D y) :
    T1 + T2 ∈ tangentCone D y := by
  rw [tangent_iff D hDc y hy] at h1 h2 ⊢
  intro ε hε
  obtain ⟨δ1, hδ1, H1⟩ := h1 (ε / 2) (by linarith)
  obtain ⟨δ2, hδ2, H2⟩ := h2 (ε / 2) (by linarith)
  refine ⟨min δ1 δ2 / 2, by positivity, fun s hs hsd => ?_⟩
  have hs1 : 2 * s ≤ δ1 := by have := min_le_left δ1 δ2; linarith
  have hs2 : 2 * s ≤ δ2 := by have := min_le_right δ1 δ2; linarith
  have a1 := H1 (2 * s) (by linarith) hs1
  have a2 := H2 (2 * s) (by linarith) hs2
  rw [div_le_iff₀ (by linarith)] at a1 a2
  have hc := infDist_le_comb D ⟨y, hy⟩ (y + s • (T1 + T2)) (y + (2 * s) • T1)
    (y + (2 * s) • T2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (fun c1 hc1 c2 hc2 => ?_)
  · rw [div_le_iff₀ hs]
    nlinarith
  refine ⟨(1 / 2 : ℝ) • c1 + (1 / 2 : ℝ) • c2, hDc hc1 hc2 (by norm_num) (by norm_num)
    (by norm_num), ?_⟩
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have : y + s • (T1 + T2) - ((1 / 2 : ℝ) • c1 + (1 / 2 : ℝ) • c2) =
      (1 / 2 : ℝ) • (y + (2 * s) • T1 - c1) + (1 / 2 : ℝ) • (y + (2 * s) • T2 - c2) := by
    simp only [smul_sub, smul_add, smul_smul]
    norm_num
    module
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

theorem tangent_smul (c : ℝ) (hc : 0 ≤ c) (T : E) (h : T ∈ tangentCone D y) :
    c • T ∈ tangentCone D y := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using tangent_zero D hDc y hy
  rw [tangent_iff D hDc y hy] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h (ε / c) (div_pos hε hc)
  refine ⟨δ / c, div_pos hδ hc, fun s hs hsd => ?_⟩
  have hsc : s * c ≤ δ := by rwa [le_div_iff₀ hc] at hsd
  have a := H (s * c) (by positivity) hsc
  rw [div_le_iff₀ (by positivity)] at a
  rw [smul_smul, div_le_iff₀ hs]
  have : ε / c * (s * c) = ε * s := by field_simp
  linarith

omit hDc hy in
theorem span_cone (C : Set E) (h0 : (0 : E) ∈ C) (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C)
    (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ a ∈ C, c • a ∈ C) (v : E) (hv : v ∈ Submodule.span ℝ C) :
    ∃ c1 ∈ C, ∃ c2 ∈ C, v = c1 - c2 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨x, hx, 0, h0, by simp⟩
  | zero => exact ⟨0, h0, 0, h0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := hx
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := hz
    exact ⟨a1 + b1, hadd _ ha1 _ hb1, a2 + b2, hadd _ ha2 _ hb2, by abel⟩
  | smul r x _ hx =>
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := hx
    rcases le_total 0 r with hr | hr
    · exact ⟨r • a1, hsmul r hr _ ha1, r • a2, hsmul r hr _ ha2, smul_sub r a1 a2⟩
    · refine ⟨(-r) • a2, hsmul _ (by linarith) _ ha2, (-r) • a1, hsmul _ (by linarith) _ ha1, ?_⟩
      simp only [smul_sub, neg_smul]; abel

omit hDc hy in
theorem affineSpan_eq_span (s : Set E) (h0 : (0 : E) ∈ s) :
    (affineSpan ℝ s : Set E) = Submodule.span ℝ s := by
  ext d
  rw [SetLike.mem_coe, ← AffineSubspace.vsub_right_mem_direction_iff_mem (mem_affineSpan ℝ h0) d,
    direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0]
  simp

end SunNLSDPProp8Aux

open SunNLSDPProp8Aux SunNLSDP.Equiv in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X) (ζbar : EuclideanSpace ℝ (Fin m)) (Γbar : SymMat n)
    (hfeas : P.feasible xbar) (hKKT : (ζbar, Γbar) ∈ P.multipliers xbar)
    (hstrict : P.StrictCQ xbar Γbar) :
    P.multipliers xbar = {(ζbar, Γbar)} ∧
      (affineSpan ℝ (P.criticalCone xbar) : Set X) = P.app xbar ζbar Γbar := by
  set f' := fderiv ℝ P.f xbar
  set h' := fderiv ℝ P.h xbar
  set g' := fderiv ℝ P.g xbar
  have hfd : HasFDerivAt P.f f' xbar :=
    ((P.f_smooth.differentiable (by norm_num)) xbar).hasFDerivAt
  have hhd : HasFDerivAt P.h h' xbar :=
    ((P.h_smooth.differentiable (by norm_num)) xbar).hasFDerivAt
  have hgd : HasFDerivAt P.g g' xbar :=
    ((P.g_smooth.differentiable (by norm_num)) xbar).hasFDerivAt
  have hlag : ∀ (ζ : EuclideanSpace ℝ (Fin m)) (Γ : SymMat n) (d : X),
      fderiv ℝ (fun y => P.lagrangian y ζ Γ) xbar d = f' d + ⟪ζ, h' d⟫ + ⟪Γ, g' d⟫ := by
    intro ζ Γ d
    have H : HasFDerivAt (fun y => P.f y + innerSL ℝ ζ (P.h y) + innerSL ℝ Γ (P.g y))
        (f' + (innerSL ℝ ζ).comp h' + (innerSL ℝ Γ).comp g') xbar :=
      (hfd.add ((innerSL ℝ ζ).hasFDerivAt.comp xbar hhd)).add
        ((innerSL ℝ Γ).hasFDerivAt.comp xbar hgd)
    have hfun : (fun y => P.lagrangian y ζ Γ) =
        (fun y => P.f y + innerSL ℝ ζ (P.h y) + innerSL ℝ Γ (P.g y)) := by
      funext y; simp [Data.lagrangian]
    rw [hfun, H.fderiv]
    simp
  have hmulteq : ∀ (ζ : EuclideanSpace ℝ (Fin m)) (Γ : SymMat n), (ζ, Γ) ∈ P.multipliers xbar →
      ∀ d, f' d + ⟪ζ, h' d⟫ + ⟪Γ, g' d⟫ = 0 := by
    intro ζ Γ hμ d
    rw [← hlag, hμ.1]
    rfl
  have hNbar : Γbar ∈ RobinsonSR.Reduction.normalCone (psdCone n) (P.g xbar) := hKKT.2.2
  refine ⟨?_, ?_⟩
  · ext ⟨ζ, Γ⟩
    simp only [Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro hμ
      have key : ∀ a B, ⟪ζ - ζbar, a⟫ + ⟪Γ - Γbar, B⟫ ≤ 0 := by
        intro a B
        obtain ⟨d, hd1, hd2, hd3⟩ := hstrict a B
        have i1 := tangent_inner_nonpos _ _ _ _ hμ.2.2 hd2
        have e1 := hmulteq _ _ hμ d
        have e2 := hmulteq _ _ hKKT d
        have hd3' : ⟪Γbar, B - g' d⟫ = 0 := hd3
        have hB : B = g' d + (B - g' d) := by abel
        rw [← hd1, hB]
        simp only [inner_sub_left, inner_add_right]
        linarith
      have := key (ζ - ζbar) (Γ - Γbar)
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
      have h1 : ‖ζ - ζbar‖ = 0 := by
        nlinarith [sq_nonneg ‖ζ - ζbar‖, sq_nonneg ‖Γ - Γbar‖, norm_nonneg (ζ - ζbar)]
      have h2 : ‖Γ - Γbar‖ = 0 := by
        nlinarith [sq_nonneg ‖ζ - ζbar‖, sq_nonneg ‖Γ - Γbar‖, norm_nonneg (Γ - Γbar)]
      exact ⟨sub_eq_zero.1 (norm_eq_zero.1 h1), sub_eq_zero.1 (norm_eq_zero.1 h2)⟩
    · rintro ⟨rfl, rfl⟩
      exact hKKT
  · have hg : P.g xbar ∈ psdCone n := hfeas.2
    have hconv : Convex ℝ (psdCone n) := by
      intro A hA B hB a b ha hb _
      have e : (a • A + b • B).toMat = a • A.toMat + b • B.toMat := by
        ext i j; simp [SymMat.toMat]
      show (a • A + b • B).toMat.PosSemidef
      rw [e]
      exact (Matrix.PosSemidef.smul hA ha).add (Matrix.PosSemidef.smul hB hb)
    set C : Set (SymMat n) := tangentCone (psdCone n) (P.g xbar) ∩ {T | ⟪Γbar, T⟫ = 0}
      with hCdef
    have hC0 : (0 : SymMat n) ∈ C := ⟨tangent_zero _ hconv _ hg, by simp⟩
    have hCadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C := by
      intro a ha b hb
      refine ⟨tangent_add _ hconv _ hg _ _ ha.1 hb.1, ?_⟩
      have h1 : ⟪Γbar, a⟫ = 0 := ha.2
      have h2 : ⟪Γbar, b⟫ = 0 := hb.2
      show ⟪Γbar, a + b⟫ = 0
      rw [inner_add_right, h1, h2, add_zero]
    have hCsmul : ∀ c : ℝ, 0 ≤ c → ∀ a ∈ C, c • a ∈ C := by
      intro c hc a ha
      refine ⟨tangent_smul _ hconv _ hg c hc _ ha.1, ?_⟩
      have h1 : ⟪Γbar, a⟫ = 0 := ha.2
      show ⟪Γbar, c • a⟫ = 0
      have := real_inner_smul_right Γbar a c
      rw [h1, mul_zero] at this
      exact this
    have hproj : metricProj (psdCone n) (P.g xbar + Γbar) = P.g xbar := by
      have hN := hNbar.2
      have e2 : P.g xbar - (P.g xbar + Γbar) = -Γbar := by abel
      have hmin : ∀ w ∈ psdCone n,
          ‖P.g xbar - (P.g xbar + Γbar)‖ ≤ ‖w - (P.g xbar + Γbar)‖ := by
        intro w hw
        have h1 := hN w hw
        have e1 : w - (P.g xbar + Γbar) = (w - P.g xbar) - Γbar := by abel
        rw [e1, e2, norm_neg, ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
          norm_sub_sq_real]
        rw [real_inner_comm] at h1
        nlinarith [sq_nonneg ‖w - P.g xbar‖]
      have hex : ∃ z ∈ psdCone n, ∀ w ∈ psdCone n,
          ‖z - (P.g xbar + Γbar)‖ ≤ ‖w - (P.g xbar + Γbar)‖ := ⟨_, hg, hmin⟩
      unfold metricProj
      rw [dif_pos hex]
      obtain ⟨hp1, hp2⟩ := Classical.choose_spec hex
      set p := Classical.choose hex
      have h1 := hp2 _ hg
      have h2 := hN p hp1
      have e1 : p - (P.g xbar + Γbar) = (p - P.g xbar) - Γbar := by abel
      rw [e1, e2, norm_neg, ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
        norm_sub_sq_real] at h1
      rw [real_inner_comm] at h2
      have h3 : ‖p - P.g xbar‖ ^ 2 ≤ 0 := by nlinarith
      have h4 : ‖p - P.g xbar‖ = 0 := by nlinarith [norm_nonneg (p - P.g xbar)]
      exact sub_eq_zero.1 (norm_eq_zero.1 h4)
    have hcritC : psdCriticalCone (P.g xbar + Γbar) = C := by
      unfold psdCriticalCone
      rw [hproj]
      ext B
      have : P.g xbar - (P.g xbar + Γbar) = -Γbar := by abel
      simp only [hCdef, Set.mem_inter_iff, Set.mem_setOf_eq, this, inner_neg_left, neg_eq_zero]
    have hcrit : ∀ d, d ∈ P.criticalCone xbar ↔ h' d = 0 ∧ g' d ∈ C := by
      intro d
      have e := hmulteq _ _ hKKT d
      constructor
      · rintro ⟨h1, h2, h3⟩
        have i := tangent_inner_nonpos _ _ _ _ hNbar h2
        rw [h1, inner_zero_right] at e
        exact ⟨h1, h2, show ⟪Γbar, g' d⟫ = 0 by linarith⟩
      · rintro ⟨h1, h2, h3⟩
        have h3' : ⟪Γbar, g' d⟫ = 0 := h3
        rw [h1, inner_zero_right, h3'] at e
        exact ⟨h1, h2, by linarith⟩
    have h0crit : (0 : X) ∈ P.criticalCone xbar := (hcrit 0).2 ⟨by simp, by simpa using hC0⟩
    rw [affineSpan_eq_span _ h0crit]
    ext d
    show d ∈ Submodule.span ℝ (P.criticalCone xbar) ↔
      h' d = 0 ∧ g' d ∈ (affineSpan ℝ (psdCriticalCone (P.g xbar + Γbar)) : Set (SymMat n))
    rw [hcritC, affineSpan_eq_span _ hC0, SetLike.mem_coe]
    constructor
    · intro hd
      have hle : Submodule.span ℝ (P.criticalCone xbar) ≤
          LinearMap.ker (h' : X →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ⊓
            Submodule.comap (g' : X →ₗ[ℝ] SymMat n) (Submodule.span ℝ C) := by
        rw [Submodule.span_le]
        intro e he
        obtain ⟨h1, h2⟩ := (hcrit e).1 he
        simp only [SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_comap,
          ContinuousLinearMap.coe_coe]
        exact ⟨h1, Submodule.subset_span h2⟩
      have := hle hd
      simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_comap,
        ContinuousLinearMap.coe_coe] at this
      exact this
    · rintro ⟨h1, h2⟩
      obtain ⟨c1, hc1, c2, hc2, hdc⟩ := span_cone C hC0 hCadd hCsmul _ h2
      obtain ⟨e0, he1, he2, he3⟩ := hstrict 0 (-c2)
      have hc' : -c2 - g' e0 ∈ C := ⟨he2, he3⟩
      have hm1 : -e0 ∈ P.criticalCone xbar := by
        refine (hcrit _).2 ⟨by rw [map_neg]; simp only [neg_eq_zero]; exact he1, ?_⟩
        have : g' (-e0) = c2 + (-c2 - g' e0) := by rw [map_neg]; abel
        rw [this]
        exact hCadd _ hc2 _ hc'
      have hm2 : d + -e0 ∈ P.criticalCone xbar := by
        refine (hcrit _).2 ⟨by rw [map_add, map_neg, h1]; simp only [zero_add, neg_eq_zero]; exact he1, ?_⟩
        have : g' (d + -e0) = c1 + (-c2 - g' e0) := by rw [map_add, map_neg, hdc]; abel
        rw [this]
        exact hCadd _ hc1 _ hc'
      have hd : d = (d + -e0) - (-e0) := by abel
      rw [hd]
      exact Submodule.sub_mem _ (Submodule.subset_span hm2) (Submodule.subset_span hm1)
