-- Prove2me | solution 1 for Subamenable.EpiDiff.eq_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:15:42.764038+00:00
-- url     : https://prove2.me/submissions/1bd1e2df-88e2-41db-93d2-b1bf28e27dc3

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology Subamenable.EpiDiff
open scoped InnerProductSpace

/-- Regular subgradients of convex functions are global subgradients. -/
lemma SA48_reg_global {m : ℕ} (θ : E m → EReal) (hbot : ∀ y, θ y ≠ ⊥)
    (hcv : Convex ℝ {p : E m × ℝ | θ p.1 ≤ (p.2 : EReal)}) {x v : E m}
    (hreg : NonconvexSplitting.Shared.IsRegularSubgrad θ x v) (y : E m) :
    (((θ x).toReal + ⟪v, y - x⟫_ℝ : ℝ) : EReal) ≤ θ y := by
  rcases eq_or_ne (θ y) ⊤ with hy | hy
  · rw [hy]; exact le_top
  have hxa : θ x = ((θ x).toReal : EReal) := (EReal.coe_toReal hreg.1 (hbot x)).symm
  have hyb : θ y = ((θ y).toReal : EReal) := (EReal.coe_toReal hy (hbot y)).symm
  set a := (θ x).toReal
  set b := (θ y).toReal
  rw [hyb, EReal.coe_le_coe_iff]
  refine le_of_forall_pos_le_add fun e he => ?_
  set ε : ℝ := e / (‖y - x‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hpath : Tendsto (fun s : ℝ => x + s • (y - x)) (𝓝[>] 0) (𝓝 x) := by
    have : Tendsto (fun s : ℝ => x + s • (y - x)) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun s : ℝ => x + s • (y - x)) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  have h1 := hpath.eventually (hreg.2 ε hε0)
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and h3)).exists
  -- convexity
  have hmem := hcv (x := (x, a)) (y := (y, b)) (by simp [← hxa]) (by simp [← hyb])
    (by linarith : (0 : ℝ) ≤ 1 - s) hs3.le (by ring)
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, smul_eq_mul] at hmem
  have hz : (1 - s) • x + s • y = x + s • (y - x) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [hz] at hmem
  have hcomb := hs1.trans hmem
  rw [hxa, ← EReal.coe_add, EReal.coe_le_coe_iff] at hcomb
  have hn : ‖s • (y - x)‖ = s * ‖y - x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs3]
  rw [add_sub_cancel_left, inner_smul_right] at hcomb
  rw [hn] at hcomb
  -- hcomb : a + (s * ⟪v, y - x⟫ - ε * (s * ‖y - x‖)) ≤ (1 - s) * a + s * b
  have key : ⟪v, y - x⟫_ℝ - ε * ‖y - x‖ ≤ b - a := by
    have : s * (⟪v, y - x⟫_ℝ - ε * ‖y - x‖) ≤ s * (b - a) := by nlinarith
    exact le_of_mul_le_mul_left this hs3
  have hεb : ε * ‖y - x‖ ≤ e := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (y - x)]
  linarith

/-- Limiting subgradients of convex functions are global subgradients. -/
lemma SA48_lim_global {m : ℕ} (θ : E m → EReal) (hbot : ∀ y, θ y ≠ ⊥)
    (hcv : Convex ℝ {p : E m × ℝ | θ p.1 ≤ (p.2 : EReal)}) {x v : E m}
    (hv : v ∈ NonconvexSplitting.Shared.LimitingSubdiff θ x) (y : E m) :
    (((θ x).toReal + ⟪v, y - x⟫_ℝ : ℝ) : EReal) ≤ θ y := by
  rcases eq_or_ne (θ y) ⊤ with hy | hy
  · rw [hy]; exact le_top
  have hyb : θ y = ((θ y).toReal : EReal) := (EReal.coe_toReal hy (hbot y)).symm
  rw [hyb, EReal.coe_le_coe_iff]
  obtain ⟨hxt, xs, vs, hxs, hfx, hvs, hreg⟩ := hv
  have hk : ∀ k, (θ (xs k)).toReal + ⟪vs k, y - xs k⟫_ℝ ≤ (θ y).toReal := by
    intro k
    have := SA48_reg_global θ hbot hcv (hreg k) y
    rwa [hyb, EReal.coe_le_coe_iff] at this
  have ht1 : Tendsto (fun k => (θ (xs k)).toReal) atTop (𝓝 (θ x).toReal) :=
    (EReal.tendsto_toReal hxt (hbot x)).comp hfx
  have ht2 : Tendsto (fun k => ⟪vs k, y - xs k⟫_ℝ) atTop (𝓝 ⟪v, y - x⟫_ℝ) :=
    hvs.inner (tendsto_const_nhds.sub hxs)
  exact le_of_tendsto' (ht1.add ht2) hk

lemma SA48_poly {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) {ybar : E m}
    (hy : ybar ∈ C) :
    IsClosed C ∧ IsClosed (tangentCone C ybar) ∧
    (∀ (t : ℝ) (w : E m), 0 < t → ybar + t • w ∈ C → w ∈ tangentCone C ybar) ∧
    (∀ w ∈ tangentCone C ybar, ∀ᶠ t in 𝓝[>] (0 : ℝ), ybar + t • w ∈ C) := by
  obtain ⟨k, c, b, rfl⟩ := hC
  set D : Set (E m) := {w | ∀ j, ⟪c j, ybar⟫_ℝ = b j → ⟪c j, w⟫_ℝ ≤ 0} with hD
  have hDc : IsClosed D := by
    rw [hD, Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · simp only [hj, forall_const]
      exact isClosed_le (by fun_prop) continuous_const
    · simp [hj]
  have hD1 : ∀ (t : ℝ) (w : E m), 0 < t →
      ybar + t • w ∈ {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} → w ∈ D := by
    intro t w ht hmem j hj
    have := hmem j
    rw [inner_add_right, inner_smul_right, hj] at this
    have : t * ⟪c j, w⟫_ℝ ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right this ht
  have hD2 : ∀ w ∈ D, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ybar + t • w ∈ {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} := by
    intro w hw
    simp only [Set.mem_setOf_eq]
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ⟪c j, ybar⟫_ℝ = b j
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [inner_add_right, inner_smul_right, hj]
      have := hw j hj
      have ht' : (0 : ℝ) < t := ht
      nlinarith
    · have hlt : ⟪c j, ybar⟫_ℝ < b j := lt_of_le_of_ne (hy j) hj
      have hcont : Continuous (fun t : ℝ => ⟪c j, ybar + t • w⟫_ℝ) := by fun_prop
      have h0 : Tendsto (fun t : ℝ => ⟪c j, ybar + t • w⟫_ℝ) (𝓝 0)
          (𝓝 ⟪c j, ybar⟫_ℝ) := by simpa using hcont.tendsto 0
      exact nhdsWithin_le_nhds ((h0.eventually (gt_mem_nhds hlt)).mono fun t ht => ht.le)
  have hTD : tangentCone {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j} ybar = D := by
    ext w
    constructor
    · rintro ⟨t, u, htp, ht0, hu, hmem⟩
      exact hDc.mem_of_tendsto hu (Eventually.of_forall fun k => hD1 _ _ (htp k) (hmem k))
    · intro hw
      have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually (hD2 w hw))
      refine ⟨fun k => 1 / (((k + N : ℕ) : ℝ) + 1), fun _ => w, fun k => by positivity,
        ?_, tendsto_const_nhds, fun k => hN (k + N) (by omega)⟩
      exact ((tendsto_add_atTop_iff_nat N).2 tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨?_, hTD ▸ hDc, fun t w ht hm => hTD ▸ hD1 t w ht hm, fun w hw => hD2 w (hTD ▸ hw)⟩
  rw [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma SA48_piece_val {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    (j : Fin R.s) {y0 w : E m} (t : ℝ) (h0 : y0 ∈ R.Omega j)
    (h1 : y0 + t • w ∈ R.Omega j) :
    θ (y0 + t • w) = (((θ y0).toReal + t * ⟪R.A j y0 + R.a j, w⟫_ℝ +
      t ^ 2 / 2 * ⟪R.A j w, w⟫_ℝ : ℝ) : EReal) := by
  rw [hrep.2.2.2 j _ h1, hrep.2.2.2 j _ h0, EReal.toReal_coe]
  congr 1
  have hsym : ⟪R.A j w, y0⟫_ℝ = ⟪R.A j y0, w⟫_ℝ := by
    have := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (hrep.2.1 j)) w y0
    exact this.trans (real_inner_comm _ _)
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, hsym]
  ring

lemma SA48_delta2_piece {m : ℕ} (θ : E m → EReal) (R : PWLQRep m)
    (hrep : IsPWLQRep θ R) (j : Fin R.s) {y0 u w : E m} {t : ℝ} (ht : 0 < t)
    (h0 : y0 ∈ R.Omega j) (h1 : y0 + t • w ∈ R.Omega j) :
    delta2 θ y0 u w t =
      ((⟪R.A j w, w⟫_ℝ - 2 / t * ⟪u - R.A j y0 - R.a j, w⟫_ℝ : ℝ) : EReal) := by
  unfold delta2
  rw [SA48_piece_val θ R hrep j t h0 h1, ← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  simp only [inner_sub_left, inner_add_left]
  field_simp
  ring

lemma SA48_sign {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    {ybar ubar : E m}
    (hsub : ∀ y, (((θ ybar).toReal + ⟪ubar, y - ybar⟫_ℝ : ℝ) : EReal) ≤ θ y)
    (j : Fin R.s) (h0 : ybar ∈ R.Omega j) {w : E m}
    (hw : ∀ᶠ s in 𝓝[>] (0 : ℝ), ybar + s • w ∈ R.Omega j) :
    ⟪ubar - R.A j ybar - R.a j, w⟫_ℝ ≤ 0 := by
  have hlim : Tendsto (fun s : ℝ => s / 2 * ⟪R.A j w, w⟫_ℝ) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => s / 2 * ⟪R.A j w, w⟫_ℝ) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => s / 2 * ⟪R.A j w, w⟫_ℝ) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [hw, self_mem_nhdsWithin] with s hs hs0
  have hs0' : (0 : ℝ) < s := hs0
  have h := hsub (ybar + s • w)
  rw [SA48_piece_val θ R hrep j s h0 hs, EReal.coe_le_coe_iff, add_sub_cancel_left,
    inner_smul_right] at h
  have : s * ⟪ubar - R.A j ybar - R.a j, w⟫_ℝ ≤ s * (s / 2 * ⟪R.A j w, w⟫_ℝ) := by
    simp only [inner_sub_left, inner_add_left] at h ⊢
    nlinarith
  exact le_of_mul_le_mul_left this hs0'

lemma SA48_poly_closed {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) : IsClosed C := by
  obtain ⟨k, c, b, rfl⟩ := hC
  rw [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma SA48_delta2_top {m : ℕ} (θ : E m → EReal) {y0 u w : E m} {t : ℝ} (ht : 0 < t)
    (hnd : y0 + t • w ∉ dom θ) : delta2 θ y0 u w t = ⊤ := by
  have htop : θ (y0 + t • w) = ⊤ := by
    by_contra hne
    exact hnd (lt_top_iff_ne_top.2 hne)
  unfold delta2
  rw [htop, EReal.top_sub_coe]
  exact EReal.top_mul_coe_of_pos (by positivity)

lemma SA48_LB {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    {ybar ubar : E m}
    (hsub : ∀ y, (((θ ybar).toReal + ⟪ubar, y - ybar⟫_ℝ : ℝ) : EReal) ≤ θ y)
    (w : E m) (M : ℝ)
    (hM : ∀ j, w ∈ pieceCritical R ybar ubar j → M < ⟪R.A j w, w⟫_ℝ) :
    ∀ᶠ p : ℝ × E m in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      (M : EReal) < delta2 θ ybar ubar p.2 p.1 := by
  set F : Filter (ℝ × E m) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w with hF
  have hpos : ∀ᶠ p : ℝ × E m in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hsnd : Tendsto (fun p : ℝ × E m => p.2) F (𝓝 w) := tendsto_snd
  have hfst : Tendsto (fun p : ℝ × E m => p.1) F (𝓝 0) :=
    (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).mono_right nhdsWithin_le_nhds
  have hpt : Tendsto (fun p : ℝ × E m => ybar + p.1 • p.2) F (𝓝 ybar) := by
    simpa using (tendsto_const_nhds (x := ybar)).add (hfst.smul hsnd)
  have hAc : ∀ j, Tendsto (fun p : ℝ × E m => ⟪R.A j p.2, p.2⟫_ℝ) F
      (𝓝 ⟪R.A j w, w⟫_ℝ) := by
    intro j
    have hc : Continuous (fun y : E m => ⟪R.A j y, y⟫_ℝ) := by fun_prop
    exact (hc.tendsto w).comp hsnd
  have key : ∀ j, ∀ᶠ p in F, ybar + p.1 • p.2 ∈ R.Omega j →
      (M : EReal) < delta2 θ ybar ubar p.2 p.1 := by
    intro j
    by_cases h0 : ybar ∈ R.Omega j
    · obtain ⟨_, hTcl, hT1, hT2⟩ := SA48_poly (hrep.1 j) h0
      by_cases hwT : w ∈ tangentCone (R.Omega j) ybar
      · have hsg := SA48_sign θ R hrep hsub j h0 (hT2 w hwT)
        rcases hsg.lt_or_eq with hlt | heq
        · set c : ℝ := -⟪ubar - R.A j ybar - R.a j, w⟫_ℝ with hc
          have hc0 : 0 < c := by linarith
          set K : ℝ := ⟪R.A j w, w⟫_ℝ - 1 with hK
          have e1 : ∀ᶠ p in F, ⟪ubar - R.A j ybar - R.a j, p.2⟫_ℝ < -c / 2 := by
            have hcont : Continuous (fun y : E m => ⟪ubar - R.A j ybar - R.a j, y⟫_ℝ) := by
              fun_prop
            exact (hcont.tendsto w |>.comp hsnd).eventually
              (gt_mem_nhds (by linarith))
          have e2 : ∀ᶠ p in F, K < ⟪R.A j p.2, p.2⟫_ℝ :=
            (hAc j).eventually (lt_mem_nhds (by linarith))
          have e3 : ∀ᶠ p in F, p.1 < c / (|M - K| + 1) :=
            hfst.eventually (gt_mem_nhds (by positivity))
          filter_upwards [e1, e2, e3, hpos] with p h1 h2 h3 h4 hmem
          rw [SA48_delta2_piece θ R hrep j h4 h0 hmem, EReal.coe_lt_coe_iff]
          have h5 : (|M - K| + 1) * p.1 < c := by
            rw [lt_div_iff₀ (by positivity)] at h3; linarith
          have h6 : c / p.1 > |M - K| + 1 := by
            rw [gt_iff_lt, lt_div_iff₀ h4]; linarith
          have h7 : 2 / p.1 * ⟪ubar - R.A j ybar - R.a j, p.2⟫_ℝ ≤ 2 / p.1 * (-c / 2) := by
            gcongr
          have h8 : 2 / p.1 * (-c / 2) = -(c / p.1) := by field_simp
          have h9 : M - K ≤ |M - K| := le_abs_self _
          linarith
        · have hcrit : w ∈ pieceCritical R ybar ubar j := ⟨h0, hwT, heq⟩
          have hMj := hM j hcrit
          filter_upwards [(hAc j).eventually (lt_mem_nhds hMj), hpos] with p h1 h4 hmem
          rw [SA48_delta2_piece θ R hrep j h4 h0 hmem, EReal.coe_lt_coe_iff]
          have hs := SA48_sign θ R hrep hsub j h0 (hT2 p.2 (hT1 p.1 p.2 h4 hmem))
          have : 0 ≤ 2 / p.1 := by positivity
          nlinarith
      · filter_upwards [hsnd.eventually (hTcl.isOpen_compl.mem_nhds hwT), hpos]
          with p h1 h4 hmem
        exact absurd (hT1 p.1 p.2 h4 hmem) h1
    · filter_upwards [hpt.eventually ((SA48_poly_closed (hrep.1 j)).isOpen_compl.mem_nhds h0)]
        with p h1 hmem
      exact absurd hmem h1
  filter_upwards [Filter.eventually_all.2 key, hpos] with p hk hp
  by_cases hdom : ybar + p.1 • p.2 ∈ dom θ
  · rw [hrep.2.2.1] at hdom
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hdom
    exact hk j hj
  · rw [SA48_delta2_top θ hp hdom]
    exact EReal.coe_lt_top M

section main
variable {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
  {ybar ubar : E m}
  (hsub : ∀ y, (((θ ybar).toReal + ⟪ubar, y - ybar⟫_ℝ : ℝ) : EReal) ≤ θ y)
include hrep

lemma SA48_ray {i : Fin R.s} {w : E m} (hw : w ∈ pieceCritical R ybar ubar i) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      delta2 θ ybar ubar w t = ((⟪R.A i w, w⟫_ℝ : ℝ) : EReal) := by
  obtain ⟨h0, hT, heq⟩ := hw
  obtain ⟨_, _, _, hT2⟩ := SA48_poly (hrep.1 i) h0
  filter_upwards [hT2 w hT, self_mem_nhdsWithin] with t ht ht0
  rw [SA48_delta2_piece θ R hrep i ht0 h0 ht, heq, mul_zero, sub_zero]

lemma SA48_consistent {i j : Fin R.s} {w : E m} (hi : w ∈ pieceCritical R ybar ubar i)
    (hj : w ∈ pieceCritical R ybar ubar j) : ⟪R.A j w, w⟫_ℝ = ⟪R.A i w, w⟫_ℝ := by
  obtain ⟨t, h1, h2⟩ := ((SA48_ray θ R hrep hi).and (SA48_ray θ R hrep hj)).exists
  rw [h1] at h2
  exact (EReal.coe_injective h2).symm

include hsub

lemma SA48_value {i : Fin R.s} {w : E m} (hw : w ∈ pieceCritical R ybar ubar i) :
    secondSubderiv θ ybar ubar w = ((⟪R.A i w, w⟫_ℝ : ℝ) : EReal) := by
  set V : ℝ := ⟪R.A i w, w⟫_ℝ
  set F : Filter (ℝ × E m) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w
  apply le_antisymm
  · have hmap : Tendsto (fun t : ℝ => (t, w)) (𝓝[>] (0 : ℝ)) F :=
      tendsto_id.prodMk tendsto_const_nhds
    unfold secondSubderiv
    calc liminf (fun p : ℝ × E m => delta2 θ ybar ubar p.2 p.1) F
        ≤ liminf (fun p : ℝ × E m => delta2 θ ybar ubar p.2 p.1)
            (map (fun t : ℝ => (t, w)) (𝓝[>] (0 : ℝ))) :=
          Filter.liminf_le_liminf_of_le hmap
      _ = liminf (fun t : ℝ => delta2 θ ybar ubar w t) (𝓝[>] (0 : ℝ)) := by
          rw [← Filter.liminf_comp]; rfl
      _ = (V : EReal) := by
          rw [Filter.liminf_congr (SA48_ray θ R hrep hw)]
          exact Filter.liminf_const _
  · by_contra hlt
    push_neg at hlt
    obtain ⟨M, hM1, hM2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hMV : M < V := EReal.coe_lt_coe_iff.1 hM2
    have hev := SA48_LB θ R hrep hsub w M (fun j hj => by
      rw [SA48_consistent θ R hrep hw hj]; exact hMV)
    have : (M : EReal) ≤ secondSubderiv θ ybar ubar w := by
      unfold secondSubderiv
      exact Filter.le_liminf_of_le (by isBoundedDefault) (hev.mono fun p hp => hp.le)
    exact absurd hM1 (not_lt.2 this)

lemma SA48_top {w : E m} (hw : ∀ i, w ∉ pieceCritical R ybar ubar i) :
    secondSubderiv θ ybar ubar w = ⊤ := by
  by_contra hne
  obtain ⟨M, hM1, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 hne)
  have hev := SA48_LB θ R hrep hsub w M (fun j hj => absurd hj (hw j))
  have : (M : EReal) ≤ secondSubderiv θ ybar ubar w := by
    unfold secondSubderiv
    exact Filter.le_liminf_of_le (by isBoundedDefault) (hev.mono fun p hp => hp.le)
  exact absurd hM1 (not_lt.2 this)

end main

theorem solution {m : ℕ} (theta : E m → EReal) (R : PWLQRep m)
    (ybar ubar : E m) (hrep : IsPWLQRep theta R)
    (hconv : IsConvexPWLQ theta) (hy : ybar ∈ dom theta)
    (hu : ubar ∈ NonconvexSplitting.Shared.LimitingSubdiff theta ybar) :
    IsProperlyTwiceEpiDiff theta ybar ubar ∧
    dom (secondSubderiv theta ybar ubar) =
      {w | ∃ i : Fin R.s, w ∈ pieceCritical R ybar ubar i} ∧
    (∀ i : Fin R.s, ∀ w ∈ pieceCritical R ybar ubar i,
      secondSubderiv theta ybar ubar w = ((⟪R.A i w, w⟫_ℝ : ℝ) : EReal)) ∧
    (∀ w, w ∉ {u | ∃ i : Fin R.s, u ∈ pieceCritical R ybar ubar i} →
      secondSubderiv theta ybar ubar w = ⊤) := by
  have hsub := SA48_lim_global theta hconv.1 hconv.2.1 hu
  have hval := fun i w (hw : w ∈ pieceCritical R ybar ubar i) =>
    SA48_value theta R hrep hsub hw
  have htop : ∀ w, w ∉ {u | ∃ i : Fin R.s, u ∈ pieceCritical R ybar ubar i} →
      secondSubderiv theta ybar ubar w = ⊤ := by
    intro w hw
    exact SA48_top theta R hrep hsub (fun i hi => hw ⟨i, hi⟩)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hval, htop⟩
  · intro w t ht0 htt
    refine ⟨fun _ => w, tendsto_const_nhds, ?_⟩
    have htw : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨htt, Eventually.of_forall fun k => ht0 k⟩
    by_cases hw : ∃ i, w ∈ pieceCritical R ybar ubar i
    · obtain ⟨i, hi⟩ := hw
      rw [hval i w hi]
      exact tendsto_const_nhds.congr' ((htw.eventually (SA48_ray theta R hrep hi)).mono
        fun k hk => hk.symm)
    · rw [htop w hw, EReal.tendsto_nhds_top_iff_real]
      intro M
      have hev := SA48_LB theta R hrep hsub w M
        (fun j hj => absurd ⟨j, hj⟩ hw)
      have hs : Tendsto (fun k => (t k, w)) atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
        htw.prodMk tendsto_const_nhds
      exact hs.eventually hev
  · intro w
    by_cases hw : ∃ i, w ∈ pieceCritical R ybar ubar i
    · obtain ⟨i, hi⟩ := hw
      rw [hval i w hi]; exact EReal.coe_ne_bot _
    · rw [htop w hw]; exact top_ne_bot
  · have hy' := hy
    rw [show dom theta = _ from hrep.2.2.1] at hy'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy'
    obtain ⟨_, _, hT1, _⟩ := SA48_poly (hrep.1 i) hi
    have h0 : (0 : E m) ∈ pieceCritical R ybar ubar i :=
      ⟨hi, hT1 1 0 one_pos (by simpa using hi), by simp⟩
    exact ⟨0, by rw [hval i 0 h0]; exact EReal.coe_ne_top _⟩
  · ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hw
      by_contra hn
      have := htop w hn
      exact (lt_top_iff_ne_top.1 hw) this
    · rintro ⟨i, hi⟩
      show secondSubderiv theta ybar ubar w < ⊤
      rw [hval i w hi]; exact EReal.coe_lt_top _
