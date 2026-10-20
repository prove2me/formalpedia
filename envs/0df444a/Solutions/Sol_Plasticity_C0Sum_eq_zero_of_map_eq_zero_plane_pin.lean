-- Prove2me | solution 1 for Plasticity.C0Sum.eq_zero_of_map_eq_zero.plane_pin
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:55.486609+00:00
-- url     : https://prove2.me/submissions/2c0012a7-d675-4cb2-b2c3-0c29a795f21d

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_Plasticity_Plane_far_comparison

/-!
The pin lemma for a plane (the pins of CUB100 Proposition 5.1).

Let `‖q‖ ≤ 1`, `‖q - 2x‖ ≤ 1` and `‖q - x‖ = 1`. A functional `f` norming `q - x` has `f q = 1`
and `f x = 0`.

* If `x = 0` and `q` is extreme (type (c)), take `w = q`. The constraints give `β = t q` by (R1),
  and the far-comparison lemma gives `‖q - y‖ ≤ 1 - t`.
* Otherwise (types (a) and (b)) the face of `f` is a segment `[e, e + L d]` between extreme points,
  with `d = x` if `x ≠ 0` and `d` a kernel vector of `f` if `x = 0`; take `w = e + L d`. In the
  coordinates `v = f(v) e + g(v) d`, every `v` with `0 ≤ g v ≤ L f v` has `‖v‖ ≤ f v` (the cone
  over the face). For `y` near `b = (1 - 2t) x + t w`, both `y + e` and `q - y` lie in that cone.
  The comparison at the extreme point `-e` gives `‖y + e‖ ≥ 1 + t`, hence `f y ≥ t`, and then
  `‖q - y‖ ≤ f (q - y) = 1 - f y ≤ 1 - t`.

The lemmas `apply_le`, `apply_le_one`, `exists_eq_smul_of_apply_eq_zero`,
`exists_ne_zero_apply_eq_zero` and `mem_extremePoints_of_le` are copied from the project's solution
`Sol_Plasticity_Plane_exists_corner_of_bad`; `segment_ends` adapts its `exists_endpoints`.
-/

namespace Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_pin

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A functional is bounded by its norm times the norm of the argument. -/
theorem apply_le (ψ : StrongDual ℝ V) (y : V) : ψ y ≤ ‖ψ‖ * ‖y‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ψ.le_opNorm y)

theorem apply_le_one {ψ : StrongDual ℝ V} (hψ : ‖ψ‖ = 1) {y : V} (hy : ‖y‖ ≤ 1) : ψ y ≤ 1 := by
  have := apply_le ψ y
  rw [hψ, one_mul] at this
  linarith

/-- In a plane, the kernel of a nonzero functional is spanned by any nonzero element of it. -/
theorem exists_eq_smul_of_apply_eq_zero (hV : Module.finrank ℝ V = 2) (f : StrongDual ℝ V)
    (a r x : V) (ha : f a = 1) (hr : r ≠ 0) (hfr : f r = 0) (hfx : f x = 0) :
    ∃ μ : ℝ, x = μ • r := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set g : V →ₗ[ℝ] ℝ := (f : V →ₗ[ℝ] ℝ) with hgdef
  have hsurj : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y • a, by simp [g, ha]⟩
  have hk : Module.finrank ℝ (LinearMap.ker g) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker g
    rw [hsurj, finrank_top, Module.finrank_self, hV] at this
    omega
  have hr' : (⟨r, by simpa [g] using hfr⟩ : LinearMap.ker g) ≠ 0 := by
    intro h
    apply hr
    simpa using congrArg Subtype.val h
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ hr').1 hk ⟨x, by simpa [g] using hfx⟩
  exact ⟨μ, by simpa using (congrArg Subtype.val hμ).symm⟩

/-- In a plane, every functional vanishes at some nonzero vector. -/
theorem exists_ne_zero_apply_eq_zero (hV : Module.finrank ℝ V = 2) (f : StrongDual ℝ V) :
    ∃ r : V, r ≠ 0 ∧ f r = 0 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set g : V →ₗ[ℝ] ℝ := (f : V →ₗ[ℝ] ℝ) with hgdef
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : Module.finrank ℝ (LinearMap.range g) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range g)
  have hne : LinearMap.ker g ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot, hV] at h1
    omega
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨r, hr0, by simpa [g] using hr⟩

/-- On the line `y + ℝ r` inside the hyperplane `{h = 1}`, the last point of the ball is an
extreme point of the ball. -/
theorem mem_extremePoints_of_le (hV : Module.finrank ℝ V = 2) {h : StrongDual ℝ V}
    (hh : ‖h‖ = 1) {y r : V} (hy : h y = 1) (hr : r ≠ 0) (hhr : h r = 0) {t : ℝ}
    (ht : ‖y + t • r‖ ≤ 1) (hmax : ∀ s : ℝ, ‖y + s • r‖ ≤ 1 → s ≤ t) :
    y + t • r ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := by
  rw [mem_extremePoints]
  refine ⟨mem_closedBall_zero_iff.2 ht, ?_⟩
  intro a ha b hb hab
  rw [mem_closedBall_zero_iff] at ha hb
  obtain ⟨α, β, hα, hβ, hαβ, hp⟩ := hab
  have hpa : h a ≤ 1 := apply_le_one hh ha
  have hpb : h b ≤ 1 := apply_le_one hh hb
  have hsum : α * h a + β * h b = 1 := by
    have := congrArg h hp
    simp only [map_add, map_smul, smul_eq_mul, hy, hhr, mul_zero, add_zero] at this
    exact this
  have ha1 : h a = 1 := by nlinarith
  have hb1 : h b = 1 := by nlinarith
  obtain ⟨s, hs⟩ := exists_eq_smul_of_apply_eq_zero hV h y r (a - y) hy hr hhr
    (by simp [ha1, hy])
  obtain ⟨s', hs'⟩ := exists_eq_smul_of_apply_eq_zero hV h y r (b - y) hy hr hhr
    (by simp [hb1, hy])
  have ha' : a = y + s • r := by rw [← hs]; abel
  have hb' : b = y + s' • r := by rw [← hs']; abel
  have hsle : s ≤ t := hmax s (by rw [← ha']; exact ha)
  have hs'le : s' ≤ t := hmax s' (by rw [← hb']; exact hb)
  have heq : (α * s + β * s') • r = t • r := by
    have h3 : α • a + β • b = y + t • r := hp
    have e2 : α • a + β • b = (α + β) • y + (α * s + β * s') • r := by
      rw [ha', hb']
      module
    rw [e2, hαβ, one_smul] at h3
    exact add_left_cancel h3
  have heq' : α * s + β * s' = t := smul_left_injective ℝ hr heq
  have hαβt : α * t + β * t = t := by rw [← add_mul, hαβ, one_mul]
  have hst : s = t := by
    by_contra hne
    have hlt : s < t := lt_of_le_of_ne hsle hne
    nlinarith [mul_lt_mul_of_pos_left hlt hα, mul_le_mul_of_nonneg_left hs'le hβ.le]
  have hs't : s' = t := by
    by_contra hne
    have hlt : s' < t := lt_of_le_of_ne hs'le hne
    nlinarith [mul_lt_mul_of_pos_left hlt hβ, mul_le_mul_of_nonneg_left hsle hα.le]
  exact ⟨by rw [ha', hst], by rw [hb', hs't]⟩

/-- The face of a unit functional `h` through `y`, along a kernel direction `d`, is a segment
`[y + tM d, y + tP d]` with extreme endpoints. -/
theorem segment_ends (hV : Module.finrank ℝ V = 2) {h : StrongDual ℝ V} (hh : ‖h‖ = 1)
    {y d : V} (hy1 : ‖y‖ ≤ 1) (hy : h y = 1) (hd : d ≠ 0) (hhd : h d = 0) :
    ∃ tP tM : ℝ, tM ≤ 0 ∧ 0 ≤ tP ∧ (∀ s : ℝ, ‖y + s • d‖ ≤ 1 → tM ≤ s ∧ s ≤ tP) ∧
      y + tP • d ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) ∧
      y + tM • d ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := by
  set T : Set ℝ := {t | ‖y + t • d‖ ≤ 1} with hT
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hbound : ∀ t ∈ T, |t| ≤ 2 / ‖d‖ := by
    intro t ht
    have ht' : ‖y + t • d‖ ≤ 1 := ht
    have h2 : ‖t • d‖ ≤ 2 := by
      calc ‖t • d‖ = ‖(y + t • d) - y‖ := by congr 1; abel
        _ ≤ ‖y + t • d‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    rw [norm_smul, Real.norm_eq_abs] at h2
    rw [le_div_iff₀ hdpos]
    exact h2
  have hclosed : IsClosed T := isClosed_le (by fun_prop) continuous_const
  have h0 : (0 : ℝ) ∈ T := by simpa [hT] using hy1
  have hne : T.Nonempty := ⟨0, h0⟩
  have hbdda : BddAbove T := ⟨2 / ‖d‖, fun t ht => (le_abs_self t).trans (hbound t ht)⟩
  have hbddb : BddBelow T := ⟨-(2 / ‖d‖), fun t ht => by
    have := hbound t ht
    rw [abs_le] at this
    linarith⟩
  set tP := sSup T with htP
  set tM := sInf T with htM
  have htPT : tP ∈ T := hclosed.csSup_mem hne hbdda
  have htMT : tM ∈ T := hclosed.csInf_mem hne hbddb
  have hp : y + tP • d ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) :=
    mem_extremePoints_of_le hV hh hy hd hhd htPT (fun s hs => le_csSup hbdda hs)
  have hq : y + tM • d ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := by
    have htMT' : ‖y + tM • d‖ ≤ 1 := htMT
    have htM' : ‖y + (-tM) • (-d)‖ ≤ 1 := by simpa using htMT'
    have := mem_extremePoints_of_le hV hh hy (neg_ne_zero.2 hd) (by simp [hhd]) htM'
      (fun s hs => by
        have hs' : -s ∈ T := by
          show ‖y + (-s) • d‖ ≤ 1
          simpa using hs
        have := csInf_le hbddb hs'
        linarith)
    simpa using this
  exact ⟨tP, tM, csInf_le hbddb h0, le_csSup hbdda h0,
    fun s hs => ⟨csInf_le hbddb hs, le_csSup hbdda hs⟩, hp, hq⟩

/-- (R1) at an extreme point `w` of the unit ball. -/
theorem eq_smul_of_extreme {w : V} (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {p : V} (hp : ‖p‖ ≤ s) (hpw : ‖p - w‖ ≤ 1 - s) :
    p = s • w := by
  have hs1' : (1 - s) ≠ 0 := by linarith
  have ha : s⁻¹ • p ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le)]
    calc s⁻¹ * ‖p‖ ≤ s⁻¹ * s := by gcongr
      _ = 1 := inv_mul_cancel₀ hs0.ne'
  have hb : (1 - s)⁻¹ • (w - p) ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by linarith)),
      norm_sub_rev]
    calc (1 - s)⁻¹ * ‖p - w‖ ≤ (1 - s)⁻¹ * (1 - s) := by gcongr
      _ = 1 := inv_mul_cancel₀ hs1'
  have hseg : w ∈ openSegment ℝ (s⁻¹ • p) ((1 - s)⁻¹ • (w - p)) := by
    refine ⟨s, 1 - s, hs0, by linarith, by ring, ?_⟩
    rw [smul_smul, smul_smul, mul_inv_cancel₀ hs0.ne', mul_inv_cancel₀ hs1', one_smul, one_smul]
    abel
  have := ((mem_extremePoints.1 hw).2 _ ha _ hb hseg).1
  rw [← this, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]

/-- The extreme points of the unit ball are symmetric. -/
theorem neg_mem_extremePoints {e : V}
    (he : e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) :
    -e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := by
  rw [mem_extremePoints] at he ⊢
  refine ⟨by simpa using he.1, fun a ha b hb hab => ?_⟩
  obtain ⟨s, s', hs, hs', hss, h⟩ := hab
  have h' : e ∈ openSegment ℝ (-a) (-b) :=
    ⟨s, s', hs, hs', hss, by rw [smul_neg, smul_neg, ← neg_add, h, neg_neg]⟩
  have := he.2 (-a) (by simpa using ha) (-b) (by simpa using hb) h'
  exact ⟨by rw [← this.1, neg_neg], by rw [← this.2, neg_neg]⟩

/-- The edge pin (types (a) and (b)): `q` and `x` positioned on the face `[e, e + L d]` of `f`. -/
theorem edge_pin (hV : Module.finrank ℝ V = 2) {f : StrongDual ℝ V} (hf : ‖f‖ = 1)
    {e d q x : V} {L κ σ : ℝ} (hfe : f e = 1) (hfd : f d = 0) (hd : d ≠ 0)
    (he : e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    (hw : e + L • d ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    (hL : 0 < L) (hκ0 : 0 ≤ κ) (hκL : 2 * κ ≤ L) (hκσ : κ < σ) (hσL : σ ≤ L)
    (hσκL : σ - κ < L) (hx : x = κ • d) (hq : q = e + σ • d) :
    ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖w - (2 : ℝ) • x‖ ≤ 1 ∧
      ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → ∃ ρ > 0, ∀ β y : V,
        ‖β‖ ≤ ‖(1 - 2 * t) • x + t • w‖ → ‖β - w‖ ≤ 1 - t →
        ‖y - ((1 - 2 * t) • x + t • w)‖ < ρ →
        (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
          ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
        ‖q - y‖ ≤ 1 - t := by
  -- a second coordinate functional `g` with `g e = 0`, `g d = 1`
  obtain ⟨k, -, hkd'⟩ := exists_dual_vector ℝ d (norm_ne_zero_iff.2 hd)
  have hkd : k d ≠ 0 := by
    rw [hkd']
    exact_mod_cast norm_ne_zero_iff.2 hd
  set g : StrongDual ℝ V := (k d)⁻¹ • (k - (k e) • f) with hg
  have hge : g e = 0 := by simp [hg, hfe]
  have hgd : g d = 1 := by simp [hg, hfd, inv_mul_cancel₀ hkd]
  -- every vector is `f v • e + g v • d`
  have hdec : ∀ v : V, v = (f v) • e + (g v) • d := by
    intro v
    have hfu : f (v - (f v) • e - (g v) • d) = 0 := by simp [hfe, hfd]
    obtain ⟨μ, hμ⟩ := exists_eq_smul_of_apply_eq_zero hV f e d _ hfe hd hfd hfu
    have hgu : g (v - (f v) • e - (g v) • d) = 0 := by simp [hge, hgd]
    rw [hμ, map_smul, hgd, smul_eq_mul, mul_one] at hgu
    rw [hgu, zero_smul, sub_sub, sub_eq_zero] at hμ
    exact hμ
  -- the cone over the face `[e, e + L d]`
  have he1 : ‖e‖ ≤ 1 := mem_closedBall_zero_iff.1 he.1
  have hw1 : ‖e + L • d‖ ≤ 1 := mem_closedBall_zero_iff.1 hw.1
  have hcone : ∀ v : V, 0 ≤ g v → g v ≤ L * f v → ‖v‖ ≤ f v := by
    intro v hg0 hgL
    have e1 : (f v - g v / L) • e + (g v / L) • (e + L • d) = (f v) • e + (g v) • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ _ hL.ne', ← add_assoc, ← add_smul, sub_add_cancel]
    have ha : 0 ≤ f v - g v / L := by
      rw [sub_nonneg, div_le_iff₀ hL]; linarith
    have hb : 0 ≤ g v / L := div_nonneg hg0 hL.le
    calc ‖v‖ = ‖(f v - g v / L) • e + (g v / L) • (e + L • d)‖ := by rw [e1, ← hdec v]
      _ ≤ ‖(f v - g v / L) • e‖ + ‖(g v / L) • (e + L • d)‖ := norm_add_le _ _
      _ = (f v - g v / L) * ‖e‖ + (g v / L) * ‖e + L • d‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ (f v - g v / L) * 1 + (g v / L) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left he1 ha) (mul_le_mul_of_nonneg_left hw1 hb)
      _ = f v := by ring
  -- coordinates of the data
  have hfx : f x = 0 := by simp [hx, hfd]
  have hgx : g x = κ := by simp [hx, hgd]
  have hfq : f q = 1 := by simp [hq, hfe, hfd]
  have hgq : g q = σ := by simp [hq, hge, hgd]
  have hfw : f (e + L • d) = 1 := by simp [hfe, hfd]
  have hgw : g (e + L • d) = L := by simp [hge, hgd]
  refine ⟨e + L • d, hw, ?_, min (1 / 2) ((σ - κ) / L),
    lt_min (by norm_num) (div_pos (by linarith) hL), fun t ht0 htt => ?_⟩
  · refine (hcone _ ?_ ?_).trans ?_
    · rw [map_sub, map_smul, hgw, hgx, smul_eq_mul]; linarith
    · rw [map_sub, map_smul, map_sub, map_smul, hgw, hgx, hfw, hfx, smul_eq_mul, smul_eq_mul]
      linarith
    · rw [map_sub, map_smul, hfw, hfx, smul_eq_mul]; linarith
  have ht12 : t < 1 / 2 := lt_of_lt_of_le htt (min_le_left _ _)
  have htL : t * L < σ - κ := (lt_div_iff₀ hL).1 (lt_of_lt_of_le htt (min_le_right _ _))
  set b := (1 - 2 * t) • x + t • (e + L • d) with hb
  have hfb : f b = t := by
    rw [hb, map_add, map_smul, map_smul, hfx, hfw, smul_eq_mul, smul_eq_mul]; ring
  have hgb : g b = (1 - 2 * t) * κ + t * L := by
    rw [hb, map_add, map_smul, map_smul, hgx, hgw, smul_eq_mul, smul_eq_mul]
  -- the four slacks
  have htκ : 0 ≤ t * κ := mul_nonneg ht0.le hκ0
  have htLp : 0 < t * L := mul_pos ht0 hL
  have h12κ : 0 ≤ (1 - 2 * t) * κ := mul_nonneg (by linarith) hκ0
  have hS1 : 0 < σ - ((1 - 2 * t) * κ + t * L) := by linarith
  have hS2 : 0 < L * (1 - t) - (σ - ((1 - 2 * t) * κ + t * L)) := by
    have h1 : 0 < (L - σ + κ) * (1 - 2 * t) := mul_pos (by linarith) (by linarith)
    have h2 : 0 ≤ t * (L - σ) := mul_nonneg ht0.le (by linarith)
    linarith
  have hS3 : 0 < (1 - 2 * t) * κ + t * L := by linarith
  have hS4 : 0 < L * (1 + t) - ((1 - 2 * t) * κ + t * L) := by linarith
  set m := min (min (σ - ((1 - 2 * t) * κ + t * L))
    (L * (1 - t) - (σ - ((1 - 2 * t) * κ + t * L))))
    (min ((1 - 2 * t) * κ + t * L) (L * (1 + t) - ((1 - 2 * t) * κ + t * L))) with hm
  have hm0 : 0 < m := lt_min (lt_min hS1 hS2) (lt_min hS3 hS4)
  have hmS1 : m ≤ σ - ((1 - 2 * t) * κ + t * L) := (min_le_left _ _).trans (min_le_left _ _)
  have hmS2 : m ≤ L * (1 - t) - (σ - ((1 - 2 * t) * κ + t * L)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hmS3 : m ≤ (1 - 2 * t) * κ + t * L := (min_le_right _ _).trans (min_le_left _ _)
  have hmS4 : m ≤ L * (1 + t) - ((1 - 2 * t) * κ + t * L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hC : 0 < L + ‖g‖ + 1 := by positivity
  refine ⟨m / (L + ‖g‖ + 1), div_pos hm0 hC, fun β y hβ hβw hy hcmp => ?_⟩
  -- the coordinates of `y` are close to those of `b`
  set δ := ‖y - b‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδm : (L + ‖g‖) * δ < m := by
    have h1 : (L + ‖g‖ + 1) * δ < m := by
      rw [lt_div_iff₀ hC] at hy; linarith
    have h2 : 0 ≤ δ := hδ0
    nlinarith [norm_nonneg g]
  have hfy : |f y - t| ≤ δ := by
    have := f.le_opNorm (y - b)
    rw [hf, one_mul, Real.norm_eq_abs, map_sub, hfb] at this
    exact this
  have hgy : |g y - ((1 - 2 * t) * κ + t * L)| ≤ ‖g‖ * δ := by
    have := g.le_opNorm (y - b)
    rw [Real.norm_eq_abs, map_sub, hgb] at this
    exact this
  rw [abs_le] at hfy hgy
  have hgδ : 0 ≤ ‖g‖ * δ := mul_nonneg (norm_nonneg g) hδ0
  -- `f β ≥ t`
  have hfβ : t ≤ f β := by
    have h1 : f (e + L • d - β) ≤ 1 - t := by
      have h2 := apply_le f (e + L • d - β)
      rw [hf, one_mul, norm_sub_rev] at h2
      linarith
    rw [map_sub, hfw] at h1
    linarith
  -- the comparison at `-e` forces `f y ≥ t`
  have hcmpe := hcmp (-e) (neg_mem_extremePoints he)
  rw [sub_neg_eq_add, sub_neg_eq_add] at hcmpe
  have hβe : 1 + t ≤ ‖β + e‖ := by
    have := apply_le f (β + e)
    rw [hf, one_mul, map_add, hfe] at this
    linarith
  have hye : 1 + t ≤ ‖y + e‖ := by
    rcases le_total 1 ‖y + e‖ with h | h
    · rw [max_eq_right h] at hcmpe; linarith
    · rw [max_eq_left h] at hcmpe; linarith
  have hLδ : 0 ≤ L * δ := mul_nonneg hL.le hδ0
  have hδm' : L * δ + ‖g‖ * δ < m := by rw [← add_mul]; exact hδm
  have hLfy1 : L * (t - δ) ≤ L * f y := mul_le_mul_of_nonneg_left (by linarith) hL.le
  have hLfy2 : L * f y ≤ L * (t + δ) := mul_le_mul_of_nonneg_left (by linarith) hL.le
  have hye' : ‖y + e‖ ≤ f (y + e) := by
    refine hcone _ ?_ ?_
    · rw [map_add, hge, add_zero]; linarith
    · rw [map_add, hge, add_zero, map_add, hfe]; linarith
  rw [map_add, hfe] at hye'
  have hfyt : t ≤ f y := by linarith
  -- and then `‖q - y‖ ≤ f (q - y) = 1 - f y ≤ 1 - t`
  have hqy : ‖q - y‖ ≤ f (q - y) := by
    refine hcone _ ?_ ?_
    · rw [map_sub, hgq]; linarith
    · rw [map_sub, hgq, map_sub, hfq]; linarith
  rw [map_sub, hfq] at hqy
  linarith

end Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_pin

open Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_pin in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (q x : V)
    (hq : ‖q‖ ≤ 1) (hq2 : ‖q - (2 : ℝ) • x‖ ≤ 1) (hq1 : ‖q - x‖ = 1) :
    ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖w - (2 : ℝ) • x‖ ≤ 1 ∧
      ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → ∃ ρ > 0, ∀ β y : V,
        ‖β‖ ≤ ‖(1 - 2 * t) • x + t • w‖ → ‖β - w‖ ≤ 1 - t →
        ‖y - ((1 - 2 * t) • x + t • w)‖ < ρ →
        (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
          ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
        ‖q - y‖ ≤ 1 - t := by
  -- a functional norming `q - x`
  obtain ⟨f, hf, hfqx'⟩ := exists_dual_vector ℝ (q - x) (by rw [hq1]; exact one_ne_zero)
  have hfqx : f (q - x) = 1 := by rw [hfqx', hq1]; simp
  have h1 : f q ≤ 1 := apply_le_one hf hq
  have h2 : f (q - (2 : ℝ) • x) ≤ 1 := apply_le_one hf hq2
  rw [map_sub] at hfqx
  rw [map_sub, map_smul, smul_eq_mul] at h2
  have hfx : f x = 0 := by linarith
  have hfq : f q = 1 := by linarith
  by_cases hc : x = 0 ∧ q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)
  · -- type (c): far comparison
    obtain ⟨hx0, hqe⟩ := hc
    subst hx0
    rw [sub_zero] at hq1
    refine ⟨q, hqe, by simpa using hq, 1, one_pos, fun t ht0 ht1 => ?_⟩
    obtain ⟨ρ, hρ, hfar⟩ := Plasticity.Plane.far_comparison hV q hqe t ht0 ht1
    refine ⟨ρ, hρ, fun β y hβ hβw hy hcmp => ?_⟩
    simp only [smul_zero, zero_add] at hβ hy
    rw [norm_smul, Real.norm_of_nonneg ht0.le, hq1, mul_one] at hβ
    have hβt : β = t • q := eq_smul_of_extreme hqe ht0 ht1 hβ hβw
    have := hfar (y - t • q) hy (fun ω hω hfarω => by
      have h3 := hcmp ω hω
      rw [hβt] at h3
      have h4 : ‖t • q - ω‖ ≤ ‖y - ω‖ := by
        rcases le_total 1 ‖y - ω‖ with h | h
        · rwa [max_eq_right h] at h3
        · rw [max_eq_left h] at h3; linarith
      rwa [add_sub_cancel])
    have e1 : (1 - t) • q - (y - t • q) = q - y := by module
    rwa [e1] at this
  · -- types (a) and (b): a pin on an edge
    by_cases hx0 : x = 0
    · subst hx0
      have hqne : q ∉ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := fun h => hc ⟨rfl, h⟩
      obtain ⟨r, hr, hfr⟩ := exists_ne_zero_apply_eq_zero hV f
      obtain ⟨tP, tM, htM, htP, hall, hP, hM⟩ := segment_ends hV hf hq hfq hr hfr
      have htP0 : tP ≠ 0 := by
        rintro h; rw [h, zero_smul, add_zero] at hP; exact hqne hP
      have htM0 : tM ≠ 0 := by
        rintro h; rw [h, zero_smul, add_zero] at hM; exact hqne hM
      have htP' : 0 < tP := lt_of_le_of_ne htP (Ne.symm htP0)
      have htM' : tM < 0 := lt_of_le_of_ne htM htM0
      have hw : q + tM • r + (tP - tM) • r = q + tP • r := by module
      exact edge_pin hV hf (e := q + tM • r) (d := r) (L := tP - tM) (κ := 0) (σ := -tM)
        (by simp [hfq, hfr]) hfr hr hM (by rw [hw]; exact hP) (by linarith) le_rfl
        (by linarith) (by linarith) (by linarith) (by linarith) (by simp) (by module)
    · obtain ⟨tP, tM, htM, htP, hall, hP, hM⟩ := segment_ends hV hf hq hfq hx0 hfx
      have htM2 : tM ≤ -2 := (hall (-2) (by
        have e1 : q + (-2 : ℝ) • x = q - (2 : ℝ) • x := by module
        rw [e1]; exact hq2)).1
      have hw : q + tM • x + (tP - tM) • x = q + tP • x := by module
      exact edge_pin hV hf (e := q + tM • x) (d := x) (L := tP - tM) (κ := 1) (σ := -tM)
        (by simp [hfq, hfx]) hfx hx0 hM (by rw [hw]; exact hP) (by linarith) zero_le_one
        (by linarith) (by linarith) (by linarith) (by linarith) (by simp) (by module)
