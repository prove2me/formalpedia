-- Prove2me | solution 1 for Plasticity.Plane.norm_sub_le_one_of_lens
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:51.300832+00:00
-- url     : https://prove2.me/submissions/933b293e-9cfb-45ac-81e6-11dd5aee26a7

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
The extreme lens (CUB99(3)).

If `‖z - b‖ > 1`, the unit vector `p` in the direction of `b - z` lies within one of `b`, and a
functional `g` norming `p` is negative at `z`. The face of `g` is a segment `[P, Q]` between two
extreme points of the ball, and the chord of `b + D` on the line `{g = 1}` is at least as long
as `[P, Q]`, so it contains `P` or `Q`. The lens hypothesis at that extreme point and `g` gives
`g z ≥ 0`, a contradiction.

The lemmas `apply_le`, `apply_le_one`, `exists_eq_smul_of_apply_eq_zero`,
`exists_ne_zero_apply_eq_zero`, `mem_extremePoints_of_le` and `exists_endpoints` are copied from
the project's solution `Sol_Plasticity_Plane_exists_corner_of_bad`.
-/

namespace Sol_Plasticity_Plane_norm_sub_le_one_of_lens

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

/-- A point of the face of a unit functional lies on a segment between two extreme points of
the ball in that face. -/
theorem exists_endpoints (hV : Module.finrank ℝ V = 2) {h : StrongDual ℝ V} (hh : ‖h‖ = 1)
    {y : V} (hy1 : ‖y‖ ≤ 1) (hy : h y = 1) :
    ∃ p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
    ∃ q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
      h p = 1 ∧ h q = 1 ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ y = p + μ • (q - p) := by
  obtain ⟨r, hr, hhr⟩ := exists_ne_zero_apply_eq_zero hV h
  set T : Set ℝ := {t | ‖y + t • r‖ ≤ 1} with hT
  have hrpos : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hbound : ∀ t ∈ T, |t| ≤ 2 / ‖r‖ := by
    intro t ht
    have ht' : ‖y + t • r‖ ≤ 1 := ht
    have h2 : ‖t • r‖ ≤ 2 := by
      calc ‖t • r‖ = ‖(y + t • r) - y‖ := by congr 1; abel
        _ ≤ ‖y + t • r‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    rw [norm_smul, Real.norm_eq_abs] at h2
    rw [le_div_iff₀ hrpos]
    exact h2
  have hclosed : IsClosed T := isClosed_le (by fun_prop) continuous_const
  have h0 : (0 : ℝ) ∈ T := by simpa [hT] using hy1
  have hne : T.Nonempty := ⟨0, h0⟩
  have hbdda : BddAbove T := ⟨2 / ‖r‖, fun t ht => (le_abs_self t).trans (hbound t ht)⟩
  have hbddb : BddBelow T := ⟨-(2 / ‖r‖), fun t ht => by
    have := hbound t ht
    rw [abs_le] at this
    linarith⟩
  set tP := sSup T with htP
  set tM := sInf T with htM
  have htPT : tP ∈ T := hclosed.csSup_mem hne hbdda
  have htMT : tM ∈ T := hclosed.csInf_mem hne hbddb
  have h0P : 0 ≤ tP := le_csSup hbdda h0
  have h0M : tM ≤ 0 := csInf_le hbddb h0
  have hp : y + tP • r ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) :=
    mem_extremePoints_of_le hV hh hy hr hhr htPT (fun s hs => le_csSup hbdda hs)
  have hq : y + tM • r ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := by
    have htMT' : ‖y + tM • r‖ ≤ 1 := htMT
    have htM' : ‖y + (-tM) • (-r)‖ ≤ 1 := by simpa using htMT'
    have := mem_extremePoints_of_le hV hh hy (neg_ne_zero.2 hr) (by simp [hhr]) htM'
      (fun s hs => by
        have hs' : -s ∈ T := by
          show ‖y + (-s) • r‖ ≤ 1
          simpa using hs
        have := csInf_le hbddb hs'
        linarith)
    simpa using this
  refine ⟨_, hp, _, hq, by simp [hy, hhr], by simp [hy, hhr], ?_⟩
  rcases eq_or_lt_of_le (h0M.trans h0P) with heq | hlt
  · have htP0 : tP = 0 := by linarith
    have htM0 : tM = 0 := by linarith
    exact ⟨0, le_refl _, zero_le_one, by simp [htP0, htM0]⟩
  · refine ⟨tP / (tP - tM), div_nonneg h0P (by linarith),
      (div_le_one (by linarith)).2 (by linarith), ?_⟩
    have hμ : tP + tP / (tP - tM) * (tM - tP) = 0 := by
      have : tP - tM ≠ 0 := by linarith
      field_simp
      ring
    calc y = y + (tP + tP / (tP - tM) * (tM - tP)) • r := by rw [hμ, zero_smul, add_zero]
      _ = _ := by module

/-- The parameters of the points of a line within distance one of `c` form an interval. -/
theorem ordConnected_line (P r c : V) : Set.OrdConnected {t : ℝ | ‖P + t • r - c‖ ≤ 1} := by
  apply Set.OrdConnected.mk
  intro x hx y hy t ht
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rcases eq_or_lt_of_le (ht.1.trans ht.2) with hxy | hxy
  · have : t = x := le_antisymm (hxy ▸ ht.2) ht.1
    rw [this]; exact hx
  set θ : ℝ := (t - x) / (y - x) with hθ
  have hyx : 0 < y - x := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [ht.1]) hyx.le
  have hθ1 : θ ≤ 1 := (div_le_one hyx).2 (by linarith [ht.2])
  have ht' : t = x + θ * (y - x) := by
    rw [hθ]; field_simp; ring
  have e : P + t • r - c = (1 - θ) • (P + x • r - c) + θ • (P + y • r - c) := by
    rw [ht']; module
  rw [e]
  calc ‖(1 - θ) • (P + x • r - c) + θ • (P + y • r - c)‖
      ≤ ‖(1 - θ) • (P + x • r - c)‖ + ‖θ • (P + y • r - c)‖ := norm_add_le _ _
    _ = (1 - θ) * ‖P + x • r - c‖ + θ * ‖P + y • r - c‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg hθ0]
    _ ≤ (1 - θ) * 1 + θ * 1 := by gcongr
    _ = 1 := by ring

/-- The chord lemma: if a point of the face `[P, Q]` of a unit functional lies within one of a
point `c` of the ball, then so does `P` or `Q`. -/
theorem chord (hV : Module.finrank ℝ V = 2) {g : StrongDual ℝ V} (hg : ‖g‖ = 1)
    {P Q c y : V} (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hgP : g P = 1) (hgQ : g Q = 1)
    (hc : ‖c‖ ≤ 1) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hy : y = P + μ • (Q - P))
    (hyc : ‖y - c‖ ≤ 1) : ‖P - c‖ ≤ 1 ∨ ‖Q - c‖ ≤ 1 := by
  set r := Q - P with hrdef
  by_cases hr : r = 0
  · left
    have : y = P := by rw [hy, hr, smul_zero, add_zero]
    rwa [this] at hyc
  have hL : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hL2 : ‖r‖ ≤ 2 := (norm_sub_le Q P).trans (by linarith)
  have hgr : g r = 0 := by simp [r, hgP, hgQ]
  have hgy : g y = 1 := by simp [hy, hgP, hgr]
  set s := 1 - g c with hs
  have hs1 : s ≤ 1 := by
    have : g (y - c) ≤ 1 := apply_le_one hg hyc
    simp only [map_sub, hgy] at this
    linarith
  have hs0 : 0 ≤ s := by
    have : g c ≤ 1 := apply_le_one hg hc
    linarith
  set k := (1 - s) / ‖r‖ with hk
  have hk0 : 0 ≤ k := div_nonneg (by linarith) hL.le
  have hkr : k * ‖r‖ = 1 - s := by rw [hk]; field_simp
  -- the two ends of a long chord of `c + D` on the line `{g = 1}`
  set A := c + (s • P - k • r) with hA
  set B := c + (s • Q + k • r) with hB
  have hAc : ‖A - c‖ ≤ 1 := by
    have e : A - c = s • P - k • r := by rw [hA]; abel
    rw [e]
    calc ‖s • P - k • r‖ ≤ ‖s • P‖ + ‖k • r‖ := norm_sub_le _ _
      _ = s * ‖P‖ + k * ‖r‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs0, Real.norm_of_nonneg hk0]
      _ ≤ s * 1 + (1 - s) := by rw [hkr]; gcongr
      _ = 1 := by ring
  have hBc : ‖B - c‖ ≤ 1 := by
    have e : B - c = s • Q + k • r := by rw [hB]; abel
    rw [e]
    calc ‖s • Q + k • r‖ ≤ ‖s • Q‖ + ‖k • r‖ := norm_add_le _ _
      _ = s * ‖Q‖ + k * ‖r‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs0, Real.norm_of_nonneg hk0]
      _ ≤ s * 1 + (1 - s) := by rw [hkr]; gcongr
      _ = 1 := by ring
  obtain ⟨a, ha⟩ := exists_eq_smul_of_apply_eq_zero hV g P r (A - P) hgP hr hgr
    (by simp [hA, hgP, hgr, hs])
  have hAa : P + a • r = A := by rw [← ha]; abel
  have hBb : P + (a + s + 2 * k) • r = B := by
    have e : B = A + (s • r + (2 * k) • r) := by
      rw [hA, hB, hrdef]; module
    rw [e, ← hAa]; module
  have hT := ordConnected_line P r c
  have hTa : a ∈ {t : ℝ | ‖P + t • r - c‖ ≤ 1} := by
    show ‖P + a • r - c‖ ≤ 1
    rw [hAa]; exact hAc
  have hTμ : μ ∈ {t : ℝ | ‖P + t • r - c‖ ≤ 1} := by
    show ‖P + μ • r - c‖ ≤ 1
    rw [← hy]; exact hyc
  have hTB : a + s + 2 * k ∈ {t : ℝ | ‖P + t • r - c‖ ≤ 1} := by
    show ‖P + (a + s + 2 * k) • r - c‖ ≤ 1
    rw [hBb]; exact hBc
  rcases le_or_gt a 0 with ha0 | ha0
  · left
    have h0 := hT.out hTa hTμ ⟨ha0, hμ0⟩
    simpa using h0
  · right
    have hk1 : 1 - s ≤ 2 * k := by
      have : (1 - s) * ‖r‖ ≤ (1 - s) * 2 := by gcongr
      nlinarith
    have h1 := hT.out hTμ hTB ⟨hμ1, by linarith⟩
    simp only [Set.mem_ofPred_eq, one_smul] at h1
    rwa [hrdef, add_sub_cancel] at h1

end Sol_Plasticity_Plane_norm_sub_le_one_of_lens

open Sol_Plasticity_Plane_norm_sub_le_one_of_lens in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (b z : V) (hb : ‖b‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (hlens : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖b - w‖ ≤ 1 →
      ∀ f : StrongDual ℝ V, ‖f‖ = 1 → f w = 1 → 0 ≤ f z) :
    ‖z - b‖ ≤ 1 := by
  by_contra hn
  push Not at hn
  set n := ‖z - b‖ with hndef
  have hn0 : 0 < n := by linarith
  have hbz : ‖b - z‖ = n := norm_sub_rev b z
  -- the unit vector in the direction of `b - z`
  set p := n⁻¹ • (b - z) with hpdef
  have hp1 : ‖p‖ = 1 := by
    rw [hpdef, norm_smul, hbz, Real.norm_of_nonneg (inv_nonneg.2 hn0.le), inv_mul_cancel₀ hn0.ne']
  have hpb : ‖p - b‖ ≤ 1 := by
    have e : p - b = n⁻¹ • ((1 - n) • b - z) := by
      rw [hpdef, smul_sub, smul_sub, smul_smul, mul_sub, mul_one, inv_mul_cancel₀ hn0.ne',
        sub_smul, one_smul]
      abel
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn0.le)]
    have h1 : ‖(1 - n) • b - z‖ ≤ n := by
      calc ‖(1 - n) • b - z‖ ≤ ‖(1 - n) • b‖ + ‖z‖ := norm_sub_le _ _
        _ = (n - 1) * ‖b‖ + ‖z‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
        _ ≤ (n - 1) * 1 + 1 := by gcongr
        _ = n := by ring
    calc n⁻¹ * ‖(1 - n) • b - z‖ ≤ n⁻¹ * n := by gcongr
      _ = 1 := inv_mul_cancel₀ hn0.ne'
  obtain ⟨g, hg1, hgp'⟩ := exists_dual_vector ℝ p (by rw [hp1]; exact one_ne_zero)
  have hgp : g p = 1 := by rw [hgp', hp1]; simp
  have hgz : g z < 0 := by
    have e : g (b - z) = n := by
      have : b - z = n • p := by rw [hpdef, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
      rw [this, map_smul, smul_eq_mul, hgp, mul_one]
    have hgb : g b ≤ 1 := apply_le_one hg1 hb
    rw [map_sub] at e
    linarith
  obtain ⟨P, hP, Q, hQ, hgP, hgQ, μ, hμ0, hμ1, hpPQ⟩ := exists_endpoints hV hg1 hp1.le hgp
  have hPn : ‖P‖ ≤ 1 := mem_closedBall_zero_iff.1 hP.1
  have hQn : ‖Q‖ ≤ 1 := mem_closedBall_zero_iff.1 hQ.1
  rcases chord hV hg1 hPn hQn hgP hgQ hb hμ0 hμ1 hpPQ hpb with h | h
  · have := hlens P hP (by rw [norm_sub_rev]; exact h) g hg1 hgP
    linarith
  · have := hlens Q hQ (by rw [norm_sub_rev]; exact h) g hg1 hgQ
    linarith
