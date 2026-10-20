-- Prove2me | solution 1 for Plasticity.C0Sum.eq_zero_of_map_eq_zero.plane_cover
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:54.338724+00:00
-- url     : https://prove2.me/submissions/ce919c1f-2a2d-4ea0-8cfb-55e4b1387e0a

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Card

/-!
Strict coverage by extreme points in a non-parallelogram plane (CUB100 Lemma 2.1(3)).

For `b ≠ 0` in the ball, the unit vector `m = b / ‖b‖` lies on the face `[M, P]` of a norming
functional `f`, with extreme endpoints. If `‖P - M‖ = 2`, a functional `g` with `g P = 1`,
`g M = -1` together with `f` shows `‖a P + c M‖ = |a| + |c|`: the ball is the parallelogram with
vertices `±P, ±M`, whose only extreme points are these four, contradicting `4 < #ext`. So
`‖P - M‖ < 2`, the nearer endpoint `e` has `‖m - e‖ < 1`, and
`‖b - e‖ ≤ ‖b‖ ‖m - e‖ + (1 - ‖b‖) < 1`.

The lemmas `apply_le`, `apply_le_one`, `exists_eq_smul_of_apply_eq_zero`,
`exists_ne_zero_apply_eq_zero` and `mem_extremePoints_of_le` are copied from the project's solution
`Sol_Plasticity_Plane_exists_corner_of_bad`; `segment_ends` adapts its `exists_endpoints`.
-/

namespace Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_cover

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

/-- A face of length two forces the ball to be a parallelogram with four extreme points. -/
theorem encard_le_four (hV : Module.finrank ℝ V = 2) {f : StrongDual ℝ V} (hf : ‖f‖ = 1)
    {P M : V} (hP1 : ‖P‖ ≤ 1) (hM1 : ‖M‖ ≤ 1) (hfP : f P = 1) (hfM : f M = 1)
    (hlong : 2 ≤ ‖P - M‖) :
    (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard ≤ 4 := by
  have hPM0 : P - M ≠ 0 := by intro h; rw [h, norm_zero] at hlong; linarith
  obtain ⟨g, hg, hgPM'⟩ := exists_dual_vector ℝ (P - M) (by linarith)
  have hgPM : g (P - M) = ‖P - M‖ := by rw [hgPM']; simp
  have hgP1 : g P ≤ 1 := apply_le_one hg hP1
  have hgM1 : g (-M) ≤ 1 := apply_le_one hg (by rwa [norm_neg])
  rw [map_sub] at hgPM
  rw [map_neg] at hgM1
  have hgP : g P = 1 := by linarith
  have hgM : g M = -1 := by linarith
  have hfPM : f (P - M) = 0 := by rw [map_sub, hfP, hfM, sub_self]
  -- coordinates `v = a P + c M`
  have hdec : ∀ v : V, v = ((f v + g v) / 2) • P + ((f v - g v) / 2) • M := by
    intro v
    set u := v - ((f v + g v) / 2) • P - ((f v - g v) / 2) • M with hu
    have hfu : f u = 0 := by
      simp only [hu, map_sub, map_smul, hfP, hfM, smul_eq_mul]; ring
    have hgu : g u = 0 := by
      simp only [hu, map_sub, map_smul, hgP, hgM, smul_eq_mul]; ring
    obtain ⟨μ, hμ⟩ := exists_eq_smul_of_apply_eq_zero hV f P (P - M) u hfP hPM0 hfPM hfu
    rw [hμ, map_smul, map_sub, hgP, hgM, smul_eq_mul] at hgu
    have hμ0 : μ = 0 := by linarith
    rw [hμ0, zero_smul, hu, sub_sub, sub_eq_zero] at hμ
    exact hμ
  -- the norm in these coordinates is `|a| + |c|`
  have hnorm : ∀ a c : ℝ, ‖a • P + c • M‖ = |a| + |c| := by
    intro a c
    apply le_antisymm
    · calc ‖a • P + c • M‖ ≤ ‖a • P‖ + ‖c • M‖ := norm_add_le _ _
        _ = |a| * ‖P‖ + |c| * ‖M‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ |a| * 1 + |c| * 1 := add_le_add (mul_le_mul_of_nonneg_left hP1 (abs_nonneg a))
              (mul_le_mul_of_nonneg_left hM1 (abs_nonneg c))
        _ = |a| + |c| := by ring
    · have h1 : |a + c| ≤ ‖a • P + c • M‖ := by
        have := f.le_opNorm (a • P + c • M)
        rwa [hf, one_mul, Real.norm_eq_abs, map_add, map_smul, map_smul, hfP, hfM,
          smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this
      have h2 : |a - c| ≤ ‖a • P + c • M‖ := by
        have := g.le_opNorm (a • P + c • M)
        rwa [hg, one_mul, Real.norm_eq_abs, map_add, map_smul, map_smul, hgP, hgM,
          smul_eq_mul, smul_eq_mul, mul_one, mul_neg_one, ← sub_eq_add_neg] at this
      rcases le_total 0 a with ha | ha <;> rcases le_total 0 c with hc | hc
      · rw [abs_of_nonneg ha, abs_of_nonneg hc]; linarith [le_abs_self (a + c)]
      · rw [abs_of_nonneg ha, abs_of_nonpos hc]; linarith [le_abs_self (a - c)]
      · rw [abs_of_nonpos ha, abs_of_nonneg hc]; linarith [neg_abs_le (a - c)]
      · rw [abs_of_nonpos ha, abs_of_nonpos hc]; linarith [neg_abs_le (a + c)]
  -- an extreme point has no symmetric perturbation
  have hpert : ∀ v ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ∀ δ : V,
      ‖v + δ‖ ≤ 1 → ‖v - δ‖ ≤ 1 → δ = 0 := by
    intro v hv δ h1 h2
    have hseg : v ∈ openSegment ℝ (v + δ) (v - δ) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    have := ((mem_extremePoints.1 hv).2 _ (mem_closedBall_zero_iff.2 h1) _
      (mem_closedBall_zero_iff.2 h2) hseg).1
    have h3 : v + δ - v = 0 := by rw [this, sub_self]
    rwa [add_sub_cancel_left] at h3
  have hP0 : P ≠ 0 := by rintro rfl; simp at hfP
  have hM0 : M ≠ 0 := by rintro rfl; simp at hfM
  have hsub : Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) ⊆ {P, -P, M, -M} := by
    intro v hv
    have hv1 : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.1 hv.1
    set a := (f v + g v) / 2 with ha
    set c := (f v - g v) / 2 with hc
    have hvac : v = a • P + c • M := hdec v
    have hac : |a| + |c| ≤ 1 := by rw [← hnorm, ← hvac]; exact hv1
    by_cases ha0 : a = 0 <;> by_cases hc0 : c = 0
    · exfalso
      have := hpert v hv P (by rw [hvac, ha0, hc0]; simpa using hP1)
        (by rw [hvac, ha0, hc0]; simpa using hP1)
      exact hP0 this
    · -- `v = c M`, so `|c| = 1`
      have hc1 : |c| = 1 := by
        by_contra hne
        have hlt : |c| < 1 := lt_of_le_of_ne (by rw [ha0, abs_zero] at hac; linarith) hne
        have h1 : ‖v + (1 - |c|) • M‖ ≤ 1 := by
          rw [hvac, ha0, zero_smul, zero_add, ← add_smul, ← zero_add ((c + (1 - |c|)) • M),
            ← zero_smul ℝ P, hnorm, abs_zero, zero_add]
          rw [abs_le]; constructor <;> linarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
        have h2 : ‖v - (1 - |c|) • M‖ ≤ 1 := by
          rw [hvac, ha0, zero_smul, zero_add, ← sub_smul, ← zero_add ((c - (1 - |c|)) • M),
            ← zero_smul ℝ P, hnorm, abs_zero, zero_add]
          rw [abs_le]; constructor <;> linarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
        have := hpert v hv _ h1 h2
        rcases smul_eq_zero.1 this with h | h
        · exact hne (by linarith)
        · exact hM0 h
      rw [hvac, ha0, zero_smul, zero_add]
      rcases abs_eq (zero_le_one) |>.1 hc1 with h | h
      · rw [h, one_smul]; simp
      · rw [h, neg_one_smul]; simp
    · -- `v = a P`, so `|a| = 1`
      have ha1 : |a| = 1 := by
        by_contra hne
        have hlt : |a| < 1 := lt_of_le_of_ne (by rw [hc0, abs_zero] at hac; linarith) hne
        have h1 : ‖v + (1 - |a|) • P‖ ≤ 1 := by
          rw [hvac, hc0, zero_smul, add_zero, ← add_smul, ← add_zero ((a + (1 - |a|)) • P),
            ← zero_smul ℝ M, hnorm, abs_zero, add_zero]
          rw [abs_le]; constructor <;> linarith [abs_nonneg a, le_abs_self a, neg_abs_le a]
        have h2 : ‖v - (1 - |a|) • P‖ ≤ 1 := by
          rw [hvac, hc0, zero_smul, add_zero, ← sub_smul, ← add_zero ((a - (1 - |a|)) • P),
            ← zero_smul ℝ M, hnorm, abs_zero, add_zero]
          rw [abs_le]; constructor <;> linarith [abs_nonneg a, le_abs_self a, neg_abs_le a]
        have := hpert v hv _ h1 h2
        rcases smul_eq_zero.1 this with h | h
        · exact hne (by linarith)
        · exact hP0 h
      rw [hvac, hc0, zero_smul, add_zero]
      rcases abs_eq (zero_le_one) |>.1 ha1 with h | h
      · rw [h, one_smul]; simp
      · rw [h, neg_one_smul]; simp
    · -- both coordinates nonzero: `v` is not extreme
      exfalso
      have hapos : 0 < |a| := abs_pos.2 ha0
      have hcpos : 0 < |c| := abs_pos.2 hc0
      set δ : V := (a * |c| / 2) • P - (c * |a| / 2) • M with hδ
      have e1 : v + δ = (a * (1 + |c| / 2)) • P + (c * (1 - |a| / 2)) • M := by
        rw [hvac, hδ]; module
      have e2 : v - δ = (a * (1 - |c| / 2)) • P + (c * (1 + |a| / 2)) • M := by
        rw [hvac, hδ]; module
      have hca : |c| ≤ 1 := by linarith
      have haa : |a| ≤ 1 := by linarith
      have h1 : ‖v + δ‖ ≤ 1 := by
        rw [e1, hnorm, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + |c| / 2),
          abs_of_pos (by linarith : (0 : ℝ) < 1 - |a| / 2)]
        nlinarith
      have h2 : ‖v - δ‖ ≤ 1 := by
        rw [e2, hnorm, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - |c| / 2),
          abs_of_pos (by linarith : (0 : ℝ) < 1 + |a| / 2)]
        nlinarith
      have hδ0 := hpert v hv δ h1 h2
      have hfδ : f δ = 0 := by rw [hδ0, map_zero]
      have hgδ : g δ = 0 := by rw [hδ0, map_zero]
      rw [hδ, map_sub, map_smul, map_smul, hfP, hfM, smul_eq_mul, smul_eq_mul] at hfδ
      rw [hδ, map_sub, map_smul, map_smul, hgP, hgM, smul_eq_mul, smul_eq_mul] at hgδ
      have : a * |c| = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact ha0 h
      · exact hc0 (abs_eq_zero.1 h)
  calc (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard
      ≤ ({P, -P, M, -M} : Set V).encard := Set.encard_le_encard hsub
    _ ≤ ({-P, M, -M} : Set V).encard + 1 := Set.encard_insert_le _ _
    _ ≤ (({M, -M} : Set V).encard + 1) + 1 := by gcongr; exact Set.encard_insert_le _ _
    _ ≤ ((({-M} : Set V).encard + 1) + 1) + 1 := by gcongr; exact Set.encard_insert_le _ _
    _ = 4 := by rw [Set.encard_singleton]; rfl

end Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_cover

open Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_cover in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2)
    (h4 : 4 < (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard)
    (b : V) (hb : ‖b‖ ≤ 1) (hb0 : b ≠ 0) :
    ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖b - e‖ < 1 := by
  have hn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  set m := ‖b‖⁻¹ • b with hm
  have hm1 : ‖m‖ = 1 := by
    rw [hm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  obtain ⟨f, hf, hfm'⟩ := exists_dual_vector ℝ m (by rw [hm1]; exact one_ne_zero)
  have hfm : f m = 1 := by rw [hfm', hm1]; simp
  obtain ⟨r, hr, hfr⟩ := exists_ne_zero_apply_eq_zero hV f
  obtain ⟨tP, tM, htM, htP, -, hP, hM⟩ := segment_ends hV hf hm1.le hfm hr hfr
  have hPM : (m + tP • r) - (m + tM • r) = (tP - tM) • r := by module
  have hrn : 0 < ‖r‖ := norm_pos_iff.2 hr
  -- the face is shorter than two
  have hshort : (tP - tM) * ‖r‖ < 2 := by
    by_contra hlong
    push Not at hlong
    have := encard_le_four hV hf (mem_closedBall_zero_iff.1 hP.1) (mem_closedBall_zero_iff.1 hM.1)
      (by simp [hfm, hfr]) (by simp [hfm, hfr])
      (by rw [hPM, norm_smul, Real.norm_of_nonneg (by linarith)]; exact hlong)
    exact absurd h4 (not_lt.2 this)
  -- the nearer endpoint
  obtain ⟨e, he, hme⟩ : ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖m - e‖ < 1 := by
    rcases le_total tP (-tM) with h | h
    · refine ⟨_, hP, ?_⟩
      rw [show m - (m + tP • r) = (-tP) • r by module, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg htP]
      nlinarith
    · refine ⟨_, hM, ?_⟩
      rw [show m - (m + tM • r) = (-tM) • r by module, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      nlinarith
  refine ⟨e, he, ?_⟩
  have he1 : ‖e‖ ≤ 1 := mem_closedBall_zero_iff.1 he.1
  have e1 : b - e = ‖b‖ • (m - e) - (1 - ‖b‖) • e := by
    rw [hm, smul_sub, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]; module
  rw [e1]
  have h1 := norm_sub_le (‖b‖ • (m - e)) ((1 - ‖b‖) • e)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hn.le, Real.norm_of_nonneg (by linarith)] at h1
  have h2 := mul_lt_mul_of_pos_left hme hn
  have h3 := mul_le_mul_of_nonneg_left he1 (by linarith : (0 : ℝ) ≤ 1 - ‖b‖)
  linarith
