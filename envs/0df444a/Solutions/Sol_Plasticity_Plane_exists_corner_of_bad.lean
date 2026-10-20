-- Prove2me | solution 1 for Plasticity.Plane.exists_corner_of_bad
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:44.640151+00:00
-- url     : https://prove2.me/submissions/fa97f922-c162-497a-9406-02e29e1aac7d

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Topology.Order.Monotone

/-!
Bad directions of a non-parallelogram plane (CUB102(2), simplified).

The lemma `exists_eq_smul_of_apply_eq_zero` is copied from the project's solution
`Sol_Plasticity_Plane_closedBall_subset_union_two_iff`.
-/

namespace Sol_Plasticity_Plane_exists_corner_of_bad

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A functional is bounded by its norm times the norm of the argument. -/
theorem apply_le (ψ : StrongDual ℝ V) (y : V) : ψ y ≤ ‖ψ‖ * ‖y‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ψ.le_opNorm y)

theorem apply_le_one {ψ : StrongDual ℝ V} (hψ : ‖ψ‖ = 1) {y : V} (hy : ‖y‖ ≤ 1) : ψ y ≤ 1 := by
  have := apply_le ψ y
  rw [hψ, one_mul] at this
  linarith

theorem abs_apply_le_one {ψ : StrongDual ℝ V} (hψ : ‖ψ‖ = 1) {y : V} (hy : ‖y‖ ≤ 1) :
    |ψ y| ≤ 1 := by
  have := ψ.le_opNorm y
  rw [hψ, one_mul, Real.norm_eq_abs] at this
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

/-- Two functionals equal to `1` at two distinct points of a plane coincide. -/
theorem eq_of_apply_eq_one (hV : Module.finrank ℝ V = 2) {h₁ h₂ : StrongDual ℝ V} {x z : V}
    (hzx : z ≠ x) (h₂x : h₂ x = 1) (h₂z : h₂ z = 1) (h₁x : h₁ x = 1) (h₁z : h₁ z = 1) :
    h₁ = h₂ := by
  ext v
  have hr : z - x ≠ 0 := sub_ne_zero.2 hzx
  obtain ⟨c, hc⟩ := exists_eq_smul_of_apply_eq_zero hV h₂ x (z - x) (v - h₂ v • x) h₂x hr
    (by simp [h₂x, h₂z]) (by simp [h₂x])
  have := congrArg h₁ hc
  simp [h₁x, h₁z] at this
  linarith

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

theorem abs_add_abs_le_one {a b : ℝ} (h1 : |a + b| ≤ 1) (h2 : |a - b| ≤ 1) :
    |a| + |b| ≤ 1 := by
  rw [abs_le] at h1 h2
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    linarith

theorem norm_smul_add_smul_le {p q : V} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) {a b : ℝ}
    (h1 : |a + b| ≤ 1) (h2 : |a - b| ≤ 1) : ‖a • p + b • q‖ ≤ 1 := by
  have h3 := abs_add_abs_le_one h1 h2
  calc ‖a • p + b • q‖ ≤ ‖a • p‖ + ‖b • q‖ := norm_add_le _ _
    _ = |a| * ‖p‖ + |b| * ‖q‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |a| * 1 + |b| * 1 := by gcongr
    _ ≤ 1 := by linarith

/-- If a face of the ball of a plane contains two points at distance two, the ball is a
parallelogram: its extreme points are among `±p, ±q`. -/
theorem extremePoints_subset_of_two_le (hV : Module.finrank ℝ V = 2) {h : StrongDual ℝ V}
    (hh : ‖h‖ = 1) {p q : V} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hhp : h p = 1) (hhq : h q = 1)
    (hpq : 2 ≤ ‖p - q‖) :
    Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) ⊆ {p, q, -p, -q} := by
  have hpq0 : ‖p - q‖ ≠ 0 := by linarith
  have hr : p - q ≠ 0 := norm_ne_zero_iff.1 hpq0
  obtain ⟨g, hg, hgpq⟩ := exists_dual_vector ℝ (p - q) hpq0
  have hgp : g p ≤ 1 := apply_le_one hg hp
  have hgq : -1 ≤ g q := by
    have := abs_apply_le_one hg hq
    rw [abs_le] at this
    linarith
  rw [map_sub] at hgpq
  have hgpq' : g p - g q = ‖p - q‖ := by simpa using hgpq
  have hgp1 : g p = 1 := by linarith
  have hgq1 : g q = -1 := by linarith
  -- `p, q` is a basis in which `h` and `g` are the sum and difference of coordinates
  have hdec : ∀ v : V, v = ((h v + g v) / 2) • p + ((h v - g v) / 2) • q := by
    intro v
    set w := v - (((h v + g v) / 2) • p + ((h v - g v) / 2) • q) with hw
    have hhw : h w = 0 := by
      simp only [w, map_sub, map_add, map_smul, smul_eq_mul, hhp, hhq]
      ring
    obtain ⟨c, hc⟩ := exists_eq_smul_of_apply_eq_zero hV h p (p - q) w hhp hr
      (by simp [hhp, hhq]) hhw
    have hgw : g w = 0 := by
      simp only [w, map_sub, map_add, map_smul, smul_eq_mul, hgp1, hgq1]
      ring
    have hc0 : c = 0 := by
      rw [hc, map_smul, smul_eq_mul, map_sub, hgp1, hgq1] at hgw
      linarith
    have : w = 0 := by rw [hc, hc0, zero_smul]
    exact sub_eq_zero.1 this
  intro v hv
  have hvD : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.1 hv.1
  have hhv := abs_apply_le_one hh hvD
  have hgv := abs_apply_le_one hg hvD
  have hv' := hdec v
  set a := (h v + g v) / 2 with ha
  set b := (h v - g v) / 2 with hb
  have hab1 : a + b = h v := by rw [ha, hb]; ring
  have hab2 : a - b = g v := by rw [ha, hb]; ring
  -- moving `v` inside the ball along `c • p + d • q` is impossible
  have slack : ∀ c d δ : ℝ, 0 < δ → |a + δ * c + (b + δ * d)| ≤ 1 →
      |a + δ * c - (b + δ * d)| ≤ 1 → |a - δ * c + (b - δ * d)| ≤ 1 →
      |a - δ * c - (b - δ * d)| ≤ 1 → c • p + d • q = 0 := by
    intro c d δ hδ h1 h2 h3 h4
    have hA := norm_smul_add_smul_le hp hq h1 h2
    have hB := norm_smul_add_smul_le hp hq h3 h4
    have hseg : v ∈ openSegment ℝ ((a + δ * c) • p + (b + δ * d) • q)
        ((a - δ * c) • p + (b - δ * d) • q) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hv']; module⟩
    have hAv := hv.2 (mem_closedBall_zero_iff.2 hA) (mem_closedBall_zero_iff.2 hB) hseg
    have h5 : δ • (c • p + d • q) = 0 := by
      have e : δ • (c • p + d • q) = ((a + δ * c) • p + (b + δ * d) • q) - (a • p + b • q) := by
        module
      rw [e, hAv, ← hv', sub_self]
    exact (smul_eq_zero.1 h5).resolve_left hδ.ne'
  have hv1 : |h v| = 1 := by
    by_contra hne
    have hlt : |h v| < 1 := lt_of_le_of_ne hhv hne
    have h6 := slack 1 1 ((1 - |h v|) / 2) (by linarith)
      (by rw [abs_le]; constructor <;> nlinarith [le_abs_self (h v), neg_abs_le (h v)])
      (by rw [show a + (1 - |h v|) / 2 * 1 - (b + (1 - |h v|) / 2 * 1) = g v by linarith]
          exact hgv)
      (by rw [abs_le]; constructor <;> nlinarith [le_abs_self (h v), neg_abs_le (h v)])
      (by rw [show a - (1 - |h v|) / 2 * 1 - (b - (1 - |h v|) / 2 * 1) = g v by linarith]
          exact hgv)
    have := congrArg h h6
    simp [hhp, hhq] at this
  have hg1 : |g v| = 1 := by
    by_contra hne
    have hlt : |g v| < 1 := lt_of_le_of_ne hgv hne
    have h6 := slack 1 (-1) ((1 - |g v|) / 2) (by linarith)
      (by rw [show a + (1 - |g v|) / 2 * 1 + (b + (1 - |g v|) / 2 * -1) = h v by linarith]
          exact hhv)
      (by rw [abs_le]; constructor <;> nlinarith [le_abs_self (g v), neg_abs_le (g v)])
      (by rw [show a - (1 - |g v|) / 2 * 1 + (b - (1 - |g v|) / 2 * -1) = h v by linarith]
          exact hhv)
      (by rw [abs_le]; constructor <;> nlinarith [le_abs_self (g v), neg_abs_le (g v)])
    have := congrArg g h6
    simp [hgp1, hgq1] at this
  rcases (abs_eq zero_le_one).1 hv1 with H1 | H1 <;>
    rcases (abs_eq zero_le_one).1 hg1 with H2 | H2
  · have : v = p := by rw [hv', ha, hb, H1, H2]; norm_num
    simp [this]
  · have : v = q := by rw [hv', ha, hb, H1, H2]; norm_num
    simp [this]
  · have : v = -q := by rw [hv', ha, hb, H1, H2]; norm_num
    simp [this]
  · have : v = -p := by rw [hv', ha, hb, H1, H2]; norm_num
    simp [this]

theorem encard_four_le {α : Type*} (a b c d : α) : ({a, b, c, d} : Set α).encard ≤ 4 := by
  calc ({a, b, c, d} : Set α).encard ≤ ({b, c, d} : Set α).encard + 1 := Set.encard_insert_le _ _
    _ ≤ (({c, d} : Set α).encard + 1) + 1 := by gcongr; exact Set.encard_insert_le _ _
    _ ≤ ((({d} : Set α).encard + 1) + 1) + 1 := by gcongr; exact Set.encard_insert_le _ _
    _ = 4 := by rw [Set.encard_singleton]; rfl

/-- Segments between points of the ball far from `e` stay away from an extreme point near `e`. -/
theorem exists_pos_le_dist (hV : Module.finrank ℝ V = 2) {x e : V}
    (hx : x ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) (hxe : ‖x - e‖ < 1) :
    ∃ ε > 0, ∀ p q : V, ‖p‖ ≤ 1 → ‖q‖ ≤ 1 → 1 ≤ ‖p - e‖ → 1 ≤ ‖q - e‖ →
      ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → ε ≤ ‖p + μ • (q - p) - x‖ := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set C : Set V := Metric.closedBall 0 1 ∩ {z | 1 ≤ ‖z - e‖} with hCdef
  have hC : IsCompact C :=
    (isCompact_closedBall (0 : V) 1).inter_right (isClosed_le continuous_const (by fun_prop))
  set K : Set (V × V × ℝ) := C ×ˢ C ×ˢ Set.Icc 0 1 with hKdef
  have hK : IsCompact K := hC.prod (hC.prod isCompact_Icc)
  set φ : V × V × ℝ → ℝ := fun z => ‖z.1 + z.2.2 • (z.2.1 - z.1) - x‖ with hφdef
  have hφ : Continuous φ := by fun_prop
  have hmem : ∀ p q : V, ‖p‖ ≤ 1 → ‖q‖ ≤ 1 → 1 ≤ ‖p - e‖ → 1 ≤ ‖q - e‖ →
      ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → (p, q, μ) ∈ K := fun p q hp hq hpe hqe μ hμ0 hμ1 =>
    ⟨⟨mem_closedBall_zero_iff.2 hp, hpe⟩, ⟨mem_closedBall_zero_iff.2 hq, hqe⟩, hμ0, hμ1⟩
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun p q hp hq hpe hqe μ hμ0 hμ1 => ?_⟩
    have := hmem p q hp hq hpe hqe μ hμ0 hμ1
    rw [hKe] at this
    exact absurd this (Set.notMem_empty _)
  obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn hKne hφ.continuousOn
  refine ⟨φ z, ?_, fun p q hp hq hpe hqe μ hμ0 hμ1 =>
    isMinOn_iff.1 hzmin _ (hmem p q hp hq hpe hqe μ hμ0 hμ1)⟩
  obtain ⟨⟨hz1D, hz1e⟩, ⟨hz2D, hz2e⟩, hz3a, hz3b⟩ := hzK
  by_contra hle
  push Not at hle
  have h0 : φ z = 0 := le_antisymm hle (norm_nonneg _)
  have hxeq : x = z.1 + z.2.2 • (z.2.1 - z.1) := (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm
  have hseg : x ∈ segment ℝ z.1 z.2.1 :=
    ⟨1 - z.2.2, z.2.2, by linarith, hz3a, by ring, by rw [hxeq]; module⟩
  rcases (mem_extremePoints_iff_forall_segment.1 hx).2 z.1 hz1D z.2.1 hz2D hseg with h | h
  · have : (1 : ℝ) ≤ ‖z.1 - e‖ := hz1e
    rw [h] at this
    linarith
  · have : (1 : ℝ) ≤ ‖z.2.1 - e‖ := hz2e
    rw [h] at this
    linarith

/-- Radial projection of a point of the hyperplane `{f = 1}` near a unit vector `x`. -/
theorem normalize_facts {f : StrongDual ℝ V} (hf : ‖f‖ = 1) {x u : V} (hxn : ‖x‖ = 1)
    (hfx : f x = 1) (hfu : f u = 1) (hux : u ≠ x) :
    1 ≤ ‖u‖ ∧ ‖‖u‖⁻¹ • u‖ = 1 ∧ ‖‖u‖⁻¹ • u - x‖ ≤ 2 * ‖u - x‖ ∧ ‖u‖⁻¹ • u ≠ x := by
  have hn : 1 ≤ ‖u‖ := by
    have := apply_le f u
    rw [hf, one_mul, hfu] at this
    exact this
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    linarith
  have hn0 : ‖u‖ ≠ 0 := by linarith
  refine ⟨hn, norm_smul_inv_norm hu0, ?_, ?_⟩
  · have h1 : ‖‖u‖⁻¹ • u - u‖ = ‖u‖ - 1 := by
      have : ‖u‖⁻¹ • u - u = (‖u‖⁻¹ - 1) • u := by rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos]
      · field_simp
        ring
      · have : ‖u‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
        linarith
    have h2 : ‖u‖ - 1 ≤ ‖u - x‖ := by
      have := norm_sub_norm_le u x
      rw [hxn] at this
      exact this
    calc ‖‖u‖⁻¹ • u - x‖ = ‖(‖u‖⁻¹ • u - u) + (u - x)‖ := by congr 1; abel
      _ ≤ ‖‖u‖⁻¹ • u - u‖ + ‖u - x‖ := norm_add_le _ _
      _ ≤ 2 * ‖u - x‖ := by rw [h1]; linarith
  · intro h
    have h1 := congrArg f h
    rw [map_smul, smul_eq_mul, hfu, hfx, mul_one] at h1
    have h2 : ‖u‖ = 1 := by
      have := inv_inv ‖u‖
      rw [h1, inv_one] at this
      exact this.symm
    rw [h2, inv_one, one_smul] at h
    exact hux h

end Sol_Plasticity_Plane_exists_corner_of_bad

open Sol_Plasticity_Plane_exists_corner_of_bad in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2)
    (hpar : 4 < (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard)
    (e : V) (he : ‖e‖ = 1)
    (hbad : ∀ p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
      ∀ q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖p - e‖ < 1 → ‖q - e‖ < 1 → p = q) :
    ∃ x ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖x - e‖ < 1 ∧
      ∃ x₁ ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
      ∃ x₂ ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
      ∃ f₁ f₂ : StrongDual ℝ V, ‖f₁‖ = 1 ∧ ‖f₂‖ = 1 ∧ x₁ ≠ x ∧ x₂ ≠ x ∧
        f₁ x₁ = 1 ∧ f₁ x = 1 ∧ f₂ x = 1 ∧ f₂ x₂ = 1 ∧ f₁ x₂ < 1 ∧ f₂ x₁ < 1 ∧
        ‖x₂ - x‖ < 2 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set E := Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) with hE
  have hE4 : ∀ {h : StrongDual ℝ V} {p q : V}, ‖h‖ = 1 → ‖p‖ ≤ 1 → ‖q‖ ≤ 1 → h p = 1 →
      h q = 1 → 2 ≤ ‖p - q‖ → False := by
    intro h p q hh hp hq hhp hhq hpq
    have := (Set.encard_le_encard (extremePoints_subset_of_two_le hV hh hp hq hhp hhq hpq)).trans
      (encard_four_le p q (-p) (-q))
    exact absurd hpar (not_lt.2 this)
  have hED : ∀ z ∈ E, ‖z‖ ≤ 1 := fun z hz => mem_closedBall_zero_iff.1 hz.1
  -- Step 1: an extreme point near `e`, on a face through `e`.
  obtain ⟨f₀, hf₀, hf₀e⟩ := exists_dual_vector ℝ e (by rw [he]; exact one_ne_zero)
  rw [he] at hf₀e
  obtain ⟨p, hp, q, hq, hf₀p, hf₀q, μ, hμ0, hμ1, hey⟩ := exists_endpoints hV hf₀ he.le hf₀e
  have step1 : ∃ x ∈ E, ‖x - e‖ < 1 ∧ ∃ f : StrongDual ℝ V, ‖f‖ = 1 ∧ f x = 1 := by
    by_cases hpe : ‖p - e‖ < 1
    · exact ⟨p, hp, hpe, f₀, hf₀, hf₀p⟩
    by_cases hqe : ‖q - e‖ < 1
    · exact ⟨q, hq, hqe, f₀, hf₀, hf₀q⟩
    exfalso
    push Not at hpe hqe
    apply hE4 hf₀ (hED p hp) (hED q hq) hf₀p hf₀q
    have h1 : p - e = -(μ • (q - p)) := by rw [hey]; abel
    have h2 : q - e = (1 - μ) • (q - p) := by rw [hey]; module
    rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0] at hpe
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hqe
    rw [norm_sub_rev]
    nlinarith
  obtain ⟨x, hx, hxe, f, hf, hfx⟩ := step1
  have hxn : ‖x‖ = 1 :=
    le_antisymm (hED x hx) (by have := apply_le f x; rw [hf] at this; linarith)
  -- A unit vector in the kernel of `f`.
  obtain ⟨r₀, hr₀, hfr₀⟩ := exists_ne_zero_apply_eq_zero hV f
  set r := ‖r₀‖⁻¹ • r₀ with hrdef
  have hr : ‖r‖ = 1 := norm_smul_inv_norm hr₀
  have hfr : f r = 0 := by simp [r, hfr₀]
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, norm_zero] at hr
    exact zero_ne_one hr
  -- Step 2: near `x`, every unit vector lies on a face through `x`.
  obtain ⟨ε, hε, hfar⟩ := exists_pos_le_dist hV hx hxe
  have side : ∀ y : V, ‖y‖ = 1 → ‖y - x‖ < ε → y ≠ x → ∃ h : StrongDual ℝ V, ‖h‖ = 1 ∧
      h y = 1 ∧ h x = 1 ∧ ∃ z ∈ E, z ≠ x ∧ h z = 1 := by
    intro y hy hyx hne
    obtain ⟨h, hh, hhy⟩ := exists_dual_vector ℝ y (by rw [hy]; exact one_ne_zero)
    rw [hy] at hhy
    obtain ⟨p, hp, q, hq, hhp, hhq, μ, hμ0, hμ1, hyeq⟩ := exists_endpoints hV hh hy.le hhy
    by_cases hpe : ‖p - e‖ < 1
    · have hpx : p = x := hbad p hp x hx hpe hxe
      refine ⟨h, hh, hhy, hpx ▸ hhp, q, hq, ?_, hhq⟩
      rintro rfl
      apply hne
      rw [hyeq, hpx]
      simp
    by_cases hqe : ‖q - e‖ < 1
    · have hqx : q = x := hbad q hq x hx hqe hxe
      refine ⟨h, hh, hhy, hqx ▸ hhq, p, hp, ?_, hhp⟩
      rintro rfl
      apply hne
      rw [hyeq, hqx]
      simp
    exfalso
    push Not at hpe hqe
    have := hfar p q (hED p hp) (hED q hq) hpe hqe μ hμ0 hμ1
    rw [← hyeq] at this
    linarith
  -- Step 3: two unit vectors near `x` on both sides of `x` along the kernel of `f`.
  set t := ε / 4 with htdef
  have ht : 0 < t := by positivity
  set uP := x + t • r with huP
  set uM := x + (-t) • r with huM
  have hfuP : f uP = 1 := by simp [uP, hfx, hfr]
  have hfuM : f uM = 1 := by simp [uM, hfx, hfr]
  have huPx : ‖uP - x‖ = t := by simp [uP, norm_smul, hr, abs_of_pos ht]
  have huMx : ‖uM - x‖ = t := by simp [uM, norm_smul, hr, abs_of_pos ht]
  have huPne : uP ≠ x := by
    intro h
    rw [h, sub_self, norm_zero] at huPx
    linarith
  have huMne : uM ≠ x := by
    intro h
    rw [h, sub_self, norm_zero] at huMx
    linarith
  obtain ⟨hnP, hyP1, hyPx, hyPne⟩ := normalize_facts hf hxn hfx hfuP huPne
  obtain ⟨hnM, hyM1, hyMx, hyMne⟩ := normalize_facts hf hxn hfx hfuM huMne
  obtain ⟨hP, hhP, hhPy, hhPx, zP, hzP, hzPx, hhPz⟩ :=
    side _ hyP1 (by rw [huPx] at hyPx; linarith) hyPne
  obtain ⟨hM, hhM, hhMy, hhMx, zM, hzM, hzMx, hhMz⟩ :=
    side _ hyM1 (by rw [huMx] at hyMx; linarith) hyMne
  -- The two functionals differ: otherwise `x` is the midpoint of `uP` and `uM`.
  have hne : hP ≠ hM := by
    intro heq
    have hnP0 : ‖uP‖ ≠ 0 := by linarith
    have hnM0 : ‖uM‖ ≠ 0 := by linarith
    have a1 : hP uP = ‖uP‖ := by
      rw [map_smul, smul_eq_mul] at hhPy
      field_simp at hhPy
      linarith
    have a2 : hP uM = ‖uM‖ := by
      rw [heq]
      rw [map_smul, smul_eq_mul] at hhMy
      field_simp at hhMy
      linarith
    have hsum : uP + uM = (2 : ℝ) • x := by
      simp only [uP, uM]
      module
    have h2 : ‖uP‖ + ‖uM‖ = 2 := by
      rw [← a1, ← a2, ← map_add, hsum, map_smul, hhPx]
      norm_num
    have e1 : ‖uP‖ = 1 := by linarith
    have e2 : ‖uM‖ = 1 := by linarith
    have hseg : x ∈ openSegment ℝ uP uM :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by simp only [uP, uM]; module⟩
    exact huPne (hx.2 (mem_closedBall_zero_iff.2 e1.le) (mem_closedBall_zero_iff.2 e2.le) hseg)
  refine ⟨x, hx, hxe, zP, hzP, zM, hzM, hP, hM, hhP, hhM, hzPx, hzMx, hhPz, hhPx, hhMx, hhMz,
    ?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le (apply_le_one hhP (hED zM hzM)) with h | h
    · exact h
    · exact absurd (eq_of_apply_eq_one hV hzMx hhMx hhMz hhPx h) hne
  · rcases lt_or_eq_of_le (apply_le_one hhM (hED zP hzP)) with h | h
    · exact h
    · exact absurd (eq_of_apply_eq_one hV hzPx hhPx hhPz hhMx h).symm hne
  · by_contra hcon
    push Not at hcon
    exact hE4 hhM (hED zM hzM) (hED x hx) hhMz hhMx hcon
