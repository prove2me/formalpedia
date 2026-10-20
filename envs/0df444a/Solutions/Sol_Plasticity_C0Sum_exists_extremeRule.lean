-- Prove2me | solution 1 for Plasticity.C0Sum.exists_extremeRule
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:02.502214+00:00
-- url     : https://prove2.me/submissions/8e137c67-1620-45cc-a4d0-b8b721662e20

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Data.Set.Card

/-!
The extreme rule and the radial inequality for c₀ sums of scalar and non-parallelogram planar
blocks (CUB100 Lemma 4.1, Propositions 4.2–4.4(1),(3); CUB101 (2.2)).

The planar lemmas `apply_le`, `apply_le_one`, `abs_apply_le_one`,
`exists_eq_smul_of_apply_eq_zero`, `abs_add_abs_le_one`, `norm_smul_add_smul_le`,
`extremePoints_subset_of_two_le` and `encard_four_le` are copied from the project's solution
`Solutions/Sol_Plasticity_Plane_exists_corner_of_bad.lean`; the c₀-sum lemmas `norm_c0Sum_le`,
`norm_apply_le` and `finite_big` from `Solutions/Sol_Plasticity_C0Sum_isometryOn_of_support.lean`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_extremeRule

open Classical

/-! ### Planar lemmas (copied, see the header) -/

section Planar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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

end Planar

/-! ### Facts at extreme points and in source blocks -/

section Extreme

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- (M): a point within one of `w` and of `-w`, for an extreme point `w`, is zero. -/
theorem eq_zero_of_extreme {w p : V} (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    (h1 : ‖p - w‖ ≤ 1) (h2 : ‖p + w‖ ≤ 1) : p = 0 := by
  have hA : w + p ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, add_comm]; exact h2
  have hB : w - p ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, ← norm_neg, neg_sub]; exact h1
  have hseg : w ∈ openSegment ℝ (w + p) (w - p) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have := hw.2 hA hB hseg
  simpa using this

/-- (R1): if `‖p‖ ≤ s` and `‖p - w‖ ≤ 1 - s` for an extreme point `w`, then `p = s • w`. -/
theorem eq_smul_of_extreme {w p : V} (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hp : ‖p‖ ≤ s) (hpw : ‖p - w‖ ≤ 1 - s) : p = s • w := by
  rcases hs0.lt_or_eq with hs0' | hs0'
  · rcases hs1.lt_or_eq with hs1' | hs1'
    · have hA : s⁻¹ • p ∈ Metric.closedBall (0 : V) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0']
        rw [inv_mul_le_iff₀ hs0']; linarith
      have h1s : 0 < 1 - s := by linarith
      have hB : (1 - s)⁻¹ • (w - p) ∈ Metric.closedBall (0 : V) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h1s]
        rw [inv_mul_le_iff₀ h1s, ← norm_neg, neg_sub]; linarith
      have hseg : w ∈ openSegment ℝ (s⁻¹ • p) ((1 - s)⁻¹ • (w - p)) := by
        refine ⟨s, 1 - s, hs0', h1s, by ring, ?_⟩
        rw [smul_smul, smul_smul, mul_inv_cancel₀ hs0'.ne', mul_inv_cancel₀ h1s.ne', one_smul,
          one_smul]
        abel
      have h := hw.2 hA hB hseg
      calc p = s • (s⁻¹ • p) := by rw [smul_smul, mul_inv_cancel₀ hs0'.ne', one_smul]
        _ = s • w := by rw [h]
    · subst hs1'
      have : ‖p - w‖ ≤ 0 := by linarith
      rw [one_smul]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  · subst hs0'
    rw [zero_smul]
    exact norm_le_zero_iff.1 hp

theorem neg_mem_extremePoints {w : V}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) :
    -w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := by
  refine ⟨by rw [mem_closedBall_zero_iff, norm_neg]; exact mem_closedBall_zero_iff.1 hw.1, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hseg
  obtain ⟨a, b, ha, hb, hab, h⟩ := hseg
  have hA : -x₁ ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_neg]; exact mem_closedBall_zero_iff.1 hx₁
  have hB : -x₂ ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_neg]; exact mem_closedBall_zero_iff.1 hx₂
  have hseg' : w ∈ openSegment ℝ (-x₁) (-x₂) :=
    ⟨a, b, ha, hb, hab, by rw [smul_neg, smul_neg, ← neg_add, h, neg_neg]⟩
  have h1 := hw.2 hA hB hseg'
  rw [← h1, neg_neg]

theorem norm_conv_le {p q : V} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : s + t = 1) : ‖s • p + t • q‖ ≤ 1 := by
  calc ‖s • p + t • q‖ ≤ ‖s • p‖ + ‖t • q‖ := norm_add_le _ _
    _ = s * ‖p‖ + t * ‖q‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ ≤ s * 1 + t * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hst]

theorem norm_half_add_le {u v : V} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (u + v)‖ ≤ 1 := by
  rw [smul_add]
  exact norm_conv_le hu hv (by norm_num) (by norm_num) (by norm_num)

theorem norm_half_add_sub_le {u v : V} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (u + v) - u‖ ≤ 1 := by
  have := norm_half_add_le hv (show ‖-u‖ ≤ 1 by rwa [norm_neg])
  convert this using 2
  module

/-- In a scalar block or a non-parallelogram plane, for `a, p` in the ball one of `‖a - p‖`,
`‖a + p‖` is below two (CUB100 Lemma 2.1(4)). -/
theorem lt_two_or_lt_two
    (hV : Module.finrank ℝ V = 1 ∨ (Module.finrank ℝ V = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard))
    {a p : V} (ha : ‖a‖ ≤ 1) (hp : ‖p‖ ≤ 1) : ‖a - p‖ < 2 ∨ ‖a + p‖ < 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- norming functionals of `a - p` and `a + p`
  have hne1 : ‖a - p‖ ≠ 0 := by linarith
  have hne2 : ‖a + p‖ ≠ 0 := by linarith
  obtain ⟨f, hf, hfap⟩ := exists_dual_vector ℝ (a - p) hne1
  obtain ⟨h, hh, hhap⟩ := exists_dual_vector ℝ (a + p) hne2
  have hfa := abs_apply_le_one hf ha
  have hfp := abs_apply_le_one hf hp
  have hha := abs_apply_le_one hh ha
  have hhp := abs_apply_le_one hh hp
  rw [abs_le] at hfa hfp hha hhp
  have hf' : f a - f p = ‖a - p‖ := by simpa [map_sub] using hfap
  have hh' : h a + h p = ‖a + p‖ := by simpa [map_add] using hhap
  have hfa1 : f a = 1 := by linarith
  have hfp1 : f p = -1 := by linarith
  have hha1 : h a = 1 := by linarith
  have hhp1 : h p = 1 := by linarith
  rcases hV with hV | ⟨hV, hext⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hfa1
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' a ha0).1 hV p
    have e1 : f p = c * f a := by rw [← hc, map_smul, smul_eq_mul]
    have e2 : h p = c * h a := by rw [← hc, map_smul, smul_eq_mul]
    rw [hfa1, hfp1] at e1
    rw [hha1, hhp1] at e2
    linarith
  · have hsub := extremePoints_subset_of_two_le hV hf ha (by rwa [norm_neg])
      hfa1 (by rw [map_neg, hfp1, neg_neg]) (by rw [sub_neg_eq_add]; exact h2)
    have := (Set.encard_le_encard hsub).trans (encard_four_le _ _ _ _)
    exact absurd (hext.trans_le this) (lt_irrefl _)

end Extreme

/-! ### Points of c₀ sums -/

section C0

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

lemma norm_c0Sum_le {x : c0Sum E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖(x : lp E ⊤) i‖ ≤ C) :
    ‖x‖ ≤ C := by
  rw [Submodule.coe_norm]
  exact lp.norm_le_of_forall_le hC h

lemma norm_apply_le (x : c0Sum E) (i : ι) : ‖(x : lp E ⊤) i‖ ≤ ‖x‖ := by
  rw [Submodule.coe_norm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ i

lemma finite_big (x : c0Sum E) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖(x : lp E ⊤) i‖ < ε}.Finite := by
  have hx : Filter.Tendsto (fun i => ‖(x : lp E ⊤) i‖) Filter.cofinite (nhds 0) := x.2
  exact Filter.eventually_cofinite.1 (hx.eventually_lt_const hε)

lemma c0_ext {x y : c0Sum E} (h : ∀ m, (x : lp E ⊤) m = (y : lp E ⊤) m) : x = y :=
  Subtype.ext (lp.ext (funext h))

/-- The function with blocks `f m` on a finite set `S` and zero elsewhere. -/
noncomputable def ofFunFun (S : Finset ι) (f : ∀ m, E m) : ∀ m, E m :=
  fun m => if m ∈ S then f m else 0

omit [∀ i, NormedSpace ℝ (E i)] in
lemma norm_ofFunFun_le (S : Finset ι) (f : ∀ m, E m) (m : ι) :
    ‖ofFunFun S f m‖ ≤ ∑ n ∈ S, ‖f n‖ := by
  unfold ofFunFun
  split_ifs with h
  · exact Finset.single_le_sum (f := fun n => ‖f n‖) (fun n _ => norm_nonneg _) h
  · rw [norm_zero]
    exact Finset.sum_nonneg fun n _ => norm_nonneg _

omit [∀ i, NormedSpace ℝ (E i)] in
lemma memℓp_ofFunFun (S : Finset ι) (f : ∀ m, E m) : Memℓp (ofFunFun S f) ⊤ := by
  refine memℓp_infty ⟨∑ n ∈ S, ‖f n‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact norm_ofFunFun_le S f m

lemma mem_c0Sum_ofFunFun (S : Finset ι) (f : ∀ m, E m) :
    (⟨ofFunFun S f, memℓp_ofFunFun S f⟩ : lp E ⊤) ∈ c0Sum E := by
  show Filter.Tendsto (fun m => ‖ofFunFun S f m‖) Filter.cofinite (nhds 0)
  refine tendsto_nhds_of_eventually_eq ?_
  refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
  intro m hm
  by_contra h
  have h' : m ∉ S := fun h'' => h (Finset.mem_coe.2 h'')
  exact hm (by simp [ofFunFun, h'])

/-- The point of `c0Sum E` with blocks `f m` on `S` and zero elsewhere. -/
noncomputable def ofFun (S : Finset ι) (f : ∀ m, E m) : c0Sum E :=
  ⟨⟨ofFunFun S f, memℓp_ofFunFun S f⟩, mem_c0Sum_ofFunFun S f⟩

lemma ofFun_apply (S : Finset ι) (f : ∀ m, E m) (m : ι) :
    ((ofFun S f : c0Sum E) : lp E ⊤) m = if m ∈ S then f m else 0 := rfl

/-- The point of `c0Sum E` with block `a` at `j` and zero elsewhere. -/
noncomputable def sg (j : ι) (a : E j) : c0Sum E := ofFun {j} (Function.update 0 j a)

lemma sg_self (j : ι) (a : E j) : ((sg j a : c0Sum E) : lp E ⊤) j = a := by
  simp [sg, ofFun_apply]

lemma sg_ne {j m : ι} (a : E j) (h : m ≠ j) : ((sg j a : c0Sum E) : lp E ⊤) m = 0 := by
  simp [sg, ofFun_apply, h]

lemma norm_sg_le (j : ι) (a : E j) : ‖sg j a‖ ≤ ‖a‖ := by
  refine norm_c0Sum_le (norm_nonneg _) fun m => ?_
  by_cases h : m = j
  · subst h; rw [sg_self]
  · rw [sg_ne a h, norm_zero]; exact norm_nonneg _

lemma sg_mem {j : ι} {a : E j} (ha : ‖a‖ ≤ 1) : sg j a ∈ Metric.closedBall (0 : c0Sum E) 1 :=
  mem_closedBall_zero_iff.2 ((norm_sg_le j a).trans ha)

end C0

/-! ### The extreme rule -/

section Main

variable {ι κ : Type*}
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    {F : c0Sum E → c0Sum E'}
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    {σ : ι ≃ κ}
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E' ⊤) (σ i)‖ ≤ ‖(x : lp E ⊤) i‖)

include hnorm in
lemma map_block_eq_zero {x : c0Sum E} (hx : x ∈ Metric.closedBall 0 1) {m : κ}
    (h : (x : lp E ⊤) (σ.symm m) = 0) : (F x : lp E' ⊤) m = 0 := by
  have := hnorm x hx (σ.symm m)
  rw [Equiv.apply_symm_apply, h, norm_zero] at this
  exact norm_le_zero_iff.1 this

include hnorm in
lemma map_zero : F 0 = 0 := by
  refine c0_ext fun m => ?_
  rw [map_block_eq_zero hnorm (Metric.mem_closedBall_self zero_le_one) (by simp)]
  simp

include hlip in
lemma norm_block_sub_le {x x' : c0Sum E} (hx : x ∈ Metric.closedBall 0 1)
    (hx' : x' ∈ Metric.closedBall 0 1) (m : κ) :
    ‖(F x : lp E' ⊤) m - (F x' : lp E' ⊤) m‖ ≤ ‖x - x'‖ := by
  have h1 : (F x : lp E' ⊤) m - (F x' : lp E' ⊤) m = ((F x - F x' : c0Sum E') : lp E' ⊤) m := by
    simp
  rw [h1]
  refine (norm_apply_le _ m).trans ?_
  have := hlip.norm_sub_le hx hx'
  simpa using this

include hbij in
lemma exists_pre {y : c0Sum E'} (hy : y ∈ Metric.closedBall 0 1) :
    ∃ x ∈ Metric.closedBall (0 : c0Sum E) 1, F x = y :=
  hbij.surjOn hy

include hbij hlip hnorm in
/-- The separation step of CUB100 Proposition 4.2. -/
lemma eq_zero_of_near (j : ι) (l : κ) (hjl : σ j = l) {w : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    {x x' : c0Sum E} (hx : x ∈ Metric.closedBall 0 1) (hx' : x' ∈ Metric.closedBall 0 1)
    (hFx : (F x : lp E' ⊤) l = w) (hFx' : (F x' : lp E' ⊤) l = -w)
    {a : E j} (ha : ‖a‖ ≤ 1) (h1 : ‖a - (x : lp E ⊤) j‖ ≤ 1)
    (h2 : ‖a - (x' : lp E ⊤) j‖ ≤ 1) : a = 0 := by
  subst hjl
  have hz : sg j a ∈ Metric.closedBall (0 : c0Sum E) 1 := sg_mem ha
  have hnear : ∀ y ∈ Metric.closedBall (0 : c0Sum E) 1, ‖a - (y : lp E ⊤) j‖ ≤ 1 →
      ‖sg j a - y‖ ≤ 1 := by
    intro y hy hay
    refine norm_c0Sum_le zero_le_one fun m => ?_
    rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
    by_cases hm : m = j
    · subst hm; rw [sg_self]; exact hay
    · rw [sg_ne a hm, zero_sub, norm_neg]
      exact (norm_apply_le y m).trans (mem_closedBall_zero_iff.1 hy)
  have hb1 := norm_block_sub_le hlip hz hx (σ j)
  have hb2 := norm_block_sub_le hlip hz hx' (σ j)
  rw [hFx] at hb1
  rw [hFx', sub_neg_eq_add] at hb2
  have hzero : (F (sg j a) : lp E' ⊤) (σ j) = 0 :=
    eq_zero_of_extreme hw ((hb1).trans (hnear x hx h1)) ((hb2).trans (hnear x' hx' h2))
  have hFz : F (sg j a) = 0 := by
    refine c0_ext fun m => ?_
    by_cases hm : m = σ j
    · subst hm; rw [hzero]; simp
    · rw [map_block_eq_zero hnorm hz (sg_ne a ?_)]
      · simp
      · intro h
        apply hm
        rw [← h, Equiv.apply_symm_apply]
  have hz0 : sg j a = 0 :=
    hbij.injOn hz (Metric.mem_closedBall_self zero_le_one) (hFz.trans (map_zero hnorm).symm)
  rw [← sg_self j a, hz0]
  simp

include hbij hlip hnorm in
lemma block_neg (j : ι) (l : κ) (hjl : σ j = l) {w : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    {x x' : c0Sum E} (hx : x ∈ Metric.closedBall 0 1) (hx' : x' ∈ Metric.closedBall 0 1)
    (hFx : (F x : lp E' ⊤) l = w) (hFx' : (F x' : lp E' ⊤) l = -w) :
    (x' : lp E ⊤) j = -(x : lp E ⊤) j := by
  have hxj := (norm_apply_le x j).trans (mem_closedBall_zero_iff.1 hx)
  have hx'j := (norm_apply_le x' j).trans (mem_closedBall_zero_iff.1 hx')
  have h0 := eq_zero_of_near hbij hlip hnorm j l hjl hw hx hx' hFx hFx'
    (norm_half_add_le hxj hx'j) (norm_half_add_sub_le hxj hx'j)
    (by rw [add_comm]; exact norm_half_add_sub_le hx'j hxj)
  have : (x : lp E ⊤) j + (x' : lp E ⊤) j = 0 := by
    have h2 : (2 : ℝ) • ((1 / 2 : ℝ) • ((x : lp E ⊤) j + (x' : lp E ⊤) j)) = 0 := by
      rw [h0, smul_zero]
    rw [smul_smul] at h2
    norm_num at h2
    exact h2
  exact (neg_eq_of_add_eq_zero_right this).symm

include hbij hlip hnorm in
lemma block_eq (j : ι) (l : κ) (hjl : σ j = l) {w : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    {x x' : c0Sum E} (hx : x ∈ Metric.closedBall 0 1) (hx' : x' ∈ Metric.closedBall 0 1)
    (hFx : (F x : lp E' ⊤) l = w) (hFx' : (F x' : lp E' ⊤) l = w) :
    (x' : lp E ⊤) j = (x : lp E ⊤) j := by
  have hwn : ‖-w‖ ≤ 1 := by rw [norm_neg]; exact mem_closedBall_zero_iff.1 hw.1
  obtain ⟨x'', hx'', hFx''⟩ := exists_pre hbij (sg_mem (j := l) hwn)
  have h'' : (F x'' : lp E' ⊤) l = -w := by rw [hFx'', sg_self]
  have e1 := block_neg hbij hlip hnorm j l hjl hw hx hx'' hFx h''
  have e2 := block_neg hbij hlip hnorm j l hjl hw hx' hx'' hFx' h''
  rw [e1] at e2
  exact (neg_inj.1 e2).symm

include hbij hlip hnorm in
lemma block_mem_extremePoints (j : ι) (l : κ) (hjl : σ j = l) {w : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    {x : c0Sum E} (hx : x ∈ Metric.closedBall 0 1) (hFx : (F x : lp E' ⊤) l = w) :
    (x : lp E ⊤) j ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E j) 1) := by
  have hwn : ‖-w‖ ≤ 1 := by rw [norm_neg]; exact mem_closedBall_zero_iff.1 hw.1
  obtain ⟨x'', hx'', hFx''⟩ := exists_pre hbij (sg_mem (j := l) hwn)
  have h'' : (F x'' : lp E' ⊤) l = -w := by rw [hFx'', sg_self]
  have e1 := block_neg hbij hlip hnorm j l hjl hw hx hx'' hFx h''
  set κ := (x : lp E ⊤) j with hκ
  have hκD : ‖κ‖ ≤ 1 := (norm_apply_le x j).trans (mem_closedBall_zero_iff.1 hx)
  refine ⟨mem_closedBall_zero_iff.2 hκD, ?_⟩
  intro p hp q hq hseg
  obtain ⟨a, b, ha, hb, hab, hκab⟩ := hseg
  have hpD := mem_closedBall_zero_iff.1 hp
  have hqD := mem_closedBall_zero_iff.1 hq
  set c := min a b with hc
  have hc0 : 0 < c := lt_min ha hb
  have hca : c ≤ a := min_le_left a b
  have hcb : c ≤ b := min_le_right a b
  set d := c • (q - p) with hd
  have hplus : ‖d + κ‖ ≤ 1 := by
    have e : d + κ = (a - c) • p + (b + c) • q := by rw [hd, ← hκab]; module
    rw [e]
    exact norm_conv_le hpD hqD (by linarith) (by linarith) (by linarith)
  have hminus : ‖d - κ‖ ≤ 1 := by
    have e : d - κ = -((a + c) • p + (b - c) • q) := by rw [hd, ← hκab]; module
    rw [e, norm_neg]
    exact norm_conv_le hpD hqD (by linarith) (by linarith) (by linarith)
  have hdn : ‖d‖ ≤ 1 := by
    have := norm_half_add_le hplus hminus
    convert this using 2
    module
  have hd0 := eq_zero_of_near hbij hlip hnorm j l hjl hw hx hx'' hFx h'' hdn hminus
    (by rw [e1, sub_neg_eq_add]; exact hplus)
  have hqp : q = p := by
    rw [hd] at hd0
    exact (sub_eq_zero.1 ((smul_eq_zero.1 hd0).resolve_left hc0.ne'))
  rw [← hκab, hqp, ← add_smul, hab, one_smul]

include hlip hnorm in
/-- Exact rays (CUB100 Lemma 4.1). -/
lemma exact_ray (j : ι) (l : κ) (hjl : σ j = l) {w : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    {r z : c0Sum E} (hr : r ∈ Metric.closedBall 0 1) (hz : z ∈ Metric.closedBall 0 1)
    (hFr : (F r : lp E' ⊤) l = w) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hzj : ‖(z : lp E ⊤) j‖ ≤ s) (hzr : ‖z - r‖ ≤ 1 - s) : (F z : lp E' ⊤) l = s • w := by
  subst hjl
  have hp : ‖(F z : lp E' ⊤) (σ j)‖ ≤ s := (hnorm z hz j).trans hzj
  have hpw : ‖(F z : lp E' ⊤) (σ j) - w‖ ≤ 1 - s := by
    rw [← hFr]; exact (norm_block_sub_le hlip hz hr (σ j)).trans hzr
  exact eq_smul_of_extreme hw hs0 hs1 hp hpw

include hlip hnorm in
/-- Comparison with midpoint backgrounds (CUB100 Proposition 4.3). -/
lemma comparison (j : ι) (l : κ) (hjl : σ j = l) {w w' : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    (hw' : w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    {r r' : c0Sum E} (hr : r ∈ Metric.closedBall 0 1) (hr' : r' ∈ Metric.closedBall 0 1)
    (hFr : (F r : lp E' ⊤) l = w) (hFr' : (F r' : lp E' ⊤) l = w') {s₀ : ℝ} (hs₀1 : s₀ ≤ 1)
    (hbd : ∀ m, m ≠ j → ‖(r : lp E ⊤) m - (r' : lp E ⊤) m‖ ≤ 2 * (1 - s₀))
    {s s' : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₀) (hs'0 : 0 ≤ s') (hs' : s' ≤ s₀) :
    ‖s • w - s' • w'‖ ≤ ‖s • (r : lp E ⊤) j - s' • (r' : lp E ⊤) j‖ := by
  set R := (r : lp E ⊤) with hR
  set R' := (r' : lp E ⊤) with hR'
  -- the points with midpoint background and block `c` at `j`
  let bg : E j → c0Sum E := fun c =>
    (1 / 2 : ℝ) • (r + r') + sg j (c - (1 / 2 : ℝ) • (R j + R' j))
  have bg_j : ∀ c, ((bg c : c0Sum E) : lp E ⊤) j = c := by
    intro c
    simp only [bg, Submodule.coe_add, Submodule.coe_smul, lp.coeFn_add, lp.coeFn_smul,
      Pi.add_apply, Pi.smul_apply, sg_self]
    rw [← hR, ← hR']
    abel
  have bg_ne : ∀ c, ∀ m, m ≠ j →
      ((bg c : c0Sum E) : lp E ⊤) m = (1 / 2 : ℝ) • (R m + R' m) := by
    intro c m hm
    simp only [bg, Submodule.coe_add, Submodule.coe_smul, lp.coeFn_add, lp.coeFn_smul,
      Pi.add_apply, Pi.smul_apply, sg_ne _ hm, add_zero]
    rfl
  have hRn : ∀ m, ‖R m‖ ≤ 1 := fun m => (norm_apply_le r m).trans (mem_closedBall_zero_iff.1 hr)
  have hR'n : ∀ m, ‖R' m‖ ≤ 1 :=
    fun m => (norm_apply_le r' m).trans (mem_closedBall_zero_iff.1 hr')
  -- membership and distance to the base point
  have key : ∀ (ρ : c0Sum E), ρ ∈ Metric.closedBall (0 : c0Sum E) 1 →
      (∀ m, m ≠ j → ‖(1 / 2 : ℝ) • (R m + R' m) - (ρ : lp E ⊤) m‖ ≤ 1 - s₀) →
      ∀ t : ℝ, 0 ≤ t → t ≤ s₀ →
        bg (t • (ρ : lp E ⊤) j) ∈ Metric.closedBall (0 : c0Sum E) 1 ∧
        ‖bg (t • (ρ : lp E ⊤) j) - ρ‖ ≤ 1 - t ∧
        ‖((bg (t • (ρ : lp E ⊤) j) : c0Sum E) : lp E ⊤) j‖ ≤ t := by
    intro ρ hρ hother t ht0 ht
    have hρj : ‖(ρ : lp E ⊤) j‖ ≤ 1 := (norm_apply_le ρ j).trans (mem_closedBall_zero_iff.1 hρ)
    have hjt : ‖((bg (t • (ρ : lp E ⊤) j) : c0Sum E) : lp E ⊤) j‖ ≤ t := by
      rw [bg_j, norm_smul, Real.norm_of_nonneg ht0]
      calc t * ‖(ρ : lp E ⊤) j‖ ≤ t * 1 := by gcongr
        _ = t := mul_one t
    refine ⟨?_, ?_, hjt⟩
    · rw [mem_closedBall_zero_iff]
      refine norm_c0Sum_le zero_le_one fun m => ?_
      by_cases hm : m = j
      · subst hm; linarith
      · rw [bg_ne _ m hm]; exact norm_half_add_le (hRn m) (hR'n m)
    · refine norm_c0Sum_le (by linarith) fun m => ?_
      rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
      by_cases hm : m = j
      · subst hm
        rw [bg_j, show t • (ρ : lp E ⊤) m - (ρ : lp E ⊤) m = -((1 - t) • (ρ : lp E ⊤) m) by
          module, norm_neg, norm_smul, Real.norm_of_nonneg (by linarith)]
        calc (1 - t) * ‖(ρ : lp E ⊤) m‖ ≤ (1 - t) * 1 := by gcongr; linarith
          _ = 1 - t := mul_one _
      · rw [bg_ne _ m hm]; exact (hother m hm).trans (by linarith)
  have hoth : ∀ m, m ≠ j → ‖(1 / 2 : ℝ) • (R m + R' m) - R m‖ ≤ 1 - s₀ := by
    intro m hm
    have e : (1 / 2 : ℝ) • (R m + R' m) - R m = (1 / 2 : ℝ) • (R' m - R m) := by module
    rw [e, norm_smul, norm_sub_rev]
    have := hbd m hm
    norm_num
    linarith
  have hoth' : ∀ m, m ≠ j → ‖(1 / 2 : ℝ) • (R m + R' m) - R' m‖ ≤ 1 - s₀ := by
    intro m hm
    have e : (1 / 2 : ℝ) • (R m + R' m) - R' m = (1 / 2 : ℝ) • (R m - R' m) := by module
    rw [e, norm_smul]
    have := hbd m hm
    norm_num
    linarith
  obtain ⟨hz, hzr, hzj⟩ := key r hr hoth s hs0 hs
  obtain ⟨hz', hzr', hzj'⟩ := key r' hr' hoth' s' hs'0 hs'
  have hFz := exact_ray hlip hnorm j l hjl hw hr hz hFr hs0 (hs.trans hs₀1) hzj hzr
  have hFz' := exact_ray hlip hnorm j l hjl hw' hr' hz' hFr' hs'0 (hs'.trans hs₀1) hzj' hzr'
  rw [← hFz, ← hFz']
  refine (norm_block_sub_le hlip hz hz' l).trans ?_
  refine norm_c0Sum_le (norm_nonneg _) fun m => ?_
  rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
  by_cases hm : m = j
  · subst hm; rw [bg_j, bg_j]
  · rw [bg_ne _ m hm, bg_ne _ m hm, sub_self, norm_zero]; exact norm_nonneg _

include hbij hlip hnorm in
/-- The choice of one helper block (CUB100, the helpers after Proposition 4.3). -/
lemma exists_helper
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (j : ι) (l : κ) (hjl : σ j = l) {p : E j} (hp : ‖p‖ ≤ 1) :
    ∃ u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1),
      ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) l = u →
        ‖(x : lp E ⊤) j - p‖ < 2 := by
  have : FiniteDimensional ℝ (E' l) := by
    rcases hE' l with h | h
    · exact Module.finite_of_finrank_pos (by omega)
    · exact Module.finite_of_finrank_pos (by omega)
  obtain ⟨u₀, hu₀⟩ := (isCompact_closedBall (0 : E' l) 1).extremePoints_nonempty
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hu₀n : ‖u₀‖ ≤ 1 := mem_closedBall_zero_iff.1 hu₀.1
  have hu₁ := neg_mem_extremePoints hu₀
  obtain ⟨x₀, hx₀, hFx₀⟩ := exists_pre hbij (sg_mem (j := l) hu₀n)
  obtain ⟨x₁, hx₁, hFx₁⟩ := exists_pre hbij (sg_mem (j := l) (show ‖-u₀‖ ≤ 1 by
    rwa [norm_neg]))
  have h0 : (F x₀ : lp E' ⊤) l = u₀ := by rw [hFx₀, sg_self]
  have h1 : (F x₁ : lp E' ⊤) l = -u₀ := by rw [hFx₁, sg_self]
  have e := block_neg hbij hlip hnorm j l hjl hu₀ hx₀ hx₁ h0 h1
  have hx₀j := (norm_apply_le x₀ j).trans (mem_closedBall_zero_iff.1 hx₀)
  rcases lt_two_or_lt_two (hE j) hx₀j hp with h | h
  · refine ⟨u₀, hu₀, fun x hx hFx => ?_⟩
    rw [block_eq hbij hlip hnorm j l hjl hu₀ hx₀ hx h0 hFx]
    exact h
  · refine ⟨-u₀, hu₁, fun x hx hFx => ?_⟩
    rw [block_eq hbij hlip hnorm j l hjl hu₁ hx₁ hx h1 hFx, e, ← norm_neg, neg_sub, sub_neg_eq_add,
      add_comm]
    exact h

include hbij hlip hnorm in
/-- Helpers: preimages with no other block at distance two. -/
lemma exists_helpers
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (j : ι) (l : κ) (hjl : σ j = l) {w w' : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    (hw' : w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1)) :
    ∃ r ∈ Metric.closedBall (0 : c0Sum E) 1, ∃ r' ∈ Metric.closedBall (0 : c0Sum E) 1,
      (F r : lp E' ⊤) l = w ∧ (F r' : lp E' ⊤) l = w' ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
        ∀ m, m ≠ j → ‖(r : lp E ⊤) m - (r' : lp E ⊤) m‖ ≤ 2 * (1 - s₀) := by
  have hwn : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.1 hw.1
  have hw'n : ‖w'‖ ≤ 1 := mem_closedBall_zero_iff.1 hw'.1
  obtain ⟨r', hr', hFr'⟩ := exists_pre hbij (sg_mem (j := l) hw'n)
  have hr'l : (F r' : lp E' ⊤) l = w' := by rw [hFr', sg_self]
  have hr'n : ∀ m, ‖(r' : lp E ⊤) m‖ ≤ 1 :=
    fun m => (norm_apply_le r' m).trans (mem_closedBall_zero_iff.1 hr')
  -- a helper in every target block
  have hU : ∀ n : κ, ∃ u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' n) 1),
      ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) n = u →
        ‖(x : lp E ⊤) (σ.symm n) - (r' : lp E ⊤) (σ.symm n)‖ < 2 :=
    fun n => exists_helper hbij hlip hnorm hE hE' (σ.symm n) n (σ.apply_symm_apply n) (hr'n _)
  choose U hUext hUprop using hU
  set Q : Finset ι := (finite_big r' (show (0 : ℝ) < 1 / 2 by norm_num)).toFinset with hQ
  set S : Finset κ := insert l (Q.image σ) with hS
  set y : c0Sum E' := ofFun S (Function.update U l w) with hy
  have hyB : y ∈ Metric.closedBall (0 : c0Sum E') 1 := by
    rw [mem_closedBall_zero_iff]
    refine norm_c0Sum_le zero_le_one fun n => ?_
    rw [hy, ofFun_apply]
    split_ifs
    · by_cases hn : n = l
      · subst hn; rw [Function.update_self]; exact hwn
      · rw [Function.update_of_ne hn]; exact mem_closedBall_zero_iff.1 (hUext n).1
    · rw [norm_zero]; exact zero_le_one
  obtain ⟨r, hr, hFr⟩ := exists_pre hbij hyB
  have hrl : (F r : lp E' ⊤) l = w := by
    rw [hFr, hy, ofFun_apply, if_pos (Finset.mem_insert_self _ _), Function.update_self]
  have hrn : ∀ m, ‖(r : lp E ⊤) m‖ ≤ 1 :=
    fun m => (norm_apply_le r m).trans (mem_closedBall_zero_iff.1 hr)
  -- blocks of the helper set are at distance below two
  have hQlt : ∀ m ∈ Q.erase j, ‖(r : lp E ⊤) m - (r' : lp E ⊤) m‖ < 2 := by
    intro m hm
    obtain ⟨hmj, hmQ⟩ := Finset.mem_erase.1 hm
    have hσm : σ m ≠ l := by
      intro h; apply hmj; rw [← hjl] at h; exact σ.injective h
    have hFrm : (F r : lp E' ⊤) (σ m) = U (σ m) := by
      rw [hFr, hy, ofFun_apply, if_pos (Finset.mem_insert_of_mem (Finset.mem_image_of_mem σ hmQ)),
        Function.update_of_ne hσm]
    have := hUprop (σ m) r hr hFrm
    rwa [Equiv.symm_apply_apply] at this
  have hrest : ∀ m, m ∉ Q → ‖(r : lp E ⊤) m - (r' : lp E ⊤) m‖ ≤ 3 / 2 := by
    intro m hm
    have hsmall : ‖(r' : lp E ⊤) m‖ < 1 / 2 := by
      by_contra hc
      exact hm ((Set.Finite.mem_toFinset _).2 hc)
    calc ‖(r : lp E ⊤) m - (r' : lp E ⊤) m‖ ≤ ‖(r : lp E ⊤) m‖ + ‖(r' : lp E ⊤) m‖ :=
          norm_sub_le _ _
      _ ≤ 3 / 2 := by linarith [hrn m]
  obtain ⟨M, hM2, hM⟩ : ∃ M : ℝ, M < 2 ∧
      ∀ m ∈ Q.erase j, ‖(r : lp E ⊤) m - (r' : lp E ⊤) m‖ ≤ M := by
    rcases (Q.erase j).eq_empty_or_nonempty with hT | hT
    · exact ⟨0, by norm_num, fun m hm => by rw [hT] at hm; simp at hm⟩
    · obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image (Q.erase j)
        (fun m => ‖(r : lp E ⊤) m - (r' : lp E ⊤) m‖) hT
      exact ⟨_, hQlt m₀ hm₀, hmax⟩
  refine ⟨r, hr, r', hr', hrl, hr'l, 1 - max M (3 / 2) / 2, ?_, ?_, ?_⟩
  · have : max M (3 / 2) < 2 := max_lt hM2 (by norm_num)
    linarith
  · have : 0 ≤ max M (3 / 2) := (by norm_num : (0 : ℝ) ≤ 3 / 2).trans (le_max_right _ _)
    linarith
  · intro m hmj
    have e : 2 * (1 - (1 - max M (3 / 2) / 2)) = max M (3 / 2) := by ring
    rw [e]
    by_cases hmQ : m ∈ Q
    · exact (hM m (Finset.mem_erase.2 ⟨hmj, hmQ⟩)).trans (le_max_left _ _)
    · exact (hrest m hmQ).trans (le_max_right _ _)

include hbij hlip hnorm in
/-- The radial inequality for nonnegative coefficients. -/
lemma radial_nonneg
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (j : ι) (l : κ) (hjl : σ j = l) {w w' : E' l}
    (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    (hw' : w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' l) 1))
    {x x' : c0Sum E} (hx : x ∈ Metric.closedBall 0 1) (hx' : x' ∈ Metric.closedBall 0 1)
    (hFx : (F x : lp E' ⊤) l = w) (hFx' : (F x' : lp E' ⊤) l = w')
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ‖α • w + β • w'‖ ≤ ‖α • (x : lp E ⊤) j + β • (x' : lp E ⊤) j‖ := by
  have hnw' := neg_mem_extremePoints hw'
  obtain ⟨r, hr, r', hr', hFr, hFr', s₀, hs₀, hs₀1, hbd⟩ :=
    exists_helpers hbij hlip hnorm hE hE' j l hjl hw hnw'
  have hrj := block_eq hbij hlip hnorm j l hjl hw hx hr hFx hFr
  have hr'j := block_neg hbij hlip hnorm j l hjl hw' hx' hr' hFx' hFr'
  rcases (add_nonneg hα hβ).lt_or_eq with hpos | hzero
  · set t := s₀ / (α + β) with ht
    have ht0 : 0 < t := div_pos hs₀ hpos
    have htα : t * α ≤ s₀ := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith
    have htβ : t * β ≤ s₀ := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith
    have hc := comparison hlip hnorm j l hjl hw hnw' hr hr' hFr hFr' hs₀1 hbd
      (mul_nonneg ht0.le hα) htα (mul_nonneg ht0.le hβ) htβ
    rw [hrj, hr'j] at hc
    have e1 : (t * α) • w - (t * β) • -w' = t • (α • w + β • w') := by module
    have e2 : (t * α) • (x : lp E ⊤) j - (t * β) • -(x' : lp E ⊤) j =
        t • (α • (x : lp E ⊤) j + β • (x' : lp E ⊤) j) := by module
    rw [e1, e2, norm_smul, norm_smul, Real.norm_of_nonneg ht0.le] at hc
    exact le_of_mul_le_mul_left hc ht0
  · have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    simp [hα0, hβ0]

end Main

end Sol_Plasticity_C0Sum_exists_extremeRule

open Sol_Plasticity_C0Sum_exists_extremeRule in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (σ : ι ≃ κ)
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E' ⊤) (σ i)‖ ≤ ‖(x : lp E ⊤) i‖) (i : ι) :
    ∃ g : E' (σ i) → E i,
      Set.MapsTo g (Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1))
        (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)) ∧
      (∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), g (-w) = -g w) ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
        (F x : lp E' ⊤) (σ i) ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1) →
          (x : lp E ⊤) i = g ((F x : lp E' ⊤) (σ i))) ∧
      ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1),
        ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), ∀ α β : ℝ,
          ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖ := by
  -- a preimage of the point with block `w` at `σ i`
  let X : E' (σ i) → c0Sum E := fun w =>
    Function.invFunOn F (Metric.closedBall 0 1) (sg (σ i) w)
  have hX : ∀ w : E' (σ i), ‖w‖ ≤ 1 →
      X w ∈ Metric.closedBall (0 : c0Sum E) 1 ∧ (F (X w) : lp E' ⊤) (σ i) = w := by
    intro w hw
    obtain ⟨h1, h2⟩ := Function.invFunOn_pos (hbij.surjOn (sg_mem (j := σ i) hw))
    exact ⟨h1, by rw [h2, sg_self]⟩
  have hXe : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1),
      X w ∈ Metric.closedBall (0 : c0Sum E) 1 ∧ (F (X w) : lp E' ⊤) (σ i) = w :=
    fun w hw => hX w (mem_closedBall_zero_iff.1 hw.1)
  let g : E' (σ i) → E i := fun w => (X w : lp E ⊤) i
  have hodd : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), g (-w) = -g w := by
    intro w hw
    exact block_neg hbij hlip hnorm i (σ i) rfl hw (hXe w hw).1
      (hX (-w) (by rw [norm_neg]; exact mem_closedBall_zero_iff.1 hw.1)).1 (hXe w hw).2
      (hX (-w) (by rw [norm_neg]; exact mem_closedBall_zero_iff.1 hw.1)).2
  have hsgn : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), ∀ α : ℝ,
      ∃ v ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), ∃ a : ℝ, 0 ≤ a ∧
        α • w = a • v ∧ α • g w = a • g v := by
    intro w hw α
    by_cases hα : 0 ≤ α
    · exact ⟨w, hw, α, hα, rfl, rfl⟩
    · refine ⟨-w, neg_mem_extremePoints hw, -α, by linarith, by rw [neg_smul_neg], ?_⟩
      rw [hodd w hw, neg_smul_neg]
  refine ⟨g, ?_, hodd, ?_, ?_⟩
  · intro w hw
    exact block_mem_extremePoints hbij hlip hnorm i (σ i) rfl hw (hXe w hw).1 (hXe w hw).2
  · intro x hx hext
    exact block_eq hbij hlip hnorm i (σ i) rfl hext (hXe _ hext).1 hx (hXe _ hext).2 rfl
  · intro w hw w' hw' α β
    obtain ⟨v, hv, a, ha, e1, e2⟩ := hsgn w hw α
    obtain ⟨v', hv', b, hb, e3, e4⟩ := hsgn w' hw' β
    rw [e1, e2, e3, e4]
    exact radial_nonneg hbij hlip hnorm hE hE' i (σ i) rfl hv hv' (hXe v hv).1 (hXe v' hv').1
      (hXe v hv).2 (hXe v' hv').2 ha hb
