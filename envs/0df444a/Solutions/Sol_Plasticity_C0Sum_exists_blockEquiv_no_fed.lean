-- Prove2me | solution 1 for Plasticity.C0Sum.exists_blockEquiv_no_fed
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:57.788812+00:00
-- url     : https://prove2.me/submissions/90cb9a33-a5b5-4e9d-91bb-bc7378762f88

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn

/-!
No planar target block is fed by scalar source blocks (CUB109 §3): the extreme rule for every
source block, four patterns at blocks fed by two scalars, and the comparison with helpers.

The planar lemmas and the c₀-sum helpers are copied from the project's solutions
`Solutions/Sol_Plasticity_C0Sum_exists_extremeRule.lean` (sections Planar and Extreme, which copy
`Solutions/Sol_Plasticity_Plane_exists_corner_of_bad.lean`),
`Solutions/Sol_Plasticity_Plane_closedBall_subset_union_two_iff.lean` (`exists_norm_attained`,
`exists_ne_zero_apply_eq_zero`).
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_blockEquiv_no_fed

open Classical

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

section C0

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

lemma norm_c0Sum_le {x : c0Sum E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖(x : lp E ⊤) i‖ ≤ C) :
    ‖x‖ ≤ C := by
  rw [Submodule.coe_norm]
  exact lp.norm_le_of_forall_le hC h

lemma norm_apply_le (x : c0Sum E) (i : ι) : ‖(x : lp E ⊤) i‖ ≤ ‖x‖ := by
  rw [Submodule.coe_norm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ i

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

lemma norm_ofFun_le (S : Finset ι) (f : ∀ m, E m) (hf : ∀ m, ‖f m‖ ≤ 1) :
    ‖ofFun S f‖ ≤ 1 := by
  refine norm_c0Sum_le zero_le_one fun m => ?_
  rw [ofFun_apply]
  split_ifs
  · exact hf m
  · simp

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

end C0


section More

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

lemma sg_sub (j : ι) (a b : E j) : sg j a - sg j b = (sg j (a - b) : c0Sum E) := by
  refine c0_ext fun m => ?_
  by_cases h : m = j
  · subst h; simp [sg_self]
  · simp [sg_ne _ h]

lemma sg_zero (j : ι) : (sg j (0 : E j) : c0Sum E) = 0 :=
  c0_ext fun m => by
    by_cases h : m = j
    · subst h; simp [sg_self]
    · simp [sg_ne _ h]

lemma sg_mem {j : ι} {a : E j} (ha : ‖a‖ ≤ 1) : sg j a ∈ Metric.closedBall (0 : c0Sum E) 1 :=
  mem_closedBall_zero_iff.2 ((norm_sg_le j a).trans ha)

lemma continuous_sg (j : ι) : Continuous (sg j : E j → c0Sum E) := by
  refine (LipschitzWith.of_dist_le_mul fun a b => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, sg_sub]
  exact norm_sg_le _ _

lemma continuous_eval (m : ι) : Continuous fun x : c0Sum E => (x : lp E ⊤) m := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have := norm_apply_le (x - y) m
  simpa using this

lemma norm_sub_sg_le {z : c0Sum E} (hz : ‖z‖ ≤ 1) {k : ι} {c : E k}
    (hzc : ‖(z : lp E ⊤) k - c‖ ≤ 1) : ‖z - sg k c‖ ≤ 1 := by
  refine norm_c0Sum_le zero_le_one fun l => ?_
  by_cases hl : l = k
  · subst hl; simpa [sg_self] using hzc
  · simpa [sg_ne _ hl] using (norm_apply_le z l).trans hz

lemma finite_big (x : c0Sum E) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖(x : lp E ⊤) i‖ < ε}.Finite := by
  have hx : Filter.Tendsto (fun i => ‖(x : lp E ⊤) i‖) Filter.cofinite (nhds 0) := x.2
  exact Filter.eventually_cofinite.1 (hx.eventually_lt_const hε)

/-- A family dominated blockwise by two points of the c₀ sum is a point of it. -/
noncomputable def mk (f : ∀ k, E k) (x x' : c0Sum E)
    (hf : ∀ k, ‖f k‖ ≤ ‖(x : lp E ⊤) k‖ + ‖(x' : lp E ⊤) k‖) : c0Sum E :=
  ⟨⟨f, memℓp_infty ⟨‖x‖ + ‖x'‖, by
    rintro _ ⟨k, rfl⟩
    exact (hf k).trans (add_le_add (norm_apply_le x k) (norm_apply_le x' k))⟩⟩, by
    show Filter.Tendsto (fun k => ‖f k‖) Filter.cofinite (nhds 0)
    have h1 : Filter.Tendsto (fun k => ‖(x : lp E ⊤) k‖ + ‖(x' : lp E ⊤) k‖)
        Filter.cofinite (nhds 0) := by simpa using x.2.add x'.2
    exact squeeze_zero (fun k => norm_nonneg _) hf h1⟩

lemma mk_apply (f : ∀ k, E k) (x x' : c0Sum E)
    (hf : ∀ k, ‖f k‖ ≤ ‖(x : lp E ⊤) k‖ + ‖(x' : lp E ⊤) k‖) (k : ι) :
    ((mk f x x' hf : c0Sum E) : lp E ⊤) k = f k := rfl

/-- A point of a c₀ sum all of whose blocks are shorter than two has blocks bounded by some
`M < 2`. -/
lemma exists_bound_lt_two (d : c0Sum E) (hd : ∀ k, ‖(d : lp E ⊤) k‖ < 2) :
    ∃ M : ℝ, M < 2 ∧ 1 ≤ M ∧ ∀ k, ‖(d : lp E ⊤) k‖ ≤ M := by
  set B := (finite_big d one_pos).toFinset
  set s : NNReal := B.sup fun k => ‖(d : lp E ⊤) k‖₊
  refine ⟨max 1 (s : ℝ), max_lt one_lt_two ?_, le_max_left _ _, fun k => ?_⟩
  · by_cases hB : B.Nonempty
    · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup B hB fun k => ‖(d : lp E ⊤) k‖₊
      have hs : (s : ℝ) = ‖(d : lp E ⊤) k‖ := by simp only [s, hk, coe_nnnorm]
      rw [hs]; exact hd k
    · rw [Finset.not_nonempty_iff_eq_empty] at hB
      simp [s, hB]
  · by_cases hk : k ∈ B
    · refine le_trans ?_ (le_max_right _ _)
      have : ‖(d : lp E ⊤) k‖₊ ≤ s := Finset.le_sup (f := fun k => ‖(d : lp E ⊤) k‖₊) hk
      exact_mod_cast this
    · simp only [B, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hk
      exact hk.le.trans (le_max_left _ _)

end More

section PlaneMore

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- In finite dimensions every functional attains its norm on the closed unit ball. -/
theorem exists_norm_attained {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (ψ : StrongDual ℝ V) : ∃ z : V, ‖z‖ ≤ 1 ∧ ψ z = ‖ψ‖ := by
  have hK : IsCompact ((fun x => ‖ψ x‖) '' Metric.closedBall (0 : V) 1) :=
    (isCompact_closedBall (0 : V) 1).image (continuous_norm.comp ψ.continuous)
  have hne : ((fun x => ‖ψ x‖) '' Metric.closedBall (0 : V) 1).Nonempty :=
    ⟨_, 0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨z, hz, hzψ⟩ := hK.sSup_mem hne
  rw [ψ.sSup_unitClosedBall_eq_norm] at hzψ
  rw [mem_closedBall_zero_iff] at hz
  rcases (abs_eq (norm_nonneg ψ)).1 (by simpa [Real.norm_eq_abs] using hzψ) with h | h
  · exact ⟨z, hz, h⟩
  · exact ⟨-z, by simpa using hz, by simp [h]⟩

theorem exists_ne_zero_apply_eq_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (u : V) (hu : u ≠ 0) :
    ∃ ψ : StrongDual ℝ V, ψ ≠ 0 ∧ ψ u = 0 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hlt : (ℝ ∙ u) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have := finrank_span_singleton (K := ℝ) hu
    rw [h, finrank_top, hV] at this
    norm_num at this
  obtain ⟨g, hg, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  refine ⟨LinearMap.toContinuousLinearMap g, ?_, ?_⟩
  · intro h
    apply hg
    ext x
    simpa using congrArg (fun F : StrongDual ℝ V => F x) h
  · have : g u ∈ (ℝ ∙ u).map g :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self u)
    rw [hmap] at this
    simpa using this


lemma eq_smul_of_finrank_one (hW : Module.finrank ℝ V = 1) {e : V} (he : ‖e‖ = 1) (a : V) :
    ∃ c : ℝ, a = c • e ∧ ‖a‖ = |c| := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' e he0).1 hW a
  exact ⟨c, hc.symm, by rw [← hc, norm_smul, he, mul_one, Real.norm_eq_abs]⟩

/-- A unit vector of a line is `e` or `-e`. -/
lemma eq_or_eq_neg_of_finrank_one (hW : Module.finrank ℝ V = 1) {e : V} (he : ‖e‖ = 1) {a : V}
    (ha : ‖a‖ = 1) : a = e ∨ a = -e := by
  obtain ⟨c, rfl, hc⟩ := eq_smul_of_finrank_one hW he a
  rw [ha] at hc
  rcases abs_eq (zero_le_one) |>.1 hc.symm with h | h
  · left; rw [h, one_smul]
  · right; rw [h, neg_one_smul]

/-- The face of a norm-one functional on the ball of a finite-dimensional space contains an
extreme point of the ball. -/
lemma exists_extreme_face [FiniteDimensional ℝ V] (φ : StrongDual ℝ V) (hφ : ‖φ‖ = 1) :
    ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), φ w = 1 := by
  set A := Metric.closedBall (0 : V) 1 ∩ {v | φ v = 1}
  obtain ⟨z, hz, hφz⟩ := exists_norm_attained φ
  have hA : A.Nonempty := ⟨z, mem_closedBall_zero_iff.2 hz, by rw [Set.mem_ofPred_eq, hφz, hφ]⟩
  have hAc : IsCompact A :=
    (isCompact_closedBall 0 1).inter_right (isClosed_eq φ.continuous continuous_const)
  obtain ⟨w, hwA, hw⟩ := hAc.extremePoints_nonempty hA
  refine ⟨w, ⟨hwA.1, fun x₁ hx₁ x₂ hx₂ hseg => ?_⟩, hwA.2⟩
  have h1 := apply_le_one hφ (mem_closedBall_zero_iff.1 hx₁)
  have h2 := apply_le_one hφ (mem_closedBall_zero_iff.1 hx₂)
  obtain ⟨a, b, ha, hb, hab, hw'⟩ := hseg
  have hφw : a * φ x₁ + b * φ x₂ = 1 := by
    have := hwA.2
    rw [Set.mem_ofPred_eq, ← hw', map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact this
  have e1 : φ x₁ = 1 := by nlinarith
  have e2 : φ x₂ = 1 := by nlinarith
  exact hw ⟨hx₁, e1⟩ ⟨hx₂, e2⟩ ⟨a, b, ha, hb, hab, hw'⟩

end PlaneMore

/-! ### Extreme targets -/

section NoFed

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  {F : c0Sum E → c0Sum E'}
  (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
  (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
  {σ : ι → κ}
  (hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ n : κ,
      (∀ i, σ i = n → (x : lp E ⊤) i = 0) → (F x : lp E' ⊤) n = 0)

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

include hsupp in
lemma rec_supp {k : ι} {a : E k} (ha : ‖a‖ ≤ 1) :
    ∀ n ≠ σ k, (F (sg k a) : lp E' ⊤) n = 0 := by
  intro n hn
  refine hsupp _ (sg_mem ha) n fun i hi => ?_
  by_cases hik : i = k
  · subst hik; exact absurd hi.symm hn
  · exact sg_ne _ hik

include hlip hsupp in
/-- The norm bound (2.1): a target block is at most as long as the longest of its sources. -/
lemma norm_bound {z : c0Sum E} (hz : z ∈ Metric.closedBall (0 : c0Sum E) 1) (n : κ) {c : ℝ}
    (hc : 0 ≤ c) (hzc : ∀ i, σ i = n → ‖(z : lp E ⊤) i‖ ≤ c) : ‖(F z : lp E' ⊤) n‖ ≤ c := by
  classical
  set z' := mk (fun k => if σ k = n then 0 else (z : lp E ⊤) k) z z (fun k => by
    split_ifs
    · simp only [norm_zero]; positivity
    · linarith [norm_nonneg ((z : lp E ⊤) k)])
  have hz' : z' ∈ Metric.closedBall (0 : c0Sum E) 1 := by
    rw [mem_closedBall_zero_iff]
    refine norm_c0Sum_le zero_le_one fun k => ?_
    rw [mk_apply]
    split_ifs
    · simp
    · exact (norm_apply_le z k).trans (mem_closedBall_zero_iff.1 hz)
  have h0 : (F z' : lp E' ⊤) n = 0 := hsupp z' hz' n fun i hi => by rw [mk_apply, if_pos hi]
  have hd : ‖z - z'‖ ≤ c := by
    refine norm_c0Sum_le hc fun k => ?_
    simp only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, z', mk_apply]
    split_ifs with hk
    · simpa using hzc k hk
    · simpa using hc
  have := norm_block_sub_le hlip hz hz' n
  rw [h0, sub_zero] at this
  exact this.trans hd

include hbij hlip hsupp in
/-- The extreme rule (CUB100 Proposition 4.2, CUB109 Lemma 3.1), for every source block: the
preimages of targets with block `u` at `σ k`, `u` extreme, share their block `k`, a unit vector,
and the preimages of `-u` have its negative there. -/
lemma extreme_rule (k : ι) (m : κ) (hkm : σ k = m) {u : E' m}
    (hu : u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' m) 1))
    (hk : 0 < Module.finrank ℝ (E k)) :
    ∃ g : E k, ‖g‖ = 1 ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) m = u → (x : lp E ⊤) k = g) ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) m = -u →
        (x : lp E ⊤) k = -g) := by
  subst hkm
  have hun : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu.1
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  have hsep : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ x' ∈ Metric.closedBall (0 : c0Sum E) 1,
      (F x : lp E' ⊤) (σ k) = u → (F x' : lp E' ⊤) (σ k) = -u → ∀ a : E k, ‖a‖ ≤ 1 →
        ‖(x : lp E ⊤) k - a‖ ≤ 1 → ‖(x' : lp E ⊤) k - a‖ ≤ 1 → a = 0 := by
    intro x hx x' hx' hFx hFx' a ha h1 h2
    have hxn := mem_closedBall_zero_iff.1 hx
    have hx'n := mem_closedBall_zero_iff.1 hx'
    have f1 := (norm_block_sub_le hlip hx (sg_mem ha) (σ k)).trans (norm_sub_sg_le hxn h1)
    have f2 := (norm_block_sub_le hlip hx' (sg_mem ha) (σ k)).trans (norm_sub_sg_le hx'n h2)
    rw [hFx] at f1
    rw [hFx'] at f2
    have hp : (F (sg k a) : lp E' ⊤) (σ k) = 0 := by
      refine eq_zero_of_extreme hu (by rw [norm_sub_rev]; exact f1) ?_
      have : (F (sg k a) : lp E' ⊤) (σ k) + u = -(-u - (F (sg k a) : lp E' ⊤) (σ k)) := by abel
      rw [this, norm_neg]; exact f2
    have hFa : F (sg k a) = F (sg k 0) := by
      rw [sg_zero, hF0]
      refine c0_ext fun n => ?_
      by_cases hn : n = σ k
      · subst hn; rw [hp]; rfl
      · rw [rec_supp hsupp ha n hn]; rfl
    have := hbij.injOn (sg_mem ha) (sg_mem (by simp : ‖(0 : E k)‖ ≤ 1)) hFa
    have := congrArg (fun x : c0Sum E => (x : lp E ⊤) k) this
    simpa [sg_self] using this
  have hkey : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ x' ∈ Metric.closedBall (0 : c0Sum E) 1,
      (F x : lp E' ⊤) (σ k) = u → (F x' : lp E' ⊤) (σ k) = -u →
        (x' : lp E ⊤) k = -(x : lp E ⊤) k ∧ ‖(x : lp E ⊤) k‖ = 1 := by
    intro x hx x' hx' hFx hFx'
    have hκ := (norm_apply_le x k).trans (mem_closedBall_zero_iff.1 hx)
    have hκ' := (norm_apply_le x' k).trans (mem_closedBall_zero_iff.1 hx')
    have h1 : (x' : lp E ⊤) k = -(x : lp E ⊤) k := by
      by_contra hne
      have hs : (x : lp E ⊤) k + (x' : lp E ⊤) k ≠ 0 := by
        intro h; exact hne (eq_neg_of_add_eq_zero_right h)
      have := hsep x hx x' hx' hFx hFx' ((1 / 2 : ℝ) • ((x : lp E ⊤) k + (x' : lp E ⊤) k))
        (norm_half_add_le hκ hκ') (by
          have e : (x : lp E ⊤) k - (1 / 2 : ℝ) • ((x : lp E ⊤) k + (x' : lp E ⊤) k) =
              (1 / 2 : ℝ) • ((x : lp E ⊤) k + -(x' : lp E ⊤) k) := by module
          rw [e]; exact norm_half_add_le hκ (by rwa [norm_neg])) (by
          have e : (x' : lp E ⊤) k - (1 / 2 : ℝ) • ((x : lp E ⊤) k + (x' : lp E ⊤) k) =
              (1 / 2 : ℝ) • ((x' : lp E ⊤) k + -(x : lp E ⊤) k) := by module
          rw [e]; exact norm_half_add_le hκ' (by rwa [norm_neg]))
      exact hs ((smul_eq_zero.1 this).resolve_left (by norm_num))
    refine ⟨h1, ?_⟩
    by_contra hne
    have hlt : ‖(x : lp E ⊤) k‖ < 1 := lt_of_le_of_ne hκ hne
    obtain ⟨w₀, hw₀⟩ : ∃ w : E k, ‖w‖ = 1 := by
      have : Nontrivial (E k) := Module.nontrivial_of_finrank_pos (R := ℝ) hk
      obtain ⟨w, hw⟩ := exists_ne (0 : E k)
      exact ⟨‖w‖⁻¹ • w, by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]⟩
    set δ := 1 - ‖(x : lp E ⊤) k‖
    have hδ : 0 < δ := by simp only [δ]; linarith
    have hδn : ‖δ • w₀‖ = δ := by rw [norm_smul, hw₀, mul_one, Real.norm_of_nonneg hδ.le]
    have := hsep x hx x' hx' hFx hFx' (δ • w₀) (by rw [hδn]; simp only [δ]; linarith [norm_nonneg ((x : lp E ⊤) k)])
      ((norm_sub_le _ _).trans (by rw [hδn]; simp only [δ]; linarith))
      (by rw [h1]; refine (norm_sub_le _ _).trans ?_; rw [norm_neg, hδn]; simp only [δ]; linarith)
    have hw0 : w₀ ≠ 0 := norm_ne_zero_iff.1 (by rw [hw₀]; norm_num)
    exact smul_ne_zero hδ.ne' hw0 this
  obtain ⟨x₀, hx₀, hFx₀⟩ := hbij.surjOn (sg_mem hun)
  obtain ⟨x₁, hx₁, hFx₁⟩ := hbij.surjOn (sg_mem (show ‖-u‖ ≤ 1 by rwa [norm_neg]))
  have h₀ : (F x₀ : lp E' ⊤) (σ k) = u := by rw [hFx₀, sg_self]
  have h₁ : (F x₁ : lp E' ⊤) (σ k) = -u := by rw [hFx₁, sg_self]
  refine ⟨(x₀ : lp E ⊤) k, (hkey x₀ hx₀ x₁ hx₁ h₀ h₁).2, fun x hx hFx => ?_,
    fun x hx hFx => (hkey x₀ hx₀ x hx h₀ hFx).1⟩
  have a1 := (hkey x hx x₁ hx₁ hFx h₁).1
  have a2 := (hkey x₀ hx₀ x₁ hx₁ h₀ h₁).1
  rw [a1] at a2
  exact neg_inj.1 a2

end NoFed

section NoFed2

variable {ι κ : Type*}
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
  {F : c0Sum E → c0Sum E'}
  (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
  (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
  {σ : ι → κ}
  (hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ n : κ,
      (∀ i, σ i = n → (x : lp E ⊤) i = 0) → (F x : lp E' ⊤) n = 0)

include hbij hlip hsupp in
/-- Four patterns (CUB109 Lemma 3.2): at a planar target block fed by two scalar blocks, every
pair of unit vectors is the pattern of some extreme point. -/
lemma four_patterns {k k' : ι} (hkk : k ≠ k') {n : κ} (hk : σ k = n) (hk' : σ k' = n)
    (hdk : Module.finrank ℝ (E k) = 1) (hdk' : Module.finrank ℝ (E k') = 1)
    (hn : Module.finrank ℝ (E' n) = 2) {p : E k} {p' : E k'} (hp : ‖p‖ = 1) (hp' : ‖p'‖ = 1) :
    ∃ u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' n) 1),
      ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) n = u →
        (x : lp E ⊤) k = p ∧ (x : lp E ⊤) k' = p' := by
  have : FiniteDimensional ℝ (E' n) := Module.finite_of_finrank_eq_succ hn
  by_contra hcon
  push Not at hcon
  set E₀ := {u : E' n | u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' n) 1) ∧
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) n = u →
      (x : lp E ⊤) k = p ∧ (x : lp E ⊤) k' = -p'}
  have hsplit : ∀ u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' n) 1),
      u ∈ E₀ ∨ -u ∈ E₀ := by
    intro u hu
    obtain ⟨g, hg, hgu, hgnu⟩ := extreme_rule hbij hlip hsupp k n hk hu (by omega)
    obtain ⟨g', hg', hg'u, hg'nu⟩ := extreme_rule hbij hlip hsupp k' n hk' hu (by omega)
    rcases eq_or_eq_neg_of_finrank_one hdk hp hg with rfl | rfl <;>
    rcases eq_or_eq_neg_of_finrank_one hdk' hp' hg' with rfl | rfl
    · obtain ⟨x, hx, hFx, hne⟩ := hcon u hu
      exact absurd (hg'u x hx hFx) (hne (hgu x hx hFx))
    · exact Or.inl ⟨hu, fun x hx hFx => ⟨hgu x hx hFx, hg'u x hx hFx⟩⟩
    · refine Or.inr ⟨neg_mem_extremePoints hu, fun x hx hFx => ⟨?_, hg'nu x hx hFx⟩⟩
      rw [hgnu x hx hFx, neg_neg]
    · obtain ⟨x, hx, hFx, hne⟩ := hcon (-u) (neg_mem_extremePoints hu)
      have h1 := hgnu x hx hFx
      have h2 := hg'nu x hx hFx
      rw [neg_neg] at h1 h2
      exact (hne h1 h2).elim
  -- the open quadrant of the two scalar coordinates
  set a : (Fin 2 → ℝ) → c0Sum E := fun s => sg k (s 0 • p) + sg k' (s 1 • (-p')) with ha
  have hak : ∀ s, (a s : lp E ⊤) k = s 0 • p := by intro s; simp [ha, sg_self, sg_ne _ hkk]
  have hak' : ∀ s, (a s : lp E ⊤) k' = s 1 • (-p') := by
    intro s; simp [ha, sg_self, sg_ne _ (Ne.symm hkk)]
  have hal : ∀ s l, l ≠ k → l ≠ k' → (a s : lp E ⊤) l = 0 := by
    intro s l h1 h2; simp [ha, sg_ne _ h1, sg_ne _ h2]
  have hac : Continuous a := by
    simp only [ha]
    exact ((continuous_sg k).comp ((continuous_apply 0).smul continuous_const)).add
      ((continuous_sg k').comp ((continuous_apply 1).smul continuous_const))
  set Q : Set (Fin 2 → ℝ) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1 with hQ
  have hQo : IsOpen Q := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have hamem : ∀ s ∈ Q, a s ∈ Metric.closedBall (0 : c0Sum E) 1 := by
    intro s hs
    rw [mem_closedBall_zero_iff]
    refine norm_c0Sum_le zero_le_one fun l => ?_
    have h0 : 0 < s 0 ∧ s 0 < 1 := hs 0 (Set.mem_univ _)
    have h1 : 0 < s 1 ∧ s 1 < 1 := hs 1 (Set.mem_univ _)
    by_cases hl : l = k
    · subst hl; rw [hak, norm_smul, hp, mul_one, Real.norm_of_nonneg h0.1.le]; exact h0.2.le
    by_cases hl' : l = k'
    · subst hl'; rw [hak', norm_smul, norm_neg, hp', mul_one, Real.norm_of_nonneg h1.1.le]
      exact h1.2.le
    · rw [hal s l hl hl', norm_zero]; exact zero_le_one
  have hasupp : ∀ s ∈ Q, ∀ l ≠ n, (F (a s) : lp E' ⊤) l = 0 := by
    intro s hs l hl
    refine hsupp _ (hamem s hs) l fun i hi => ?_
    by_cases h1 : i = k
    · subst h1; exact absurd (hk.symm.trans hi) (Ne.symm hl)
    by_cases h2 : i = k'
    · subst h2; exact absurd (hk'.symm.trans hi) (Ne.symm hl)
    · exact hal s i h1 h2
  set Φ : (Fin 2 → ℝ) → E' n := fun s => (F (a s) : lp E' ⊤) n
  have hΦc : ContinuousOn Φ Q :=
    (continuous_eval n).comp_continuousOn (hlip.continuousOn.comp hac.continuousOn hamem)
  have hp0 : p ≠ 0 := norm_ne_zero_iff.1 (by rw [hp]; norm_num)
  have hp'0 : -p' ≠ 0 := neg_ne_zero.2 (norm_ne_zero_iff.1 (by rw [hp']; norm_num))
  have hΦi : Set.InjOn Φ Q := by
    intro s hs s' hs' hss
    have hF : F (a s) = F (a s') := by
      refine c0_ext fun l => ?_
      by_cases hl : l = n
      · subst hl; exact hss
      · rw [hasupp s hs l hl, hasupp s' hs' l hl]
    have haa := hbij.injOn (hamem s hs) (hamem s' hs') hF
    have e0 := congrArg (fun x : c0Sum E => (x : lp E ⊤) k) haa
    have e1 := congrArg (fun x : c0Sum E => (x : lp E ⊤) k') haa
    simp only [hak, hak'] at e0 e1
    funext i
    fin_cases i
    · exact smul_left_injective ℝ hp0 e0
    · exact smul_left_injective ℝ hp'0 e1
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = Module.finrank ℝ (E' n) := by
    rw [Module.finrank_fin_fun, hn]
  have hopen := Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq hdim Q hQo Φ hΦc hΦi
  set s₀ : Fin 2 → ℝ := fun _ => 1 / 2
  have hs₀ : s₀ ∈ Q := fun i _ => by norm_num [s₀]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen (Φ s₀) ⟨s₀, hs₀, rfl⟩
  set c := Φ s₀
  have hnear : ∀ u ∈ E₀, ∀ s ∈ Q, ‖Φ s - u‖ ≤ 1 := by
    intro u hu s hs
    obtain ⟨x, hx, hFx⟩ := hbij.surjOn (sg_mem (mem_closedBall_zero_iff.1 hu.1.1))
    have hFxn : (F x : lp E' ⊤) n = u := by rw [hFx, sg_self]
    obtain ⟨hxk, hxk'⟩ := hu.2 x hx hFxn
    have h0 : 0 < s 0 ∧ s 0 < 1 := hs 0 (Set.mem_univ _)
    have h1 : 0 < s 1 ∧ s 1 < 1 := hs 1 (Set.mem_univ _)
    have hd : ‖a s - x‖ ≤ 1 := by
      refine norm_c0Sum_le zero_le_one fun l => ?_
      simp only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
      by_cases hl : l = k
      · subst hl
        rw [hak, hxk, show s 0 • p - p = (s 0 - 1) • p by module, norm_smul, hp, mul_one, Real.norm_eq_abs,
          abs_of_neg (by linarith)]
        linarith
      by_cases hl' : l = k'
      · subst hl'
        rw [hak', hxk', show s 1 • -p' - -p' = (s 1 - 1) • -p' by module, norm_smul, norm_neg, hp', mul_one, Real.norm_eq_abs,
          abs_of_neg (by linarith)]
        linarith
      · rw [hal s l hl hl', zero_sub, norm_neg]
        exact (norm_apply_le x l).trans (mem_closedBall_zero_iff.1 hx)
    have := norm_block_sub_le hlip (hamem s hs) hx n
    rw [hFxn] at this
    exact this.trans hd
  have hpos : ∀ u ∈ E₀, ∀ φ : StrongDual ℝ (E' n), ‖φ‖ = 1 → φ u = 1 → 0 < φ c := by
    intro u hu φ hφ hφu
    have hun : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu.1.1
    have hv : c - (r / 2) • u ∈ Φ '' Q := by
      refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg (by positivity)]
      nlinarith
    obtain ⟨s, hs, hsv⟩ := hv
    have h1 := hnear u hu s hs
    rw [hsv, norm_sub_rev] at h1
    have h2 := φ.le_opNorm (u - (c - (r / 2) • u))
    rw [hφ, one_mul, Real.norm_eq_abs] at h2
    have h3 := (le_abs_self _).trans (h2.trans h1)
    rw [map_sub, map_sub, map_smul, hφu, smul_eq_mul] at h3
    linarith
  obtain ⟨φ, hφ, hφc⟩ : ∃ φ : StrongDual ℝ (E' n), ‖φ‖ = 1 ∧ φ c = 0 := by
    by_cases hc0 : c = 0
    · obtain ⟨w, hw⟩ : ∃ w : E' n, w ≠ 0 := by
        have : Nontrivial (E' n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
        exact exists_ne 0
      obtain ⟨g, hg, -⟩ := exists_dual_vector ℝ w (norm_ne_zero_iff.2 hw)
      exact ⟨g, hg, by rw [hc0, map_zero]⟩
    · obtain ⟨g, hg, hgc⟩ := exists_ne_zero_apply_eq_zero hn c hc0
      have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.2 hg
      refine ⟨‖g‖⁻¹ • g, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgn], ?_⟩
      rw [ContinuousLinearMap.smul_apply, hgc, smul_zero]
  obtain ⟨w, hw, hφw⟩ := exists_extreme_face φ hφ
  rcases hsplit w hw with h | h
  · have := hpos w h φ hφ hφw
    rw [hφc] at this
    exact lt_irrefl _ this
  · have := hpos (-w) h (-φ) (by rw [norm_neg, hφ])
      (by rw [ContinuousLinearMap.neg_apply, map_neg, hφw, neg_neg])
    rw [ContinuousLinearMap.neg_apply, hφc, neg_zero] at this
    exact lt_irrefl _ this

include hbij hlip hsupp in
/-- Helpers (CUB100 Proposition 4.3, CUB109 Proposition 3.3): an extreme point of a target block
whose preimages stay away from distance two of `q'` at every source block of norm one. -/
lemma exists_helper
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hplane : ∀ i, Module.finrank ℝ (E i) = 2 → ∀ k, σ k = σ i → k = i)
    (hscal : ∀ h h', Module.finrank ℝ (E' (σ h)) = 1 → σ h' = σ h → h' = h)
    (hthree : ∀ a b c, σ a = σ b → σ a = σ c → a = b ∨ a = c ∨ b = c)
    {q' : c0Sum E} (n : κ) (hfin : Module.finrank ℝ (E' n) = 1 ∨ Module.finrank ℝ (E' n) = 2) :
    ∃ u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' n) 1),
      ∀ k, σ k = n → ‖(q' : lp E ⊤) k‖ = 1 → ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
        (F x : lp E' ⊤) n = u → ‖(x : lp E ⊤) k - (q' : lp E ⊤) k‖ < 2 := by
  have : FiniteDimensional ℝ (E' n) :=
    Module.finite_of_finrank_pos (by rcases hfin with h | h <;> omega)
  have hposE : ∀ i, 0 < Module.finrank ℝ (E i) := fun i => by
    rcases hE i with h | ⟨h, _⟩ <;> omega
  obtain ⟨u₀, hu₀⟩ := (isCompact_closedBall (0 : E' n) 1).extremePoints_nonempty
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  by_cases hA : ∃ k k', k ≠ k' ∧ σ k = n ∧ σ k' = n ∧ ‖(q' : lp E ⊤) k‖ = 1 ∧
      ‖(q' : lp E ⊤) k'‖ = 1
  · obtain ⟨k, k', hkk, hk, hk', hq, hq'⟩ := hA
    have hdk : Module.finrank ℝ (E k) = 1 := by
      rcases hE k with h | ⟨h, _⟩
      · exact h
      · exact absurd (hplane k h k' (hk'.trans hk.symm)) (Ne.symm hkk)
    have hdk' : Module.finrank ℝ (E k') = 1 := by
      rcases hE k' with h | ⟨h, _⟩
      · exact h
      · exact absurd (hplane k' h k (hk.trans hk'.symm)) hkk
    have hn2 : Module.finrank ℝ (E' n) = 2 := by
      rcases hfin with h | h
      · exact absurd (hscal k k' (by rw [hk]; exact h) (hk'.trans hk.symm)) (Ne.symm hkk)
      · exact h
    obtain ⟨u, hu, hpat⟩ := four_patterns hbij hlip hsupp hkk hk hk' hdk hdk' hn2 hq hq'
    refine ⟨u, hu, fun i hi _ x hx hFx => ?_⟩
    rcases hthree k k' i (hk.trans hk'.symm) (hk.trans hi.symm) with h | h | h
    · exact absurd h hkk
    · subst h; rw [(hpat x hx hFx).1, sub_self, norm_zero]; norm_num
    · subst h; rw [(hpat x hx hFx).2, sub_self, norm_zero]; norm_num
  push Not at hA
  by_cases hB : ∃ k, σ k = n ∧ ‖(q' : lp E ⊤) k‖ = 1
  · obtain ⟨k, hk, hq⟩ := hB
    obtain ⟨g, hg, hgu, hgnu⟩ := extreme_rule hbij hlip hsupp k n hk hu₀ (hposE k)
    have huniq : ∀ i, σ i = n → ‖(q' : lp E ⊤) i‖ = 1 → i = k := fun i hi hqi => by
      by_contra h; exact hA i k h hi hk hqi hq
    rcases lt_two_or_lt_two (hE k) hg.le hq.le with h | h
    · refine ⟨u₀, hu₀, fun i hi hqi x hx hFx => ?_⟩
      obtain rfl := huniq i hi hqi
      rw [hgu x hx hFx]; exact h
    · refine ⟨-u₀, neg_mem_extremePoints hu₀, fun i hi hqi x hx hFx => ?_⟩
      obtain rfl := huniq i hi hqi
      rw [hgnu x hx hFx]
      have : -g - (q' : lp E ⊤) i = -(g + (q' : lp E ⊤) i) := by abel
      rw [this, norm_neg]; exact h
  · push Not at hB
    exact ⟨u₀, hu₀, fun i hi hqi => absurd hqi (hB i hi)⟩

include hbij hlip hsupp in
/-- Two extreme points with equal decided patterns at a scalar block have equal preimage blocks
there. -/
lemma same_pattern {i : ι} {j : κ} (hi : σ i = j) (hd : Module.finrank ℝ (E i) = 1) {e : E i}
    (he : ‖e‖ = 1) {w w' : E' j} (hw : w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' j) 1))
    (hw' : w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' j) 1))
    (hdec : decide (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) j = w →
        (x : lp E ⊤) i = e) =
      decide (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) j = w' →
        (x : lp E ⊤) i = e)) :
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ x' ∈ Metric.closedBall (0 : c0Sum E) 1,
      (F x : lp E' ⊤) j = w → (F x' : lp E' ⊤) j = w' → (x : lp E ⊤) i = (x' : lp E ⊤) i := by
  intro x hx x' hx' hFx hFx'
  obtain ⟨g, hg, hgw, -⟩ := extreme_rule hbij hlip hsupp i j hi hw (by omega)
  obtain ⟨g', hg', hg'w, -⟩ := extreme_rule hbij hlip hsupp i j hi hw' (by omega)
  rw [hgw x hx hFx, hg'w x' hx' hFx']
  have hP : (∀ y ∈ Metric.closedBall (0 : c0Sum E) 1, (F y : lp E' ⊤) j = w →
      (y : lp E ⊤) i = e) ↔ g = e :=
    ⟨fun h => by rw [← hgw x hx hFx]; exact h x hx hFx,
      fun h y hy hFy => by rw [hgw y hy hFy, h]⟩
  have hP' : (∀ y ∈ Metric.closedBall (0 : c0Sum E) 1, (F y : lp E' ⊤) j = w' →
      (y : lp E ⊤) i = e) ↔ g' = e :=
    ⟨fun h => by rw [← hg'w x' hx' hFx']; exact h x' hx' hFx',
      fun h y hy hFy => by rw [hg'w y hy hFy, h]⟩
  have hiff : g = e ↔ g' = e := by
    rw [← hP, ← hP']
    simpa using hdec
  have he0 : e ≠ -e := by
    intro h
    have : e = 0 := by
      have h2 : (2 : ℝ) • e = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel e
      exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
    rw [this, norm_zero] at he; norm_num at he
  rcases eq_or_eq_neg_of_finrank_one hd he hg with h1 | h1 <;>
    rcases eq_or_eq_neg_of_finrank_one hd he hg' with h2 | h2
  · rw [h1, h2]
  · exact absurd (h2.symm.trans (hiff.1 h1)) (Ne.symm he0)
  · exact absurd (h1.symm.trans (hiff.2 h2)) (Ne.symm he0)
  · rw [h1, h2]

end NoFed2

end Sol_Plasticity_C0Sum_exists_blockEquiv_no_fed

open Sol_Plasticity_C0Sum_exists_blockEquiv_no_fed in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ (Module.finrank ℝ (E' k) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E' k) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (σ : ι → κ)
    (hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ n : κ,
      (∀ i, σ i = n → (x : lp E ⊤) i = 0) → (F x : lp E' ⊤) n = 0)
    (hplane : ∀ i, Module.finrank ℝ (E i) = 2 → ∀ k, σ k = σ i → k = i)
    (hscal : ∀ h h', Module.finrank ℝ (E' (σ h)) = 1 → σ h' = σ h → h' = h)
    (hthree : ∀ a b c, σ a = σ b → σ a = σ c → a = b ∨ a = c ∨ b = c) :
    ∀ h, Module.finrank ℝ (E h) = 1 → Module.finrank ℝ (E' (σ h)) = 1 := by
  classical
  intro h hh
  by_contra hne
  have hj := (hE' (σ h)).resolve_left hne
  obtain ⟨hj2, hjext⟩ := hj
  have : FiniteDimensional ℝ (E' (σ h)) := Module.finite_of_finrank_eq_succ hj2
  have hfinE' : ∀ n, Module.finrank ℝ (E' n) = 1 ∨ Module.finrank ℝ (E' n) = 2 :=
    fun n => (hE' n).imp id And.left
  -- the fibre of `σ h`
  obtain ⟨h', hh'j, hfib⟩ : ∃ h', σ h' = σ h ∧ ∀ i, σ i = σ h → i = h ∨ i = h' := by
    by_cases hx : ∃ h', h' ≠ h ∧ σ h' = σ h
    · obtain ⟨h', hh'h, hh'j⟩ := hx
      refine ⟨h', hh'j, fun i hi => ?_⟩
      rcases hthree h h' i hh'j.symm hi.symm with h1 | h1 | h1
      · exact absurd h1.symm hh'h
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    · push Not at hx
      refine ⟨h, rfl, fun i hi => Or.inl ?_⟩
      by_contra hc
      exact hx i hc hi
  have hfibdim : ∀ i, σ i = σ h → Module.finrank ℝ (E i) = 1 := by
    intro i hi
    rcases hE i with h1 | ⟨h2, _⟩
    · exact h1
    · have := hplane i h2 h hi.symm
      subst this; omega
  have hunit : ∀ i, Module.finrank ℝ (E i) = 1 → ∃ e : E i, ‖e‖ = 1 := by
    intro i hi
    have : Nontrivial (E i) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    obtain ⟨w, hw⟩ := exists_ne (0 : E i)
    exact ⟨‖w‖⁻¹ • w, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]⟩
  obtain ⟨eh, heh⟩ := hunit h hh
  obtain ⟨eh', heh'⟩ := hunit h' (hfibdim h' hh'j)
  -- two distinct extreme points with the same pattern
  set f : E' (σ h) → Bool × Bool := fun w =>
    (decide (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) (σ h) = w →
      (x : lp E ⊤) h = eh),
     decide (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) (σ h) = w →
      (x : lp E ⊤) h' = eh'))
  have hnotinj : ¬ Set.InjOn f (Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ h)) 1)) := by
    intro hinj
    have h1 := hinj.encard_image
    have h2 : (f '' Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ h)) 1)).encard ≤ 4 := by
      refine (Set.encard_le_encard (Set.subset_univ _)).trans ?_
      rw [Set.encard_univ]
      simp
    rw [h1] at h2
    exact absurd hjext (not_lt.2 h2)
  simp only [Set.InjOn, not_forall] at hnotinj
  obtain ⟨w, hw, w', hw', hfw, hww⟩ := hnotinj
  have hsame : ∀ i, σ i = σ h → ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
      ∀ x' ∈ Metric.closedBall (0 : c0Sum E) 1, (F x : lp E' ⊤) (σ h) = w →
        (F x' : lp E' ⊤) (σ h) = w' → (x : lp E ⊤) i = (x' : lp E ⊤) i := by
    intro i hi
    rcases hfib i hi with rfl | rfl
    · exact same_pattern hbij hlip hsupp rfl hh heh hw hw' (congrArg Prod.fst hfw)
    · exact same_pattern hbij hlip hsupp hh'j (hfibdim i hh'j) heh' hw hw'
        (congrArg Prod.snd hfw)
  -- the comparison
  have hwn : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.1 hw.1
  have hw'n : ‖w'‖ ≤ 1 := mem_closedBall_zero_iff.1 hw'.1
  obtain ⟨x', hx', hFx'⟩ := hbij.surjOn (sg_mem hw'n)
  have hq'j : (F x' : lp E' ⊤) (σ h) = w' := by rw [hFx', sg_self]
  have hx'b : ∀ k, ‖(x' : lp E ⊤) k‖ ≤ 1 := fun k =>
    (norm_apply_le x' k).trans (mem_closedBall_zero_iff.1 hx')
  have hhelp : ∀ n, ∃ u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' n) 1),
      ∀ k, σ k = n → ‖(x' : lp E ⊤) k‖ = 1 → ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
        (F x : lp E' ⊤) n = u → ‖(x : lp E ⊤) k - (x' : lp E ⊤) k‖ < 2 :=
    fun n => exists_helper hbij hlip hsupp hE hplane hscal hthree n (hfinE' n)
  choose U hU hUprop using hhelp
  set Qs := (finite_big x' (by norm_num : (0 : ℝ) < 1 / 2)).toFinset
  set y : c0Sum E' := ofFun (insert (σ h) (Qs.image σ)) (Function.update U (σ h) w)
  have hy : ‖y‖ ≤ 1 := by
    refine norm_ofFun_le _ _ fun n => ?_
    by_cases hn : n = σ h
    · subst hn; rw [Function.update_self]; exact hwn
    · rw [Function.update_of_ne hn]; exact mem_closedBall_zero_iff.1 (hU n).1
  obtain ⟨x, hx, hFx⟩ := hbij.surjOn (mem_closedBall_zero_iff.2 hy)
  have hxb : ∀ k, ‖(x : lp E ⊤) k‖ ≤ 1 := fun k =>
    (norm_apply_le x k).trans (mem_closedBall_zero_iff.1 hx)
  have hFxj : (F x : lp E' ⊤) (σ h) = w := by
    rw [hFx, ofFun_apply, if_pos (Finset.mem_insert_self _ _), Function.update_self]
  have hdist : ∀ k, ‖(x : lp E ⊤) k - (x' : lp E ⊤) k‖ < 2 ∧
      (σ k = σ h → (x : lp E ⊤) k = (x' : lp E ⊤) k) := by
    intro k
    by_cases hkj : σ k = σ h
    · have := hsame k hkj x hx x' hx' hFxj hq'j
      exact ⟨by rw [this, sub_self, norm_zero]; norm_num, fun _ => this⟩
    refine ⟨?_, fun h1 => absurd h1 hkj⟩
    by_cases hq1 : ‖(x' : lp E ⊤) k‖ = 1
    · have hkQ : k ∈ Qs := by
        simp only [Qs, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hq1]; norm_num
      have hFxk : (F x : lp E' ⊤) (σ k) = U (σ k) := by
        rw [hFx, ofFun_apply, if_pos (Finset.mem_insert_of_mem (Finset.mem_image_of_mem σ hkQ)),
          Function.update_of_ne hkj]
      exact hUprop (σ k) k rfl hq1 x hx hFxk
    · have hlt : ‖(x' : lp E ⊤) k‖ < 1 := lt_of_le_of_ne (hx'b k) hq1
      calc ‖(x : lp E ⊤) k - (x' : lp E ⊤) k‖ ≤ ‖(x : lp E ⊤) k‖ + ‖(x' : lp E ⊤) k‖ :=
            norm_sub_le _ _
        _ < 2 := by linarith [hxb k]
  obtain ⟨M, hM2, hM1, hM⟩ := exists_bound_lt_two (x - x') (fun k => by simpa using (hdist k).1)
  have hMk : ∀ k, ‖(x : lp E ⊤) k - (x' : lp E ⊤) k‖ ≤ M := fun k => by simpa using hM k
  set s := 1 - M / 2 with hs
  have hs0 : 0 < s := by linarith
  have hs1 : s ≤ 1 / 2 := by linarith
  set z := mk (fun k => if σ k = σ h then s • (x : lp E ⊤) k
      else (1 / 2 : ℝ) • ((x : lp E ⊤) k + (x' : lp E ⊤) k)) x x' (fun k => by
    split_ifs
    · rw [norm_smul, Real.norm_of_nonneg hs0.le]
      nlinarith [norm_nonneg ((x : lp E ⊤) k), norm_nonneg ((x' : lp E ⊤) k)]
    · rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      nlinarith [norm_add_le ((x : lp E ⊤) k) ((x' : lp E ⊤) k),
        norm_nonneg ((x : lp E ⊤) k), norm_nonneg ((x' : lp E ⊤) k)])
  have hzmem : z ∈ Metric.closedBall (0 : c0Sum E) 1 := by
    rw [mem_closedBall_zero_iff]
    refine norm_c0Sum_le zero_le_one fun k => ?_
    rw [mk_apply]
    split_ifs
    · rw [norm_smul, Real.norm_of_nonneg hs0.le]; nlinarith [hxb k, norm_nonneg ((x : lp E ⊤) k)]
    · rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      nlinarith [norm_add_le ((x : lp E ⊤) k) ((x' : lp E ⊤) k), hxb k, hx'b k]
  have hzx : ‖z - x‖ ≤ 1 - s := by
    refine norm_c0Sum_le (by linarith) fun k => ?_
    simp only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, z, mk_apply]
    split_ifs
    · rw [show s • (x : lp E ⊤) k - (x : lp E ⊤) k = (s - 1) • (x : lp E ⊤) k by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      nlinarith [hxb k, norm_nonneg ((x : lp E ⊤) k)]
    · rw [show (1 / 2 : ℝ) • ((x : lp E ⊤) k + (x' : lp E ⊤) k) - (x : lp E ⊤) k =
          (1 / 2 : ℝ) • -((x : lp E ⊤) k - (x' : lp E ⊤) k) by module,
        norm_smul, norm_neg, Real.norm_of_nonneg (by norm_num)]
      nlinarith [hMk k]
  have hzx' : ‖z - x'‖ ≤ 1 - s := by
    refine norm_c0Sum_le (by linarith) fun k => ?_
    simp only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, z, mk_apply]
    split_ifs with hk
    · rw [(hdist k).2 hk, show s • (x' : lp E ⊤) k - (x' : lp E ⊤) k =
          (s - 1) • (x' : lp E ⊤) k by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      nlinarith [hx'b k, norm_nonneg ((x' : lp E ⊤) k)]
    · rw [show (1 / 2 : ℝ) • ((x : lp E ⊤) k + (x' : lp E ⊤) k) - (x' : lp E ⊤) k =
          (1 / 2 : ℝ) • ((x : lp E ⊤) k - (x' : lp E ⊤) k) by module,
        norm_smul, Real.norm_of_nonneg (by norm_num)]
      nlinarith [hMk k]
  have hFz : ‖(F z : lp E' ⊤) (σ h)‖ ≤ s := by
    refine norm_bound hlip hsupp hzmem (σ h) hs0.le fun i hi => ?_
    rw [mk_apply, if_pos hi, norm_smul, Real.norm_of_nonneg hs0.le]
    nlinarith [hxb i, norm_nonneg ((x : lp E ⊤) i)]
  have h1 : ‖(F z : lp E' ⊤) (σ h) - w‖ ≤ 1 - s := by
    rw [← hFxj]; exact (norm_block_sub_le hlip hzmem hx (σ h)).trans hzx
  have h2 : ‖(F z : lp E' ⊤) (σ h) - w'‖ ≤ 1 - s := by
    rw [← hq'j]; exact (norm_block_sub_le hlip hzmem hx' (σ h)).trans hzx'
  have e1 := eq_smul_of_extreme hw hs0.le (by linarith) hFz h1
  have e2 := eq_smul_of_extreme hw' hs0.le (by linarith) hFz h2
  rw [e1] at e2
  exact hww (smul_right_injective _ hs0.ne' e2)
