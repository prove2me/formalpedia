-- Prove2me | solution 1 for Plasticity.Plane.far_comparison
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:50.449728+00:00
-- url     : https://prove2.me/submissions/33832f99-f348-4990-a5f1-b97cc0c745cb

/-
Credits (this project): `abs_apply_le`, `apply_le`, `neg_le_apply` and `decomp` are copied from
`Solutions/Sol_Plasticity_Plane_corner_cover.lean`; `norm_eq_one` from
`Solutions/Sol_Plasticity_Plane_exists_adjacent_edges_of_countable.lean`;
`exists_ne_zero_apply_eq_zero`, `exists_eq_smul_of_apply_eq_zero` and `exists_norm_attained` from
`Solutions/Sol_Plasticity_Plane_closedBall_subset_union_two_iff.lean`; `exists_norming` from
`Solutions/Sol_Plasticity_Plane_exists_open_completions.lean`.
-/
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

namespace Sol_Plasticity_Plane_far_comparison

open Metric Set

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A functional of norm at most one is at most the norm. -/
theorem abs_apply_le {θ : StrongDual ℝ V} (h : ‖θ‖ ≤ 1) (v : V) : |θ v| ≤ ‖v‖ := by
  have := θ.le_opNorm v
  rw [Real.norm_eq_abs] at this
  calc |θ v| ≤ ‖θ‖ * ‖v‖ := this
    _ ≤ 1 * ‖v‖ := by gcongr
    _ = ‖v‖ := one_mul _

theorem apply_le {θ : StrongDual ℝ V} (h : ‖θ‖ ≤ 1) (v : V) : θ v ≤ ‖v‖ :=
  (le_abs_self _).trans (abs_apply_le h v)

/-- A functional of norm at most one is at least minus the norm. -/
theorem neg_le_apply {θ : StrongDual ℝ V} (h : ‖θ‖ ≤ 1) (v : V) : -‖v‖ ≤ θ v :=
  (abs_le.mp (abs_apply_le h v)).1

/-- In a plane, the coordinates of a functional in the dual basis `f₁, f₂`, computed on
`r₂ ∈ ker f₂` and `r₁ ∈ ker f₁`. -/
theorem decomp (hV : Module.finrank ℝ V = 2) {r₁ r₂ : V} {f₁ f₂ : StrongDual ℝ V}
    (h11 : f₁ r₁ = 0) (h22 : f₂ r₂ = 0) (h12 : f₁ r₂ ≠ 0) (h21 : f₂ r₁ ≠ 0)
    (θ : StrongDual ℝ V) (v : V) :
    θ v = θ r₂ / f₁ r₂ * f₁ v + θ r₁ / f₂ r₁ * f₂ v := by
  have hli : LinearIndependent ℝ ![r₁, r₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg f₁ hst
    have e2 := congrArg f₂ hst
    simp only [map_add, map_smul, smul_eq_mul, h11, h22, map_zero, mul_zero, zero_add,
      add_zero] at e1 e2
    exact ⟨(mul_eq_zero.mp e2).resolve_right h21, (mul_eq_zero.mp e1).resolve_right h12⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  rw [Matrix.range_cons_cons_empty] at hspan
  have hv : v ∈ Submodule.span ℝ {r₁, r₂} := by rw [hspan]; trivial
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp only [map_add, map_smul, smul_eq_mul, h11, h22, mul_zero, zero_add, add_zero]
  field_simp
  ring

/-- Extreme points of the unit ball of a plane are unit vectors. -/
theorem norm_eq_one (hE : Module.finrank ℝ V = 2) {x : V}
    (hx : x ∈ extremePoints ℝ (closedBall (0 : V) 1)) : ‖x‖ = 1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hE
  simpa using extremePoints_closedBall_subset_sphere hx

/-- In a plane, a nonzero vector is annihilated by a nonzero functional. -/
theorem exists_ne_zero_apply_eq_zero (hV : Module.finrank ℝ V = 2) (u : V) (hu : u ≠ 0) :
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

/-- In finite dimensions every functional attains its norm on the closed unit ball. -/
theorem exists_norm_attained [FiniteDimensional ℝ V] (ψ : StrongDual ℝ V) :
    ∃ z : V, ‖z‖ ≤ 1 ∧ ψ z = ‖ψ‖ := by
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

/-- A unit functional norming a given nonzero vector. -/
theorem exists_norming {x : V} (hx : x ≠ 0) :
    ∃ g : StrongDual ℝ V, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℝ x (norm_ne_zero_iff.2 hx)
  exact ⟨g, hg, by simpa using hgx⟩

/-- **Conclusion.** Two functionals `ψp, ψm` of norm at most one, positive at `u`, with points
`yp, ym` of the ball where `ψp yp ≥ ψp u`, `ψm ym ≥ ψm u` and each functional drops by at least `c`
from `u` to the other point: then every `k` with `‖k‖ ≤ min c 1` on which both functionals are
nonnegative has `‖u - k‖ ≤ 1`. -/
theorem conclude (hV : Module.finrank ℝ V = 2) {u yp ym k : V} {ψp ψm : StrongDual ℝ V} {c : ℝ}
    (hu : ‖u‖ ≤ 1) (hyp : ‖yp‖ ≤ 1) (hym : ‖ym‖ ≤ 1) (hψp : ‖ψp‖ ≤ 1) (hψm : ‖ψm‖ ≤ 1)
    (h1 : ψp u ≤ ψp yp) (h2 : ψm u ≤ ψm ym) (hc : 0 < c) (h3 : c ≤ ψm u - ψm yp)
    (h4 : c ≤ ψp u - ψp ym) (h5 : 0 < ψp u) (h6 : 0 < ψm u)
    (hk : ‖k‖ ≤ c) (hk1 : ‖k‖ ≤ 1) (hkp : 0 ≤ ψp k) (hkm : 0 ≤ ψm k) : ‖u - k‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hne : u - k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlt
    linarith
  obtain ⟨φ, hφ, hφx⟩ := exists_norming hne
  set r₁ : V := ψm yp • u - ψm u • yp with hr₁
  set r₂ : V := ψp ym • u - ψp u • ym with hr₂
  have h11 : ψm r₁ = 0 := by
    simp only [r₁, map_sub, map_smul, smul_eq_mul]
    ring
  have h22 : ψp r₂ = 0 := by
    simp only [r₂, map_sub, map_smul, smul_eq_mul]
    ring
  have h21 : ψp r₁ ≠ 0 := by
    simp only [r₁, map_sub, map_smul, smul_eq_mul]
    have : ψm yp < ψm u := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 h6.le, mul_lt_mul_of_pos_right this h5]
  have h12 : ψm r₂ ≠ 0 := by
    simp only [r₂, map_sub, map_smul, smul_eq_mul]
    have : ψp ym < ψp u := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h5.le, mul_lt_mul_of_pos_right this h6]
  have hd := decomp hV h11 h22 h12 h21 φ
  set A := φ r₂ / ψm r₂
  set B := φ r₁ / ψp r₁
  have eu := hd u
  have eyp := hd yp
  have eym := hd ym
  have ek := hd k
  have hφ1 : ‖φ‖ ≤ 1 := hφ.le
  have hφu : φ u ≤ 1 := (apply_le hφ1 u).trans hu
  have hφyp : φ yp ≤ 1 := (apply_le hφ1 yp).trans hyp
  have hφym : φ ym ≤ 1 := (apply_le hφ1 ym).trans hym
  have hφk : -‖k‖ ≤ φ k := neg_le_apply hφ1 k
  have hψpk : ψp k ≤ ‖k‖ := apply_le hψp k
  have hψmk : ψm k ≤ ‖k‖ := apply_le hψm k
  have hφuk : 1 < φ u - φ k := by
    have : φ (u - k) = φ u - φ k := map_sub φ u k
    linarith
  rcases le_or_gt 0 A with hA | hA <;> rcases le_or_gt 0 B with hB | hB
  · nlinarith [mul_nonneg hA hkm, mul_nonneg hB hkp]
  · -- the clockwise case: compare with `ym`
    nlinarith [mul_nonneg hA (show 0 ≤ ψm ym - ψm u by linarith),
      mul_le_mul_of_nonpos_left h4 hB.le, mul_nonneg hA hkm,
      mul_nonneg (show 0 ≤ -B by linarith) (show 0 ≤ ‖k‖ - ψp k by linarith),
      mul_nonneg (show 0 ≤ -B by linarith) (show 0 ≤ c - ‖k‖ by linarith)]
  · nlinarith [mul_nonneg hB (show 0 ≤ ψp yp - ψp u by linarith),
      mul_le_mul_of_nonpos_left h3 hA.le, mul_nonneg hB hkp,
      mul_nonneg (show 0 ≤ -A by linarith) (show 0 ≤ ‖k‖ - ψm k by linarith),
      mul_nonneg (show 0 ≤ -A by linarith) (show 0 ≤ c - ‖k‖ by linarith)]
  · have e1 : A * ψm u < 0 := mul_neg_of_neg_of_pos hA h6
    have e2 : B * ψp u < 0 := mul_neg_of_neg_of_pos hB h5
    linarith

/-- **Far point.** For a unit vector `u` and a nonzero functional `g` vanishing at `u` there is a
norming functional `φ` of `u` and, for every `ε > 0`, an extreme point `ω` of the ball with
`g ω < 0` and `φ ω < -1 + ε`. -/
theorem far_point (hV : Module.finrank ℝ V = 2) {u : V} (hu : ‖u‖ = 1) {g : StrongDual ℝ V}
    (hg : g ≠ 0) (hgu : g u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : StrongDual ℝ V, ‖φ‖ ≤ 1 ∧ φ u = 1 ∧
      ∃ ω ∈ extremePoints ℝ (closedBall (0 : V) 1), g ω < 0 ∧ φ ω < -1 + ε := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  obtain ⟨φa, hφa, hφau⟩ := exists_norming hu0
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  -- the largest `s ≥ 0` with `φa + s g` still of norm at most one
  set R : ℝ := 2 / ‖g‖ with hR
  have hR0 : 0 ≤ R := by positivity
  set K : Set ℝ := Icc 0 R ∩ {s | ‖φa + s • g‖ ≤ 1} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)
  have hK0 : (0 : ℝ) ∈ K := ⟨⟨le_refl _, hR0⟩, by simp [hφa]⟩
  obtain ⟨s₁, hs₁K, hs₁max⟩ := hKc.exists_isGreatest ⟨0, hK0⟩
  set φ := φa + s₁ • g with hφdef
  have hφn : ‖φ‖ ≤ 1 := hs₁K.2
  have hφu : φ u = 1 := by
    simp [φ, hgu, hφau, hu]
  set s : ℝ := ε / (‖g‖ + 1) with hsdef
  have hs : 0 < s := by positivity
  set χ := φ + s • g with hχdef
  have hχ : 1 < ‖χ‖ := by
    by_contra hle
    rw [not_lt] at hle
    have hs₁0 : 0 ≤ s₁ := hs₁K.1.1
    have heq : φa + (s₁ + s) • g = χ := by
      simp only [χ, φ, add_smul, add_assoc]
    have hmem : s₁ + s ∈ K := by
      refine ⟨⟨by linarith, ?_⟩, ?_⟩
      · by_contra hRlt
        rw [not_le] at hRlt
        have h1 : ‖(s₁ + s) • g‖ ≤ ‖χ‖ + ‖φa‖ := by
          have : (s₁ + s) • g = χ - φa := by rw [← heq]; abel
          rw [this]
          exact norm_sub_le _ _
        rw [norm_smul, Real.norm_of_nonneg (by linarith)] at h1
        have h2 : R * ‖g‖ = 2 := by
          rw [hR]
          field_simp
        nlinarith
      · show ‖φa + (s₁ + s) • g‖ ≤ 1
        rw [heq]
        exact hle
    have := hs₁max hmem
    linarith
  obtain ⟨z, hz, hχz⟩ := exists_norm_attained χ
  -- Krein–Milman: an extreme point where `χ < -1`
  have hex : ∃ ω ∈ extremePoints ℝ (closedBall (0 : V) 1), χ ω < -1 := by
    by_contra hno
    push Not at hno
    have hsub : closedBall (0 : V) 1 ⊆ {x | -1 ≤ χ x} := by
      rw [← closure_convexHull_extremePoints (isCompact_closedBall (0 : V) 1)
        (convex_closedBall (0 : V) 1)]
      exact closure_minimal (convexHull_min hno (convex_halfSpace_ge χ.toLinearMap.isLinear _))
        (isClosed_le continuous_const χ.continuous)
    have hmz : -z ∈ Metric.closedBall (0 : V) 1 := by
      rw [mem_closedBall_zero_iff, norm_neg]
      exact hz
    have := hsub hmz
    simp only [mem_ofPred_eq, map_neg] at this
    linarith
  obtain ⟨ω, hω, hχω⟩ := hex
  have hω1 : ‖ω‖ ≤ 1 := by
    have := (mem_extremePoints.1 hω).1
    rwa [mem_closedBall_zero_iff] at this
  have hφω : -1 ≤ φ ω := by
    have := neg_le_apply hφn ω
    linarith
  have hgω : |g ω| ≤ ‖g‖ := by
    have := g.le_opNorm ω
    rw [Real.norm_eq_abs] at this
    nlinarith [norm_nonneg g]
  have hχω' : χ ω = φ ω + s * g ω := by
    simp [χ]
  refine ⟨φ, hφn, hφu, ω, hω, ?_, ?_⟩
  · nlinarith
  · have hsg : s * ‖g‖ < ε := by
      rw [hsdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have : -(s * g ω) ≤ s * ‖g‖ := by
      have := neg_abs_le (g ω)
      nlinarith
    linarith

/-- Scalar core of the drop estimate. -/
theorem real_est {A B U Y s m σ : ℝ} (hAB : 1 + m ≤ A + B) (hB : m ≤ B)
    (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (he : U = A * Y + B - s) (hs : s ≤ σ) :
    m - σ ≤ A * (U - Y) := by
  rcases le_or_gt 1 A with h | h
  · nlinarith [mul_nonneg (show 0 ≤ A - 1 by linarith) hU0]
  · nlinarith [mul_nonneg (show 0 ≤ 1 - A by linarith) (show 0 ≤ 1 - U by linarith)]

/-- **Drop estimate.** If `u = a x₁ + b x₂` with `a, b > 0` and `a‖x₁‖ + b‖x₂‖ ≥ 1 + m`, and `ψ`
norms `x₂ + h`, then `ψ` drops by a definite amount from `u` to the direction of `x₁ + h`. -/
theorem drop {u x₁ x₂ h : V} {a b m : ℝ} {ψ : StrongDual ℝ V} (hψ : ‖ψ‖ ≤ 1)
    (hurep : u = a • x₁ + b • x₂) (ha : 0 < a) (hb : 0 < b)
    (h₁ : ‖x₁‖ ≤ ‖x₁ + h‖) (h₂ : ‖x₂‖ ≤ ‖x₂ + h‖) (hx₁ : 0 < ‖x₁‖) (hh1 : ‖h‖ ≤ 1)
    (hψ₂ : ψ (x₂ + h) = ‖x₂ + h‖) (hU0 : 0 ≤ ψ u) (hU1 : ψ u ≤ 1)
    (hm : 1 + m ≤ a * ‖x₁‖ + b * ‖x₂‖) (hm₂ : m ≤ b * ‖x₂‖) (hm0 : 0 < m)
    (hσ : (a + b) * ‖h‖ ≤ m / 2) :
    m / 2 / (a * (‖x₁‖ + 1)) ≤ ψ u - ψ (‖x₁ + h‖⁻¹ • (x₁ + h)) := by
  set L₁ := ‖x₁ + h‖ with hL₁def
  set L₂ := ‖x₂ + h‖ with hL₂def
  have hL₁ : 0 < L₁ := by linarith
  set Y := ψ (L₁⁻¹ • (x₁ + h)) with hYdef
  have hY : ψ (x₁ + h) = L₁ * Y := by
    rw [hYdef, map_smul, smul_eq_mul]
    field_simp
  have hvec : u + (a + b) • h = a • (x₁ + h) + b • (x₂ + h) := by
    rw [hurep]
    module
  have he : ψ u = (a * L₁) * Y + b * L₂ - (a + b) * ψ h := by
    have := congrArg ψ hvec
    simp only [map_add, map_smul, smul_eq_mul] at this
    have hY' : ψ x₁ + ψ h = L₁ * Y := by rw [← map_add]; exact hY
    have hψ₂' : ψ x₂ + ψ h = L₂ := by rw [← map_add]; exact hψ₂
    linear_combination this + a * hY' + b * hψ₂'
  have hs : (a + b) * ψ h ≤ m / 2 :=
    (mul_le_mul_of_nonneg_left (apply_le hψ h) (by positivity)).trans hσ
  have hAB : 1 + m ≤ a * L₁ + b * L₂ := by
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha.le, mul_le_mul_of_nonneg_left h₂ hb.le]
  have hB : m ≤ b * L₂ := by nlinarith [mul_le_mul_of_nonneg_left h₂ hb.le]
  have key := real_est hAB hB hU0 hU1 he hs
  have hL₁le : L₁ ≤ ‖x₁‖ + 1 := (norm_add_le _ _).trans (by linarith)
  have hAle : a * L₁ ≤ a * (‖x₁‖ + 1) := mul_le_mul_of_nonneg_left hL₁le ha.le
  have hpos : 0 ≤ ψ u - Y := by
    by_contra hneg
    rw [not_le] at hneg
    have : a * L₁ * (ψ u - Y) < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hAle hpos]

/-- **One far point.** If `x = t u - ω` with `‖ω‖ ≤ 1` and `‖x + h‖ ≥ ‖x‖ > 1 + ‖h‖`, a norming
functional of `x + h` is nonnegative at `h` and positive at `u`. -/
theorem side {x h ω u : V} {t : ℝ} (hx : x = t • u - ω) (hω : ‖ω‖ ≤ 1) (ht : 0 < t)
    (hadm : ‖x‖ ≤ ‖x + h‖) (hlam : 1 + ‖h‖ < ‖x‖) :
    ∃ ψ : StrongDual ℝ V, ‖ψ‖ = 1 ∧ ψ (x + h) = ‖x + h‖ ∧ 0 ≤ ψ h ∧ 0 < ψ u := by
  have hne : x + h ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hadm
    linarith [norm_nonneg h]
  obtain ⟨ψ, hψ, hψx⟩ := exists_norming hne
  have hψ1 : ‖ψ‖ ≤ 1 := hψ.le
  have hψx' : ψ x + ψ h = ‖x + h‖ := by rw [← map_add]; exact hψx
  have hψxle : ψ x ≤ ‖x‖ := apply_le hψ1 x
  have hψh : ψ h ≤ ‖h‖ := apply_le hψ1 h
  have hψω : -‖ω‖ ≤ ψ ω := neg_le_apply hψ1 ω
  have htu : t * ψ u = ψ x + ψ ω := by
    have : t • u = x + ω := by rw [hx]; abel
    rw [← smul_eq_mul, ← map_smul, this, map_add]
  refine ⟨ψ, hψ, hψx, by linarith, ?_⟩
  have : 0 < t * ψ u := by linarith
  exact pos_of_mul_pos_right this ht.le

/-- **Two far points straddling `u`.** For an extreme point `u` of the ball of a plane and `t > 0`
there are extreme points `ωp, ωm` with `‖t u - ω‖ > 1 + t/2` such that `u` is a positive
combination of `t u - ωp` and `t u - ωm` whose coefficients, weighted by the norms, sum to more
than one. -/
theorem straddle (hV : Module.finrank ℝ V = 2) {u : V}
    (hu : u ∈ extremePoints ℝ (closedBall (0 : V) 1)) {t : ℝ} (ht0 : 0 < t) :
    ∃ ωp ∈ extremePoints ℝ (closedBall (0 : V) 1), ∃ ωm ∈ extremePoints ℝ (closedBall (0 : V) 1),
      ∃ a₀ b₀ : ℝ, 0 < a₀ ∧ 0 < b₀ ∧ 1 + t / 2 < ‖t • u - ωp‖ ∧ 1 + t / 2 < ‖t • u - ωm‖ ∧
        u = a₀ • (t • u - ωp) + b₀ • (t • u - ωm) ∧
        1 < a₀ * ‖t • u - ωp‖ + b₀ * ‖t • u - ωm‖ := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hu1 : ‖u‖ = 1 := norm_eq_one hV hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu1
    norm_num at hu1
  obtain ⟨g, hg, hgu⟩ := exists_ne_zero_apply_eq_zero hV u hu0
  have ht2 : 0 < t / 2 := by linarith
  -- one far extreme point on each side of the line through `u`
  obtain ⟨φp, hφpn, hφpu, ωp, hωp, hgωp, hφpωp⟩ := far_point hV hu1 hg hgu ht2
  obtain ⟨φm, hφmn, hφmu, ωm, hωm, hgωm, hφmωm⟩ :=
    far_point hV hu1 (neg_ne_zero.2 hg) (by simp [hgu]) ht2
  simp only [neg_apply] at hgωm
  have hωp1 : ‖ωp‖ ≤ 1 := by
    have := (mem_extremePoints.1 hωp).1
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hωm1 : ‖ωm‖ ≤ 1 := by
    have := (mem_extremePoints.1 hωm).1
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  set xp := t • u - ωp with hxp
  set xm := t • u - ωm with hxm
  have hgxp : 0 < g xp := by
    simp only [xp, map_sub, map_smul, hgu, smul_eq_mul, mul_zero]
    linarith
  have hgxm : g xm < 0 := by
    simp only [xm, map_sub, map_smul, hgu, smul_eq_mul, mul_zero]
    linarith
  have hφpxp : 1 + t / 2 < φp xp := by
    simp only [xp, map_sub, map_smul, hφpu, smul_eq_mul, mul_one]
    linarith
  have hφmxm : 1 + t / 2 < φm xm := by
    simp only [xm, map_sub, map_smul, hφmu, smul_eq_mul, mul_one]
    linarith
  have hφpxm : t - 1 ≤ φp xm := by
    simp only [xm, map_sub, map_smul, hφpu, smul_eq_mul, mul_one]
    linarith [apply_le hφpn ωm]
  have hφmxp : t - 1 ≤ φm xp := by
    simp only [xp, map_sub, map_smul, hφmu, smul_eq_mul, mul_one]
    linarith [apply_le hφmn ωp]
  have hlp : 1 + t / 2 < ‖xp‖ := lt_of_lt_of_le hφpxp (apply_le hφpn xp)
  have hlm : 1 + t / 2 < ‖xm‖ := lt_of_lt_of_le hφmxm (apply_le hφmn xm)
  -- the segment from `xp` to `xm` crosses the open ray through `u`
  have hden : 0 < g xp - g xm := by linarith
  set θ := g xp / (g xp - g xm) with hθ
  have hθ0 : 0 < θ := div_pos hgxp hden
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hden]
    linarith
  set z := (1 - θ) • xp + θ • xm with hz
  have hgz : g z = 0 := by
    simp only [z, map_add, map_smul, smul_eq_mul]
    rw [hθ]
    field_simp
    ring
  obtain ⟨r, hr⟩ := exists_eq_smul_of_apply_eq_zero hV g ((g xp)⁻¹ • xp) u z
    (by rw [map_smul, smul_eq_mul]; field_simp) hu0 hgu hgz
  have hrp : φp z = r := by rw [hr, map_smul, hφpu, smul_eq_mul, mul_one]
  have hrm : φm z = r := by rw [hr, map_smul, hφmu, smul_eq_mul, mul_one]
  have hφpz : φp z = (1 - θ) * φp xp + θ * φp xm := by
    simp only [z, map_add, map_smul, smul_eq_mul]
  have hφmz : φm z = (1 - θ) * φm xp + θ * φm xm := by
    simp only [z, map_add, map_smul, smul_eq_mul]
  have hr0 : 3 * t / 4 ≤ r := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - θ by linarith) (show 0 ≤ φp xp - (1 + t / 2) by linarith),
      mul_nonneg (show 0 ≤ 1 - θ by linarith) (show 0 ≤ φm xp - (t - 1) by linarith),
      mul_nonneg hθ0.le (show 0 ≤ φp xm - (t - 1) by linarith),
      mul_nonneg hθ0.le (show 0 ≤ φm xm - (1 + t / 2) by linarith)]
  have hrpos : 0 < r := by linarith
  set a₀ := (1 - θ) / r with ha₀def
  set b₀ := θ / r with hb₀def
  have ha₀ : 0 < a₀ := div_pos (by linarith) hrpos
  have hb₀ : 0 < b₀ := div_pos hθ0 hrpos
  have hurep : u = a₀ • xp + b₀ • xm := by
    have h1 : r • u = (1 - θ) • xp + θ • xm := hr.symm
    rw [ha₀def, hb₀def, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← h1,
      smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
  -- extremality of `u`: the triangle inequality is strict
  have hlp0 : 0 < ‖xp‖ := by linarith
  have hlm0 : 0 < ‖xm‖ := by linarith
  have hsum : 1 < a₀ * ‖xp‖ + b₀ * ‖xm‖ := by
    have hle : 1 ≤ a₀ * ‖xp‖ + b₀ * ‖xm‖ := by
      calc (1 : ℝ) = ‖u‖ := hu1.symm
        _ = ‖a₀ • xp + b₀ • xm‖ := by rw [← hurep]
        _ ≤ ‖a₀ • xp‖ + ‖b₀ • xm‖ := norm_add_le _ _
        _ = a₀ * ‖xp‖ + b₀ * ‖xm‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha₀.le, Real.norm_of_nonneg hb₀.le]
    rcases hle.lt_or_eq with h | h
    · exact h
    exfalso
    have hmp : ‖xp‖⁻¹ • xp ∈ Metric.closedBall (0 : V) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hlp0.ne']
    have hmm : ‖xm‖⁻¹ • xm ∈ Metric.closedBall (0 : V) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hlm0.ne']
    have hseg : u ∈ openSegment ℝ (‖xp‖⁻¹ • xp) (‖xm‖⁻¹ • xm) := by
      refine ⟨a₀ * ‖xp‖, b₀ * ‖xm‖, by positivity, by positivity, h.symm, ?_⟩
      rw [smul_smul, smul_smul, mul_assoc, mul_assoc, mul_inv_cancel₀ hlp0.ne',
        mul_inv_cancel₀ hlm0.ne', mul_one, mul_one, hurep]
    have he := ((mem_extremePoints.1 hu).2 _ hmp _ hmm hseg).1
    have hge := congrArg g he
    rw [map_smul, smul_eq_mul, hgu] at hge
    rcases mul_eq_zero.1 hge with h0 | h0
    · exact inv_ne_zero hlp0.ne' h0
    · linarith
  exact ⟨ωp, hωp, ωm, hωm, a₀, b₀, ha₀, hb₀, hlp, hlm, hurep, hsum⟩

end

end Sol_Plasticity_Plane_far_comparison

open Sol_Plasticity_Plane_far_comparison in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (u : V)
    (hu : u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ρ > 0, ∀ h : V, ‖h‖ < ρ →
      (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), 1 < ‖t • u - ω‖ →
        ‖t • u - ω‖ ≤ ‖t • u + h - ω‖) →
      ‖(1 - t) • u - h‖ ≤ 1 - t := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hu1 : ‖u‖ = 1 := norm_eq_one hV hu
  have ht2 : 0 < t / 2 := by linarith
  have h1t : 0 < 1 - t := by linarith
  obtain ⟨ωp, hωp, ωm, hωm, a₀, b₀, ha₀, hb₀, hlp, hlm, hurep, hsum⟩ := straddle hV hu ht0
  have hωp1 : ‖ωp‖ ≤ 1 := by
    have := (mem_extremePoints.1 hωp).1
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hωm1 : ‖ωm‖ ≤ 1 := by
    have := (mem_extremePoints.1 hωm).1
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  set xp := t • u - ωp with hxp
  set xm := t • u - ωm with hxm
  have hurep' : u = b₀ • xm + a₀ • xp := by rw [hurep, add_comm]
  have hlp0 : 0 < ‖xp‖ := by linarith
  have hlm0 : 0 < ‖xm‖ := by linarith
  -- the constants
  set m := min (a₀ * ‖xp‖ + b₀ * ‖xm‖ - 1) (min (a₀ * ‖xp‖) (b₀ * ‖xm‖)) with hmdef
  have hm0 : 0 < m := lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hmκ : m ≤ a₀ * ‖xp‖ + b₀ * ‖xm‖ - 1 := min_le_left _ _
  have hmA : m ≤ a₀ * ‖xp‖ := (min_le_right _ _).trans (min_le_left _ _)
  have hmB : m ≤ b₀ * ‖xm‖ := (min_le_right _ _).trans (min_le_right _ _)
  set cm := m / 2 / (a₀ * (‖xp‖ + 1)) with hcm
  set cp := m / 2 / (b₀ * (‖xm‖ + 1)) with hcp
  have hcm0 : 0 < cm := by positivity
  have hcp0 : 0 < cp := by positivity
  set c := min cp cm with hc
  have hc0 : 0 < c := lt_min hcp0 hcm0
  refine ⟨min (min (t / 2) ((1 - t) * c)) (min (m / (2 * (a₀ + b₀ + 1))) (1 - t)),
    by positivity, ?_⟩
  intro h hh hadm
  have hh1 : ‖h‖ < t / 2 := lt_of_lt_of_le hh ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : ‖h‖ < (1 - t) * c := lt_of_lt_of_le hh ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : ‖h‖ < m / (2 * (a₀ + b₀ + 1)) :=
    lt_of_lt_of_le hh ((min_le_right _ _).trans (min_le_left _ _))
  have hh4 : ‖h‖ < 1 - t := lt_of_lt_of_le hh ((min_le_right _ _).trans (min_le_right _ _))
  have hhle1 : ‖h‖ ≤ 1 := by linarith
  have hσ : (a₀ + b₀) * ‖h‖ ≤ m / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hh3
    have e : ‖h‖ * (2 * (a₀ + b₀ + 1)) = 2 * ((a₀ + b₀) * ‖h‖) + 2 * ‖h‖ := by ring
    linarith [norm_nonneg h]
  have hσ' : (b₀ + a₀) * ‖h‖ ≤ m / 2 := by rw [add_comm]; exact hσ
  -- admissibility at the two far points
  have hadmp : ‖xp‖ ≤ ‖xp + h‖ := by
    have := hadm ωp hωp (by linarith)
    have e : t • u + h - ωp = xp + h := by rw [hxp]; abel
    rwa [e] at this
  have hadmm : ‖xm‖ ≤ ‖xm + h‖ := by
    have := hadm ωm hωm (by linarith)
    have e : t • u + h - ωm = xm + h := by rw [hxm]; abel
    rwa [e] at this
  obtain ⟨ψp, hψp, hψpx, hψph, hψpu⟩ := side hxp hωp1 ht0 hadmp (by linarith)
  obtain ⟨ψm, hψm, hψmx, hψmh, hψmu⟩ := side hxm hωm1 ht0 hadmm (by linarith)
  have hψpu1 : ψp u ≤ 1 := (apply_le hψp.le u).trans hu1.le
  have hψmu1 : ψm u ≤ 1 := (apply_le hψm.le u).trans hu1.le
  -- the two drops
  have dm : cm ≤ ψm u - ψm (‖xp + h‖⁻¹ • (xp + h)) :=
    drop hψm.le hurep ha₀ hb₀ hadmp hadmm hlp0 hhle1 hψmx hψmu.le hψmu1 (by linarith) hmB hm0 hσ
  have dp : cp ≤ ψp u - ψp (‖xm + h‖⁻¹ • (xm + h)) :=
    drop hψp.le hurep' hb₀ ha₀ hadmm hadmp hlm0 hhle1 hψpx hψpu.le hψpu1 (by linarith) hmA hm0
      hσ'
  have hLp : 0 < ‖xp + h‖ := by linarith
  have hLm : 0 < ‖xm + h‖ := by linarith
  have hyp1 : ‖‖xp + h‖⁻¹ • (xp + h)‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hLp.ne']
  have hym1 : ‖‖xm + h‖⁻¹ • (xm + h)‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hLm.ne']
  have hψpyp : ψp (‖xp + h‖⁻¹ • (xp + h)) = 1 := by
    rw [map_smul, hψpx, smul_eq_mul, inv_mul_cancel₀ hLp.ne']
  have hψmym : ψm (‖xm + h‖⁻¹ • (xm + h)) = 1 := by
    rw [map_smul, hψmx, smul_eq_mul, inv_mul_cancel₀ hLm.ne']
  -- the conclusion for `k = h / (1 - t)`
  have hk : ‖(1 - t)⁻¹ • h‖ = ‖h‖ / (1 - t) := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg h1t.le, div_eq_inv_mul]
  have hkc : ‖(1 - t)⁻¹ • h‖ ≤ c := by
    rw [hk, div_le_iff₀ h1t]
    linarith
  have hk1 : ‖(1 - t)⁻¹ • h‖ ≤ 1 := by
    rw [hk, div_le_iff₀ h1t]
    linarith
  have hkp : 0 ≤ ψp ((1 - t)⁻¹ • h) := by
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 h1t.le) hψph
  have hkm : 0 ≤ ψm ((1 - t)⁻¹ • h) := by
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 h1t.le) hψmh
  have hcon := conclude hV hu1.le hyp1 hym1 hψp.le hψm.le (by rw [hψpyp]; exact hψpu1)
    (by rw [hψmym]; exact hψmu1) hc0 ((min_le_right _ _).trans dm) ((min_le_left _ _).trans dp)
    hψpu hψmu hkc hk1 hkp hkm
  have e : (1 - t) • u - h = (1 - t) • (u - (1 - t)⁻¹ • h) := by
    rw [smul_sub, smul_inv_smul₀ h1t.ne']
  rw [e, norm_smul, Real.norm_of_nonneg h1t.le]
  nlinarith
