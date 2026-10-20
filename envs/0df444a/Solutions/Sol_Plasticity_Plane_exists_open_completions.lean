-- Prove2me | solution 1 for Plasticity.Plane.exists_open_completions
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:48.915737+00:00
-- url     : https://prove2.me/submissions/628176dc-599b-45e7-a373-32c87d9b8c60

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
The helper `exists_norm_attained` is copied from the project's solution
`Solutions/Sol_Plasticity_Plane_closedBall_subset_union_two_iff.lean`.
-/

namespace Sol_Plasticity_Plane_exists_open_completions

open Metric Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem apply_le (ψ : StrongDual ℝ V) (y : V) : ψ y ≤ ‖ψ‖ * ‖y‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ψ.le_opNorm y)

theorem abs_apply_le {ψ : StrongDual ℝ V} (hψ : ‖ψ‖ ≤ 1) (y : V) : |ψ y| ≤ ‖y‖ := by
  have h := ψ.le_opNorm y
  rw [Real.norm_eq_abs] at h
  calc |ψ y| ≤ ‖ψ‖ * ‖y‖ := h
    _ ≤ 1 * ‖y‖ := by gcongr
    _ = ‖y‖ := one_mul _

theorem apply_le_one {ψ : StrongDual ℝ V} (hψ : ‖ψ‖ ≤ 1) {y : V} (hy : ‖y‖ ≤ 1) : ψ y ≤ 1 :=
  (le_abs_self _).trans ((abs_apply_le hψ y).trans hy)

theorem neg_one_le_apply {ψ : StrongDual ℝ V} (hψ : ‖ψ‖ ≤ 1) {y : V} (hy : ‖y‖ ≤ 1) :
    -1 ≤ ψ y := by
  have := abs_apply_le hψ y
  rw [abs_le] at this
  linarith [this.1]

theorem apply_le_norm (ψ : StrongDual ℝ V) {y : V} (hy : ‖y‖ ≤ 1) : ψ y ≤ ‖ψ‖ :=
  (apply_le ψ y).trans (by nlinarith [norm_nonneg ψ])

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

/-- Two functionals of a plane that are independent on two vectors: a dual pair of vectors and
the resulting coordinate formula. -/
theorem exists_u (hV : Module.finrank ℝ V = 2) (ψ₁ ψ₂ : StrongDual ℝ V) (x y : V)
    (hd : ψ₁ x * ψ₂ y - ψ₁ y * ψ₂ x ≠ 0) :
    ∃ u₁ u₂ : V, ψ₁ u₁ = 0 ∧ ψ₂ u₁ = -1 ∧ ψ₂ u₂ = 0 ∧ ψ₁ u₂ = -1 ∧
      ∀ z, z = -(ψ₁ z) • u₂ - (ψ₂ z) • u₁ := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set d := ψ₁ x * ψ₂ y - ψ₁ y * ψ₂ x with hd_def
  set u₁ : V := d⁻¹ • (ψ₁ y • x - ψ₁ x • y) with hu₁
  set u₂ : V := d⁻¹ • (ψ₂ x • y - ψ₂ y • x) with hu₂
  have h11 : ψ₁ u₁ = 0 := by
    simp only [u₁, map_smul, map_sub, smul_eq_mul]; ring
  have h21 : ψ₂ u₁ = -1 := by
    simp only [u₁, map_smul, map_sub, smul_eq_mul]
    field_simp
    rw [hd_def]; ring
  have h22 : ψ₂ u₂ = 0 := by
    simp only [u₂, map_smul, map_sub, smul_eq_mul]; ring
  have h12 : ψ₁ u₂ = -1 := by
    simp only [u₂, map_smul, map_sub, smul_eq_mul]
    field_simp
    rw [hd_def]; ring
  refine ⟨u₁, u₂, h11, h21, h22, h12, ?_⟩
  let L : V →ₗ[ℝ] ℝ × ℝ := (ψ₁ : V →ₗ[ℝ] ℝ).prod (ψ₂ : V →ₗ[ℝ] ℝ)
  have hL : ∀ w, L w = (ψ₁ w, ψ₂ w) := fun w => rfl
  have hsurj : Function.Surjective L := by
    rintro ⟨a, b⟩
    refine ⟨-a • u₂ - b • u₁, ?_⟩
    rw [hL]
    simp only [map_sub, map_smul, smul_eq_mul, h11, h21, h22, h12, Prod.mk.injEq]
    constructor <;> ring
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hV])).2 hsurj
  intro z
  apply hinj
  rw [hL, hL]
  simp only [map_sub, map_smul, smul_eq_mul, h11, h21, h22, h12, Prod.mk.injEq]
  constructor <;> ring

theorem eq_of_apply_eq (hV : Module.finrank ℝ V = 2) {ψ₁ ψ₂ : StrongDual ℝ V} {x y : V}
    (hd : ψ₁ x * ψ₂ y - ψ₁ y * ψ₂ x ≠ 0) {z z' : V} (h₁ : ψ₁ z = ψ₁ z') (h₂ : ψ₂ z = ψ₂ z') :
    z = z' := by
  obtain ⟨u₁, u₂, -, -, -, -, h⟩ := exists_u hV ψ₁ ψ₂ x y hd
  rw [h z, h z', h₁, h₂]

/-- The separation step: with `u₁, u₂` dual to `-ψ₂, -ψ₁`, a point `v` of the ball far from `e`
has no norming functional `φ₁` with `φ₁ u₁ ≤ 0` together with a norming functional `φ₂` with
`φ₂ u₂ ≤ 0`, provided no nonnegative combination of `ψ₁, ψ₂` norms a far point (`H2`) and
`ψ₁, ψ₂` norm no common point (`H3`). -/
theorem core {ψ₁ ψ₂ : StrongDual ℝ V} {u₁ u₂ e : V}
    (hdec : ∀ z, z = -(ψ₁ z) • u₂ - (ψ₂ z) • u₁)
    (H2 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 < a + b → ∀ v : V, ‖v‖ ≤ 1 → 1 ≤ ‖v - e‖ →
      (a • ψ₁ + b • ψ₂) v < ‖a • ψ₁ + b • ψ₂‖)
    (H3 : ∀ w : V, ‖w‖ ≤ 1 → ψ₁ w = ‖ψ₁‖ → ψ₂ w = ‖ψ₂‖ → False)
    {v : V} (hv : ‖v‖ ≤ 1) (hve : 1 ≤ ‖v - e‖) {φ₁ φ₂ : StrongDual ℝ V}
    (hφ₁ : ‖φ₁‖ ≤ 1) (hφ₂ : ‖φ₂‖ ≤ 1) (hφ₁v : φ₁ v = 1) (hφ₂v : φ₂ v = 1)
    (h1 : φ₁ u₁ ≤ 0) (h2 : φ₂ u₂ ≤ 0) : False := by
  have decF : ∀ φ : StrongDual ℝ V, φ = (-φ u₂) • ψ₁ + (-φ u₁) • ψ₂ := by
    intro φ
    ext z
    conv_lhs => rw [hdec z]
    simp only [map_sub, map_smul, smul_eq_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
    ring
  have conv : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
      ‖s • φ₁ + t • φ₂‖ ≤ 1 ∧ (s • φ₁ + t • φ₂) v = 1 := by
    intro s t hs ht hst
    refine ⟨?_, ?_⟩
    · calc ‖s • φ₁ + t • φ₂‖ ≤ ‖s • φ₁‖ + ‖t • φ₂‖ := norm_add_le _ _
        _ = s * ‖φ₁‖ + t * ‖φ₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
        _ ≤ s * 1 + t * 1 := by gcongr
        _ = 1 := by rw [mul_one, mul_one, hst]
    · simp [hφ₁v, hφ₂v, hst]
  have key : ∀ γ : StrongDual ℝ V, ‖γ‖ ≤ 1 → γ v = 1 → ¬ (0 ≤ -γ u₂ ∧ 0 ≤ -γ u₁) := by
    rintro γ hγ hγv ⟨ha, hb⟩
    have hγdec := decF γ
    rcases (add_nonneg ha hb).lt_or_eq with hab | hab
    · have := H2 _ _ ha hb hab v hv hve
      rw [← hγdec, hγv] at this
      linarith
    · have ha0 : -γ u₂ = 0 := by linarith
      have hb0 : -γ u₁ = 0 := by linarith
      rw [ha0, hb0, zero_smul, zero_smul, add_zero] at hγdec
      rw [hγdec] at hγv
      simp at hγv
  have corner1 : ∀ γ : StrongDual ℝ V, ‖γ‖ ≤ 1 → γ v = 1 → γ u₁ = 0 → 0 < γ u₂ →
      ψ₁ (-v) = ‖ψ₁‖ := by
    intro γ hγ hγv hu1 hu2
    have hγdec := decF γ
    rw [hu1, neg_zero, zero_smul, add_zero] at hγdec
    have ha0 : -γ u₂ < 0 := by linarith
    have hval : -γ u₂ * ψ₁ v = 1 := by
      have := congrArg (fun φ : StrongDual ℝ V => φ v) hγdec
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at this
      rw [← this, hγv]
    have hnorm : γ u₂ * ‖ψ₁‖ ≤ 1 := by
      have : ‖γ‖ = γ u₂ * ‖ψ₁‖ := by
        conv_lhs => rw [hγdec]
        rw [norm_smul, Real.norm_of_nonpos ha0.le, neg_neg]
      linarith
    have hle : ψ₁ (-v) ≤ ‖ψ₁‖ := apply_le_norm ψ₁ (by rwa [norm_neg])
    rw [map_neg] at hle ⊢
    apply le_antisymm hle
    have h' : γ u₂ * ‖ψ₁‖ ≤ γ u₂ * (-ψ₁ v) := by linarith
    exact le_of_mul_le_mul_left h' hu2
  have corner2 : ∀ γ : StrongDual ℝ V, ‖γ‖ ≤ 1 → γ v = 1 → γ u₂ = 0 → 0 < γ u₁ →
      ψ₂ (-v) = ‖ψ₂‖ := by
    intro γ hγ hγv hu2 hu1
    have hγdec := decF γ
    rw [hu2, neg_zero, zero_smul, zero_add] at hγdec
    have hb0 : -γ u₁ < 0 := by linarith
    have hval : -γ u₁ * ψ₂ v = 1 := by
      have := congrArg (fun φ : StrongDual ℝ V => φ v) hγdec
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at this
      rw [← this, hγv]
    have hnorm : γ u₁ * ‖ψ₂‖ ≤ 1 := by
      have : ‖γ‖ = γ u₁ * ‖ψ₂‖ := by
        conv_lhs => rw [hγdec]
        rw [norm_smul, Real.norm_of_nonpos hb0.le, neg_neg]
      linarith
    have hle : ψ₂ (-v) ≤ ‖ψ₂‖ := apply_le_norm ψ₂ (by rwa [norm_neg])
    rw [map_neg] at hle ⊢
    apply le_antisymm hle
    have h' : γ u₁ * ‖ψ₂‖ ≤ γ u₁ * (-ψ₂ v) := by linarith
    exact le_of_mul_le_mul_left h' hu1
  -- coefficients of `φ₁, φ₂` in the basis `ψ₁, ψ₂`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, φ₁ u₂ = -α := ⟨-φ₁ u₂, by ring⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, φ₁ u₁ = -β := ⟨-φ₁ u₁, by ring⟩
  obtain ⟨α', hα'⟩ : ∃ α' : ℝ, φ₂ u₂ = -α' := ⟨-φ₂ u₂, by ring⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : ℝ, φ₂ u₁ = -β' := ⟨-φ₂ u₁, by ring⟩
  have hβ0 : 0 ≤ β := by linarith
  have hα'0 : 0 ≤ α' := by linarith
  have hα0 : α < 0 := by
    by_contra h
    replace h := le_of_not_gt h
    exact key φ₁ hφ₁ hφ₁v ⟨by rw [hα]; linarith, by rw [hβ]; linarith⟩
  have hβ'0 : β' < 0 := by
    by_contra h
    replace h := le_of_not_gt h
    exact key φ₂ hφ₂ hφ₂v ⟨by rw [hα']; linarith, by rw [hβ']; linarith⟩
  have hda : 0 < α' - α := by linarith
  have hdb : 0 < β - β' := by linarith
  have app : ∀ s t : ℝ, ∀ u : V, (s • φ₁ + t • φ₂) u = s * φ₁ u + t * φ₂ u := by
    intro s t u; simp
  -- the combination with vanishing `ψ₁`-coefficient
  obtain ⟨hγa, hγav⟩ := conv (α' / (α' - α)) (-α / (α' - α)) (div_nonneg hα'0 hda.le)
    (div_nonneg (by linarith) hda.le) (by field_simp; ring)
  have hγa2 : ((α' / (α' - α)) • φ₁ + (-α / (α' - α)) • φ₂) u₂ = 0 := by
    rw [app, hα, hα']; field_simp; ring
  have hγa1 : ((α' / (α' - α)) • φ₁ + (-α / (α' - α)) • φ₂) u₁ =
      (α * β' - α' * β) / (α' - α) := by
    rw [app, hβ, hβ']; field_simp; ring
  -- the combination with vanishing `ψ₂`-coefficient
  obtain ⟨hγb, hγbv⟩ := conv (-β' / (β - β')) (β / (β - β')) (div_nonneg (by linarith) hdb.le)
    (div_nonneg hβ0 hdb.le) (by field_simp; ring)
  have hγb1 : ((-β' / (β - β')) • φ₁ + (β / (β - β')) • φ₂) u₁ = 0 := by
    rw [app, hβ, hβ']; field_simp; ring
  have hγb2 : ((-β' / (β - β')) • φ₁ + (β / (β - β')) • φ₂) u₂ =
      (α * β' - α' * β) / (β - β') := by
    rw [app, hα, hα']; field_simp; ring
  rcases le_or_gt (α * β' - α' * β) 0 with hΔ | hΔ
  · apply key _ hγa hγav
    constructor
    · rw [hγa2]; simp
    · rw [hγa1]
      have := div_nonpos_of_nonpos_of_nonneg hΔ hda.le
      linarith
  · have e1 := corner1 _ hγb hγbv hγb1 (by rw [hγb2]; positivity)
    have e2 := corner2 _ hγa hγav hγa2 (by rw [hγa1]; positivity)
    exact H3 (-v) (by rwa [norm_neg]) e1 e2

/-- A point `y` of the ball whose functionals of norm at most one are, unless far from norming
`y`, bounded below by `m` at `u`, lies in the closed unit ball about every point near `t₀ • u`. -/
theorem close {y u c : V} {m t₀ r : ℝ} (hy : ‖y‖ ≤ 1) (ht₀ : 0 < t₀)
    (hcu : ‖c - t₀ • u‖ < r) (h1 : t₀ * ‖u‖ + r ≤ m) (h2 : r ≤ t₀ * m)
    (hφ : ∀ φ : StrongDual ℝ V, ‖φ‖ ≤ 1 → φ y ≤ 1 - m ∨ m ≤ φ u) : ‖y - c‖ ≤ 1 := by
  by_cases h0 : y - c = 0
  · rw [h0, norm_zero]; exact zero_le_one
  obtain ⟨φ, hφn, hφv⟩ := exists_norming h0
  rw [← hφv]
  have hsplit : φ (y - c) = φ y - t₀ * φ u - φ (c - t₀ • u) := by
    simp only [map_sub, map_smul, smul_eq_mul]; ring
  have hc : |φ (c - t₀ • u)| ≤ ‖c - t₀ • u‖ := abs_apply_le hφn.le _
  have hu : |φ u| ≤ ‖u‖ := abs_apply_le hφn.le _
  have hy1 : φ y ≤ 1 := apply_le_one hφn.le hy
  rw [abs_le] at hc hu
  rw [hsplit]
  rcases hφ φ hφn.le with h | h
  · nlinarith [mul_nonneg ht₀.le (by linarith : 0 ≤ φ u + ‖u‖)]
  · nlinarith [mul_le_mul_of_nonneg_left h ht₀.le]

/-- The cover estimate: if no point of the ball far from `e` has norming functionals `φ₁, φ₂`
with `φ₁ u₁ ≤ 0` and `φ₂ u₂ ≤ 0`, then small balls about small multiples of `u₁, u₂` give the
required open set of completions. -/
theorem cover (hV : Module.finrank ℝ V = 2) {e : V} (he : ‖e‖ = 1) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) {u₁ u₂ : V} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hcore : ∀ v : V, ‖v‖ ≤ 1 → 1 ≤ ‖v - e‖ → ∀ φ₁ φ₂ : StrongDual ℝ V, ‖φ₁‖ ≤ 1 →
      ‖φ₂‖ ≤ 1 → φ₁ v = 1 → φ₂ v = 1 → φ₁ u₁ ≤ 0 → φ₂ u₂ ≤ 0 → False) :
    ∃ U : Set (V × V), IsOpen U ∧ U.Nonempty ∧ ∀ c ∈ U, c.1 ≠ 0 ∧ c.2 ≠ 0 ∧
      ‖c.1‖ ≤ 1 ∧ ‖c.2‖ ≤ 1 ∧
      Metric.closedBall (0 : V) 1 ⊆
        Metric.closedBall (s • e) 1 ∪ Metric.closedBall c.1 1 ∪ Metric.closedBall c.2 1 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set C : Set V := closedBall (0 : V) 1 ∩ {v | 1 ≤ ‖v - e‖} with hC
  have hCc : IsCompact C := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  set K : Set (V × StrongDual ℝ V × StrongDual ℝ V) :=
    C ×ˢ (closedBall (0 : StrongDual ℝ V) 1 ×ˢ closedBall (0 : StrongDual ℝ V) 1) with hK
  have hKc : IsCompact K :=
    hCc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hKne : K.Nonempty := by
    refine ⟨(-e, 0, 0), ⟨?_, ?_⟩, ?_, ?_⟩
    · simp [he]
    · show 1 ≤ ‖-e - e‖
      rw [show -e - e = (-2 : ℝ) • e by module, norm_smul, he]; norm_num
    · simp
    · simp
  let G : V × StrongDual ℝ V × StrongDual ℝ V → ℝ := fun x =>
    max (max (1 - x.2.1 x.1) (1 - x.2.2 x.1)) (max (x.2.1 u₁) (x.2.2 u₂))
  have hG : Continuous G := by
    have c1 : Continuous fun x : V × StrongDual ℝ V × StrongDual ℝ V => x.2.1 x.1 :=
      continuous_snd.fst.clm_apply continuous_fst
    have c2 : Continuous fun x : V × StrongDual ℝ V × StrongDual ℝ V => x.2.2 x.1 :=
      continuous_snd.snd.clm_apply continuous_fst
    have c3 : Continuous fun x : V × StrongDual ℝ V × StrongDual ℝ V => x.2.1 u₁ :=
      continuous_snd.fst.clm_apply continuous_const
    have c4 : Continuous fun x : V × StrongDual ℝ V × StrongDual ℝ V => x.2.2 u₂ :=
      continuous_snd.snd.clm_apply continuous_const
    exact ((continuous_const.sub c1).max (continuous_const.sub c2)).max (c3.max c4)
  obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hKne hG.continuousOn
  set m := G x₀ with hm_def
  have hm : 0 < m := by
    by_contra hle
    replace hle := le_of_not_gt hle
    obtain ⟨⟨hy1, hy2⟩, hφ1, hφ2⟩ := hx₀
    rw [mem_closedBall_zero_iff] at hy1 hφ1 hφ2
    simp only [m, G, max_le_iff] at hle
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hle
    have e1 : x₀.2.1 x₀.1 = 1 := le_antisymm (apply_le_one hφ1 hy1) (by linarith)
    have e2 : x₀.2.2 x₀.1 = 1 := le_antisymm (apply_le_one hφ2 hy1) (by linarith)
    exact hcore x₀.1 hy1 hy2 _ _ hφ1 hφ2 e1 e2 h3 h4
  have hdich : ∀ y ∈ C, (∀ φ : StrongDual ℝ V, ‖φ‖ ≤ 1 → φ y ≤ 1 - m ∨ m ≤ φ u₁) ∨
      (∀ φ : StrongDual ℝ V, ‖φ‖ ≤ 1 → φ y ≤ 1 - m ∨ m ≤ φ u₂) := by
    intro y hy
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [not_forall, not_or, not_le] at h1 h2
    obtain ⟨φ₁, hφ₁, hφ₁y, hφ₁u⟩ := h1
    obtain ⟨φ₂, hφ₂, hφ₂y, hφ₂u⟩ := h2
    have hmem : (y, φ₁, φ₂) ∈ K :=
      ⟨hy, by rwa [mem_closedBall_zero_iff], by rwa [mem_closedBall_zero_iff]⟩
    have := hmin hmem
    simp only [Set.mem_ofPred_eq] at this
    have hlt : G (y, φ₁, φ₂) < m := by
      simp only [G]
      refine max_lt (max_lt ?_ ?_) (max_lt hφ₁u hφ₂u) <;> linarith
    exact absurd this (not_le.2 hlt)
  -- the parameters
  have hn₁ : 0 < ‖u₁‖ := norm_pos_iff.2 hu₁
  have hn₂ : 0 < ‖u₂‖ := norm_pos_iff.2 hu₂
  set μ := min m 1 with hμ
  have hμ0 : 0 < μ := lt_min hm one_pos
  have hμm : μ ≤ m := min_le_left _ _
  have hμ1 : μ ≤ 1 := min_le_right _ _
  set M := max ‖u₁‖ ‖u₂‖ + 1 with hM
  have hM1 : 1 ≤ M := by have := le_max_left ‖u₁‖ ‖u₂‖; linarith
  have hMu₁ : ‖u₁‖ ≤ M := by have := le_max_left ‖u₁‖ ‖u₂‖; linarith
  have hMu₂ : ‖u₂‖ ≤ M := by have := le_max_right ‖u₁‖ ‖u₂‖; linarith
  set ρ := min ‖u₁‖ ‖u₂‖ with hρ
  have hρ0 : 0 < ρ := lt_min hn₁ hn₂
  set t₀ := μ / (2 * M) with ht₀
  have ht₀0 : 0 < t₀ := by positivity
  have ht₀M : t₀ * M = μ / 2 := by rw [ht₀]; field_simp
  have ht₀1 : t₀ ≤ 1 / 2 := by
    rw [ht₀, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set r := t₀ * min (μ / 2) (ρ / 2) with hr
  have hr0 : 0 < r := by positivity
  have hrμ : r ≤ t₀ * (μ / 2) := mul_le_mul_of_nonneg_left (min_le_left _ _) ht₀0.le
  have hrρ : r ≤ t₀ * (ρ / 2) := mul_le_mul_of_nonneg_left (min_le_right _ _) ht₀0.le
  have hk : ∀ u : V, ρ ≤ ‖u‖ → ‖u‖ ≤ M → ∀ c : V, ‖c - t₀ • u‖ < r →
      c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ t₀ * ‖u‖ + r ≤ m ∧ r ≤ t₀ * m := by
    intro u hρu huM c hc
    have htu : t₀ * ‖u‖ ≤ μ / 2 := by
      rw [← ht₀M]; exact mul_le_mul_of_nonneg_left huM ht₀0.le
    have hnorm_tu : ‖t₀ • u‖ = t₀ * ‖u‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht₀0.le]
    have hlow : t₀ * ‖u‖ - ‖c - t₀ • u‖ ≤ ‖c‖ := by
      have := norm_sub_norm_le (t₀ • u) (t₀ • u - c)
      rw [sub_sub_cancel, hnorm_tu, norm_sub_rev] at this
      linarith
    have hup : ‖c‖ ≤ t₀ * ‖u‖ + ‖c - t₀ • u‖ := by
      have := norm_add_le (t₀ • u) (c - t₀ • u)
      rw [add_sub_cancel, hnorm_tu] at this
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      have hc0 : ‖c‖ = 0 := by rw [h0, norm_zero]
      have : t₀ * ρ ≤ t₀ * ‖u‖ := mul_le_mul_of_nonneg_left hρu ht₀0.le
      linarith [mul_pos ht₀0 hρ0]
    · nlinarith
    · nlinarith
    · nlinarith
  refine ⟨ball (t₀ • u₁) r ×ˢ ball (t₀ • u₂) r, isOpen_ball.prod isOpen_ball,
    ⟨(t₀ • u₁, t₀ • u₂), mem_ball_self hr0, mem_ball_self hr0⟩, ?_⟩
  rintro ⟨c₁, c₂⟩ ⟨hc₁, hc₂⟩
  rw [mem_ball, dist_eq_norm] at hc₁ hc₂
  obtain ⟨hc₁0, hc₁1, hc₁a, hc₁b⟩ := hk u₁ (min_le_left _ _) hMu₁ c₁ hc₁
  obtain ⟨hc₂0, hc₂1, hc₂a, hc₂b⟩ := hk u₂ (min_le_right _ _) hMu₂ c₂ hc₂
  refine ⟨hc₁0, hc₂0, hc₁1, hc₂1, ?_⟩
  intro y hy
  rw [mem_closedBall_zero_iff] at hy
  by_cases hye : ‖y - e‖ ≤ 1
  · left; left
    rw [mem_closedBall, dist_eq_norm]
    have : y - s • e = (1 - s) • y + s • (y - e) := by module
    rw [this]
    calc ‖(1 - s) • y + s • (y - e)‖ ≤ ‖(1 - s) • y‖ + ‖s • (y - e)‖ := norm_add_le _ _
      _ = (1 - s) * ‖y‖ + s * ‖y - e‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg hs0.le]
      _ ≤ (1 - s) * 1 + s * 1 := by gcongr
      _ = 1 := by ring
  · have hyC : y ∈ C := ⟨by rwa [mem_closedBall_zero_iff], by
      show 1 ≤ ‖y - e‖; linarith [le_of_not_ge hye]⟩
    rcases hdich y hyC with h | h
    · left; right
      rw [mem_closedBall, dist_eq_norm]
      exact close hy ht₀0 hc₁ hc₁a hc₁b h
    · right
      rw [mem_closedBall, dist_eq_norm]
      exact close hy ht₀0 hc₂ hc₂a hc₂b h

/-- The real inequalities behind `cone_interior`. -/
theorem real_cone {c₁ c₂ α β X Y P Q E₁ E₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (h1 : 0 ≤ -c₁ * X + c₂ * (P - Y)) (h2 : 0 ≤ c₁ * (Q - X) - c₂ * Y)
    (h3 : 0 < -α * X + β * (P - Y)) (h4 : 0 < α * (Q - X) - β * Y)
    (h5 : α * E₁ + β * E₂ ≤ 0) : False := by
  have hPY : 0 ≤ P - Y := by
    by_contra h
    have := mul_neg_of_pos_of_neg hc₂ (lt_of_not_ge h)
    nlinarith [mul_nonneg hc₁.le hX]
  have hQX : 0 ≤ Q - X := by
    by_contra h
    have := mul_neg_of_pos_of_neg hc₁ (lt_of_not_ge h)
    nlinarith [mul_nonneg hc₂.le hY]
  rcases le_or_gt 0 α with hα | hα <;> rcases le_or_gt 0 β with hβ | hβ
  · have := mul_nonneg hα hE₁.le
    have := mul_nonneg hβ hE₂.le
    have hα0 : α = 0 := by
      by_contra h
      have := mul_pos (lt_of_le_of_ne hα (Ne.symm h)) hE₁
      linarith
    have hβ0 : β = 0 := by
      by_contra h
      have := mul_pos (lt_of_le_of_ne hβ (Ne.symm h)) hE₂
      linarith
    subst hα0 hβ0
    simp at h3
  · nlinarith [mul_nonneg hα hX, mul_nonpos_of_nonneg_of_nonpos hPY hβ.le]
  · nlinarith [mul_nonneg hβ hY, mul_nonpos_of_nonneg_of_nonpos hQX hα.le]
  · have hX0 : 0 < X := by
      rcases hX.lt_or_eq with h | h
      · exact h
      · subst h
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hPY hβ.le]
    have hY0 : 0 < Y := by
      rcases hY.lt_or_eq with h | h
      · exact h
      · subst h
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hQX hα.le]
    have k1 : c₁ * X ≤ c₂ * (P - Y) := by linarith
    have k2 : c₂ * Y ≤ c₁ * (Q - X) := by linarith
    have k3 : (-β) * (P - Y) < (-α) * X := by linarith
    have k4 : (-α) * (Q - X) < (-β) * Y := by linarith
    have m1 : (c₁ * X) * (c₂ * Y) ≤ (c₂ * (P - Y)) * (c₁ * (Q - X)) :=
      mul_le_mul k1 k2 (by positivity) (by nlinarith)
    have m2 : ((-β) * (P - Y)) * ((-α) * (Q - X)) < ((-α) * X) * ((-β) * Y) :=
      mul_lt_mul'' k3 k4 (by nlinarith) (by nlinarith)
    have e1 : (c₁ * c₂) * (X * Y) ≤ (c₁ * c₂) * ((P - Y) * (Q - X)) := by linarith
    have e2 : (α * β) * ((P - Y) * (Q - X)) < (α * β) * (X * Y) := by linarith
    have f1 := le_of_mul_le_mul_left e1 (mul_pos hc₁ hc₂)
    have f2 := lt_of_mul_lt_mul_left e2 (mul_pos_of_neg_of_neg hα hβ).le
    linarith

/-- Elementary bounds for two norming pairs near `e`. -/
theorem pair_bounds {e p q : V} {χ₁ χ₂ : StrongDual ℝ V} (h1 : ‖χ₁‖ ≤ 1) (h2 : ‖χ₂‖ ≤ 1)
    (hχ₁p : χ₁ p = 1) (hχ₂q : χ₂ q = 1) (hχ₂p : χ₂ p < 1) (hχ₁q : χ₁ q < 1)
    (hpe : ‖p - e‖ < 1) (hqe : ‖q - e‖ < 1) :
    -1 < χ₂ p ∧ -1 < χ₁ q ∧ 0 < 1 - χ₁ q * χ₂ p ∧ 0 < χ₁ e ∧ 0 < χ₂ e := by
  have hpq : ‖q - p‖ < 2 := by
    calc ‖q - p‖ = ‖(q - e) - (p - e)‖ := by congr 1; abel
      _ ≤ ‖q - e‖ + ‖p - e‖ := norm_sub_le _ _
      _ < 2 := by linarith
  have a1 : χ₂ (q - p) ≤ ‖q - p‖ := (le_abs_self _).trans (abs_apply_le h2 _)
  have a2 : χ₁ (p - q) ≤ ‖p - q‖ := (le_abs_self _).trans (abs_apply_le h1 _)
  have b1 : χ₁ (p - e) ≤ ‖p - e‖ := (le_abs_self _).trans (abs_apply_le h1 _)
  have b2 : χ₂ (q - e) ≤ ‖q - e‖ := (le_abs_self _).trans (abs_apply_le h2 _)
  rw [norm_sub_rev] at a2
  rw [map_sub] at a1 a2 b1 b2
  have c1 : -1 < χ₂ p := by linarith
  have c2 : -1 < χ₁ q := by linarith
  refine ⟨c1, c2, ?_, by linarith, by linarith⟩
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - χ₁ q) (by linarith : (0:ℝ) < 1 + χ₂ p),
    mul_pos (by linarith : (0:ℝ) < 1 + χ₁ q) (by linarith : (0:ℝ) < 1 - χ₂ p)]

/-- Strictly positive combinations of two functionals norming points near `e` (each below one at
the other point) norm no point of the ball far from `e`. -/
theorem cone_interior (hV : Module.finrank ℝ V = 2) {e p q : V} {χ₁ χ₂ : StrongDual ℝ V}
    (h1 : ‖χ₁‖ ≤ 1) (h2 : ‖χ₂‖ ≤ 1) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (hχ₁p : χ₁ p = 1) (hχ₂q : χ₂ q = 1) (hχ₂p : χ₂ p < 1) (hχ₁q : χ₁ q < 1)
    (hpe : ‖p - e‖ < 1) (hqe : ‖q - e‖ < 1) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    {v : V} (hv : ‖v‖ ≤ 1) (hve : 1 ≤ ‖v - e‖) :
    (c₁ • χ₁ + c₂ • χ₂) v < ‖c₁ • χ₁ + c₂ • χ₂‖ := by
  by_contra hcon
  replace hcon := le_of_not_gt hcon
  obtain ⟨-, -, hdet, hE₁, hE₂⟩ := pair_bounds h1 h2 hχ₁p hχ₂q hχ₂p hχ₁q hpe hqe
  have hφp := apply_le_norm (c₁ • χ₁ + c₂ • χ₂) hp
  have hφq := apply_le_norm (c₁ • χ₁ + c₂ • χ₂) hq
  have hve0 : v - e ≠ 0 := by
    intro h; rw [h, norm_zero] at hve; linarith
  obtain ⟨χ, hχn, hχv⟩ := exists_norming hve0
  have hd : χ₁ p * χ₂ q - χ₁ q * χ₂ p ≠ 0 := by rw [hχ₁p, hχ₂q]; linarith
  obtain ⟨u₁, u₂, -, -, -, -, hdec⟩ := exists_u hV χ₁ χ₂ p q hd
  have hχdec : ∀ z, χ z = (-χ u₂) * χ₁ z + (-χ u₁) * χ₂ z := by
    intro z
    conv_lhs => rw [hdec z]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have f1 : χ v ≤ 1 := apply_le_one hχn.le hv
  have f2 : χ (p - e) ≤ ‖p - e‖ := (le_abs_self _).trans (abs_apply_le hχn.le _)
  have f3 : χ (q - e) ≤ ‖q - e‖ := (le_abs_self _).trans (abs_apply_le hχn.le _)
  rw [map_sub] at hχv f2 f3
  have g1 : χ₁ v ≤ 1 := apply_le_one h1 hv
  have g2 : χ₂ v ≤ 1 := apply_le_one h2 hv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    at hφp hφq hcon
  rw [hχ₁p] at hφp
  rw [hχ₂q] at hφq
  have dv := hχdec v
  have dp := hχdec p
  have dq := hχdec q
  have de := hχdec e
  rw [hχ₁p] at dp
  rw [hχ₂q] at dq
  refine real_cone (X := 1 - χ₁ v) (Y := 1 - χ₂ v) (P := 1 - χ₂ p) (Q := 1 - χ₁ q)
    (α := -χ u₂) (β := -χ u₁) (E₁ := χ₁ e) (E₂ := χ₂ e) hc₁ hc₂ (by linarith) (by linarith)
    hE₁ hE₂ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

/-- A functional of norm at most one norming two distinct extreme points near `e` norms no
point of the ball far from `e`. -/
theorem edge (hV : Module.finrank ℝ V = 2) {e y₁ y₂ : V} {χ : StrongDual ℝ V} (hχ : ‖χ‖ ≤ 1)
    (hy₁ : y₁ ∈ extremePoints ℝ (closedBall (0 : V) 1))
    (hy₂ : y₂ ∈ extremePoints ℝ (closedBall (0 : V) 1)) (hne : y₁ ≠ y₂)
    (h1 : χ y₁ = 1) (h2 : χ y₂ = 1) (he1 : ‖y₁ - e‖ < 1) (he2 : ‖y₂ - e‖ < 1)
    {v : V} (hv : ‖v‖ ≤ 1) (hve : 1 ≤ ‖v - e‖) : χ v < 1 := by
  by_contra hcon
  have hχv : χ v = 1 := le_antisymm (apply_le_one hχ hv) (le_of_not_gt hcon)
  have h21 : y₂ - y₁ ≠ 0 := sub_ne_zero.2 hne.symm
  obtain ⟨θ, -, hθ⟩ := exists_norming h21
  have hd0 : 0 < θ y₂ - θ y₁ := by rw [← map_sub, hθ]; exact norm_pos_iff.2 h21
  have hd : χ y₁ * θ y₂ - χ y₂ * θ y₁ ≠ 0 := by rw [h1, h2]; linarith
  have hvt : v = y₁ + ((θ v - θ y₁) / (θ y₂ - θ y₁)) • (y₂ - y₁) := by
    apply eq_of_apply_eq hV hd
    · simp [h1, h2, hχv]
    · simp only [map_add, map_smul, map_sub, smul_eq_mul]
      field_simp
      ring
  set t := (θ v - θ y₁) / (θ y₂ - θ y₁) with ht
  have hy₁' := mem_extremePoints.1 hy₁
  have hy₂' := mem_extremePoints.1 hy₂
  have hvB : v ∈ closedBall (0 : V) 1 := mem_closedBall_zero_iff.2 hv
  rcases lt_or_ge t 0 with ht0 | ht0
  · have h1t : (1 - t) ≠ 0 := by linarith
    have h := hy₁'.2 v hvB y₂ hy₂'.1 ⟨1 / (1 - t), -t / (1 - t), by
      apply div_pos one_pos; linarith, by apply div_pos <;> linarith, by
      field_simp; ring, by
      rw [hvt]
      match_scalars <;> field_simp <;> ring⟩
    exact hne h.2.symm
  rcases le_or_gt t 1 with ht1 | ht1
  · have hsplit : v - e = (1 - t) • (y₁ - e) + t • (y₂ - e) := by rw [hvt]; module
    have hlt : ‖v - e‖ < 1 := by
      rw [hsplit]
      calc ‖(1 - t) • (y₁ - e) + t • (y₂ - e)‖ ≤ ‖(1 - t) • (y₁ - e)‖ + ‖t • (y₂ - e)‖ :=
            norm_add_le _ _
        _ = (1 - t) * ‖y₁ - e‖ + t * ‖y₂ - e‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
        _ < 1 := by
          rcases ht0.lt_or_eq with htp | hte
          · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) (norm_nonneg (y₁ - e))]
          · rw [← hte]; simpa using he1
    linarith
  · have h := hy₂'.2 y₁ hy₁'.1 v hvB ⟨1 - 1 / t, 1 / t, by
      rw [sub_pos, div_lt_one (by linarith)]; exact ht1, by
      apply div_pos one_pos; linarith, by ring, by
      rw [hvt]
      have ht0' : t ≠ 0 := by linarith
      match_scalars <;> field_simp <;> ring⟩
    exact hne h.1

/-- On the compact set of points of the ball far from `e`, a functional below one stays below
`1 - δ`. -/
theorem margin (hV : Module.finrank ℝ V = 2) {e : V} {χ : StrongDual ℝ V}
    (h : ∀ v : V, ‖v‖ ≤ 1 → 1 ≤ ‖v - e‖ → χ v < 1) :
    ∃ δ > 0, ∀ v : V, ‖v‖ ≤ 1 → 1 ≤ ‖v - e‖ → χ v ≤ 1 - δ := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  set C : Set V := closedBall (0 : V) 1 ∩ {v | 1 ≤ ‖v - e‖} with hC
  have hCc : IsCompact C := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun v hv hve => ?_⟩
    have hvC : v ∈ C := ⟨mem_closedBall_zero_iff.2 hv, hve⟩
    rw [hCe] at hvC
    exact absurd hvC (Set.notMem_empty v)
  · obtain ⟨v₀, hv₀, hmax⟩ := hCc.exists_isMaxOn hCne χ.continuous.continuousOn
    have hv₀lt := h v₀ (mem_closedBall_zero_iff.1 hv₀.1) hv₀.2
    refine ⟨1 - χ v₀, by linarith, fun v hv hve => ?_⟩
    have := hmax (show v ∈ C from ⟨mem_closedBall_zero_iff.2 hv, hve⟩)
    simp only [Set.mem_ofPred_eq] at this
    linarith

/-- The data needed by `core`, from a functional norming two distinct extreme points near `e`. -/
theorem caseA (hV : Module.finrank ℝ V = 2) {e y₁ y₂ : V} {χ : StrongDual ℝ V} (hχ : ‖χ‖ ≤ 1)
    (hy₁ : y₁ ∈ extremePoints ℝ (closedBall (0 : V) 1))
    (hy₂ : y₂ ∈ extremePoints ℝ (closedBall (0 : V) 1)) (hne : y₁ ≠ y₂)
    (h1 : χ y₁ = 1) (h2 : χ y₂ = 1) (he1 : ‖y₁ - e‖ < 1) (he2 : ‖y₂ - e‖ < 1) :
    ∃ ψ₁ ψ₂ : StrongDual ℝ V, ∃ x y : V, ψ₁ x * ψ₂ y - ψ₁ y * ψ₂ x ≠ 0 ∧
      (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 < a + b → ∀ v : V, ‖v‖ ≤ 1 → 1 ≤ ‖v - e‖ →
        (a • ψ₁ + b • ψ₂) v < ‖a • ψ₁ + b • ψ₂‖) ∧
      (∀ w : V, ‖w‖ ≤ 1 → ψ₁ w = ‖ψ₁‖ → ψ₂ w = ‖ψ₂‖ → False) := by
  obtain ⟨δ, hδ, hmar⟩ :=
    margin hV (fun v hv hve => edge hV hχ hy₁ hy₂ hne h1 h2 he1 he2 hv hve)
  have h21 : y₂ - y₁ ≠ 0 := sub_ne_zero.2 hne.symm
  obtain ⟨θ, hθn, hθ⟩ := exists_norming h21
  have hd0 : 0 < θ y₂ - θ y₁ := by rw [← map_sub, hθ]; exact norm_pos_iff.2 h21
  have hy₁n : ‖y₁‖ ≤ 1 := mem_closedBall_zero_iff.1 (mem_extremePoints.1 hy₁).1
  have hy₂n : ‖y₂‖ ≤ 1 := mem_closedBall_zero_iff.1 (mem_extremePoints.1 hy₂).1
  have hε0 : 0 < δ / 3 := by positivity
  refine ⟨χ + (δ / 3) • θ, χ - (δ / 3) • θ, y₁, y₂, ?_, ?_, ?_⟩
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, h1, h2]
    intro h
    nlinarith [mul_pos hε0 hd0]
  · intro a b ha hb hab v hv hve
    have hθv : |θ v| ≤ 1 := (abs_apply_le hθn.le v).trans hv
    have hθy : |θ y₁| ≤ 1 := (abs_apply_le hθn.le y₁).trans hy₁n
    have hlow := apply_le_norm (a • (χ + (δ / 3) • θ) + b • (χ - (δ / 3) • θ)) hy₁n
    have hχv := hmar v hv hve
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at hlow ⊢
    rw [h1] at hlow
    have hab' : |a - b| ≤ a + b := abs_le.2 ⟨by linarith, by linarith⟩
    have k1 : (a - b) * θ v ≤ a + b := by
      have : |(a - b) * θ v| ≤ a + b := by
        rw [abs_mul]
        calc |a - b| * |θ v| ≤ (a + b) * 1 := mul_le_mul hab' hθv (abs_nonneg _) (by linarith)
          _ = a + b := mul_one _
      linarith [le_abs_self ((a - b) * θ v)]
    have k2 : -((a - b) * θ y₁) ≤ a + b := by
      have : |(a - b) * θ y₁| ≤ a + b := by
        rw [abs_mul]
        calc |a - b| * |θ y₁| ≤ (a + b) * 1 := mul_le_mul hab' hθy (abs_nonneg _) (by linarith)
          _ = a + b := mul_one _
      linarith [neg_abs_le ((a - b) * θ y₁)]
    nlinarith [mul_le_mul_of_nonneg_left k1 hε0.le, mul_le_mul_of_nonneg_left k2 hε0.le,
      mul_le_mul_of_nonneg_left hχv (by linarith : (0:ℝ) ≤ a + b), mul_pos hab hδ]
  · intro w hw hψ₁ hψ₂
    have l2 := apply_le_norm (χ + (δ / 3) • θ) hy₂n
    have l3 := apply_le_norm (χ - (δ / 3) • θ) hy₁n
    have hχw := apply_le_one hχ hw
    rw [← hψ₁] at l2
    rw [← hψ₂] at l3
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, h1, h2] at l2 l3
    nlinarith [mul_pos hε0 hd0]

/-- The data needed by `core`, from two functionals norming points near `e`, each below one at
the other point, whose sum has norm below two. -/
theorem caseB (hV : Module.finrank ℝ V = 2) {e p q : V} {χ₁ χ₂ : StrongDual ℝ V}
    (h1 : ‖χ₁‖ ≤ 1) (h2 : ‖χ₂‖ ≤ 1) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (hχ₁p : χ₁ p = 1) (hχ₂q : χ₂ q = 1) (hχ₂p : χ₂ p < 1) (hχ₁q : χ₁ q < 1)
    (hpe : ‖p - e‖ < 1) (hqe : ‖q - e‖ < 1) (hN : ‖χ₁ + χ₂‖ < 2) :
    ∃ ψ₁ ψ₂ : StrongDual ℝ V, ∃ x y : V, ψ₁ x * ψ₂ y - ψ₁ y * ψ₂ x ≠ 0 ∧
      (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 < a + b → ∀ v : V, ‖v‖ ≤ 1 → 1 ≤ ‖v - e‖ →
        (a • ψ₁ + b • ψ₂) v < ‖a • ψ₁ + b • ψ₂‖) ∧
      (∀ w : V, ‖w‖ ≤ 1 → ψ₁ w = ‖ψ₁‖ → ψ₂ w = ‖ψ₂‖ → False) := by
  obtain ⟨hb1, hb2, hdet, -, -⟩ := pair_bounds h1 h2 hχ₁p hχ₂q hχ₂p hχ₁q hpe hqe
  have hN0 : 0 ≤ ‖χ₁ + χ₂‖ := norm_nonneg _
  have hε0 : 0 < (2 - ‖χ₁ + χ₂‖) / 8 := by linarith
  have hε1 : (2 - ‖χ₁ + χ₂‖) / 8 < 1 := by linarith
  refine ⟨χ₁ + ((2 - ‖χ₁ + χ₂‖) / 8) • χ₂, ((2 - ‖χ₁ + χ₂‖) / 8) • χ₁ + χ₂, p, q, ?_, ?_, ?_⟩
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hχ₁p, hχ₂q]
    intro h
    have hprod : (1 - ((2 - ‖χ₁ + χ₂‖) / 8) ^ 2) * (1 - χ₁ q * χ₂ p) = 0 := by linarith
    rcases mul_eq_zero.1 hprod with h' | h'
    · nlinarith
    · linarith
  · intro a b ha hb hab v hv hve
    have heq : a • (χ₁ + ((2 - ‖χ₁ + χ₂‖) / 8) • χ₂) + b • (((2 - ‖χ₁ + χ₂‖) / 8) • χ₁ + χ₂) =
        (a + b * ((2 - ‖χ₁ + χ₂‖) / 8)) • χ₁ + (a * ((2 - ‖χ₁ + χ₂‖) / 8) + b) • χ₂ := by
      module
    rw [heq]
    have hc₁ : 0 < a + b * ((2 - ‖χ₁ + χ₂‖) / 8) := by
      rcases ha.lt_or_eq with ha' | ha'
      · nlinarith [mul_nonneg hb hε0.le]
      · rw [← ha'] at hab ⊢; nlinarith [mul_pos (by linarith : (0:ℝ) < b) hε0]
    have hc₂ : 0 < a * ((2 - ‖χ₁ + χ₂‖) / 8) + b := by
      rcases hb.lt_or_eq with hb' | hb'
      · nlinarith [mul_nonneg ha hε0.le]
      · rw [← hb'] at hab ⊢; nlinarith [mul_pos (by linarith : (0:ℝ) < a) hε0]
    exact cone_interior hV h1 h2 hp hq hχ₁p hχ₂q hχ₂p hχ₁q hpe hqe hc₁ hc₂ hv hve
  · intro w hw hψ₁ hψ₂
    have l1 := apply_le_norm (χ₁ + ((2 - ‖χ₁ + χ₂‖) / 8) • χ₂) hp
    have l2 := apply_le_norm (((2 - ‖χ₁ + χ₂‖) / 8) • χ₁ + χ₂) hq
    have l3 := apply_le_norm (χ₁ + χ₂) hw
    rw [← hψ₁] at l1
    rw [← hψ₂] at l2
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hχ₁p, hχ₂q] at l1 l2 l3
    nlinarith [mul_le_mul_of_nonneg_left l3 (by linarith : (0:ℝ) ≤ 1 + (2 - ‖χ₁ + χ₂‖) / 8),
      mul_le_mul_of_nonneg_left hb1.le hε0.le, mul_le_mul_of_nonneg_left hb2.le hε0.le,
      mul_pos (by linarith : (0:ℝ) < 2 - ‖χ₁ + χ₂‖) (by linarith : (0:ℝ) < 6 - ‖χ₁ + χ₂‖)]

/-- A point of the ball normed by two functionals that separate points is extreme. -/
theorem mem_extremePoints_of_two (hV : Module.finrank ℝ V = 2) {χ₁ χ₂ : StrongDual ℝ V}
    {x y w : V} (hd : χ₁ x * χ₂ y - χ₁ y * χ₂ x ≠ 0) (h1 : ‖χ₁‖ ≤ 1) (h2 : ‖χ₂‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (hw1 : χ₁ w = 1) (hw2 : χ₂ w = 1) :
    w ∈ extremePoints ℝ (closedBall (0 : V) 1) := by
  rw [mem_extremePoints]
  refine ⟨mem_closedBall_zero_iff.2 hw, fun z₁ hz₁ z₂ hz₂ hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hzw⟩ := hseg
  rw [mem_closedBall_zero_iff] at hz₁ hz₂
  have k1 := apply_le_one h1 hz₁
  have k2 := apply_le_one h1 hz₂
  have k3 := apply_le_one h2 hz₁
  have k4 := apply_le_one h2 hz₂
  have e1 : a * χ₁ z₁ + b * χ₁ z₂ = 1 := by rw [← hw1, ← hzw]; simp
  have e2 : a * χ₂ z₁ + b * χ₂ z₂ = 1 := by rw [← hw2, ← hzw]; simp
  have f1 : χ₁ z₁ = 1 := le_antisymm k1 (by nlinarith [mul_nonneg hb.le (sub_nonneg.2 k2)])
  have f2 : χ₁ z₂ = 1 := le_antisymm k2 (by nlinarith [mul_nonneg ha.le (sub_nonneg.2 k1)])
  have f3 : χ₂ z₁ = 1 := le_antisymm k3 (by nlinarith [mul_nonneg hb.le (sub_nonneg.2 k4)])
  have f4 : χ₂ z₂ = 1 := le_antisymm k4 (by nlinarith [mul_nonneg ha.le (sub_nonneg.2 k3)])
  exact ⟨eq_of_apply_eq hV hd (by rw [f1, hw1]) (by rw [f3, hw2]),
    eq_of_apply_eq hV hd (by rw [f2, hw1]) (by rw [f4, hw2])⟩

end Sol_Plasticity_Plane_exists_open_completions

open Sol_Plasticity_Plane_exists_open_completions in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (e p q : V) (he : ‖e‖ = 1)
    (hp : p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1))
    (hq : q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) (hpq : p ≠ q)
    (hpe : ‖p - e‖ < 1) (hqe : ‖q - e‖ < 1) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ U : Set (V × V), IsOpen U ∧ U.Nonempty ∧ ∀ c ∈ U, c.1 ≠ 0 ∧ c.2 ≠ 0 ∧
      ‖c.1‖ ≤ 1 ∧ ‖c.2‖ ≤ 1 ∧
      Metric.closedBall (0 : V) 1 ⊆
        Metric.closedBall (s • e) 1 ∪ Metric.closedBall c.1 1 ∪ Metric.closedBall c.2 1 := by
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have hpn : ‖p‖ = 1 := by simpa using extremePoints_closedBall_subset_sphere hp
  have hqn : ‖q‖ = 1 := by simpa using extremePoints_closedBall_subset_sphere hq
  have hp0 : p ≠ 0 := by intro h; rw [h, norm_zero] at hpn; exact zero_ne_one hpn
  have hq0 : q ≠ 0 := by intro h; rw [h, norm_zero] at hqn; exact zero_ne_one hqn
  obtain ⟨χp, hχpn, hχpp⟩ := exists_norming hp0
  obtain ⟨χq, hχqn, hχqq⟩ := exists_norming hq0
  rw [hpn] at hχpp
  rw [hqn] at hχqq
  obtain ⟨ψ₁, ψ₂, x, y, hd, H2, H3⟩ : ∃ ψ₁ ψ₂ : StrongDual ℝ V, ∃ x y : V,
      ψ₁ x * ψ₂ y - ψ₁ y * ψ₂ x ≠ 0 ∧
      (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 < a + b → ∀ v : V, ‖v‖ ≤ 1 → 1 ≤ ‖v - e‖ →
        (a • ψ₁ + b • ψ₂) v < ‖a • ψ₁ + b • ψ₂‖) ∧
      (∀ w : V, ‖w‖ ≤ 1 → ψ₁ w = ‖ψ₁‖ → ψ₂ w = ‖ψ₂‖ → False) := by
    by_cases hpq1 : χp q = 1
    · exact caseA hV hχpn.le hp hq hpq hχpp hpq1 hpe hqe
    by_cases hqp1 : χq p = 1
    · exact caseA hV hχqn.le hq hp hpq.symm hχqq hqp1 hqe hpe
    have hpq' : χp q < 1 := lt_of_le_of_ne (apply_le_one hχpn.le hqn.le) hpq1
    have hqp' : χq p < 1 := lt_of_le_of_ne (apply_le_one hχqn.le hpn.le) hqp1
    by_cases hN : ‖χp + χq‖ < 2
    · exact caseB hV hχpn.le hχqn.le hpn.le hqn.le hχpp hχqq hqp' hpq' hpe hqe hN
    · have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
      obtain ⟨w, hw, hww⟩ := exists_norm_attained (χp + χq)
      have hN2 : ‖χp + χq‖ = 2 := by
        refine le_antisymm ?_ (le_of_not_gt hN)
        calc ‖χp + χq‖ ≤ ‖χp‖ + ‖χq‖ := norm_add_le _ _
          _ = 2 := by rw [hχpn, hχqn]; norm_num
      rw [hN2] at hww
      simp only [ContinuousLinearMap.add_apply] at hww
      have hw1 : χp w = 1 := by
        linarith [apply_le_one hχpn.le hw, apply_le_one hχqn.le hw]
      have hw2 : χq w = 1 := by
        linarith [apply_le_one hχpn.le hw, apply_le_one hχqn.le hw]
      have hwe : ‖w - e‖ < 1 := by
        by_contra hcon
        have := cone_interior hV hχpn.le hχqn.le hpn.le hqn.le hχpp hχqq hqp' hpq' hpe hqe
          one_pos one_pos hw (le_of_not_gt hcon)
        simp only [one_smul, ContinuousLinearMap.add_apply] at this
        rw [hN2] at this
        linarith
      obtain ⟨-, -, hdet, -, -⟩ := pair_bounds hχpn.le hχqn.le hχpp hχqq hqp' hpq' hpe hqe
      have hd : χp p * χq q - χp q * χq p ≠ 0 := by rw [hχpp, hχqq]; linarith
      have hwext := mem_extremePoints_of_two hV hd hχpn.le hχqn.le hw hw1 hw2
      have hpw : p ≠ w := by intro h; rw [h] at hqp'; linarith
      exact caseA hV hχpn.le hp hwext hpw hχpp hw1 hpe hwe
  obtain ⟨u₁, u₂, -, h21, -, h12, hdec⟩ := exists_u hV ψ₁ ψ₂ x y hd
  have hu₁ : u₁ ≠ 0 := by intro h; rw [h, map_zero] at h21; norm_num at h21
  have hu₂ : u₂ ≠ 0 := by intro h; rw [h, map_zero] at h12; norm_num at h12
  exact cover hV he hs0 hs1 hu₁ hu₂
    (fun v hv hve φ₁ φ₂ hφ₁ hφ₂ h1 h2 h3 h4 => core hdec H2 H3 hv hve hφ₁ hφ₂ h1 h2 h3 h4)
