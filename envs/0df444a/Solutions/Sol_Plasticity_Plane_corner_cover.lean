-- Prove2me | solution 1 for Plasticity.Plane.corner_cover
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:42.625079+00:00
-- url     : https://prove2.me/submissions/2734b993-7b7d-4042-a07b-57c9d2c626ef

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Filter Topology

namespace Sol_Plasticity_Plane_corner_cover

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

/-- Joint continuity of evaluation along a filter. -/
theorem tendsto_apply {ι : Type*} {l : Filter ι} {φ : ι → StrongDual ℝ V} {u : ι → V}
    {φ₀ : StrongDual ℝ V} {w : V} (hφ : Tendsto φ l (𝓝 φ₀)) (hu : Tendsto u l (𝓝 w)) :
    Tendsto (fun n => φ n (u n)) l (𝓝 (φ₀ w)) :=
  ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := ℝ)).continuous.tendsto (φ₀, w)).comp
    (hφ.prodMk_nhds hu)

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

end

/-- The scalar core of the case analysis. -/
theorem scalar {a b a' b' p q : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : b' ≤ 0)
    (h1 : a + b ≤ 1) (h2 : -(a + b) ≤ 1) (h3 : a' + b' ≤ 1) (h4 : -(a' + b') ≤ 1)
    (e1 : a * p + b * q = 1) (e2 : a' * p + b' * q = 1)
    (hp1 : p ≤ 1) (hp2 : -1 ≤ p) (hq1 : q ≤ 1) (hq2 : -1 ≤ q) :
    (p = 1 ∧ q = 1) ∨ (p = -1 ∧ q = -1) := by
  have eq1 : (a' * b - a * b') * q = a' - a := by linear_combination a' * e1 - a * e2
  have eq2 : (a' * b - a * b') * p = b - b' := by linear_combination b * e2 - b' * e1
  have k1 : a' * b - a * b' ≤ a' - a := by
    nlinarith [mul_nonneg ha' (show 0 ≤ 1 - (a + b) by linarith),
      mul_nonneg (show 0 ≤ -a by linarith) (show 0 ≤ 1 - (a' + b') by linarith)]
  have k2 : -(a' * b - a * b') ≤ a' - a := by
    nlinarith [mul_nonneg ha' (show 0 ≤ 1 + (a + b) by linarith),
      mul_nonneg (show 0 ≤ -a by linarith) (show 0 ≤ 1 + (a' + b') by linarith)]
  have k3 : a' * b - a * b' ≤ b - b' := by
    nlinarith [mul_nonneg hb (show 0 ≤ 1 - (a' + b') by linarith),
      mul_nonneg (show 0 ≤ -b' by linarith) (show 0 ≤ 1 - (a + b) by linarith)]
  have k4 : -(a' * b - a * b') ≤ b - b' := by
    nlinarith [mul_nonneg hb (show 0 ≤ 1 + (a' + b') by linarith),
      mul_nonneg (show 0 ≤ -b' by linarith) (show 0 ≤ 1 + (a + b) by linarith)]
  set N := a' * b - a * b' with hN
  rcases lt_trichotomy N 0 with hn | hn | hn
  · right
    constructor
    · nlinarith
    · nlinarith
  · exfalso
    rw [hn, zero_mul] at eq1 eq2
    have : a = 0 := by linarith
    have : b = 0 := by linarith
    subst a b
    linarith
  · left
    constructor
    · nlinarith
    · nlinarith

/-- A functional with both coordinates positive norms only the corner direction. -/
theorem sA {A B P Q N : ℝ} (hA : 0 < A) (hB : 0 < B) (e : N = A * P + B * Q)
    (hP : P ≤ N) (hQ : Q ≤ N) (hAB : A + B ≤ 1) (hN : 0 ≤ N) : P = N ∧ Q = N := by
  constructor
  · by_contra h
    have h' : 0 < N - P := by
      rcases lt_or_gt_of_ne h with h | h
      · linarith
      · linarith
    nlinarith [mul_pos hA h', mul_nonneg hB.le (show 0 ≤ N - Q by linarith),
      mul_nonneg (show 0 ≤ 1 - A - B by linarith) hN]
  · by_contra h
    have h' : 0 < N - Q := by
      rcases lt_or_gt_of_ne h with h | h
      · linarith
      · linarith
    nlinarith [mul_pos hB h', mul_nonneg hA.le (show 0 ≤ N - P by linarith),
      mul_nonneg (show 0 ≤ 1 - A - B by linarith) hN]

/-- The inequality used near `-x`. -/
theorem sD {A B P Q N X : ℝ} (hA : A < 0) (hB : 0 < B) (e : N = A * P + B * Q)
    (hP : -N ≤ P) (hX : -(A + B * X) ≤ 1) (hN : 0 ≤ N) : 0 ≤ X * N + Q := by
  have h : 0 ≤ B * (X * N + Q) := by
    nlinarith [mul_nonneg (show 0 ≤ -A by linarith) (show 0 ≤ P + N by linarith),
      mul_nonneg hN (show 0 ≤ 1 + A + B * X by linarith)]
  exact (mul_nonneg_iff_of_pos_left hB).mp h

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- One half of the limit analysis: the side of the functionals `φ n` norming
`z n + μ n • (x - x₁)`. -/
theorem half (hV : Module.finrank ℝ V = 2) {x x₁ x₂ : V} {f₁ f₂ : StrongDual ℝ V}
    (hf₁ : ‖f₁‖ ≤ 1) (hf₂ : ‖f₂‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (h₁x₁ : f₁ x₁ = 1) (h₁x : f₁ x = 1) (h₂x : f₂ x = 1) (h₂x₂ : f₂ x₂ = 1)
    (h₁x₂ : f₁ x₂ < 1) (h₂x₁ : f₂ x₁ < 1)
    {z : ℕ → V} {μ : ℕ → ℝ} {φ : ℕ → StrongDual ℝ V} {w : V} {φ₀ : StrongDual ℝ V}
    (hz : ∀ n, ‖z n‖ ≤ 1) (hμ : ∀ n, 0 < μ n) (hμ0 : Tendsto μ atTop (𝓝 0))
    (hu : ∀ n, 1 < ‖z n + μ n • (x - x₁)‖)
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (hφu : ∀ n, φ n (z n + μ n • (x - x₁)) = ‖z n + μ n • (x - x₁)‖)
    (hzw : Tendsto z atTop (𝓝 w)) (hφl : Tendsto φ atTop (𝓝 φ₀)) (hφ₀ : ‖φ₀‖ ≤ 1) :
    0 ≤ φ₀ (x - x₁) / f₂ (x - x₁) ∧
    φ₀ (x₂ - x) / f₁ (x₂ - x) + φ₀ (x - x₁) / f₂ (x - x₁) ≤ 1 ∧
    -(φ₀ (x₂ - x) / f₁ (x₂ - x) + φ₀ (x - x₁) / f₂ (x - x₁)) ≤ 1 ∧
    φ₀ (x₂ - x) / f₁ (x₂ - x) * f₁ w + φ₀ (x - x₁) / f₂ (x - x₁) * f₂ w = 1 ∧
    (0 < φ₀ (x₂ - x) / f₁ (x₂ - x) → f₁ w = 1 ∧ f₂ w = 1) ∧
    (‖x₁‖ ≤ 1 → ¬ (f₁ w = -1 ∧ f₂ w = -1)) := by
  have h11 : f₁ (x - x₁) = 0 := by rw [map_sub, h₁x, h₁x₁, sub_self]
  have h22 : f₂ (x₂ - x) = 0 := by rw [map_sub, h₂x, h₂x₂, sub_self]
  have hB : 0 < f₂ (x - x₁) := by rw [map_sub, h₂x]; linarith
  have hA : f₁ (x₂ - x) < 0 := by rw [map_sub, h₁x]; linarith
  have dec := decomp hV h11 h22 hA.ne hB.ne'
  set r₁ := x - x₁ with hr₁
  set r₂ := x₂ - x with hr₂
  set u : ℕ → V := fun n => z n + μ n • r₁ with hu_def
  have hul : Tendsto u atTop (𝓝 w) := by
    have := hzw.add (hμ0.smul_const r₁)
    simpa using this
  have hnu : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖w‖) := hul.norm
  have hw1 : ‖w‖ ≤ 1 := le_of_tendsto' hzw.norm hz
  have hw2 : 1 ≤ ‖w‖ := ge_of_tendsto' hnu (fun n => (hu n).le)
  have hw : ‖w‖ = 1 := le_antisymm hw1 hw2
  have hpos : ∀ n, 0 < φ n r₁ := by
    intro n
    have h1 := hφu n
    rw [map_add, map_smul, smul_eq_mul] at h1
    have h2 := apply_le (hφ n) (z n)
    have h3 := hz n
    have h4 := hu n
    have h5 : 0 < μ n * φ n r₁ := by linarith
    exact pos_of_mul_pos_right h5 (hμ n).le
  have hφw : φ₀ w = 1 := by
    have h1 : Tendsto (fun n => φ n (u n)) atTop (𝓝 (φ₀ w)) := tendsto_apply hφl hul
    have h2 : (fun n => φ n (u n)) = fun n => ‖u n‖ := funext hφu
    rw [h2] at h1
    rw [← hw]
    exact tendsto_nhds_unique h1 hnu
  have hr₁l : Tendsto (fun n => φ n r₁) atTop (𝓝 (φ₀ r₁)) := tendsto_apply hφl tendsto_const_nhds
  have hr₂l : Tendsto (fun n => φ n r₂) atTop (𝓝 (φ₀ r₂)) := tendsto_apply hφl tendsto_const_nhds
  have hb : 0 ≤ φ₀ r₁ / f₂ r₁ := div_nonneg (ge_of_tendsto' hr₁l (fun n => (hpos n).le)) hB.le
  have hx_dec : φ₀ x = φ₀ r₂ / f₁ r₂ + φ₀ r₁ / f₂ r₁ := by rw [dec φ₀ x, h₁x, h₂x]; ring
  have hab1 : φ₀ r₂ / f₁ r₂ + φ₀ r₁ / f₂ r₁ ≤ 1 := hx_dec ▸ (apply_le hφ₀ x).trans hx
  have hab2 : -(φ₀ r₂ / f₁ r₂ + φ₀ r₁ / f₂ r₁) ≤ 1 := by
    rw [← hx_dec]; linarith [neg_le_apply hφ₀ x]
  have hw_dec : φ₀ r₂ / f₁ r₂ * f₁ w + φ₀ r₁ / f₂ r₁ * f₂ w = 1 := by rw [← dec φ₀ w, hφw]
  have hal : Tendsto (fun n => φ n r₂ / f₁ r₂) atTop (𝓝 (φ₀ r₂ / f₁ r₂)) := hr₂l.div_const _
  have hf₁u : Tendsto (fun n => f₁ (u n)) atTop (𝓝 (f₁ w)) := (f₁.continuous.tendsto w).comp hul
  have hf₂u : Tendsto (fun n => f₂ (u n)) atTop (𝓝 (f₂ w)) := (f₂.continuous.tendsto w).comp hul
  refine ⟨hb, hab1, hab2, hw_dec, ?_, ?_⟩
  · intro ha
    have hev := hal.eventually_const_lt ha
    have key : ∀ᶠ n in atTop, f₁ (u n) = ‖u n‖ ∧ f₂ (u n) = ‖u n‖ := by
      filter_upwards [hev] with n hn
      have d2 := dec (φ n) x
      rw [h₁x, h₂x, mul_one, mul_one] at d2
      refine sA hn (div_pos (hpos n) hB) ((hφu n).symm.trans (dec (φ n) (u n)))
        (apply_le hf₁ _) (apply_le hf₂ _) ?_ (norm_nonneg _)
      rw [← d2]
      exact (apply_le (hφ n) x).trans hx
    rw [hw] at hnu
    exact ⟨tendsto_nhds_unique_of_eventuallyEq hf₁u hnu (key.mono fun n hn => hn.1),
      tendsto_nhds_unique_of_eventuallyEq hf₂u hnu (key.mono fun n hn => hn.2)⟩
  · rintro hx₁ ⟨hp, hq⟩
    have ha : φ₀ r₂ / f₁ r₂ < 0 := by rw [hp, hq] at hw_dec; linarith
    have hev := hal.eventually_lt_const ha
    have key : ∀ᶠ n in atTop, 0 ≤ f₂ x₁ * ‖u n‖ + f₂ (u n) := by
      filter_upwards [hev] with n hn
      have d3 := dec (φ n) x₁
      rw [h₁x₁, mul_one] at d3
      refine sD hn (div_pos (hpos n) hB) ((hφu n).symm.trans (dec (φ n) (u n)))
        (neg_le_apply hf₁ _) ?_ (norm_nonneg _)
      rw [← d3]
      linarith [neg_le_apply (hφ n) x₁]
    have hlim : Tendsto (fun n => f₂ x₁ * ‖u n‖ + f₂ (u n)) atTop
        (𝓝 (f₂ x₁ * ‖w‖ + f₂ w)) := (hnu.const_mul _).add hf₂u
    have := ge_of_tendsto hlim key
    rw [hw, hq] at this
    linarith

end

end Sol_Plasticity_Plane_corner_cover

open Sol_Plasticity_Plane_corner_cover in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (x x₁ x₂ : V) (f₁ f₂ : StrongDual ℝ V)
    (hf₁ : ‖f₁‖ = 1) (hf₂ : ‖f₂‖ = 1) (hx₁ : ‖x₁‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (h₁x₁ : f₁ x₁ = 1) (h₁x : f₁ x = 1) (h₂x : f₂ x = 1) (h₂x₂ : f₂ x₂ = 1)
    (h₁x₂ : f₁ x₂ < 1) (h₂x₁ : f₂ x₁ < 1) (U : Set V) (hU : U ∈ nhds x) :
    ∃ r > 0, ∀ μ μ' : ℝ, 0 < μ → μ ≤ r → 0 < μ' → μ' ≤ r →
      Metric.closedBall (0 : V) 1 ⊆
        U ∪ Metric.closedBall (-(μ • (x - x₁))) 1 ∪ Metric.closedBall (μ' • (x₂ - x)) 1 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  by_contra H
  have H' : ∀ n : ℕ, ∃ μ : ℝ, ∃ μ' : ℝ, ∃ z : V, 0 < μ ∧ μ ≤ 1 / ((n : ℝ) + 1) ∧ 0 < μ' ∧
      μ' ≤ 1 / ((n : ℝ) + 1) ∧ ‖z‖ ≤ 1 ∧ δ ≤ dist z x ∧ 1 < ‖z + μ • (x - x₁)‖ ∧
      1 < ‖z + μ' • (x - x₂)‖ := by
    intro n
    have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hn
    apply H
    refine ⟨1 / ((n : ℝ) + 1), hr, fun μ μ' hμ hμr hμ' hμ'r z hz => ?_⟩
    by_contra hzn
    apply hn
    refine ⟨μ, μ', z, hμ, hμr, hμ', hμ'r, mem_closedBall_zero_iff.mp hz, ?_, ?_, ?_⟩
    · by_contra h
      push Not at h
      exact hzn (Or.inl (Or.inl (hball (Metric.mem_ball.mpr h))))
    · by_contra h
      push Not at h
      refine hzn (Or.inl (Or.inr ?_))
      rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add]
      exact h
    · by_contra h
      push Not at h
      refine hzn (Or.inr ?_)
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : z - μ' • (x₂ - x) = z + μ' • (x - x₂) := by
        rw [← neg_sub x x₂, smul_neg, sub_neg_eq_add]
      rw [this]
      exact h
  choose μ μ' z hμ hμr hμ' hμ'r hz hzx hu hv using H'
  choose φ hφ1 hφu using fun n =>
    exists_dual_vector ℝ (z n + μ n • (x - x₁)) (by linarith [hu n])
  choose ψ hψ1 hψv using fun n =>
    exists_dual_vector ℝ (z n + μ' n • (x - x₂)) (by linarith [hv n])
  set K := Metric.closedBall (0 : V) 1 ×ˢ
    (Metric.closedBall (0 : StrongDual ℝ V) 1 ×ˢ Metric.closedBall (0 : StrongDual ℝ V) 1)
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨⟨w, φ₀, ψ₀⟩, hmem, σ, hσ, hlim⟩ := hK.tendsto_subseq (x := fun n => (z n, φ n, ψ n))
    (fun n => ⟨mem_closedBall_zero_iff.mpr (hz n), mem_closedBall_zero_iff.mpr (hφ1 n).le,
      mem_closedBall_zero_iff.mpr (hψ1 n).le⟩)
  obtain ⟨hw₀, hφ₀, hψ₀⟩ := hmem
  simp only [mem_closedBall_zero_iff] at hw₀ hφ₀ hψ₀
  have hzl : Tendsto (z ∘ σ) atTop (𝓝 w) := (continuous_fst.tendsto _).comp hlim
  have hφl : Tendsto (φ ∘ σ) atTop (𝓝 φ₀) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hψl : Tendsto (ψ ∘ σ) atTop (𝓝 ψ₀) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  have hσn : Tendsto (fun n => 1 / ((σ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop
  have hμl : Tendsto (μ ∘ σ) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hμ _).le) (fun n => hμr _) hσn
  have hμ'l : Tendsto (μ' ∘ σ) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hμ' _).le) (fun n => hμ'r _) hσn
  have hwx : w ≠ x := by
    have : δ ≤ dist w x := ge_of_tendsto' (hzl.dist tendsto_const_nhds) (fun n => hzx _)
    intro h
    rw [h, dist_self] at this
    linarith
  have hf₁' : ‖f₁‖ ≤ 1 := hf₁.le
  have hf₂' : ‖f₂‖ ≤ 1 := hf₂.le
  obtain ⟨hb, hab1, hab2, hφw, hA, hD⟩ := half hV hf₁' hf₂' hx h₁x₁ h₁x h₂x h₂x₂ h₁x₂ h₂x₁
    (z := z ∘ σ) (μ := μ ∘ σ) (φ := φ ∘ σ) (fun n => hz _) (fun n => hμ _) hμl
    (fun n => hu _) (fun n => (hφ1 _).le) (fun n => by simpa using hφu (σ n)) hzl hφl hφ₀
  obtain ⟨ha', hab1', hab2', hψw, hB', -⟩ := half hV hf₂' hf₁' hx h₂x₂ h₂x h₁x h₁x₁ h₂x₁ h₁x₂
    (z := z ∘ σ) (μ := μ' ∘ σ) (φ := ψ ∘ σ) (fun n => hz _) (fun n => hμ' _) hμ'l
    (fun n => hv _) (fun n => (hψ1 _).le) (fun n => by simpa using hψv (σ n)) hzl hψl hψ₀
  have e1 : ψ₀ (x - x₂) / f₁ (x - x₂) = ψ₀ (x₂ - x) / f₁ (x₂ - x) := by
    rw [← neg_sub x₂ x, map_neg, map_neg, neg_div_neg_eq]
  have e2 : ψ₀ (x₁ - x) / f₂ (x₁ - x) = ψ₀ (x - x₁) / f₂ (x - x₁) := by
    rw [← neg_sub x x₁, map_neg, map_neg, neg_div_neg_eq]
  rw [e1] at ha'
  rw [e1, e2] at hab1' hab2' hψw
  rw [e2] at hB'
  have h11 : f₁ (x - x₁) = 0 := by rw [map_sub, h₁x, h₁x₁, sub_self]
  have h22 : f₂ (x₂ - x) = 0 := by rw [map_sub, h₂x, h₂x₂, sub_self]
  have hB : 0 < f₂ (x - x₁) := by rw [map_sub, h₂x]; linarith
  have hA0 : f₁ (x₂ - x) < 0 := by rw [map_sub, h₁x]; linarith
  have hxeq : f₁ w = 1 → f₂ w = 1 → w = x := by
    intro hp hq
    by_contra hne
    have hne' : ‖w - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ (w - x) hne'
    have := decomp hV h11 h22 hA0.ne hB.ne' g (w - x)
    have k1 : f₁ (w - x) = 0 := by rw [map_sub, hp, h₁x, sub_self]
    have k2 : f₂ (w - x) = 0 := by rw [map_sub, hq, h₂x, sub_self]
    rw [k1, k2, mul_zero, mul_zero, add_zero] at this
    apply hne'
    have hg' : g (w - x) = ‖w - x‖ := by simpa using hg
    rw [← hg', this]
  have hp1 := apply_le hf₁' w
  have hp2 := neg_le_apply hf₁' w
  have hq1 := apply_le hf₂' w
  have hq2 := neg_le_apply hf₂' w
  by_cases ha : 0 < φ₀ (x₂ - x) / f₁ (x₂ - x)
  · obtain ⟨hp, hq⟩ := hA ha
    exact hwx (hxeq hp hq)
  by_cases hb' : 0 < ψ₀ (x - x₁) / f₂ (x - x₁)
  · obtain ⟨hq, hp⟩ := hB' hb'
    exact hwx (hxeq hp hq)
  push Not at ha hb'
  rcases scalar ha hb ha' hb' hab1 hab2 (by linarith) (by linarith) hφw (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) with ⟨hp, hq⟩ | hpq
  · exact hwx (hxeq hp hq)
  · exact hD hx₁ hpq
