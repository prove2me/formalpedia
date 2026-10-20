-- Prove2me | solution 1 for Plasticity.C0Sum.eq_zero_of_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:52.73321+00:00
-- url     : https://prove2.me/submissions/9d1db744-607d-4a40-a0e8-a032fe335444

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_Plane_norm_sub_le_one_of_lens
import Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_of_blocks
import Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_cover
import Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_pin

/-!
No collapse (CUB100 Proposition 5.1, with the scalar blocks of CUB109 §4).

The part card `of_blocks` derives the conclusion from three properties of every block: strict
coverage by extreme points, displacement, and the pin lemma. Here they are verified: for planes by
the part cards `plane_cover` and `plane_pin` and by the extreme lens, and for one-dimensional
blocks directly, where every unit vector is extreme and every pin has `x = 0` and `q` extreme.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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

/-! ### One-dimensional blocks -/

theorem line_eq_smul (hV : Module.finrank ℝ V = 1) {u : V} (hu : u ≠ 0) (v : V) :
    ∃ c : ℝ, v = c • u := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u hu).1 hV v
  exact ⟨c, hc.symm⟩

/-- On a line, every unit vector is an extreme point of the unit ball. -/
theorem line_extreme (hV : Module.finrank ℝ V = 1) {u : V} (hu : ‖u‖ = 1) :
    u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [mem_extremePoints]
  refine ⟨by simp [hu], ?_⟩
  intro a ha b hb hab
  obtain ⟨α, rfl⟩ := line_eq_smul hV hu0 a
  obtain ⟨β, rfl⟩ := line_eq_smul hV hu0 b
  rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le] at ha hb
  obtain ⟨s, s', hs, hs', hss, h⟩ := hab
  have h2 : (s * α + s' * β) • u = (1 : ℝ) • u := by
    rw [one_smul, add_smul, mul_smul, mul_smul]; exact h
  have h1 : s * α + s' * β = 1 := smul_left_injective ℝ hu0 h2
  have hα : α = 1 := le_antisymm ha.2 (by nlinarith)
  have hβ : β = 1 := le_antisymm hb.2 (by nlinarith)
  simp [hα, hβ]

theorem line_exists_unit (hV : Module.finrank ℝ V = 1) : ∃ u : V, ‖u‖ = 1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hV]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨‖v‖⁻¹ • v, ?_⟩
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

theorem norm_sub_normalize {b : V} (hb : ‖b‖ ≤ 1) (hb0 : b ≠ 0) :
    ‖b - ‖b‖⁻¹ • b‖ = 1 - ‖b‖ := by
  have hn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  have e : b - ‖b‖⁻¹ • b = (1 - ‖b‖⁻¹) • b := by rw [sub_smul, one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonpos]
  · field_simp
    ring
  · have : 1 ≤ ‖b‖⁻¹ := by rw [le_inv_comm₀ one_pos hn, inv_one]; exact hb
    linarith

theorem norm_normalize {b : V} (hb0 : b ≠ 0) : ‖‖b‖⁻¹ • b‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hb0)]

theorem line_cover (hV : Module.finrank ℝ V = 1) (b : V) (hb : ‖b‖ ≤ 1) (hb0 : b ≠ 0) :
    ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖b - e‖ < 1 := by
  refine ⟨‖b‖⁻¹ • b, line_extreme hV (norm_normalize hb0), ?_⟩
  rw [norm_sub_normalize hb hb0]
  linarith [norm_pos_iff.2 hb0]

theorem line_disp (hV : Module.finrank ℝ V = 1) (b z : V) (hb : ‖b‖ ≤ 1) (hz : ‖z‖ ≤ 1 / 2)
    (h : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖b - w‖ ≤ 1 → ‖z - w‖ ≤ 1) :
    ‖b - (2 : ℝ) • z‖ ≤ 1 := by
  by_cases hb0 : b = 0
  · obtain ⟨u, hu⟩ := line_exists_unit hV
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have hnu : ‖-u‖ = 1 := by rw [norm_neg, hu]
    have h1 := h u (line_extreme hV hu) (by simp [hb0, hu])
    have h2 := h (-u) (line_extreme hV hnu) (by simp [hb0, hu])
    obtain ⟨ζ, rfl⟩ := line_eq_smul hV hu0 z
    have e1 : ζ • u - u = (ζ - 1) • u := by rw [sub_smul, one_smul]
    have e2 : ζ • u - -u = (ζ + 1) • u := by rw [add_smul, one_smul, sub_neg_eq_add]
    rw [e1, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le] at h1
    rw [e2, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le] at h2
    have hζ : ζ = 0 := by linarith [h1.1, h2.2]
    simp [hb0, hζ]
  · set u := ‖b‖⁻¹ • b with hudef
    have hu : ‖u‖ = 1 := norm_normalize hb0
    have hu0 : u ≠ 0 := by rintro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
    have hn : 0 < ‖b‖ := norm_pos_iff.2 hb0
    have hbu : b = ‖b‖ • u := by rw [hudef, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have h1 := h u (line_extreme hV hu) (by rw [hudef, norm_sub_normalize hb hb0]; linarith)
    obtain ⟨ζ, rfl⟩ := line_eq_smul hV hu0 z
    have e1 : ζ • u - u = (ζ - 1) • u := by rw [sub_smul, one_smul]
    rw [e1, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le] at h1
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le] at hz
    have e2 : b - (2 : ℝ) • ζ • u = (‖b‖ - 2 * ζ) • u := by
      rw [sub_smul, ← hbu, smul_smul]
    rw [e2, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith

theorem line_pin (hV : Module.finrank ℝ V = 1) (q x : V)
    (hq : ‖q‖ ≤ 1) (hq2 : ‖q - (2 : ℝ) • x‖ ≤ 1) (hq1 : ‖q - x‖ = 1) :
    ∃ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖w - (2 : ℝ) • x‖ ≤ 1 ∧
      ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → ∃ ρ > 0, ∀ β y : V,
        ‖β‖ ≤ ‖(1 - 2 * t) • x + t • w‖ → ‖β - w‖ ≤ 1 - t →
        ‖y - ((1 - 2 * t) • x + t • w)‖ < ρ →
        (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
          ‖β - ω‖ ≤ max 1 ‖y - ω‖) →
        ‖q - y‖ ≤ 1 - t := by
  -- `x = 0` and `q` is a unit vector
  have hd0 : q - x ≠ 0 := by intro h; rw [h, norm_zero] at hq1; exact zero_ne_one hq1
  obtain ⟨c, hc⟩ := line_eq_smul hV hd0 x
  have eq1 : q = (1 + c) • (q - x) := by rw [add_smul, one_smul, ← hc]; abel
  have eq2 : q - (2 : ℝ) • x = (1 - c) • (q - x) := by
    rw [sub_smul, one_smul, ← hc, two_smul]; abel
  rw [eq1, norm_smul, hq1, mul_one, Real.norm_eq_abs, abs_le] at hq
  rw [eq2, norm_smul, hq1, mul_one, Real.norm_eq_abs, abs_le] at hq2
  have hc0 : c = 0 := by linarith [hq.2, hq2.2]
  have hx : x = 0 := by rw [hc, hc0, zero_smul]
  subst hx
  rw [sub_zero] at hq1
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq1
  refine ⟨q, line_extreme hV hq1, by simp [hq1], 1, one_pos, fun t ht0 ht1 => ?_⟩
  refine ⟨1 - t, by linarith, fun β y hβ hβw hy hcmp => ?_⟩
  simp only [smul_zero, zero_add] at hβ hy
  rw [norm_smul, Real.norm_of_nonneg ht0.le, hq1, mul_one] at hβ
  have hβt : β = t • q := eq_smul_of_extreme (line_extreme hV hq1) ht0 ht1 hβ hβw
  have hnq : ‖-q‖ = 1 := by rw [norm_neg, hq1]
  have h1 := hcmp (-q) (line_extreme hV hnq)
  rw [hβt, sub_neg_eq_add] at h1
  have e3 : t • q + q = (t + 1) • q := by rw [add_smul, one_smul]
  rw [e3, norm_smul, hq1, mul_one, Real.norm_of_nonneg (by linarith)] at h1
  obtain ⟨η, rfl⟩ := line_eq_smul hV hq0 y
  have e4 : η • q - -q = (η + 1) • q := by rw [add_smul, one_smul, sub_neg_eq_add]
  have e5 : η • q - t • q = (η - t) • q := by rw [sub_smul]
  have e6 : q - η • q = (1 - η) • q := by rw [sub_smul, one_smul]
  rw [e4, norm_smul, hq1, mul_one, Real.norm_eq_abs] at h1
  rw [e5, norm_smul, hq1, mul_one, Real.norm_eq_abs, abs_lt] at hy
  rw [e6, norm_smul, hq1, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [abs_of_pos (by linarith)] at h1
  have : t + 1 ≤ η + 1 := by
    rcases le_total 1 (η + 1) with h | h
    · rw [max_eq_right h] at h1; exact h1
    · rw [max_eq_left h] at h1; linarith
  linarith

/-! ### Planes: displacement from the extreme lens -/

theorem plane_disp (hV : Module.finrank ℝ V = 2) (b z : V) (hb : ‖b‖ ≤ 1) (hz : ‖z‖ ≤ 1 / 2)
    (h : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖b - w‖ ≤ 1 → ‖z - w‖ ≤ 1) :
    ‖b - (2 : ℝ) • z‖ ≤ 1 := by
  have h2z : ‖(2 : ℝ) • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
  have := Plasticity.Plane.norm_sub_le_one_of_lens hV b ((2 : ℝ) • z) hb h2z
    (fun w hw hbw f hf hfw => by
      have hzw := h w hw hbw
      have h1 : f (w - z) ≤ 1 := by
        have := (le_abs_self (f (w - z))).trans (f.le_opNorm (w - z))
        rw [hf, one_mul, norm_sub_rev] at this
        linarith
      rw [map_sub, hfw] at h1
      rw [map_smul, smul_eq_mul]
      linarith)
  rwa [norm_sub_rev] at this

end Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero

open Sol_Plasticity_C0Sum_eq_zero_of_map_eq_zero in
theorem solution {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (F : c0Sum E → c0Sum E)
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E ⊤) i‖ ≤ ‖(x : lp E ⊤) i‖)
    (hext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E ⊤) i ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1) →
        (x : lp E ⊤) i = (F x : lp E ⊤) i)
    (x : c0Sum E) (hx : x ∈ Metric.closedBall (0 : c0Sum E) 1) (i : ι)
    (hFx : (F x : lp E ⊤) i = 0) : (x : lp E ⊤) i = 0 := by
  have hfin : ∀ i, FiniteDimensional ℝ (E i) := fun i => by
    rcases hE i with h | ⟨h, _⟩ <;> exact Module.finite_of_finrank_pos (by omega)
  refine Plasticity.C0Sum.eq_zero_of_map_eq_zero.of_blocks E ?_ ?_ ?_ F hbij hlip hnorm hext
    x hx i hFx
  · intro j b hb hb0
    rcases hE j with h | ⟨h, h4⟩
    · exact line_cover h b hb hb0
    · exact Plasticity.C0Sum.eq_zero_of_map_eq_zero.plane_cover h h4 b hb hb0
  · intro j b z hb hz h
    rcases hE j with hj | ⟨hj, -⟩
    · exact line_disp hj b z hb hz h
    · exact plane_disp hj b z hb hz h
  · intro j q y hq hq2 hq1
    rcases hE j with hj | ⟨hj, -⟩
    · exact line_pin hj q y hq hq2 hq1
    · exact Plasticity.C0Sum.eq_zero_of_map_eq_zero.plane_pin hj q y hq hq2 hq1
