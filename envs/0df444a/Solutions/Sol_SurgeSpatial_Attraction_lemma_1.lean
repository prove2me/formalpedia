-- Prove2me | solution 1 for SurgeSpatial.Attraction.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:57:54.29545+00:00
-- url     : https://prove2.me/submissions/397c070f-555a-4e38-9f71-a25e230dff2f

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeAuxL1
open SurgeSpatial.Attraction Filter

lemma Fbar_nonneg (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) (q : ℝ) :
    0 ≤ M.Fbar y q := by
  unfold Market.Fbar; linarith [hM.F_le_one y hy q]

lemma Fbar_eq_zero (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) {q : ℝ}
    (hq : M.Vbar ≤ q) : M.Fbar y q = 0 := by
  unfold Market.Fbar
  have h1 := hM.F_mono y hy hq
  have h2 := hM.F_le_one y hy q
  rw [hM.F_Vbar y hy] at h1
  linarith

lemma lam_nonneg (M : Market) (y : E) : 0 ≤ M.lam y := ENNReal.toReal_nonneg

lemma R_le_one (M : Market) (y : E) (q s : ℝ) : M.R y q s ≤ 1 := by
  unfold Market.R
  split_ifs <;> simp

lemma R_nonneg (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) (q s : ℝ) :
    0 ≤ M.R y q s := by
  unfold Market.R
  split_ifs with h
  · exact le_min zero_le_one
      (div_nonneg (mul_nonneg (lam_nonneg M y) (Fbar_nonneg M hM hy q)) h.le)
  · exact zero_le_one
  · exact le_rfl

lemma R_eq_zero (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) {q : ℝ}
    (hq : M.Vbar ≤ q) (s : ℝ) : M.R y q s = 0 := by
  unfold Market.R
  rw [Fbar_eq_zero M hM hy hq]
  simp

lemma Ufun_nonneg (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) {q : ℝ}
    (hq : 0 ≤ q) (s : ℝ) : 0 ≤ M.Ufun y q s := by
  unfold Market.Ufun
  exact mul_nonneg (mul_nonneg hM.α_pos.le hq) (R_nonneg M hM hy q s)

lemma Ufun_le (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) (q s : ℝ) :
    M.Ufun y q s ≤ M.α * M.Vbar := by
  unfold Market.Ufun
  rcases le_or_gt M.Vbar q with h | h
  · rw [R_eq_zero M hM hy h]; simp; exact mul_nonneg hM.α_pos.le hM.Vbar_pos.le
  · rcases le_or_gt q 0 with h0 | h0
    · have := R_nonneg M hM hy q s
      have : M.α * q * M.R y q s ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hM.α_pos.le h0) this
      nlinarith [hM.α_pos, hM.Vbar_pos]
    · have h1 := R_le_one M y q s
      have h2 := R_nonneg M hM hy q s
      calc M.α * q * M.R y q s ≤ M.α * q * 1 :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hM.α_pos.le h0.le)
        _ ≤ M.α * M.Vbar := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left h.le hM.α_pos.le

/-- generic essSup comparison in `ℝ`. -/
lemma essSup_le_add {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {f g : α → ℝ} {a b c : ℝ} (hfa : ∀ᵐ y ∂μ, a ≤ f y) (hgb : ∀ᵐ y ∂μ, g y ≤ b)
    (h : ∀ᵐ y ∂μ, f y ≤ g y + c) : essSup f μ ≤ essSup g μ + c := by
  haveI : (ae μ).NeBot := ae_neBot.mpr hμ
  have hg : ∀ᵐ y ∂μ, g y ≤ essSup g μ := ae_le_essSup (isBoundedUnder_of_eventually_le hgb)
  refine essSup_le_of_ae_le _ ?_ (isCoboundedUnder_le_of_eventually_le _ hfa)
  filter_upwards [hg, h] with y h1 h2
  linarith

lemma le_essSup_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {f : α → ℝ} {b c : ℝ} (hfb : ∀ᵐ y ∂μ, f y ≤ b) (h : ∀ᵐ y ∂μ, c ≤ f y) :
    c ≤ essSup f μ := by
  haveI : (ae μ).NeBot := ae_neBot.mpr hμ
  calc c = essSup (fun _ => c) μ := (essSup_const c hμ).symm
    _ ≤ essSup f μ := essSup_mono_ae h
        (isCoboundedUnder_le_of_eventually_le _ (Eventually.of_forall fun _ => le_rfl))
        (isBoundedUnder_of_eventually_le hfb)

lemma essSup_le_of_ae' {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {f : α → ℝ} {a c : ℝ} (hfa : ∀ᵐ y ∂μ, a ≤ f y) (h : ∀ᵐ y ∂μ, f y ≤ c) :
    essSup f μ ≤ c := by
  haveI : (ae μ).NeBot := ae_neBot.mpr hμ
  exact essSup_le_of_ae_le _ h (isCoboundedUnder_le_of_eventually_le _ hfa)

/-- Bounds on `Π` for destinations in `C`. -/
lemma Pi_bounds (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E)) {K : ℝ}
    (hK : ∀ y ∈ M.C, ‖y‖ ≤ K) (x : E) {y : E} (hy : y ∈ M.C) (hp : 0 ≤ p y) :
    -(K + ‖x‖) ≤ M.Pi p T x y ∧ M.Pi p T x y ≤ M.α * M.Vbar := by
  unfold Market.Pi Market.U
  have h1 := Ufun_nonneg M hM hy hp (M.sT T y)
  have h2 := Ufun_le M hM hy (p y) (M.sT T y)
  have h3 : ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
  have h4 := hK y hy
  constructor <;> nlinarith [norm_nonneg (y - x)]

lemma VB_le_add (M : Market) (hM : M.Standing) (B : Set E) (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (hΓB : 0 < M.Γ B) (p : E → ℝ) (hp0 : ∀ y ∈ B, 0 ≤ p y)
    (T : Measure (E × E)) (x x' : E) :
    M.VB B p T x ≤ M.VB B p T x' + ‖x - x'‖ := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ y ∈ M.C, ‖y‖ ≤ K := by
    obtain ⟨K, hK⟩ := hM.compact_C.isBounded.exists_norm_le
    exact ⟨K, hK⟩
  have hμ : M.Γ.restrict B ≠ 0 := by
    intro h
    have := congrArg (fun μ : Measure E => μ B) h
    simp [Measure.restrict_apply hB] at this
    exact hΓB.ne' this
  have hmem : ∀ᵐ y ∂(M.Γ.restrict B), y ∈ B := ae_restrict_mem hB
  unfold Market.VB
  refine essSup_le_add hμ (a := -(K + ‖x‖)) (b := M.α * M.Vbar) ?_ ?_ ?_
  · filter_upwards [hmem] with y hy
    exact (Pi_bounds M hM p T hK x (hBC hy) (hp0 y hy)).1
  · filter_upwards [hmem] with y hy
    exact (Pi_bounds M hM p T hK x' (hBC hy) (hp0 y hy)).2
  · filter_upwards with y
    unfold Market.Pi
    have : ‖y - x'‖ ≤ ‖y - x‖ + ‖x - x'‖ := by
      calc ‖y - x'‖ = ‖(y - x) + (x - x')‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith

end SurgeAuxL1

namespace SurgeSpatial.Attraction
end SurgeSpatial.Attraction

open SurgeSpatial.Attraction in
theorem solution (M : Market) (hM : M.Standing) (B : Set E) (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (hΓB : 0 < M.Γ B) (p : E → ℝ) (hp : Measurable (B.domRestrict p))
    (hp0 : ∀ y ∈ B, 0 ≤ p y) (T : Measure (E × E)) (hT : M.FeasFlow T) :
    LipschitzOnWith 1 (M.VB B p T) M.C := by
  refine LipschitzOnWith.of_le_add_mul 1 ?_
  intro x _ y _
  have := SurgeAuxL1.VB_le_add M hM B hB hBC hΓB p hp0 T x y
  rw [dist_eq_norm]
  simpa using this
