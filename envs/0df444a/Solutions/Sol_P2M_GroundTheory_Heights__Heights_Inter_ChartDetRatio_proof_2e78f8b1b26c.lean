-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_proof_2e78f8b1b26c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:38.129812+00:00
-- url     : https://prove2.me/submissions/1c6e6d61-85e0-4382-b091-e606a7fd68b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_mem_adjoin_of_mem_chartRing_d26bab57a1af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_sum_a71ef09db231
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_ne_zero_9a848b44ec1c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartDetRatio
theorem _root_.solution : ChartDetRatio.Statement := by
  intro Ω _ _ ι ν _ _ E _ _ x B e δ i₀ hx hδ
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  have hR : ∀ a ∈ chartRing ℤ x i₀, a ∈ F := fun a ha => ChartDetRatio.mem_adjoin_of_mem_chartRing x i₀ ha
  obtain ⟨k, f, c, hf, -, hcf, hb⟩ := B.frame i₀ hx
  obtain ⟨l₁, hl₁⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcf
  obtain ⟨b, hbli, hbsp, hbiff⟩ := hb l₁
  have hfF : f l₁ ∈ F := hR _ (hf l₁)
  have hcoord : ∀ u ∈ B.lat i₀, ∃ a : Fin 2 → Ω, (∀ q, a q ∈ F) ∧ u = ∑ q, a q • b q := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := (hbiff u).1 ⟨0, by simpa using hu⟩
    refine ⟨a, fun q => ?_, rfl⟩
    obtain ⟨n, hn⟩ := ha q
    have h2 : a q = (f l₁ ^ n)⁻¹ * (f l₁ ^ n * a q) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl₁), one_mul]
    rw [h2]
    exact mul_mem (inv_mem (pow_mem hfF n)) (hR _ hn)
  set D := T.detE e (b 0) (b 1) with hDdef
  have hD : D ≠ 0 := ChartDetRatio.detE_ne_zero e b hbli hbsp
  have hdet : ∀ u ∈ B.lat i₀, ∀ w ∈ B.lat i₀, ∃ s ∈ F, T.detE e u w = D * s := by
    intro u hu w hw
    obtain ⟨a, ha, rfl⟩ := hcoord u hu
    obtain ⟨a', ha', rfl⟩ := hcoord w hw
    refine ⟨a 0 * a' 1 - a 1 * a' 0,
      sub_mem (mul_mem (ha 0) (ha' 1)) (mul_mem (ha 1) (ha' 0)), ?_⟩
    rw [ChartDetRatio.detE_sum, mul_comm]
  have hspan : ∀ y ∈ Submodule.span (chartRing ℤ x i₀)
      {d | ∃ u ∈ B.lat i₀, ∃ w ∈ B.lat i₀, d = x i₀ * T.detE e u w}, ∃ s ∈ F, y = x i₀ * D * s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, w, hw, rfl⟩ := hy
      obtain ⟨s, hs, h⟩ := hdet u hu w hw
      exact ⟨s, hs, by rw [h]; ring⟩
    | zero => exact ⟨0, zero_mem _, by ring⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨s + t, add_mem hs ht, by ring⟩
    | smul a y _ hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      refine ⟨(a : Ω) * s, mul_mem (hR _ a.2) hs, ?_⟩
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
  have hδs : ∀ l, ∃ s ∈ F, δ l = x i₀ * D * s := fun l => hspan _ ((hδ i₀ hx).1 l)
  have hbmem : ∀ q, ∃ n : ℕ, f l₁ ^ n • b q ∈ B.lat i₀ := by
    intro q
    refine (hbiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases h : q' = q
      · subst h
        simp [one_mem (chartRing ℤ x i₀)]
      · simp [h, zero_mem (chartRing ℤ x i₀)]
    · fin_cases q <;> simp
  obtain ⟨n0, h0⟩ := hbmem 0
  obtain ⟨n1, h1⟩ := hbmem 1
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, δ l₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hm := (hδ i₀ hx).2 _ h0 _ h1
    have hbot : Submodule.span (chartRing ℤ x i₀) (Set.range fun l => (x i₀)⁻¹ * δ l) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      simp [h l]
    rw [hbot, Submodule.mem_bot] at hm
    have hsm : T.detE e (f l₁ ^ n0 • b 0) (f l₁ ^ n1 • b 1) = f l₁ ^ n0 * f l₁ ^ n1 * D := by
      simp only [T.detE, map_smul, Finsupp.smul_apply, smul_eq_mul, hDdef]
      ring
    rw [hsm] at hm
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl₁) (pow_ne_zero _ hl₁)) hD hm
  obtain ⟨s₀, hs₀, hδ₀⟩ := hδs l₀
  have hs₀ne : s₀ ≠ 0 := by
    rintro rfl
    exact hl₀ (by rw [hδ₀, mul_zero])
  refine ⟨l₀, hl₀, fun l => ?_⟩
  obtain ⟨s, hs, hδl⟩ := hδs l
  rw [hδl, hδ₀, mul_div_mul_left _ _ (mul_ne_zero hx hD)]
  exact div_mem hs hs₀
end ChartDetRatio
end GroundTheory.Heights₂.Heights.Inter
