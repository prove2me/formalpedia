-- Prove2me | solution 1 for StarShapedRisk.Representation.proposition2_star_shaped_iff_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:51:33.636529+00:00
-- url     : https://prove2.me/submissions/04438de4-2d5f-41dc-a2ad-5c031bf4b6e9

import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet
import Mathlib.Tactic
open StarShapedRisk.Representation

private theorem star_small {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hs : IsStarShaped 𝒳 ρ) (X : 𝒳.carrier) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ρ (t • X) ≤ t * ρ X := by
  have hh := hs (t • X) t⁻¹ ((one_lt_inv₀ ht0).mpr ht1)
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht0.le
  simpa [← mul_assoc,mul_inv_cancel₀ ht0.ne'] using hm


private theorem risk_const {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsRiskMeasure 𝒳 ρ) (m : ℝ) : ρ (𝒳.const m)=m := by
  have he : (0 : 𝒳.carrier)-𝒳.const (-m)=𝒳.const m := by ext ω; simp [PositionSpace.const]
  have hh := hρ.2.1 0 (-m)
  have hn : ρ 0=0 := hρ.2.2
  rw [he,hn] at hh
  simpa using hh

private theorem shifts_bounds {Ω : Type*} (𝒳 : PositionSpace Ω) (A : Set 𝒳.carrier)
    (hA : IsAcceptanceSet 𝒳 A) (X : 𝒳.carrier) :
    {m : ℝ | X-𝒳.const m ∈ A}.Nonempty ∧ BddBelow {m : ℝ | X-𝒳.const m ∈ A} := by
  obtain ⟨C,hC⟩ := 𝒳.bounded X X.property
  obtain ⟨m,hm⟩ := hA.1.nonempty
  constructor
  · refine ⟨C-m,hA.2 (𝒳.const m) hm (X-𝒳.const (C-m)) ?_⟩
    intro ω
    change X.val ω-(C-m) ≤ m
    have := (abs_le.mp (hC ω)).2
    linarith
  · refine ⟨-C,?_⟩
    intro m hm
    have hac : 𝒳.const (-C-m) ∈ A := hA.2 _ hm _ (by
      intro ω
      change -C-m ≤ X.val ω-m
      have := (abs_le.mp (hC ω)).1
      linarith)
    have hh := hA.1.1 hac
    change -C-m ≤ 0 at hh
    linarith

theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsStarShaped 𝒳 ρ,
       StarConvex ℝ (0 : 𝒳.carrier) (acceptanceSet 𝒳 ρ),
       ∃ A : Set 𝒳.carrier, IsAcceptanceSet 𝒳 A ∧ StarConvex ℝ (0 : 𝒳.carrier) A ∧
         ρ = riskOf 𝒳 A] := by
  tfae_have 1 → 2
  · intro hs Y hY a b ha hb hab
    simp only [smul_zero,zero_add]
    change ρ (b • Y) ≤ 0
    change ρ Y ≤ 0 at hY
    rcases eq_or_lt_of_le hb with hb|hb
    · rw [← hb,zero_smul]
      exact le_of_eq hρ.2.2
    rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1|hb1
    · simpa only [hb1,one_smul] using hY
    · exact (star_small 𝒳 ρ hs Y b hb hb1).trans (mul_nonpos_of_nonneg_of_nonpos hb.le hY)
  tfae_have 2 → 3
  · intro hs
    refine ⟨acceptanceSet 𝒳 ρ,?_,hs,?_⟩
    · constructor
      · have he : {m : ℝ | 𝒳.const m ∈ acceptanceSet 𝒳 ρ}=Set.Iic 0 := by
          ext m
          simp only [acceptanceSet,Set.mem_setOf_eq,Set.mem_Iic,risk_const 𝒳 ρ hρ]
        rw [he]
        exact isLUB_Iic
      · intro X hX Y hYX
        exact (hρ.1 X Y hYX).trans hX
    · funext X
      have he : {m : ℝ | X-𝒳.const m ∈ acceptanceSet 𝒳 ρ}=Set.Ici (ρ X) := by
        ext m
        change ρ (X-𝒳.const m) ≤ 0 ↔ ρ X ≤ m
        rw [hρ.2.1]
        exact sub_nonpos
      simp only [riskOf,he,csInf_Ici]
  tfae_have 3 → 1
  · rintro ⟨A,hA,hs,rfl⟩ X t ht
    have ht0 : 0 < t := by linarith
    apply le_csInf (shifts_bounds 𝒳 A hA (t • X)).1
    intro m hm
    have he : (1-t⁻¹) • (0 : 𝒳.carrier) + t⁻¹ • (t • X-𝒳.const m) = X-𝒳.const (m/t) := by
      ext ω
      simp only [Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Submodule.coe_zero,Pi.zero_apply,
        Submodule.coe_sub,Pi.sub_apply,PositionSpace.const]
      field_simp
      ring
    have hx : X-𝒳.const (m/t) ∈ A := by
      rw [← he]
      exact hs hm (sub_nonneg.mpr ((inv_lt_one₀ ht0).mpr ht).le) (inv_pos.mpr ht0).le (by ring)
    have hi : riskOf 𝒳 A X ≤ m/t := csInf_le (shifts_bounds 𝒳 A hA X).2 hx
    simpa only [mul_comm] using (le_div_iff₀ ht0).mp hi
  tfae_finish

