-- Prove2me | solution 1 for StarShapedRisk.LawInvariant.proposition2_star_shaped_tfae
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T06:14:53.418256+00:00
-- url     : https://prove2.me/submissions/ec8e5776-fe0f-4198-b90c-09a2b386adef

import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace StarShapedRisk.LawInvariant

lemma lr_star_small {Ω : Type*} [MeasurableSpace Ω] (ρ : Positions Ω → ℝ)
    (hs : IsStarShaped ρ) (X : Positions Ω) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ρ (t • X) ≤ t * ρ X := by
  have hh := hs (t • X) t⁻¹ ((one_lt_inv₀ ht0).mpr ht1)
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht0.le
  simpa [← mul_assoc,mul_inv_cancel₀ ht0.ne'] using hm


lemma lr_risk_const {Ω : Type*} [MeasurableSpace Ω] (ρ : Positions Ω → ℝ)
    (hρ : IsRiskMeasure ρ) (m : ℝ) : ρ (const m)=m := by
  have he : (0 : Positions Ω)-const (-m)=const m := by ext ω; simp [const]
  have hh := hρ.2.1 0 (-m)
  have hn : ρ 0=0 := hρ.2.2
  rw [he,hn] at hh
  simpa using hh

lemma lr_shifts_bounds {Ω : Type*} [MeasurableSpace Ω] (A : Set (Positions Ω))
    (hA : IsAcceptanceSet A) (X : Positions Ω) :
    {m : ℝ | X-const m ∈ A}.Nonempty ∧ BddBelow {m : ℝ | X-const m ∈ A} := by
  obtain ⟨C,hC⟩ := X.property.2
  obtain ⟨m,hm⟩ := hA.1.nonempty
  constructor
  · refine ⟨C-m,hA.2 (const m) hm (X-const (C-m)) ?_⟩
    intro ω
    change X.val ω-(C-m) ≤ m
    have := (abs_le.mp (hC ω)).2
    linarith
  · refine ⟨-C,?_⟩
    intro m hm
    have hac : const (-C-m) ∈ A := hA.2 _ hm _ (by
      intro ω
      change -C-m ≤ X.val ω-m
      have := (abs_le.mp (hC ω)).1
      linarith)
    have hh := hA.1.1 hac
    change -C-m ≤ 0 at hh
    linarith

theorem proposition2_star_shaped_tfae {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ) :
    List.TFAE
      [IsStarShaped ρ,
       StarConvex ℝ (0 : Positions Ω) (acceptanceSetOf ρ),
       ∃ A : Set (Positions Ω), IsAcceptanceSet A ∧ StarConvex ℝ (0 : Positions Ω) A ∧
         ρ = rhoOf A] := by
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
    · exact (lr_star_small ρ hs Y b hb hb1).trans (mul_nonpos_of_nonneg_of_nonpos hb.le hY)
  tfae_have 2 → 3
  · intro hs
    refine ⟨acceptanceSetOf ρ,?_,hs,?_⟩
    · constructor
      · have he : {m : ℝ | const m ∈ acceptanceSetOf ρ}=Set.Iic 0 := by
          ext m
          simp only [acceptanceSetOf,Set.mem_setOf_eq,Set.mem_Iic,lr_risk_const ρ hρ]
        rw [he]
        exact isLUB_Iic
      · intro X hX Y hYX
        exact (hρ.1 X Y hYX).trans hX
    · funext X
      have he : {m : ℝ | X-const m ∈ acceptanceSetOf ρ}=Set.Ici (ρ X) := by
        ext m
        change ρ (X-const m) ≤ 0 ↔ ρ X ≤ m
        rw [hρ.2.1]
        exact sub_nonpos
      simp only [rhoOf,he,csInf_Ici]
  tfae_have 3 → 1
  · rintro ⟨A,hA,hs,rfl⟩ X t ht
    have ht0 : 0 < t := by linarith
    apply le_csInf (lr_shifts_bounds A hA (t • X)).1
    intro m hm
    have he : (1-t⁻¹) • (0 : Positions Ω) + t⁻¹ • (t • X-const m) = X-const (m/t) := by
      ext ω
      simp only [Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Submodule.coe_zero,Pi.zero_apply,
        Submodule.coe_sub,Pi.sub_apply,const]
      field_simp
      ring
    have hx : X-const (m/t) ∈ A := by
      rw [← he]
      exact hs hm (sub_nonneg.mpr ((inv_lt_one₀ ht0).mpr ht).le) (inv_pos.mpr ht0).le (by ring)
    have hi : rhoOf A X ≤ m/t := csInf_le (lr_shifts_bounds A hA X).2 hx
    simpa only [mul_comm] using (le_div_iff₀ ht0).mp hi
  tfae_finish


end StarShapedRisk.LawInvariant

open StarShapedRisk.LawInvariant in

/-- Castagnoli et al. (2022), Proposition 2 (p. 2642), on the space of bounded measurable
positions: for a risk measure `ρ`, the following are equivalent:
(i) `ρ` is star-shaped; (ii) the acceptance set `A_ρ` is star-shaped;
(iii) `ρ = ρ_A` for some star-shaped acceptance set `A`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ) :
    List.TFAE
      [IsStarShaped ρ,
       StarConvex ℝ 0 (acceptanceSetOf ρ),
       ∃ A : Set (Positions Ω), IsAcceptanceSet A ∧ StarConvex ℝ 0 A ∧ ρ = rhoOf A] := by
  exact proposition2_star_shaped_tfae ρ hρ


#check solution
#print axioms solution
