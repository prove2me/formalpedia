-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionSmall_proof_2216872fd496
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:04.58593+00:00
-- url     : https://prove2.me/submissions/d51560a5-fbd3-4c3c-a9c9-3da919cae69a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_den_mul_sub_mem_b5370e9419ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_eq_of_mem_c6a1a6b1f6e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_live_of_ne_76717d206e78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_exists_chart_da5014d82c1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_evalCone_chartMonomial_ne_zero_504e49938418
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_eval_cross_e4a6675d6be6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall
namespace GroundTheory.Heights₂.Heights.SectionSmall
theorem _root_.solution : SectionSmall.Statement := by
  intro ι _ _ n P A s
  have bound : ∀ C : ℝ, s.SupNormLE A C → ∀ p q : MvPolynomial (Coord n) ℤ,
      P.mkF p = s.toFun * P.mkF q →
      ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ Real.exp C * (‖evalCone z q‖ * A.metric z) := by
    intro C hC p q hpq z hz
    obtain ⟨c, hc⟩ := exists_chart hz
    obtain ⟨d, e, he⟩ := s.regular c (live_of_ne hz hc)
    have hcross := eval_cross s (den_mul_sub_mem s hpq) he.2 hz
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hb := hC z hz c d e he hc
    rw [div_le_iff₀ (mul_pos hm hh)] at hb
    have hnorm : ‖evalCone z e‖ * ‖evalCone z q‖ =
        ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖ := by
      rw [← norm_mul, ← norm_mul, hcross]
    refine le_of_mul_le_mul_right ?_ hm
    calc ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖
        = ‖evalCone z e‖ * ‖evalCone z q‖ := hnorm.symm
      _ ≤ Real.exp C * (‖evalCone z (chartMonomial c d)‖ * A.metric z) * ‖evalCone z q‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = Real.exp C * (‖evalCone z q‖ * A.metric z) * ‖evalCone z (chartMonomial c d)‖ := by ring
  refine ⟨bound, ⟨fun hs p q δp δq _ _ _ hpq z hz ↦ ?_, fun hsm z hz c d e he hc ↦ ?_⟩⟩
  · simpa [Real.exp_zero] using bound 0 hs p q hpq z hz
  · obtain ⟨⟨δ, hδ, hδd⟩, hmem⟩ := he
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hsmall := hsm e (chartMonomial c d) δ d hδ (isWeightedHomogeneous_chartMonomial c d)
      (fun k ↦ by rw [hδd k]; ring) (mkF_eq_of_mem s hmem) z hz
    rw [Real.exp_zero, div_le_one (mul_pos hm hh)]
    exact hsmall
end GroundTheory.Heights₂.Heights.SectionSmall
