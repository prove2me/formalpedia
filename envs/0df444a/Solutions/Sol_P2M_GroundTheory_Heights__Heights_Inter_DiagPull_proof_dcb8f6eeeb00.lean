-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_proof_dcb8f6eeeb00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:23.858179+00:00
-- url     : https://prove2.me/submissions/60ef6af8-b172-4a95-af57-d5957c27c48f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_prod_YBlk_228ddc3d6696
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_divCycle_eq_b3ebe5418455
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_prop_543201ba58eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_diagonalPullback_secondLine_eq_759650f7ce4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_isMultiHomog


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.Inter
namespace DiagPull
theorem _root_.solution : DiagPull.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x e φ δ a₀
  refine ⟨fun s d hs => DiagPull.divCycle_eq x δ e φ a₀ s d hs, ?_, ?_⟩
  · intro A A₀ A₁ h0 h1 z hz
    obtain ⟨c, hc, hk⟩ := DiagPull.exists_line_prop x δ e φ a₀ hz
    refine ⟨c, hc, hk, ?_⟩
    rw [h1.2, h0.2, DiagPull.diagonalPullback_secondLine_eq hk]
    have hne : ∀ b, DiagPull.lineScal c b ≠ 0 := fun b => by cases b <;> simp [DiagPull.lineScal, hc]
    rw [A.smul _ _ hne]
    congr 1
    rw [DiagPull.prod_YBlk]
    simp [DiagPull.lineScal]
  · intro s d hs A A₀ A₁ hA h0 h1 z hz
    obtain ⟨c, hc, hk⟩ := DiagPull.exists_line_prop x δ e φ a₀ hz
    have hne : ∀ b, DiagPull.lineScal c b ≠ 0 := fun b => by cases b <;> simp [DiagPull.lineScal, hc]
    have hh : A₁.h z = ‖c‖ ^ (d .line) * A₀.h z := by
      rw [h1.2, h0.2, DiagPull.diagonalPullback_secondLine_eq hk, A.smul _ _ hne, DiagPull.prod_YBlk, hA .line]
      simp [DiagPull.lineScal]
    have hev : eval z (map (Int.castRingHom ℂ) (rename (T.yyEmb 1) s)) =
        c ^ (d .line) * eval z (map (Int.castRingHom ℂ) (rename (T.yyEmb 0) s)) := by
      rw [map_rename, map_rename, eval_rename, eval_rename]
      have e1 : z ∘ T.yyEmb 1 = fun p => DiagPull.lineScal c p.1 * (z ∘ T.yyEmb 0) p :=
        DiagPull.diagonalPullback_secondLine_eq hk
      rw [e1, eval_smul_of_isMultiHomog hs, DiagPull.prod_YBlk]
      simp [DiagPull.lineScal]
    unfold logNorm
    rw [hev, hh, norm_mul, norm_pow, mul_div_mul_left]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
end DiagPull
end GroundTheory.Heights₂.Heights.Inter
