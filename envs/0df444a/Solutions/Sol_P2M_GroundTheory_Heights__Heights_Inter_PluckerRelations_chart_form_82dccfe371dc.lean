-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_chart_form_82dccfe371dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:16.795012+00:00
-- url     : https://prove2.me/submissions/e9453afc-0402-4fce-9f75-4e59f666d091

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_add_744f9eecfdc9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_C_5ce2a68ac976
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_coord_base_7abc0b27051f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_rename_X_base_630ad48861ea

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
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerRelations
theorem _root_.solution (i : S.ι) (hi : S.x i ≠ 0) {a : S.Ω} (ha : a ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base d) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base d) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ d * a) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, X ⟨T.YBlk.base, j⟩, exHomog_X _ _, ?_, ?_⟩
    · rw [rename_X_base]
      exact exHomog_X (ι := S.WIdx) T.WBlk.base j
    · rw [rename_X_base, aeval_X, coord_base]
      congr 1
      field_simp
  | algebraMap r =>
    refine ⟨0, C r, homog_C _ _, ?_, ?_⟩
    · rw [rename_C]
      exact homog_C _ _
    · simp
  | add y z _ _ hy hz =>
    obtain ⟨d₁, Q₁, h₁, h₁', e₁⟩ := hy
    obtain ⟨d₂, Q₂, h₂, h₂', e₂⟩ := hz
    refine ⟨d₁ + d₂, Q₁ * X ⟨T.YBlk.base, i⟩ ^ d₂ + Q₂ * X ⟨T.YBlk.base, i⟩ ^ d₁, ?_, ?_, ?_⟩
    · refine homog_add ?_ ?_
      · convert exHomog_mul h₁ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₂) using 1
        funext b; cases b <;> simp
      · convert exHomog_mul h₂ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₁) using 1
        funext b; cases b <;> simp [add_comm]
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base]
      refine homog_add ?_ ?_
      · convert exHomog_mul h₁' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₂) using 1
        funext b; cases b <;> simp
      · convert exHomog_mul h₂' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₁) using 1
        funext b; cases b <;> simp [add_comm]
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base, map_add, map_mul, map_mul, map_pow, map_pow,
        aeval_X, e₁, e₂, coord_base]
      simp only [map_add, map_mul, map_pow]
      ring
  | mul y z _ _ hy hz =>
    obtain ⟨d₁, Q₁, h₁, h₁', e₁⟩ := hy
    obtain ⟨d₂, Q₂, h₂, h₂', e₂⟩ := hz
    refine ⟨d₁ + d₂, Q₁ * Q₂, ?_, ?_, ?_⟩
    · convert exHomog_mul h₁ h₂ using 1
      funext b; cases b <;> simp
    · rw [map_mul]
      convert exHomog_mul h₁' h₂' using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_mul, e₁, e₂]
      simp only [map_mul, map_pow]
      ring
end GroundTheory.Heights₂.Heights.Inter.PluckerRelations
