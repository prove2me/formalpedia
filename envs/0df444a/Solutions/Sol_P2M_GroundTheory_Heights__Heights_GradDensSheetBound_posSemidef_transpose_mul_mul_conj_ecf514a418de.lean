-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_posSemidef_transpose_mul_mul_conj_ecf514a418de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:21.276425+00:00
-- url     : https://prove2.me/submissions/71d2afed-e4c0-4e0b-b890-dd875ab745d0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound

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
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound
namespace GroundTheory.Heights₂.Heights.GradDensSheetBound
theorem _root_.solution {n m : ℕ} (J : Matrix (Fin n) (Fin m) ℂ)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) :
    (Jᵀ * P * J.map (starRingEnd ℂ)).PosSemidef := by
  have e : Jᵀ = (J.map (starRingEnd ℂ))ᴴ := by
    ext i j; simp [conjTranspose_apply]
  rw [e]
  exact hP.conjTranspose_mul_mul_same _
end GroundTheory.Heights₂.Heights.GradDensSheetBound
