-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_mdisc_cons_smul_tail_e30b329eeb60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:11.876356+00:00
-- url     : https://prove2.me/submissions/41b01ab2-19c4-4072-b3fb-9e6c28631699

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_fst
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_mul_mul


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
theorem _root_.solution {n : ℕ} (c : ℂ) (hc : c ≠ 0)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (W : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons X (fun i => c • W i) : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c ^ n * mdisc (Fin.cons X W : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have e : (Fin.cons X (fun i => c • W i) : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun k => (c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) *
        (Fin.cons (c⁻¹ • X) W : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k * 1 := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [smul_smul, hc]
    · simp
  rw [e, mdisc_mul_mul, mdisc_cons_smul_fst, Matrix.det_smul, det_one, Fintype.card_fin]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.GradDensSheetBound
