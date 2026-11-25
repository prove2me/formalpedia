-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_gaussNormOf_rename_9e948dcb4a17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:39.004395+00:00
-- url     : https://prove2.me/submissions/5b15cc84-26d8-49ab-920d-6a1af59fd369

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R : Type*} [CommRing R] (w : AbsoluteValue R ℝ) {σ τ : Type*}
    {f : σ → τ} (hf : Function.Injective f) (x : MvPolynomial σ R) :
    gaussNormOf w (rename f x) = gaussNormOf w x := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (gaussNormOf_nonneg w x) fun d => ?_
    by_cases hd : ∃ m, Finsupp.mapDomain f m = d
    · obtain ⟨m, rfl⟩ := hd
      rw [coeff_rename_mapDomain f hf]
      exact le_gaussNormOf w x m
    · rw [coeff_rename_eq_zero f x d fun m h => (hd ⟨m, h⟩).elim, map_zero]
      exact gaussNormOf_nonneg w x
  · refine gaussNormOf_le w (gaussNormOf_nonneg w _) fun m => ?_
    rw [← coeff_rename_mapDomain f hf]
    exact le_gaussNormOf w _ _
end GroundTheory.Heights₂.Heights.Vertical
