-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_rootCoord_isIntegral_77b0fc8c9165
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:14:17.892204+00:00
-- url     : https://prove2.me/submissions/d2e0c004-588b-4e61-a2c6-587a67a97972

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
namespace GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
theorem _root_.solution {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  classical
  apply IsIntegral.det
  intro a b
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  generalize p.2.1.orderEmbOfFin p.2.2 b = c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · rw [Fin.append_left]
    by_cases h : a = c
    · subst h; rw [Matrix.one_apply_eq]; exact isIntegral_one
    · rw [Matrix.one_apply_ne h]; exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hpow⟩ := hζ p.1 a c
    exact IsIntegral.of_pow hk (by rw [hpow]; exact isIntegral_one)
end GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
