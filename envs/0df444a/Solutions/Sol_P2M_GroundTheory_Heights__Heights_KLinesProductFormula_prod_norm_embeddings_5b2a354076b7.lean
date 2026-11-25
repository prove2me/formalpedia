-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesProductFormula_prod_norm_embeddings_5b2a354076b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:56.65745+00:00
-- url     : https://prove2.me/submissions/d86f02fb-6fbe-4022-8345-e598c4bf1f51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProductFormula

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
open NumberField
open GroundTheory.Heights₂.Heights.KLinesProductFormula
namespace GroundTheory.Heights₂.Heights.KLinesProductFormula
theorem _root_.solution (K : Type) [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  classical
  have h := congr_arg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖)
    (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [← h, eq_ratCast, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]
end GroundTheory.Heights₂.Heights.KLinesProductFormula
