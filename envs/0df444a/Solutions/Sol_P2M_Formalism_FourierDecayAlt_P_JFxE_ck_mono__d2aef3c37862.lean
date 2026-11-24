-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:53:57.508801+00:00
-- url     : https://prove2.me/submissions/f7540a13-2ec1-458b-a5dc-cd6ba5f9cf6f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {m m' : ℕ} (h : m ≤ m') {f : Mat k r → E} (hf : CkOn ((m' : ℕ) : ℕ∞) (GV k r) f) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hcd, hfe⟩ := hf g₀ hg₀
  refine ⟨U, f', hU, hg, hcd.of_le ?_, hfe⟩
  first | exact_mod_cast h | exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr h) | (norm_cast)
end Formalism.FourierDecayAlt.P.JFxE
