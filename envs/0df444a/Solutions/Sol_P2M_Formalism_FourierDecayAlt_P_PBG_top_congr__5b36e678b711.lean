-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBG_top_congr__5b36e678b711
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:05.71741+00:00
-- url     : https://prove2.me/submissions/a1197729-2c46-48ee-aad6-f48849eff59b

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_eabH_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)
include hU₀
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (u : ℂ) (a b : Fin (2 * r + k + 1)) {h₁ h₂ : Mat k r → E}
    (he : ∀ x ∈ U₀, x ∈ GV k r → h₁ x = h₂ x) (g : Mat k r) (hg : g ∈ U₀) (hgG : g ∈ GV k r) :
    Top (EabH (Hpk k r)) u a b h₁ g = QuantumDeterminants.Top (EabH (Hpk k r)) u a b h₂ g := by
  unfold QuantumDeterminants.Top
  rw [he g hg hgG, eabH_congr a b hU₀ hg hgG he]
end Formalism.FourierDecayAlt.P.PBG
