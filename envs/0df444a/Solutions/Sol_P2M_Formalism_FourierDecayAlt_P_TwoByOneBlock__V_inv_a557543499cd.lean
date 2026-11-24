-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__V_inv_a557543499cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:12:04.448315+00:00
-- url     : https://prove2.me/submissions/62bd6689-ad0e-4e34-aa8c-a5721c6151e0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWb_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mulVec_meas
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_inv_582dedf997ff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (T' : ℝ) {g : Mat k r} (hg : g ∈ UWb k r) : (σV k r T').map (fun v => g *ᵥ v) = σV k r T' := by
  obtain ⟨μ, hμ, rfl⟩ := (UWb_iff g).1 hg
  unfold σV
  rw [Measure.map_map (mulVec_meas _) jV_meas]
  have : (fun v => embWb k r μ *ᵥ v) ∘ jV k r = jV k r ∘ (fun u => μ *ᵥ u) := by
    funext u; exact emb_mulVec_jV μ u
  rw [this, ← Measure.map_map jV_meas (mulVec_meas _), σb_inv T' hμ]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
