-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_inv_582dedf997ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:47:32.207158+00:00
-- url     : https://prove2.me/submissions/c1c83d3a-0b9e-45d8-a543-cf6d860979c9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Nq_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_scl_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_shell_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mulVec_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_map_mulVec_volume

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
theorem _root_.solution (T' : ℝ) {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) :
    (σb k T').map (fun u => μ *ᵥ u) = σb k T' := by
  unfold σb
  rw [Measure.map_map (mulVec_meas μ) (scl_meas T')]
  have h1 : (fun u => μ *ᵥ u) ∘ scl k T' = scl k T' ∘ (fun u => μ *ᵥ u) := by
    funext u
    simp only [Function.comp, scl, Nq_UH hμ, Matrix.mulVec_smul]
  rw [h1, ← Measure.map_map (scl_meas T') (mulVec_meas μ)]
  congr 1
  have h2 : (fun u => μ *ᵥ u) ⁻¹' shell k T' = shell k T' := by
    ext u
    show (0 < Nq k (μ *ᵥ u) ∧ Nq k (μ *ᵥ u) ≤ T') ↔ (0 < Nq k u ∧ Nq k u ≤ T')
    rw [Nq_UH hμ]
  conv_lhs => rw [← h2]
  rw [← Measure.restrict_map (mulVec_meas μ) (shell_meas T'), map_mulVec_volume μ (UHb_det hμ)]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
