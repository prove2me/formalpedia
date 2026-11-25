-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_push_ea8e063f042e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:11.95884+00:00
-- url     : https://prove2.me/submissions/97684aa1-5730-4b82-9444-fabe0a369262

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hb_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_push_calc
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_Hb
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_Hb_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Nq_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_scl_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mulVec_meas
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_inv_582dedf997ff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_zW_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_zW_meas


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
theorem _root_.solution (hk : 1 ≤ k) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (zb : Fin (k + 1) → ℂ)
    (hz : herm (Hb k) zb zb = -((T : ℝ) : ℂ)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ (σb k T').map (fun u => herm (Hb k) u zb) =
      c • (volume : Measure ℂ).withDensity (fun ζ => ENNReal.ofReal (zWeight k T T' ζ)) := by
  obtain ⟨c, hc0, hc1, hc⟩ := push_calc k hk T T' hT hT'
  refine ⟨c, hc0, hc1, ?_⟩
  set z₀ : Fin (k + 1) → ℂ := ((√T : ℝ) : ℂ) • bvec (Fin.last k) with hz₀
  have hz₀z₀ : herm (Hb k) z₀ z₀ = ((-T : ℝ) : ℂ) := by
    rw [herm_Hb_self, hz₀, Nq_smul, Real.sq_sqrt hT.le]
    simp [Nq, bvec]
  obtain ⟨g, hg, hgz, -⟩ := trans (Hb k) Hb_herm z₀ zb (-T) (neg_ne_zero.2 hT.ne') hz₀z₀ (by rw [hz]; push_cast; rfl)
  have hgi := UHb_inv hg
  have hf : (fun u => herm (Hb k) u zb) = (fun u => herm (Hb k) u z₀) ∘ (fun u => g⁻¹ *ᵥ u) := by
    funext u
    have := herm_UH hg (g⁻¹ *ᵥ u) z₀
    rw [hgz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hgi.1, Matrix.one_mulVec] at this
    exact this
  have hm0 : Measurable (fun u : Fin (k + 1) → ℂ => herm (Hb k) u z₀) := by
    simp only [herm_Hb]
    fun_prop
  rw [hf, ← Measure.map_map hm0 (mulVec_meas _), σb_inv T' hgi.2]
  unfold σb
  rw [Measure.map_map hm0 (scl_meas T')]
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ (hm0.comp (scl_meas T')), lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (zW_meas k T T') hφ]
  have := hc φ hφ
  simp only [Pi.mul_apply, smul_eq_mul]
  rw [← this]
  refine lintegral_congr fun u => ?_
  congr 1
  simp only [Function.comp, scl, herm_Hb, hz₀, bvec]
  simp
  ring
end Formalism.FourierDecayAlt.P.TwoByOneBlock
