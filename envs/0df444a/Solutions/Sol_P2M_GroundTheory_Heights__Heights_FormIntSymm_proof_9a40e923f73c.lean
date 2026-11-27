-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FormIntSymm_proof_9a40e923f73c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:11.040158+00:00
-- url     : https://prove2.me/submissions/3b573314-ced2-4c54-9042-b327ffc81138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormIntSymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ne_zero_of_mem_zeroSet_slice_195945c55013
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_contDiffOn_log_dualNorm_e8475040d0f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_fsLogReg_ea0641a814f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLogReg_smul_17c74930b878


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
namespace FormIntSymm
theorem _root_.solution (hI : SliceIdeal.Statement) (hS : StokesOnVariety.Statement)
    (hC : SliceCutOffLimit.Statement) : FormIntSymm.Statement := by
  intro n e h W u u' ε δ hW ⟨g, hg⟩ hε hδ
  unfold formInt
  split_ifs with hℓ
  · have hℓW : linForm hℓ.choose ∉ W := hℓ.choose_spec
    generalize hℓ.choose = ℓ at hℓW ⊢
    obtain ⟨hJ, hdim, -⟩ := hI n (e + 1) W g ℓ hW hg hℓW
    have hnear : ∀ F : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ F {x | x ≠ 0} →
        SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) F := fun F hF =>
      ⟨{x | x ≠ 0}, isOpen_ne, fun x hx => ne_zero_of_mem_zeroSet_slice hx, hF⟩
    obtain ⟨χ, hχs, hχc, hlim⟩ := hC n e h W g ℓ hW hg hℓW
    obtain ⟨h1, h2⟩ := hlim (fsLogReg h u δ) (fsLogReg h u' ε) (fsLogReg_smul h u δ)
      (fsLogReg_smul h u' ε) (contDiffOn_fsLogReg h u hδ) (contDiffOn_fsLogReg h u' hε)
    refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
    exact (hS n e _ (fun x => χ k x * fsLogReg h u δ x) (fsLogReg h u' ε)
      (fun _ x => Real.log (h.dualNorm x)) hJ hdim
      (hnear _ ((hχs k).contDiffOn.mul (contDiffOn_fsLogReg h u hδ)))
      (hnear _ (contDiffOn_fsLogReg h u' hε)) (fun _ => hnear _ h.contDiffOn_log_dualNorm)
      (Or.inl (hχc k).mul_right)).symm
  · rfl
end FormIntSymm
end GroundTheory.Heights₂.Heights
