-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineConjugation_normSq_conj_18ec6e099b06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:56.820894+00:00
-- url     : https://prove2.me/submissions/79f39a1d-cdd2-48e6-a01c-0794e5058a5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineConj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_recover_conj_9765c37a03f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_re_conj_form_4aad91b58e80

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineConjugation
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualLineConjugation
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by
  unfold dualNormSq
  rw [recover_conj]
  refine Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_
  have hσ : conjPerm K σ = conjugate σ := rfl
  rw [hσ, F.conj σ]
  exact re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)
end GroundTheory.Heights₂.Heights.DualLineConjugation
