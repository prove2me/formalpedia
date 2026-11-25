-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineConjugation_recover_conj_9765c37a03f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:14.733182+00:00
-- url     : https://prove2.me/submissions/254d41cd-e3ff-4c4a-a860-fabc982b7409

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineConj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_conj_mulVec_cc64338be361

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
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by
  have h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w := fun w => by
    simp [dualRecover]
  apply (dualRecover b hb).symm.injective
  rw [LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1,
    LinearEquiv.symm_apply_apply]
end GroundTheory.Heights₂.Heights.DualLineConjugation
