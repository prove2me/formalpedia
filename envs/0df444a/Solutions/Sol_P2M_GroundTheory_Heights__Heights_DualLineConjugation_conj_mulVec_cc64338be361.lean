-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineConjugation_conj_mulVec_cc64338be361
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:03.444476+00:00
-- url     : https://prove2.me/submissions/ab6a5113-9cde-4cae-a5e9-0b4c99c0f6d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineConj

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
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualLineConjugation
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by
  funext t
  simp only [mulVec, dotProduct, map_sum, map_mul]
  refine Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_
  simp [conjPerm, dualEmbMatrix]
end GroundTheory.Heights₂.Heights.DualLineConjugation
