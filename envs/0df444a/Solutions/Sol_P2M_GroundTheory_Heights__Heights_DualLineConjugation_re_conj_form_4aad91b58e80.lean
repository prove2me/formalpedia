-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineConjugation_re_conj_form_4aad91b58e80
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:50.627511+00:00
-- url     : https://prove2.me/submissions/20c64e79-26f8-45f2-9181-bfe8f7b0757f

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
namespace GroundTheory.Heights₂.Heights.DualLineConjugation
theorem _root_.solution {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by
  rw [← Complex.conj_re (star v ⬝ᵥ _)]
  congr 1
  simp [dotProduct, mulVec, map_sum, map_mul]
end GroundTheory.Heights₂.Heights.DualLineConjugation
