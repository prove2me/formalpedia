-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_intNumL_cons_eq_snoc_d16d0916dd87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:42.899291+00:00
-- url     : https://prove2.me/submissions/1c297d17-eadf-4a1f-a7a6-a5e3ba08eea8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumSymm_proof_70e6ef43d2f0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type} [Field F] (P : Ideal (MRing ι F)) (x : K → ℤ)
    (L : List (K → ℤ)) :
    intNumL F P (x :: L) = intNum F P (Fin.snoc (α := fun _ => K → ℤ) L.get x) := by
  have hget : (x :: L).get = Fin.cons (α := fun _ => K → ℤ) x L.get := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  have h := FieldNumbers.IntNumSymm.proof F K ι P (L.length + 1)
    (Fin.cons (α := fun _ => K → ℤ) x L.get) (finRotate _)
  rw [intNumL, hget, Fin.snoc_eq_cons_rotate, ← h]
  rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof
