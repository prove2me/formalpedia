-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_perm_8e7327d5a04e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:20.996732+00:00
-- url     : https://prove2.me/submissions/16eef538-520e-4c26-bf9f-58819a61b30b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_eq_9d5a3e5ca313

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
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
variable {K : Type*} [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
theorem _root_.solution {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    {l l' : List (K → ℤ)} (h : l.Perm l') : intNumL F P l = intNumL F P l' := by
  rw [intNumL_eq, intNumL_eq, h.foldr_eq]
end GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
