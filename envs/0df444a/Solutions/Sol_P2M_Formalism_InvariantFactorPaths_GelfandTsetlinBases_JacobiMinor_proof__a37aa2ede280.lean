-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_JacobiMinor_proof__a37aa2ede280
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:02.691443+00:00
-- url     : https://prove2.me/submissions/eb87bd6c-50f8-4ac7-aae0-a0a922b04bc4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_neg_one_pow_eq_of
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_jacobi_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_epsN_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_epsN_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open SignTwistStarLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : JacobiMinor := by
  intro R _ n m I J hIJ
  rw [jacobi_gen]
  congr 1
  apply neg_one_pow_eq_of
  have h1 := epsN_compl I
  have h2 := epsN_compl J
  rw [epsN_eq I] at h1
  rw [epsN_eq J, ← hIJ] at h2
  refine ⟨epsN Iᶜ + ∑ a ∈ I, a.val, ?_⟩
  generalize I.card * (n + 1) = w at h1 h2
  omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
