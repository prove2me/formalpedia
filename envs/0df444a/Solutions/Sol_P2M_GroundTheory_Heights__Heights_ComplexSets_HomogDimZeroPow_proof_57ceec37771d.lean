-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_HomogDimZeroPow_proof_57ceec37771d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:58.386259+00:00
-- url     : https://prove2.me/submissions/671d9bc0-f740-4c82-bb83-c05cf036ed1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_le_originIdeal_of_isHomogeneous_7394c352b960
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_isMaximal_of_isPrime_of_quotient_dim_le_zero_3c4a7f03bbc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_isMaximal_8f869c9b3ce4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace HomogDimZeroPow
theorem _root_.solution : HomogDimZeroPow.Statement := by
  intro n K hK hdim
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hKP, hP⟩ => ?_
  set 𝒜 := homogeneousSubmodule (Fin n) ℂ
  have hcP : (P.homogeneousCore 𝒜).toIdeal.IsPrime := hP.homogeneousCore
  have hKc : K ≤ (P.homogeneousCore 𝒜).toIdeal := by
    rw [← hK.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hKP
  have hmax := isMaximal_of_isPrime_of_quotient_dim_le_zero hdim hcP hKc
  have hle := le_originIdeal_of_isHomogeneous (P.homogeneousCore 𝒜).isHomogeneous hmax.ne_top
  exact ((hmax.eq_of_le (originIdeal_isMaximal n).ne_top hle).symm.le).trans
    (Ideal.toIdeal_homogeneousCore_le 𝒜 P)
end HomogDimZeroPow
end GroundTheory.Heights₂.Heights.ComplexSets
