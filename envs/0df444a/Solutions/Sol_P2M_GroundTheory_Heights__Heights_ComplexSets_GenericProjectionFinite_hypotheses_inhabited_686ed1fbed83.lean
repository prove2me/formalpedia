-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_hypotheses_inhabited_686ed1fbed83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:10:57.159884+00:00
-- url     : https://prove2.me/submissions/e711ed02-1aaf-4187-9d63-08e110c631da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isPrime_a6929b93aaa1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_dim_44deeb4b2e7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_coneProj_mem_orthoRows_4bca22bd21ba

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
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace GenericProjectionFinite
theorem _root_.solution :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ)) ∧
      (orthoRows 2 3 ⊆ orthoRows 2 3 ∧ orthoRows 2 3 ⊆ closure (orthoRows 2 3) ∧
        coneProj ∈ orthoRows 2 3) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨⟨cone_isPrime, cone_dim⟩, ⟨subset_rfl, subset_closure, coneProj_mem_orthoRows⟩, one_mem _⟩
end GenericProjectionFinite
end GroundTheory.Heights₂.Heights.ComplexSets
