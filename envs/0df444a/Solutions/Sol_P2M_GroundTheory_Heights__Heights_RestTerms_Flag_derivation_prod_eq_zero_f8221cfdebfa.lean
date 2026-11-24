-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:51.401982+00:00
-- url     : https://prove2.me/submissions/dfd2ce33-d14a-4c6f-b18d-1bb561981ff5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) {ι : Type*} (s : Finset ι) (g : ι → A) (hg : ∀ i ∈ s, D (g i) = 0) :
    D (∏ i ∈ s, g i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, hg a (Finset.mem_insert_self a s),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)), smul_zero, smul_zero, add_zero]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
