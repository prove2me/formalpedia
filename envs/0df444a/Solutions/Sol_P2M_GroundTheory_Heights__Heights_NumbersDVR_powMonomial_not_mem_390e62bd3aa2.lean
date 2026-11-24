-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_not_mem_390e62bd3aa2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.074381+00:00
-- url     : https://prove2.me/submissions/446b2d55-ae6b-48ba-badb-70c7176b3ebb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf

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
open MvPolynomial
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W) (e : K → ℕ) :
    ∃ i : ∀ k, ι k, powMonomial e i ∉ W := by
  choose i hi using hrel
  refine ⟨i, fun hmem => ?_⟩
  have h : powMonomial e i ∈ W.primeCompl :=
    W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hi k) _
  exact h hmem
end GroundTheory.Heights₂.Heights.NumbersDVR
