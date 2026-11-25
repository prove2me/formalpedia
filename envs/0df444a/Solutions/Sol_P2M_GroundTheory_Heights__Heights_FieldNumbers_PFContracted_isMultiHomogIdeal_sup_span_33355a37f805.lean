-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_sup_span_33355a37f805
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:49.931792+00:00
-- url     : https://prove2.me/submissions/857a5d6e-0323-4e33-90c2-5482d31681db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isHomogeneous_iff_07f1d1421071

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {f : MRing ι F} {c : K → ℕ} (hf : IsMultiHomog f c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {f}) := by
  classical
  have hI' : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    (isHomogeneous_iff (blockWeight ι) I).mpr fun m r hr => hI r hr m
  have : (I ⊔ Ideal.span {f}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    hI'.sup (Ideal.homogeneous_span _ _ fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨c, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩)
  intro r hr b
  exact (isHomogeneous_iff _ _).mp this b r hr
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
