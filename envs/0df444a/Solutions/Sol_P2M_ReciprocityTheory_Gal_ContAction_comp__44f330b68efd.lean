-- Prove2me | solution 1 for P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:54.854411+00:00
-- url     : https://prove2.me/submissions/d72801c2-6557-4358-ba41-866c76679d76

import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
namespace ReciprocityTheory.Gal
namespace ContAction
theorem _root_.solution [TopologicalSpace Γ] {D : Type*} [Group D] [TopologicalSpace D]
    {rho : Representation R Γ M} (h : ContAction rho) {φ : D →* Γ} (hφ : Continuous φ) :
    ContAction (rho.comp φ) := by
  exact Continuous.comp (show Continuous (fun p : Γ × M => rho p.1 p.2) from h)
    ((hφ.comp continuous_fst).prodMk continuous_snd)
end ContAction
end ReciprocityTheory.Gal
