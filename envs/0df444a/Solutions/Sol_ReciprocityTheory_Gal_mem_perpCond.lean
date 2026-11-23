-- Prove2me | solution 1 for ReciprocityTheory.Gal.mem_perpCond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:38.75785+00:00
-- url     : https://prove2.me/submissions/c34301c3-0c27-41cc-a12f-3868bd9ddff9

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
variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)
namespace ReciprocityTheory.Gal
theorem _root_.solution {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) (i : I) (y : H1 ((twDual χ rho).comp (phi i))) :
    y ∈ perpCond χ rho phi hrho L i ↔ ∀ x ∈ L i, cupH1H1TwistedDual χ rho (phi i) (hrho i) y x = 0 := by
  show y ∈ ⨅ x ∈ L i, LinearMap.ker ((cupH1H1TwistedDual χ rho (phi i) (hrho i)).flip x) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
end ReciprocityTheory.Gal
