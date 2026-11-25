-- Prove2me | solution 1 for PI.InvTopW.tmul_mem_IntAf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:02.906268+00:00
-- url     : https://prove2.me/submissions/2991c310-69c8-43be-9d51-fbdf4050f055

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
namespace PI.InvTopW
theorem _root_.solution (I : AutInst) {x : I.E} (hx : x ∈ Formalism.UG.intOE I.E)
    {a : Formalism.MainNotions.S.Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) :
    x ⊗ₜ[I.F] a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
  have h1 : x ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F) ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    refine Subring.subset_closure ?_
    exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  have h2 : (1 : I.E) ⊗ₜ[I.F] a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    refine Subring.subset_closure ?_
    exact Or.inr ⟨⟨a, ha⟩, rfl⟩
  have h3 := mul_mem h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3
end PI.InvTopW
