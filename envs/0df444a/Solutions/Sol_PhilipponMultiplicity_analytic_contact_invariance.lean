-- Prove2me | solution 1 for PhilipponMultiplicity.analytic_contact_invariance
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T13:20:05.608782+00:00
-- url     : https://prove2.me/submissions/614c8d5c-2a37-4f1f-b4be-12fcefd1fde0

import Theorems.Thm_PhilipponMultiplicity_projective_lift_contact_invariance
import Theorems.Thm_PhilipponMultiplicity_analyticCodimension_eq_zero_of_carrier_subset
import Theorems.Thm_PhilipponMultiplicity_analytic_subgroup_containment_of_codimension_zero
import Theorems.Thm_PhilipponMultiplicity_analyticCodimension_le_dimension
import Theorems.Thm_PhilipponMultiplicity_exists_transverseCoordinateFamily
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology
open Filter

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) :
    (∀ (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      IsMultihomogeneousOfDegree G P D →
      ∀ f : A.ParameterSpace → G.ambient.Variable → K,
        (∀ v, AnalyticAt K (fun z => f z v) 0) →
        (∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
          ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
              G.embedding (g + A.map ⟨z, hz⟩) i) →
        vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
          {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0})) ∧
    (∀ H : AlgebraicSubgroup G,
      analyticCodimension A H.carrier ≤ A.dimension ∧
      (analyticCodimension A H.carrier = 0 ↔ A.carrier ⊆ H.carrier) ∧
      ∃ directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension,
        IsTransverseCoordinateFamily A H directions)  := by
  refine ⟨projective_lift_contact_invariance K hK G A, ?_⟩
  intro H
  exact ⟨analyticCodimension_le_dimension A H,
    ⟨analytic_subgroup_containment_of_codimension_zero K hK G A H,
      analyticCodimension_eq_zero_of_carrier_subset A H⟩,
    exists_transverseCoordinateFamily A H⟩


