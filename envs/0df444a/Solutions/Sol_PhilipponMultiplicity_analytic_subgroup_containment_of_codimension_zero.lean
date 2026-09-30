-- Prove2me | solution 1 for PhilipponMultiplicity.analytic_subgroup_containment_of_codimension_zero
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T21:38:57.885256+00:00
-- url     : https://prove2.me/submissions/413d2eba-31e7-421a-810c-f7e2e60ca5fa

import Definitions.Def_PhilipponMultiplicity_Analytic
import Theorems.Thm_PhilipponMultiplicity_analytic_subgroup_containment_of_local_containment
import Theorems.Thm_PhilipponMultiplicity_analytic_subgroup_local_containment_of_tangent
set_option autoImplicit false
open scoped BigOperators Topology
open Filter PhilipponMultiplicity

noncomputable section
namespace PhilipponMultiplicity

-- Source: Solutions/PhilipponProjectiveContact.lean
private theorem completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact completeSpace_of_isometric_ringEquiv e he

end PhilipponMultiplicity
end

namespace PhilipponMultiplicity

-- Source: Solutions/PhilipponAnalyticGlobalContainment.lean
theorem AnalyticSubgroup.tangentKernel_eq_top_of_codimension_zero
    {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (V : Set G.Point)
    (hzero : analyticCodimension A V = 0) : A.tangentKernel V = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hp : Module.finrank K A.ParameterSpace = A.parameterDimension := by
    simp [AnalyticSubgroup.ParameterSpace]
  have hle := (A.tangentKernel V).finrank_le
  rw [hp] at hle ⊢
  exact Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hzero)

end PhilipponMultiplicity

theorem solution (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hzero : analyticCodimension A H.carrier = 0) : A.carrier ⊆ H.carrier := by
  letI : CompleteSpace K := hK.completeSpace
  apply analytic_subgroup_containment_of_local_containment K G A H
  exact analytic_subgroup_local_containment_of_tangent K hK G A H
    (A.tangentKernel_eq_top_of_codimension_zero H.carrier hzero)
#print axioms solution
