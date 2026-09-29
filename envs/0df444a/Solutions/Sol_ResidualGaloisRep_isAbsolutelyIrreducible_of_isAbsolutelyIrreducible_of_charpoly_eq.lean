-- Prove2me | solution 1 for ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7c19815c-1039-562e-8a83-b57383fb7de8

import Definitions.Def_GaloisRep_ResidualEquiv
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq

p2m_open "Module P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq.Module LinearMap"

namespace Module
p2m_export "Module" "Injective finrank End finrank_linearMap finBasis"
namespace End
p2m_open "Module.End Module"

section

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem eq_zero_of_forall_trace_mul_eq_zero {f : Module.End k V}
    (h : ∀ x : Module.End k V, trace k V (f * x) = 0) : f = 0 := by
  classical
  let b := Module.finBasis k V
  have hmat : ∀ x : Matrix _ _ k, (x * LinearMap.toMatrix b b f).trace = (x * 0).trace := by
    intro x
    rw [Matrix.mul_zero, Matrix.trace_zero]
    conv_lhs => rw [← (LinearMap.toMatrix b b).apply_symm_apply x]
    rw [← LinearMap.toMatrix_mul b, ← LinearMap.trace_eq_matrix_trace k b, trace_mul_comm]
    exact h _
  have hf0 : LinearMap.toMatrix b b f = 0 := Matrix.ext_iff_trace_mul_left.mpr hmat
  simpa using congrArg (LinearMap.toMatrix b b).symm hf0

noncomputable def tracePairing {G : Type*} (ρ : G → Module.End k V) :
    Module.End k V →ₗ[k] (G → k) :=
  LinearMap.pi fun g => (LinearMap.trace k V) ∘ₗ LinearMap.mulRight k (ρ g)

omit [FiniteDimensional k V] in
@[scoped simp] theorem tracePairing_apply {G : Type*} (ρ : G → Module.End k V) (a : Module.End k V)
    (g : G) : tracePairing ρ a g = trace k V (a * ρ g) := rfl

theorem tracePairing_injective {G : Type*} (ρ : G → Module.End k V)
    (hspan : Submodule.span k (Set.range ρ) = ⊤) : Function.Injective (tracePairing ρ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine eq_zero_of_forall_trace_mul_eq_zero fun x => ?_
  have hle : Submodule.span k (Set.range ρ) ≤
      LinearMap.ker ((LinearMap.trace k V) ∘ₗ LinearMap.mulLeft k a) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    simpa using congrFun ha g
  rw [hspan] at hle
  simpa using hle (Submodule.mem_top (x := x))

end

section

variable {k : Type*} [Field k]
  {V₁ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  {V₂ : Type*} [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]

theorem span_range_eq_top_of_span_range_eq_top_of_trace_eq {G : Type*} [Mul G]
    (ρ₁ : G → Module.End k V₁) (ρ₂ : G → Module.End k V₂)
    (hmul₁ : ∀ g h, ρ₁ (g * h) = ρ₁ g * ρ₁ h) (hmul₂ : ∀ g h, ρ₂ (g * h) = ρ₂ g * ρ₂ h)
    (htr : ∀ g, trace k V₁ (ρ₁ g) = trace k V₂ (ρ₂ g))
    (hspan₁ : Submodule.span k (Set.range ρ₁) = ⊤)
    (hrank : finrank k V₁ = finrank k V₂) :
    Submodule.span k (Set.range ρ₂) = ⊤ := by

  have hshift : ∀ h : G, tracePairing ρ₁ (ρ₁ h) = tracePairing ρ₂ (ρ₂ h) := fun h =>
    funext fun g => by rw [tracePairing_apply, tracePairing_apply, ← hmul₁, ← hmul₂, htr]

  have hle : LinearMap.range (tracePairing ρ₁) ≤
      (Submodule.span k (Set.range ρ₂)).map (tracePairing ρ₂) := by
    rw [LinearMap.range_eq_map, ← hspan₁, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact Submodule.mem_map.mpr ⟨ρ₂ h, Submodule.subset_span ⟨h, rfl⟩, (hshift h).symm⟩

  have h1 : finrank k (Module.End k V₁) = finrank k (LinearMap.range (tracePairing ρ₁)) :=
    (LinearMap.finrank_range_of_inj (tracePairing_injective ρ₁ hspan₁)).symm
  have h2 : finrank k (LinearMap.range (tracePairing ρ₁)) ≤
      finrank k ((Submodule.span k (Set.range ρ₂)).map (tracePairing ρ₂)) :=
    Submodule.finrank_mono hle
  have h3 : finrank k ((Submodule.span k (Set.range ρ₂)).map (tracePairing ρ₂)) ≤
      finrank k (Submodule.span k (Set.range ρ₂)) := Submodule.finrank_map_le _ _
  have h4 : finrank k (Submodule.span k (Set.range ρ₂)) ≤ finrank k (Module.End k V₂) :=
    Submodule.finrank_le _
  have h5 : finrank k (Module.End k V₁) = finrank k (Module.End k V₂) := by
    rw [Module.finrank_linearMap, Module.finrank_linearMap, hrank]
  exact Submodule.eq_top_of_finrank_eq (by omega)

end

end Module.End
p2m_reactivate "P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq.Module P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq.Module.End"
p2m_reactivate "P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq.Module"

theorem solution
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (h₁ : ρ₁.IsAbsolutelyIrreducible)
    (hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly) :
    ρ₂.IsAbsolutelyIrreducible := by
  rw [ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top] at h₁ ⊢
  refine Module.End.span_range_eq_top_of_span_range_eq_top_of_trace_eq ⇑ρ₁.ρ ⇑ρ₂.ρ
    (map_mul ρ₁.ρ) (map_mul ρ₂.ρ) (fun σ => ?_) h₁ (by rw [ρ₁.finrank_eq, ρ₂.finrank_eq])
  classical
  rw [LinearMap.trace_eq_matrix_trace k (Module.finBasis k ρ₁.V),
    LinearMap.trace_eq_matrix_trace k (Module.finBasis k ρ₂.V), Matrix.trace_eq_neg_charpoly_nextCoeff,
    Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix,
    hcp]

end S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
end P2MW
export P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq (solution)
