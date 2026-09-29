-- Prove2me | solution 1 for ResidualGaloisRep.trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6a7bd4dc-f083-5ba0-bde9-953e95faf9d5

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Theorems.Thm_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic

set_option autoImplicit false

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[k]
      (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)))
    (hE : ∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) :
    LinearMap.trace k _ E ≠ 0 := by
  classical

  obtain ⟨b, hsup, -⟩ :=
    GaloisRepAdic.exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic p hp2
      (GaloisRepAdic.ofResidualGaloisRep ρbar) hdet hord P hP
  have hWeq : (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) = k ∙ ((b 0 : (GaloisRepAdic.ofResidualGaloisRep ρbar).V) : ρbar.V) := hsup

  have hV2 : Module.finrank k ρbar.V = 2 := ρbar.finrank_eq
  haveI : FiniteDimensional k ρbar.V := Module.finite_of_finrank_eq_succ hV2
  have hb0 : ((b 0 : (GaloisRepAdic.ofResidualGaloisRep ρbar).V) : ρbar.V) ≠ 0 := b.ne_zero 0
  have hW1 : Module.finrank k ↥(⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1) : Submodule k ρbar.V) = 1 :=
    (LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ hWeq)).trans (finrank_span_singleton hb0)
  have hQ1 : Module.finrank k (ρbar.V ⧸ (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1))) = 1 := by
    have := Submodule.finrank_quotient_add_finrank (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1))
    omega

  have hsurj : Function.Surjective E := by
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) q
    refine ⟨Submodule.Quotient.mk (ρbar.ρ σ⁻¹ v), ?_⟩
    rw [hE, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  intro htr

  let bQ := Module.finBasisOfFinrankEq k (ρbar.V ⧸ (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1))) hQ1
  have hEb : E (bQ 0) = (LinearMap.trace k _ E) • bQ 0 := by
    have h1 : E (bQ 0) = (bQ.repr (E (bQ 0)) 0) • bQ 0 := by
      conv_lhs => rw [← bQ.sum_repr (E (bQ 0))]
      simp
    rw [h1, LinearMap.trace_eq_matrix_trace k bQ E, Matrix.trace_fin_one, LinearMap.toMatrix_apply]
  rw [htr, zero_smul] at hEb
  have hE0 : E = 0 := bQ.ext fun i => by
    fin_cases i
    simpa using hEb
  haveI : Nontrivial (ρbar.V ⧸ (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1))) := Module.nontrivial_of_finrank_eq_succ hQ1
  obtain ⟨q, hq⟩ := exists_ne (0 : ρbar.V ⧸ (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)))
  obtain ⟨q', hq'⟩ := hsurj q
  rw [hE0, LinearMap.zero_apply] at hq'
  exact hq hq'.symm

end S_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
end P2MW
export P2MW.S_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic (solution)
