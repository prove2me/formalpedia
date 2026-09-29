-- Prove2me | solution 1 for RibetIrr.linearEquiv_of_charpoly_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/51d79d6f-e8ab-5fbd-98e8-e5fd616d8311

import Theorems.Thm_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetIrr_linearEquiv_of_charpoly_eq_of_span_eq_top

namespace RibetIrrSol6

open Module

private theorem _root_.RibetIrrSol6.trace_eq_neg_charpoly_coeff {K V : Type*} [CommRing K] [Nontrivial K] [AddCommGroup V]
    [Module K V] [Module.Free K V] [Module.Finite K V] (f : Module.End K V)
    (hV : 0 < Module.finrank K V) :
    LinearMap.trace K V f = -(LinearMap.charpoly f).coeff (Module.finrank K V - 1) := by
  classical
  let b := Module.Free.chooseBasis K V
  haveI : Nonempty (Module.Free.ChooseBasisIndex K V) := by
    rw [Module.finrank_eq_card_chooseBasisIndex] at hV
    exact Fintype.card_pos_iff.mp hV
  rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.charpoly_toMatrix f b,
    Matrix.trace_eq_neg_charpoly_coeff, Module.finrank_eq_card_chooseBasisIndex]

p2m_export "RibetIrrSol6" "trace_eq_neg_charpoly_coeff"
end RibetIrrSol6

theorem solution
    {K : Type} [Field K]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module K V₁] [Module.Finite K V₁]
    [AddCommGroup V₂] [Module K V₂] [Module.Finite K V₂]
    (ρ₁ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K V₁)
    (ρ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K V₂)
    (hfr₁ : Module.finrank K V₁ = 2) (hfr₂ : Module.finrank K V₂ = 2)
    (hspan₁ : Submodule.span K (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span K (Set.range ⇑ρ₂) = ⊤)
    (hcharpoly : ∀ σ, LinearMap.charpoly (ρ₁ σ) = LinearMap.charpoly (ρ₂ σ)) :
    ∃ e : V₁ ≃ₗ[K] V₂,
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V₁),
        e (ρ₁ σ v) = ρ₂ σ (e v) := by
  haveI : Module.Free K V₁ := Module.Free.of_divisionRing K V₁
  haveI : Module.Free K V₂ := Module.Free.of_divisionRing K V₂
  refine Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
    ρ₁ ρ₂ (hfr₁.trans hfr₂.symm) hspan₁ hspan₂ fun σ => ?_
  rw [RibetIrrSol6.trace_eq_neg_charpoly_coeff (ρ₁ σ) (by omega),
    RibetIrrSol6.trace_eq_neg_charpoly_coeff (ρ₂ σ) (by omega), hcharpoly σ, hfr₁, hfr₂]

end S_RibetIrr_linearEquiv_of_charpoly_eq_of_span_eq_top
end P2MW
export P2MW.S_RibetIrr_linearEquiv_of_charpoly_eq_of_span_eq_top (solution)
