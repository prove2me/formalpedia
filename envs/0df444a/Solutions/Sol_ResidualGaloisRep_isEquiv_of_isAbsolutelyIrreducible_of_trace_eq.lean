-- Prove2me | solution 1 for ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/15f94520-c16a-56fb-9704-bfbb168b44bd

import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq

open Module LinearMap

theorem solution
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h₁ : ρ₁.IsAbsolutelyIrreducible) (h₂ : ρ₂.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ)) :
    ρ₁.IsEquiv ρ₂ := by
  haveI : Nontrivial ρ₁.V := Module.nontrivial_of_finrank_pos (R := k) (by rw [ρ₁.finrank_eq]; norm_num)
  obtain ⟨e, he⟩ := BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq ρ₁.ρ ρ₂.ρ
    ((ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ₁).mp h₁)
    ((ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ₂).mp h₂) htr
  exact ⟨⟨e, he⟩⟩

end S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq
end P2MW
export P2MW.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq (solution)
