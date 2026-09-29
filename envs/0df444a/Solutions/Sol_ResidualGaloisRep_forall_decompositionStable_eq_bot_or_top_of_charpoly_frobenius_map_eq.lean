-- Prove2me | solution 1 for ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_charpoly_frobenius_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/74010efe-fe49-5c46-a736-a8332e23f87e

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_isEquiv_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_charpoly_frobenius_map_eq
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow"

set_option autoImplicit false

namespace DichW1

private theorem hnsl_of_hW2_at_id {k' : Type} [Field k'] (ρ₀ : ResidualGaloisRep k') (p : ℕ)
    (hW2 : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ (k'' : Type) (_ : Field k'') (ψ'' : k' →+* k''),
        ∀ L : Submodule k'' (ρ₀.baseChangeAlong ψ'').V,
          (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, (ρ₀.baseChangeAlong ψ'').ρ σ v ∈ L) →
          L = ⊥ ∨ L = ⊤) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ L : Submodule k' ρ₀.V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ₀.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤ :=
  ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_isEquiv_baseChangeAlong
    (RingHom.id k') ρ₀ (ρ₀.baseChangeAlong (RingHom.id k'))
    ⟨ResidualGaloisRep.Equiv.refl _⟩
    (fun P hP L hL => hW2 P hP k' _ (RingHom.id k') L hL)

private theorem isAbsolutelyIrreducible_of_hW2 {k' : Type} [Field k']
    (ρ₀ : ResidualGaloisRep k')
    (P₀ : ValuationSubring (AlgebraicClosure ℚ))
    (hW2P : ∀ (k'' : Type) (_ : Field k'') (ψ'' : k' →+* k''),
        ∀ L : Submodule k'' (ρ₀.baseChangeAlong ψ'').V,
          (∀ σ ∈ P₀.decompositionSubgroup ℚ, ∀ v ∈ L, (ρ₀.baseChangeAlong ψ'').ρ σ v ∈ L) →
          L = ⊥ ∨ L = ⊤) :
    ρ₀.IsAbsolutelyIrreducible := by

  have hAlg : (algebraMap k' (AlgebraicClosure k')).toAlgebra =
      (inferInstance : Algebra k' (AlgebraicClosure k')) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hrep : ρ₀.baseChangeAlong (algebraMap k' (AlgebraicClosure k')) =
      ρ₀.baseChange (AlgebraicClosure k') := by
    show (letI := (algebraMap k' (AlgebraicClosure k')).toAlgebra;
          ρ₀.baseChange (AlgebraicClosure k')) = _
    congr 1

  show (ρ₀.baseChange (AlgebraicClosure k')).IsIrreducible
  rw [← hrep]
  intro W hW
  exact hW2P (AlgebraicClosure k') _ (algebraMap k' (AlgebraicClosure k')) W
    (fun σ _ v hv => hW σ v hv)

end DichW1

theorem solution
    {k k' : Type} [Field k] [Field k'] (e : k →+* k')
    (ρ : ResidualGaloisRep k) (ρ₀ : ResidualGaloisRep k') (p : ℕ) (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.charpoly (ρ₀.ρ τ) = (LinearMap.charpoly (ρ.ρ τ)).map e)
    (hW2 : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ (k'' : Type) (_ : Field k'') (ψ'' : k' →+* k''),
        ∀ L : Submodule k'' (ρ₀.baseChangeAlong ψ'').V,
          (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, (ρ₀.baseChangeAlong ψ'').ρ σ v ∈ L) →
          L = ⊥ ∨ L = ⊤) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ L : Submodule k ρ.V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤ := by

  by_cases hPex : ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p
  case neg => exact fun P hP => absurd ⟨P, hP⟩ hPex
  case pos =>
  obtain ⟨P₀, hP₀⟩ := hPex

  have hirr₀ : ρ₀.IsAbsolutelyIrreducible :=
    DichW1.isAbsolutelyIrreducible_of_hW2 ρ₀ P₀ (hW2 P₀ hP₀)

  have hcp : ∀ σ, LinearMap.charpoly ((ρ.baseChangeAlong e).ρ σ) =
      LinearMap.charpoly (ρ₀.ρ σ) := by
    refine ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq
      (fun M _ _ _ => FrobeniusDensity.statement M) (ρ.baseChangeAlong e) ρ₀ S ?_
    intro ℓ hℓ hℓS A τ hA hτ
    rw [ResidualGaloisRep.charpoly_baseChangeAlong, hfrob ℓ hℓ hℓS A hA τ hτ]

  have hirrρ : (ρ.baseChangeAlong e).IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
      ρ₀ (ρ.baseChangeAlong e) hirr₀ (fun σ => (hcp σ).symm)

  have hequiv : (ρ.baseChangeAlong e).IsEquiv ρ₀ :=
    ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
      (ρ.baseChangeAlong e) ρ₀ hirrρ hirr₀ hcp

  have hnsl₀ := DichW1.hnsl_of_hW2_at_id ρ₀ p hW2

  exact ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_isEquiv_baseChangeAlong
    e ρ ρ₀ hequiv hnsl₀

end S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_charpoly_frobenius_map_eq
end P2MW
export P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_charpoly_frobenius_map_eq (solution)
