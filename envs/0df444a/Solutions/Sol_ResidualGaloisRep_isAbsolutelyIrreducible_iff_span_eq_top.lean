-- Prove2me | solution 1 for ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1baa6a6f-a168-5b24-aecd-6c63d034e70a

import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top

open Module LinearMap
open scoped TensorProduct

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace C6P1R

section Bridges
variable {k : Type} [Field k]

theorem isIrreducible_iff_rep (ρ : ResidualGaloisRep k) : ρ.IsIrreducible ↔ Representation.IsIrreducible ρ.ρ := by
  haveI : Nontrivial ρ.V := Module.nontrivial_of_finrank_pos (R := k) (by rw [ρ.finrank_eq]; norm_num)
  have hne : (⊥ : Subrepresentation ρ.ρ) ≠ ⊤ := fun h =>
    bot_ne_top (α := Submodule k ρ.V) (congrArg Subrepresentation.toSubmodule h)
  constructor
  · intro h
    refine { toNontrivial := ⟨⟨⊥, ⊤, hne⟩⟩, eq_bot_or_eq_top := fun W => ?_ }
    rcases h W.toSubmodule (fun σ x hx => W.apply_mem_toSubmodule σ hx) with h0 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h0)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  · intro h W hW
    rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem isIrreducible_of_span_eq_top (ρ : ResidualGaloisRep k) (h : Submodule.span k (Set.range ⇑ρ.ρ) = ⊤) :
    ρ.IsIrreducible := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot

  have hstab : ∀ f : Module.End k ρ.V, ∀ x ∈ W, f x ∈ W := by
    intro f
    have hf : f ∈ Submodule.span k (Set.range ⇑ρ.ρ) := by rw [h]; trivial
    refine Submodule.span_induction (p := fun f _ => ∀ x ∈ W, f x ∈ W) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨σ, rfl⟩ x hx; exact hW σ x hx
    · intro x _; exact W.zero_mem
    · intro f g _ _ hf hg x hx; exact W.add_mem (hf x hx) (hg x hx)
    · intro c f _ hf x hx; exact W.smul_mem c (hf x hx)
  rw [eq_top_iff]
  intro w _

  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hv0
  have h1 : (φ v) • w ∈ W := hstab (φ.smulRight w) v hvW
  have h2 := W.smul_mem (φ v)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hφ, one_smul] at h2

theorem baseChange_ρ_apply (K : Type) [Field K] [Algebra k K] (ρ : ResidualGaloisRep k) (σ : Γℚ) :
    (ρ.baseChange K).ρ σ = (ρ.ρ σ).baseChange K := rfl

theorem range_baseChange_ρ (K : Type) [Field K] [Algebra k K] (ρ : ResidualGaloisRep k) :
    Set.range ⇑(ρ.baseChange K).ρ = Set.range fun σ => (ρ.ρ σ).baseChange K := rfl

end Bridges

end C6P1R

open C6P1R in
theorem solution
    {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsAbsolutelyIrreducible ↔ Submodule.span k (Set.range ⇑ρ.ρ) = ⊤ := by
  constructor
  · intro h
    have h1 : Representation.IsIrreducible (ρ.baseChange (AlgebraicClosure k)).ρ := (isIrreducible_iff_rep _).mp h
    have h2 := Representation.span_range_eq_top_of_isIrreducible (ρ.baseChange (AlgebraicClosure k)).ρ
    rw [range_baseChange_ρ] at h2
    exact (Representation.span_range_baseChange_eq_top_iff (K := AlgebraicClosure k) ρ.ρ).mp h2
  · intro h
    have h2 := (Representation.span_range_baseChange_eq_top_iff (K := AlgebraicClosure k) ρ.ρ).mpr h
    exact isIrreducible_of_span_eq_top _ (by rw [range_baseChange_ρ]; exact h2)

end S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
end P2MW
export P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top (solution)
