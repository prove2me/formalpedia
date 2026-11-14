-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.character_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:20:23.540194+00:00
-- url     : https://prove2.me/submissions/71300647-d8cf-47a6-9660-c2095a2e5424

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Extend50.P31
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [DecidableEq A] {n : ℕ}
private def bundled (U : UnitaryIrrep G n) : Representation ℂ G (Fin n → ℂ) where
  toFun g := (U.rho g).mulVecLin
  map_one' := by ext v i; simp [U.one]
  map_mul' g h := by ext v i; simp [U.mul, Matrix.mulVec_mulVec]

private lemma bundled_irred (U : UnitaryIrrep G n) : Representation.IsIrreducible (bundled U) := by
  have hn : Nonempty (Fin n) := ⟨⟨0, U.positive⟩⟩
  letI := hn
  have hne : (⊥ : Subrepresentation (bundled U)) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hh
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro S
  rcases U.irreducible S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private lemma bundled_char (U : UnitaryIrrep G n) (g : G) :
    (bundled U).character g = character U g := by
  exact Matrix.trace_toLin'_eq (U.rho g)


set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (a b : A) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character (F.irrep a) g * character (F.irrep b) g⁻¹ =
      if a = b then 1 else 0 := by
  classical
  letI := bundled_irred (F.irrep a)
  letI := bundled_irred (F.irrep b)
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G).ne')
  have he : Nonempty (Representation.Equiv (bundled (F.irrep b)) (bundled (F.irrep a))) ↔ a = b := by
    constructor
    · rintro ⟨e⟩
      exact (F.inequivalent b a ⟨e.toLinearEquiv, fun g x =>
        congrArg (fun f : (Fin (F.dim b) → ℂ) →ₗ[ℂ] (Fin (F.dim a) → ℂ) => f x)
          (e.toIntertwiningMap.isIntertwining' g)⟩).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa only [bundled_char, he, Nat.card_eq_fintype_card, Nat.cast_one, Nat.cast_zero] using
    Representation.char_orthonormal (bundled (F.irrep a)) (bundled (F.irrep b))