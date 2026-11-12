-- Prove2me | solution 1 for OddOrder.Algebra.exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:11.514926+00:00
-- url     : https://prove2.me/submissions/6853005b-dca7-45af-95c3-7726a7b2eb40

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/GaloisRationalInteger.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_Algebra_GaloisRationalInteger
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

-- ===== OddOrder/Algebra/GaloisRationalInteger.lean =====
namespace OddOrder.Algebra

open Polynomial IntermediateField

/-- **Isaacs 3.14 core.** An algebraic integer `α : ℂ` fixed by every ring automorphism of `ℂ`
is a rational integer. -/
theorem _root_.solution {α : ℂ}
    (hα : IsIntegral ℤ α) (hfix : ∀ σ : ℂ ≃+* ℂ, σ α = α) :
    ∃ z : ℤ, (z : ℂ) = α := by
  apply exists_int_of_isIntegral_of_mem_range_rat hα
  -- Work inside the splitting field `K = ℚ(rootSet (minpoly ℚ α)) ⊆ ℂ`.
  have hαℚ : IsIntegral ℚ α := hα.tower_top (A := ℚ)
  set p := minpoly ℚ α with hp
  have hp0 : p ≠ 0 := minpoly.ne_zero hαℚ
  have hsplits : (p.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ) with hK
  have hSF : IsSplittingField ℚ K p := IntermediateField.adjoin_rootSet_isSplittingField hsplits
  have : Normal ℚ K := Normal.of_isSplittingField p
  have : FiniteDimensional ℚ K := IsSplittingField.finiteDimensional K p
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  have : Algebra.IsSeparable ℚ K := inferInstance
  have : IsGalois ℚ K := ⟨⟩
  -- `α` lies in `K` (it is a root of its own minimal polynomial).
  have hαmem : α ∈ K := by
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    exact ⟨hp0, minpoly.aeval ℚ α⟩
  -- The element `⟨α, hαmem⟩ : K` is fixed by every `ℚ`-automorphism of `K`.
  have hfixedK : ∀ σ : K ≃ₐ[ℚ] K, σ ⟨α, hαmem⟩ = ⟨α, hαmem⟩ := by
    intro σ
    obtain ⟨τ, hτ⟩ := OddOrder.RepresentationTheory.exists_complexRingEquiv_extends K σ.toRingEquiv
    have hval : (σ ⟨α, hαmem⟩ : ℂ) = α := by
      have h1 : τ (α : ℂ) = ((σ ⟨α, hαmem⟩ : K) : ℂ) := hτ ⟨α, hαmem⟩
      have h2 : τ (α : ℂ) = α := hfix τ
      rw [h2] at h1
      exact h1.symm
    exact Subtype.ext hval
  -- By the Galois correspondence, `⟨α, hαmem⟩ ∈ ⊥`, i.e. `α` is rational.
  have hbot : (⟨α, hαmem⟩ : K) ∈ (⊥ : IntermediateField ℚ K) :=
    (IsGalois.mem_bot_iff_fixed _).mpr hfixedK
  rw [IntermediateField.mem_bot] at hbot
  obtain ⟨q, hq⟩ := hbot
  refine ⟨q, ?_⟩
  have : (algebraMap ℚ K q : ℂ) = ((⟨α, hαmem⟩ : K) : ℂ) := by rw [hq]
  simpa using this

end OddOrder.Algebra
