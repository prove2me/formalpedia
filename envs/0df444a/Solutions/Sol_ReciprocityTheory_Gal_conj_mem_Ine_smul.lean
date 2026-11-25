-- Prove2me | solution 1 for ReciprocityTheory.Gal.conj_mem_Ine_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:25.365456+00:00
-- url     : https://prove2.me/submissions/166dd890-790a-4734-a697-15ccf4f41ed1

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA
import Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_le_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain Pointwise
namespace ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
section deg
variable {F : Type*} [Field F] [NumberField F]
end deg
section conj
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
private theorem smul_valuationSubring_valuation_lt_one_iff (γ : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (γ • A).valuation y < 1 ↔ A.valuation ((γ⁻¹ : G F Ω) y) < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  · have hy' : (γ⁻¹ : G F Ω) y ≠ 0 := (map_ne_zero (γ⁻¹ : G F Ω)).2 hy
    rw [Valuation.val_lt_one_iff _ hy, Valuation.val_lt_one_iff _ hy', ← not_le, ← not_le,
      smul_valuation_le_one_iff, map_inv₀]
end conj
end ReciprocityTheory.Gal
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution {A : ValuationSubring Ω} {γ σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) :
    γ * σ * γ⁻¹ ∈ Ine (F := F) (γ • A) := by
  obtain ⟨hσ1, hσ2⟩ := hσ
  show γ * σ * γ⁻¹ ∈ Inertia (F := F) (γ • A)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • A = A := hσ1
    show (γ * σ * γ⁻¹) • (γ • A) = γ • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · rw [smul_valuation_le_one_iff] at hx
    rw [smul_valuationSubring_valuation_lt_one_iff]
    have e : (γ⁻¹ : G F Ω) ((γ * σ * γ⁻¹) x - x) =
        σ ((γ⁻¹ : G F Ω) x) - (γ⁻¹ : G F Ω) x := by
      rw [map_sub]
      congr 1
      show (γ⁻¹ : G F Ω) (γ (σ ((γ⁻¹ : G F Ω) x))) = σ ((γ⁻¹ : G F Ω) x)
      first | exact γ.symm_apply_apply _ | simp
    rw [e]
    exact hσ2 _ hx
end ReciprocityTheory.Gal
