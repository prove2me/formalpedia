-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mem_span_26ad69966bfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:03.447224+00:00
-- url     : https://prove2.me/submissions/a75e7591-77ae-4fb3-97be-c984b82c6d19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mul_atBlock_mem_f996223746d1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (D : ℕ)
    {g : MvPolynomial (Coord n) ℂ} (hg : g ∈ fibreIdeal P k₀ w) :
    coeffVec (offMonos n k₀ D) g ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
  have key : ∀ h : MvPolynomial (Coord n) ℂ, coeffVec (offMonos n k₀ D) (h * g) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
    refine Submodule.span_induction (p := fun g _ ↦ ∀ h : MvPolynomial (Coord n) ℂ,
      coeffVec (offMonos n k₀ D) (h * g) ∈
        Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D))
      ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨p, hp, rfl⟩ h
      exact coeffVec_mul_atBlock_mem P k₀ w D h p hp
    · intro h
      rw [mul_zero, map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy h
      rw [mul_add, map_add]
      exact Submodule.add_mem _ (hx h) (hy h)
    · intro a x _ hx h
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (h * a)
  simpa using key 1
end GroundTheory.Heights₂.Heights.BlockSurjectivity
