-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_int_mul_3eff43bbc16e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:39.802797+00:00
-- url     : https://prove2.me/submissions/00ebc3d3-a0f1-4b8e-82d0-441a8fa880e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution {κ : Type*} (F : MvPolynomial κ ℚ) :
    ∃ (N : ℤ) (P : MvPolynomial κ ℤ), N ≠ 0 ∧ map (Int.castRingHom ℚ) P = C (N : ℚ) * F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, by exact_mod_cast a.den_nz, ?_⟩
    rw [map_C, ← C_mul]
    congr 1
    rw [eq_intCast, Int.cast_natCast]
    exact (Rat.den_mul_eq_num a).symm
  | add f g hf hg =>
    obtain ⟨N₁, P₁, h₁, e₁⟩ := hf
    obtain ⟨N₂, P₂, h₂, e₂⟩ := hg
    refine ⟨N₁ * N₂, C N₂ * P₁ + C N₁ * P₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [map_add, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, e₁, e₂, Int.cast_mul,
      C_mul]
    simp only [eq_intCast]
    ring
  | mul_X f p hf =>
    obtain ⟨N, P, h, e⟩ := hf
    exact ⟨N, P * X p, h, by rw [map_mul, e, map_X, mul_assoc]⟩
end GroundTheory.Heights₂.Heights.OrbitConjSum
