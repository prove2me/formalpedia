-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_add_7ddf77459fd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:34.18128+00:00
-- url     : https://prove2.me/submissions/bab25994-627d-4d3e-a025-830ea0fa0a17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_split_140b0b462c0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_prod_pow_add_fd787651d819

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
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution {Ω : Type} [Field Ω] (y : Coord n → Ω) (d e : ι → ℕ) :
    monomialValues y (d + e) = monomialValues y d * monomialValues y e := by
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    obtain ⟨μ₁, μ₂, rfl, h₁, h₂⟩ := exists_split μ d e hμ
    exact Set.mem_mul.mpr ⟨_, ⟨μ₁, h₁, rfl⟩, _, ⟨μ₂, h₂, rfl⟩, (prod_pow_add y μ₁ μ₂).symm⟩
  · intro hs
    obtain ⟨_, ⟨μ₁, h₁, rfl⟩, _, ⟨μ₂, h₂, rfl⟩, rfl⟩ := Set.mem_mul.mp hs
    exact ⟨μ₁ + μ₂, fun k ↦ by simp [Finset.sum_add_distrib, h₁, h₂], (prod_pow_add y μ₁ μ₂).symm⟩
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
