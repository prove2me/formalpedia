-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_exists_chartRing_308442e990d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:36.062925+00:00
-- url     : https://prove2.me/submissions/9b4e1e56-c2eb-4e2d-84ef-e6ae49706205

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartCoord_989f89da8026

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
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.AddBlockBridge
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) {r : Ω}
    (hr : r ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ η ∈ P.chartRing c, funHom P y hP η = constMap ι r := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨P.chartCoord c p, Subring.subset_closure ⟨p, rfl⟩, funHom_chartCoord P y hP c p⟩
  | algebraMap z =>
    exact ⟨(z : P.FunField), intCast_mem _ z, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨η, hη, he⟩ := hx
    obtain ⟨η', hη', he'⟩ := hx'
    exact ⟨η + η', add_mem hη hη', by rw [map_add, map_add, he, he']⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨η, hη, he⟩ := hx
    obtain ⟨η', hη', he'⟩ := hx'
    exact ⟨η * η', mul_mem hη hη', by rw [map_mul, map_mul, he, he']⟩
end GroundTheory.Heights₂.Heights.AddBlockBridge
