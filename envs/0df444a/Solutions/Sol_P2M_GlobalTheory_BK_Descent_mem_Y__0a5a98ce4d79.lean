-- Prove2me | solution 1 for P2M_GlobalTheory_BK_Descent_mem_Y__0a5a98ce4d79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:23.83988+00:00
-- url     : https://prove2.me/submissions/288e2b9e-c5e0-49df-a857-0f7c61e5009e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
omit [NeZero e]
namespace GlobalTheory.BK.Descent
theorem _root_.solution {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Y' η ↔ ∃ y₀ ∈ Δ.Y η, (X : K⟦X⟧) ^ e • y₀ = y :=
  Iff.rfl
end GlobalTheory.BK.Descent
