-- Prove2me | solution 1 for P2M_GlobalTheory_BK_Descent_Hom_app_mem_Y__a74defe19476
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:50.823962+00:00
-- url     : https://prove2.me/submissions/4c2cd51b-d0b8-48ad-8559-f166f70e2dc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_P2M_GlobalTheory_BK_Descent_mem_Y__0a5a98ce4d79
import Theorems.Thm_GlobalTheory_BK_Descent_Hom_app_mem_Y

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
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
open GlobalTheory.BK.Descent.Hom
variable {Δ₁ : Descent P} {Δ₂ : Descent Q} {Δ₃ : Descent T} (F : Hom Δ₁ Δ₂)
omit [NeZero e]
namespace GlobalTheory.BK.Descent.Hom
theorem _root_.solution {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y' η) : F.app y ∈ Δ₂.Y' η := by
  obtain ⟨y₀, h₀, rfl⟩ := Δ₁.mem_Y'.1 hy
  exact Δ₂.mem_Y'.2 ⟨_, F.app_mem_Y h₀, (map_smul _ _ _).symm⟩
end GlobalTheory.BK.Descent.Hom
