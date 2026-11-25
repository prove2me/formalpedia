-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.avgF_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:05:32.057899+00:00
-- url     : https://prove2.me/submissions/e0634ef2-afa6-4429-9b3e-17b9663a2dd0

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_avgF_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0)
    (hnt : ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1) (c₀ : R) (F : Nb p g → C) :
    avgF β H U i c₀ F 0 = 0 := by
  obtain ⟨δ, hδ⟩ := hnt
  have he := avgF_eig β hS U hmul h1 hi c₀ F δ 0
  rw [show nbAct H (β δ) 0 = 0 from Matrix.mulVec_zero _] at he
  have hne : algebraMap R C (U.sg i (β δ)) - 1 ≠ 0 := by
    intro h0
    rw [map_sub, map_one, h0, map_zero] at hδ
    exact zero_ne_one hδ
  have hm : (algebraMap R C (U.sg i (β δ)) - 1) * avgF β H U i c₀ F 0 = 0 := by
    rw [sub_mul, ← he, one_mul, sub_self]
  exact (mul_eq_zero.mp hm).resolve_left hne
end ReciprocityTheory.PGsh.Up
