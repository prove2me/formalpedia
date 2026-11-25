-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.avgF_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:04.861066+00:00
-- url     : https://prove2.me/submissions/146ae54b-77ce-4706-857e-dbfeb9b19f75

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_comp_mem


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
theorem _root_.solution {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m) (c₀ : R)
    {F : Nb p g → C} (hF : F ∈ H.AA.carrier) : avgF β H U i c₀ F ∈ H.AA.carrier := by
  have hsum : avgF β H U i c₀ F = ∑ γ, (c₀ * U.sg i (β γ⁻¹)) • (fun y => F (nbAct H (β γ) y)) := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [avgF, Algebra.smul_def]
  rw [hsum]
  exact Submodule.sum_mem _ fun γ _ => Submodule.smul_mem _ _ (comp_mem H _ hF)
end ReciprocityTheory.PGsh.Up
