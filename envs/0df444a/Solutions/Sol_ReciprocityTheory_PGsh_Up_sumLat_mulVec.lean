-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sumLat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:44.46546+00:00
-- url     : https://prove2.me/submissions/516293d1-18fc-43ec-813d-282df237bcb6

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Theorems.Thm_ReciprocityTheory_PGsh_Up_sumLat_apply
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


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
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (c : Fin n × Fin s → C) (τ : Fin n)
    (i : Fin s) : ((sumLat Mτ).B *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
  simp only [Matrix.mulVec, dotProduct, sumLat_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun j _ => if_neg (Ne.symm hb)
  · intro h; exact absurd (Finset.mem_univ τ) h
end ReciprocityTheory.PGsh.Up
