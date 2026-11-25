-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.delta_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:06:36.356094+00:00
-- url     : https://prove2.me/submissions/3d9aba50-68da-40c3-aa6b-ab656dda384f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (y x : ι → ZMod p) : delta k y x = if x = y then 1 else 0 := by
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hfac : ∀ i, (1 : k) + -1 * (xc k i x + -ZMod.castHom (dvd_refl p) k (y i)) ^ (p - 1) =
      if x i = y i then 1 else 0 := by
    intro i
    have e : xc k i x + -ZMod.castHom (dvd_refl p) k (y i) =
        ZMod.castHom (dvd_refl p) k (x i - y i) := by
      simp [xc, sub_eq_add_neg]
    rw [e, ← map_pow]
    by_cases hxy : x i = y i
    · simp [hxy, zero_pow hp1]
    · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hxy)]
      simp [hxy]
  simp only [delta, Finset.prod_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, hfac]
  rw [Finset.prod_boole]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hn : ¬ ∀ i ∈ (univ : Finset ι), x i = y i := fun hall => hxy (funext fun i => hall i (mem_univ i))
    rw [if_neg hn, if_neg hxy]
end ReciprocityTheory.PGsh.Up
