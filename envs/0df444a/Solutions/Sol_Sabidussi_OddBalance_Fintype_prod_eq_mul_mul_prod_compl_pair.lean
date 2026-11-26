-- Prove2me | solution 1 for Sabidussi.OddBalance.Fintype.prod_eq_mul_mul_prod_compl_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:44.451781+00:00
-- url     : https://prove2.me/submissions/0b5b5381-7767-4668-bdad-bc9ca9e01118

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
namespace Fintype
theorem _root_.solution {M : Type*} [CommMonoid M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (h : a ≠ b) (g : ι → M) :
    (∏ i, g i) = g a * g b * ∏ i ∈ ({a, b} : Finset ι)ᶜ, g i := by
  rw [Fintype.prod_eq_mul_prod_compl a]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (by simpa using h.symm)]
  have hset : ({a} : Finset ι)ᶜ \ {b} = ({a, b} : Finset ι)ᶜ := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_insert, not_or]
  rw [hset, mul_assoc]
end Fintype
end Sabidussi.OddBalance
