-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_sl_two_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:30:47.522405+00:00
-- url     : https://prove2.me/submissions/4700ef18-ac99-472b-8aab-254785c1abbc

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] :
    Fintype.card SL(2, ZMod q) = q * (q ^ 2 - 1) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  letI : Fintype (GL (Fin 2) (ZMod q)) :=
    Fintype.ofInjective Units.val Units.val_injective
  have hGL : Nat.card (GL (Fin 2) (ZMod q)) =
      (q ^ 2 - 1) * (q ^ 2 - q) := by
    rw [Matrix.card_GL_field (n := 2)]
    simp [ZMod.card]
  let detHom :=
    (Matrix.GeneralLinearGroup.det :
      GL (Fin 2) (ZMod q) →* (ZMod q)ˣ)
  have hdetRange : detHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective
  have hker := detHom.ker.card_mul_index
  rw [Subgroup.index_ker, hdetRange, Subgroup.card_top] at hker
  have hUnits : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hUnits, hGL] at hker
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (specialLinearTwoEquivDetKer q)]
  have hfactor : q ^ 2 - q = q * (q - 1) := by
    simp [pow_two, Nat.mul_sub_left_distrib]
  rw [hfactor] at hker
  have hqTwo : 2 ≤ q := (Fact.out : q.Prime).two_le
  apply Nat.mul_right_cancel (by omega : 0 < q - 1)
  calc
    Nat.card detHom.ker * (q - 1) =
        (q ^ 2 - 1) * (q * (q - 1)) := hker
    _ = (q * (q ^ 2 - 1)) * (q - 1) := by ring
end QEC.Coding.TannerLiftedProduct
