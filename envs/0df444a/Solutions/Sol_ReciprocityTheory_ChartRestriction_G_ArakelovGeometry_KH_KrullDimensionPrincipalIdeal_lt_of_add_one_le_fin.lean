-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal.lt_of_add_one_le_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:32.841437+00:00
-- url     : https://prove2.me/submissions/1f691359-596c-49f1-acaa-669946036b62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_RingKrullDimQuotientAddOneLeOfLt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_DimFormulaOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
open ReciprocityTheory.CA
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
theorem _root_.solution (x y : WithBot ℕ∞) (n : ℕ) (hx : x ≠ ⊥) (hxn : x ≤ n)
    (h : x + 1 ≤ y) : x < y := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl hx
  | coe a =>
  induction y using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe b =>
  norm_cast at h hxn ⊢
  induction a using ENat.recTopCoe with
  | top => exact absurd hxn (by simp)
  | coe a =>
  induction b using ENat.recTopCoe with
  | top => exact WithTop.coe_lt_top a
  | coe b =>
  norm_cast at h ⊢
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
