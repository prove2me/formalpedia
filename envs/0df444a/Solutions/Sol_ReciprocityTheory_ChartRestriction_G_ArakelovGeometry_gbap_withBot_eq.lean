-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_withBot_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:14.736553+00:00
-- url     : https://prove2.me/submissions/47bd16f6-029a-483c-95c7-8f000154e833

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MvPolynomial Module ReciprocityTheory.AnForm.R
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : WithBot ℕ∞} {d a : ℕ}
    (h : x + (a : WithBot ℕ∞) = ((d + a : ℕ) : WithBot ℕ∞)) : x = (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add] at h
    exact WithBot.bot_ne_coe h
  | coe y =>
    have h' : y + (a : ℕ∞) = ((d + a : ℕ) : ℕ∞) := by exact_mod_cast h
    have hy : y = (d : ℕ∞) := by
      induction y using ENat.recTopCoe with
      | top =>
        exfalso
        rw [top_add] at h'
        exact ENat.coe_ne_top _ h'.symm
      | coe y =>
        norm_cast at h' ⊢
        omega
    rw [hy]
    rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
