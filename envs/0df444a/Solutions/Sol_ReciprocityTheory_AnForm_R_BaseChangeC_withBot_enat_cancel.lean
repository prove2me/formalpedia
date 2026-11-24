-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:41.029706+00:00
-- url     : https://prove2.me/submissions/58a60f82-98c8-4a1f-a627-c201d98a30bd

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R.BaseChangeC
theorem _root_.solution {h : ℕ∞} {a b : WithBot ℕ∞} {N : ℕ}
    (ha : (h : WithBot ℕ∞) + a = N) (hb : (h : WithBot ℕ∞) + b = N) : a = b := by
  induction a using WithBot.recBotCoe with
  | bot => simp at ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at hb
    | coe b =>
      have ha' : h + a = N := by exact_mod_cast ha
      have hb' : h + b = N := by exact_mod_cast hb
      congr 1
      induction h using ENat.recTopCoe with
      | top => simp at ha'
      | coe h => exact WithTop.add_left_cancel (ENat.coe_ne_top h) (ha'.trans hb'.symm)
end ReciprocityTheory.AnForm.R.BaseChangeC
