-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_iter_single_eq_polyDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:29:01.525068+00:00
-- url     : https://prove2.me/submissions/bcf269fb-309c-417b-acc6-af2afe58c65c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_itD_perm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_eq_itD_ofFn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pdTerm_eq_itD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_monomial_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (F : EuclideanSpace ℂ ι → ℂ)
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (j : ℕ) (v : Fin j → ι) :
    iteratedFDeriv ℂ j F 0 (fun k => EuclideanSpace.single (v k) (1 : ℂ)) =
      polyDeriv (MvPolynomial.monomial (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι)) (1 : ℂ))
        (fun i => EuclideanSpace.single i (1 : ℂ)) F 0 := by
  rw [ct_iter_eq_itD_ofFn, polyDeriv_monomial_one, pdTerm_eq_itD, Multiset.toFinsupp_toMultiset]
  have hl : (List.ofFn fun k => EuclideanSpace.single (v k) (1 : ℂ)) =
      (List.ofFn v).map (fun i => EuclideanSpace.single i (1 : ℂ)) := by
    rw [List.map_ofFn]
    rfl
  have hp : (List.ofFn fun k => EuclideanSpace.single (v k) (1 : ℂ)).Perm
      (((↑(List.ofFn v) : Multiset ι).toList).map fun i => EuclideanSpace.single i (1 : ℂ)) := by
    rw [hl]
    exact List.Perm.map _ (Multiset.coe_eq_coe.1 (Multiset.coe_toList _)).symm
  exact congrFun (ct_itD_perm hF hp) 0
end ReciprocityTheory.ChartRestriction.G.I2
