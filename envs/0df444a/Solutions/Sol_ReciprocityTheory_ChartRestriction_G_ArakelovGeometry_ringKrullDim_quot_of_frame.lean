-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.ringKrullDim_quot_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:26:15.373802+00:00
-- url     : https://prove2.me/submissions/d2bdf9f6-1de4-4d19-82af-619bb1a76f23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_le_of_isIntegral__578cfa688125
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_coneMap_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isIntegralElem_of_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isIntegralElem_coneMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_coneMap_injective_of_frame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_mvPoly_fin_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_le_ringKrullDim_of_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  have hq : ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) =
      ringKrullDim (coneMap ℤ v).range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMap ℤ v)).toRingEquiv
  let f : MvPolynomial (Fin (D + 1)) ℤ →+* (coneMap ℤ v).range :=
    ((coneMap ℤ v).rangeRestrict.comp (rename e)).toRingHom
  have hvalf : ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω).comp f =
      (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω) := by
    refine RingHom.ext fun p => ?_
    simp [f, coneMap_rename]
  have hinj : Function.Injective f := by
    intro a b hab
    apply coneMap_injective_of_frame v e hf
    have := congrArg ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω) hab
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hvalf] at this
    exact this
  have hint : f.IsIntegral := fun s => by
    obtain ⟨q, hq⟩ := s.2
    apply isIntegralElem_of_comp f ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω)
      Subtype.val_injective
    rw [hvalf]
    change RingHom.IsIntegralElem _ (s : Polynomial Ω)
    rw [← hq]
    exact isIntegralElem_coneMap v e hf q
  rw [hq]
  apply le_antisymm
  · let _ := f.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin (D + 1)) ℤ) (coneMap ℤ v).range := ⟨hint⟩
    rw [← ringKrullDim_mvPoly_fin_int]
    exact ringKrullDim_le_of_isIntegral'
  · exact le_ringKrullDim_of_isIntegral f hint hinj _ ringKrullDim_mvPoly_fin_int.ge
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
