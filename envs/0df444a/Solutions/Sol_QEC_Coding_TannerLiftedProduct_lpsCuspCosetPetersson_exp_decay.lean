-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:23:42.957872+00:00
-- url     : https://prove2.me/submissions/2f97b7e8-1eb2-4e96-93b6-7b99ae19e742

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
open ConjAct Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    ∃a>0,(fun τ => lpsCuspCosetPetersson N f g τ γ)=O[atImInfty]
      (fun τ => Real.exp (-a*τ.im)) := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  let Γ : Subgroup (GL (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 N
  have hcast : Matrix.SpecialLinearGroup.mapGL ℝ h=(h:GL (Fin 2) ℝ) := by
    ext i k
    rfl
  have : ((toConjAct (((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ)⁻¹)) • Γ).IsArithmetic := by
    simpa [Γ,(show Rat.castHom ℝ=algebraMap ℚ ℝ by rfl),map_inv,Matrix.SpecialLinearGroup.map_mapGL,hcast]
      using Subgroup.IsArithmetic.conj Γ (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹
  obtain ⟨a,ha,hb⟩ := (CuspFormClass.zero_at_infty (CuspForm.translate f (((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ)))).petersson_exp_decay_left
    2 _ (CuspForm.translate g (((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ)))
  refine ⟨a,ha,?_⟩
  change (petersson 2 ((f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) ((g:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹))=O[atImInfty]
    (fun τ => Real.exp (-a*τ.im)) at hb
  have he : petersson 2 ((f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) ((g:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹)=
      (fun τ => lpsCuspCosetPetersson N f g τ ⟦h⟧) := by
    funext τ
    exact petersson_slash_SL 2 f g h⁻¹ τ
  rw [he] at hb
  exact hb
end QEC.Coding.TannerLiftedProduct
