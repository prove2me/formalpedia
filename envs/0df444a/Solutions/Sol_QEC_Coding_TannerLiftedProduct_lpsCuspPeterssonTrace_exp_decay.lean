-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:24:27.961147+00:00
-- url     : https://prove2.me/submissions/76d33c4a-8f33-4198-a3b3-b3d39acdaa54

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_exp_decay

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃a>0,lpsCuspPeterssonTrace N f g=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  choose a ha hb using lpsCuspCosetPetersson_exp_decay N f g
  have hne : (Finset.univ : Finset (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)).Nonempty :=
    ⟨⟦(1:SL(2,ℤ))⟧,Finset.mem_univ _⟩
  let b : ℝ := Finset.univ.inf' hne a
  have hpos : 0<b := by
    obtain ⟨γ,hγ,hmin⟩ := Finset.exists_mem_eq_inf' hne a
    change 0<Finset.univ.inf' hne a
    rw [hmin]
    exact ha γ
  have hba (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : b≤a γ :=
    Finset.inf'_le _ (Finset.mem_univ γ)
  refine ⟨b,hpos,?_⟩
  have hγ (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      (fun τ => lpsCuspCosetPetersson N f g τ γ)=O[atImInfty] (fun τ => Real.exp (-b*τ.im)) := by
    apply (hb γ).trans
    apply isBigO_of_le
    intro τ
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    nlinarith [hba γ,τ.im_pos]
  exact IsBigO.fun_sum (fun γ _ => hγ γ)
end QEC.Coding.TannerLiftedProduct
