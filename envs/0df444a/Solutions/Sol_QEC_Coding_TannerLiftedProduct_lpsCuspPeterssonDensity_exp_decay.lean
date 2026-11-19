-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:25:28.433787+00:00
-- url     : https://prove2.me/submissions/e12d8b1b-87ad-49ab-b7f9-f0553d781426

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_exp_decay

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃a>0,lpsCuspPeterssonDensity N f=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by
  obtain ⟨a,ha,hb⟩ := lpsCuspPeterssonTrace_exp_decay N f f
  refine ⟨a,ha,?_⟩
  have h : lpsCuspPeterssonDensity N f=O[atImInfty] lpsCuspPeterssonTrace N f f :=
    isBigO_of_le atImInfty (fun τ => by
      exact Complex.abs_re_le_norm _)
  exact h.trans hb
end QEC.Coding.TannerLiftedProduct
