-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonMass_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:17:09.11959+00:00
-- url     : https://prove2.me/submissions/603530a8-1e92-4cf9-8631-75411d74923b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Defs
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_self_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ)=0 ↔ f=0 := by
  constructor
  · exact lpsWeightTwoCusp_eq_zero_of_peterssonMass_eq_zero N f
  · intro h
    have hp := (lpsCuspPeterssonPairing_self_eq_zero_iff N f).mpr h
    rw [lpsCuspPeterssonPairing_self_eq] at hp
    exact Complex.ofReal_eq_zero.mp hp
end QEC.Coding.TannerLiftedProduct
