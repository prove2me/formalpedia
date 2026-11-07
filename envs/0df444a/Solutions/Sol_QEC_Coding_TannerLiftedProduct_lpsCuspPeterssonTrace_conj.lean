-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:37.196647+00:00
-- url     : https://prove2.me/submissions/abedb431-1a8d-4dfa-a2df-43a8a84f0abb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_conj

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : lpsCuspPeterssonTrace N g f τ=conj (lpsCuspPeterssonTrace N f g τ) := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  change (∑γ,lpsCuspCosetPetersson N g f τ γ)=conj (∑γ,lpsCuspCosetPetersson N f g τ γ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  exact lpsCuspCosetPetersson_conj N f g τ γ
end QEC.Coding.TannerLiftedProduct
