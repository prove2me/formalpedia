-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaPeterssonPairing_norm_sq_le_mass_mul_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:35:30.319904+00:00
-- url     : https://prove2.me/submissions/e1cc91e7-c79f-40e6-af8e-c8e573a781b7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_norm_sq_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_self_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (g : CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2) :
    let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
    ‖lpsCuspPeterssonPairing ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) g‖^2 ≤
      lpsThetaRankinMass q hq4*(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity ((4*q)^2) g τ) := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  have h := lpsCuspPeterssonPairing_norm_sq_le ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) g
  rw [lpsCuspPeterssonPairing_self_eq,lpsCuspPeterssonPairing_self_eq] at h
  exact h
end QEC.Coding.TannerLiftedProduct
