-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0_trace_sub_two_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:12.550969+00:00
-- url     : https://prove2.me/submissions/8656824c-fa9c-46e9-824b-d3b8ab40cfc5

import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZModFour_trace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 4∣N) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    (4:ℤ)∣(γ:Matrix (Fin 2) (Fin 2) ℤ).trace-2 := by
  have hNc : (N:ℤ)∣γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have h4N : (4:ℤ)∣(N:ℤ) := by exact_mod_cast hN
  have h4c := h4N.trans hNc
  have hc : (γ 1 0:ZMod 4)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h4c
  have hd := γ.det_coe
  rw [Matrix.det_fin_two] at hd
  have hz := congrArg (Int.castRingHom (ZMod 4)) hd
  change (((γ 0 0*γ 1 1-γ 0 1*γ 1 0:ℤ):ZMod 4))=1 at hz
  simp only [Int.cast_sub,Int.cast_mul,hc,mul_zero,sub_zero] at hz
  have ht := lpsZModFour_trace (γ 0 0) (γ 1 1) hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa [Matrix.trace_fin_two] using sub_eq_zero.mpr ht
end QEC.Coding.TannerLiftedProduct
