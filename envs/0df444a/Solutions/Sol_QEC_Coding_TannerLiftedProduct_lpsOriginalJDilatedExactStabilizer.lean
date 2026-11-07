-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedExactStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:25:18.473825+00:00
-- url     : https://prove2.me/submissions/8bbdd0fe-ba59-471d-a2b8-e54fccbe5c93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineDistinctPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilationColumnGcdLt
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilatedAtScaledCusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedCompose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    (∀ τ : ℍ,lpsOriginalJDilated N hN (γ•τ)=lpsOriginalJDilated N hN τ)↔
      γ∈CongruenceSubgroup.Gamma0 N := by
  constructor
  · intro he
    rw [CongruenceSubgroup.Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]
    by_contra hc
    let g := Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)
    have hg : 0<g := lpsOriginalDilationColumnGcdPos N hN γ
    have hlt : g<N := lpsOriginalDilationColumnGcdLt N hN γ hc
    have hsq : g^2<N^2 := by nlinarith
    obtain ⟨r,hr⟩ := lpsOriginalDilatedAtScaledCusp N hN γ
    apply lpsOriginalAffineDistinctPole (g^2) (N^2) (pow_pos hg 2)
      (pow_pos hN 2) hsq r
    intro σ
    rw [←hr σ,he,lpsOriginalJDilatedCompose]
  · intro hγ τ
    exact lpsOriginalJDilated_integral_Gamma0_invariant N hN γ hγ τ
end QEC.Coding.TannerLiftedProduct
