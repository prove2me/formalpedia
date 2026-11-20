-- Prove2me | solution 2 for QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_unit_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:44.316478+00:00
-- url     : https://prove2.me/submissions/8d06cd56-3083-422e-98b2-ca90eee8c31d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (γ : SL(2,ℤ))
    (hC : γ 1 0=(N:ℤ)) : IsUnit ((γ 0 0:ℤ):ZMod N) := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  have hcast := congrArg (fun x : ℤ => (x:ZMod N)) hd
  have hN : (N:ZMod N)=0 := ZMod.natCast_self N
  rw [hC] at hcast
  push_cast at hcast
  simp only [hN,mul_zero,sub_zero] at hcast
  exact ⟨⟨_,_,hcast,by rw [mul_comm];exact hcast⟩,rfl⟩
end QEC.Coding.TannerLiftedProduct
