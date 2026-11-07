-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:04.914879+00:00
-- url     : https://prove2.me/submissions/2c7fe522-75f7-4ac5-96de-e9a7d74ce43f

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperMatrix_index_unique
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_spec

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ)
      (lpsHeckeRightIndex N p hNp γ hγ i)=i := by
  let j := lpsHeckeRightIndex N p hNp γ hγ i
  let k := lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ) j
  obtain ⟨δ,_hδ,hf⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
  obtain ⟨ε,_hε,hb⟩ := lpsHeckeRightIndex_spec N p hNp γ⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem hγ) j
  have he : lpsHeckeUpperMatrix p i=
      ((δ*ε:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p k := by
    calc
      lpsHeckeUpperMatrix p i=
          (lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ))*((γ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one,Matrix.mul_one]
      _ = _ := by
        dsimp only [j,k] at hb ⊢
        rw [hf,Matrix.mul_assoc,hb,←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul]
  exact (lpsHeckeUpperMatrix_index_unique p i k _ he).symm
end QEC.Coding.TannerLiftedProduct
