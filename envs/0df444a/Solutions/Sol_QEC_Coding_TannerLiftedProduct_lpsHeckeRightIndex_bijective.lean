-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:03.582412+00:00
-- url     : https://prove2.me/submissions/d57ceb38-a96b-49e2-bcd9-6f0187df8bc3

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_inverse

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    Function.Bijective (lpsHeckeRightIndex N p hNp γ hγ) := by
  have hl : Function.LeftInverse
      (lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ))
      (lpsHeckeRightIndex N p hNp γ hγ) := lpsHeckeRightIndex_inverse N p hNp γ hγ
  have hr : Function.RightInverse
      (lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ))
      (lpsHeckeRightIndex N p hNp γ hγ) := by
    intro i
    simpa only [inv_inv] using lpsHeckeRightIndex_inverse N p hNp γ⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem hγ) i
  exact ⟨hl.injective,hr.surjective⟩
end QEC.Coding.TannerLiftedProduct
