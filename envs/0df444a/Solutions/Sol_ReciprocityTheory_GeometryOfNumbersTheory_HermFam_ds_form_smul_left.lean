-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:06.978035+00:00
-- url     : https://prove2.me/submissions/d5544fcd-0407-433a-95a4-78d267051afb

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
namespace HermFam
theorem _root_.solution (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]
end HermFam
end ReciprocityTheory.GeometryOfNumbersTheory
