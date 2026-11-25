-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:11:27.280496+00:00
-- url     : https://prove2.me/submissions/06ef6404-aa6f-4a03-8c1a-af2c752863e2

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_form_zero_right

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
theorem _root_.solution (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.ds_form_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, ih]
end HermFam
end ReciprocityTheory.GeometryOfNumbersTheory
