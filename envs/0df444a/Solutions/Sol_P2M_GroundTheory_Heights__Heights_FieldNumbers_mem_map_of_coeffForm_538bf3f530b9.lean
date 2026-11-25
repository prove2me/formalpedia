-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_map_of_coeffForm_538bf3f530b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:46.814+00:00
-- url     : https://prove2.me/submissions/8e2c1c86-e4fa-4f18-9c5e-184f5d02fecf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.FieldNumbers.coeff_coeffForm

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F'}
    (h : ∀ φ : F' →ₗ[F] F, coeffForm φ f ∈ I) : f ∈ I.map (map (algebraMap F F')) := by
  classical
  let b := Module.Basis.ofVectorSpace F F'
  let J := f.support.biUnion (fun μ => (b.repr (coeff μ f)).support)
  have hf : f = ∑ j ∈ J, C (b j) * map (algebraMap F F') (coeffForm (b.coord j) f) := by
    ext ν
    rw [coeff_sum]
    simp only [coeff_C_mul, coeff_map, coeff_coeffForm, Module.Basis.coord_apply]
    have hsub : (b.repr (coeff ν f)).support ⊆ J := by
      by_cases hν : ν ∈ f.support
      · exact Finset.subset_biUnion_of_mem (fun μ => (b.repr (coeff μ f)).support) hν
      · rw [MvPolynomial.notMem_support_iff.mp hν, map_zero, Finsupp.support_zero]
        exact Finset.empty_subset _
    conv_lhs => rw [← b.linearCombination_repr (coeff ν f)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hsub (fun i a => a • b i) (fun j _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [hf]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))
end GroundTheory.Heights₂.Heights.FieldNumbers
