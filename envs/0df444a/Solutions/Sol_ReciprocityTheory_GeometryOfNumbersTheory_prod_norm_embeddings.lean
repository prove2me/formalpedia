-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.prod_norm_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:56.314252+00:00
-- url     : https://prove2.me/submissions/0a0912ea-e7fc-4965-a130-80dcdde4f41c

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable (K : Type*) [Field K] [NumberField K]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (a : K) :
    ∏ σ : K →+* ℂ, ‖σ a‖ = |(Algebra.norm ℚ a : ℝ)| := by
  have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
  simp only [norm_prod] at h
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ : K →+* ℂ => ‖σ a‖)
    (fun σ : K →ₐ[ℚ] ℂ => ‖σ a‖) (fun σ => rfl), ← h]
  simp
end ReciprocityTheory.GeometryOfNumbersTheory
