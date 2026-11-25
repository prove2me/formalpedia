-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pderiv_aeval_eq_sum_be961d70ab0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:35:51.674669+00:00
-- url     : https://prove2.me/submissions/0d402eaf-eac9-4694-b7fd-af9b77874c77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    {σ τ : Type*} [Fintype σ] (ψ : σ → MvPolynomial τ K) (i : τ) (g : MvPolynomial σ F) :
    pderiv i (aeval ψ g) = ∑ j, aeval ψ (pderiv j g) * pderiv i (ψ j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add, add_mul,
      Finset.sum_add_distrib, pderiv_X, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · refine Finset.sum_congr rfl fun b _ => by ring
end GroundTheory.Heights₂.Heights
