-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eq_ker_eval_of_X_sub_C_mem_79f08b70e1ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:00.98408+00:00
-- url     : https://prove2.me/submissions/470926eb-5d02-4812-a46a-aab7a6554b52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAwayZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAwayZariski

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
theorem _root_.solution {n : ℕ} (q : Fin n → ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : P.IsPrime) (h : ∀ k, X k - C (q k) ∈ P) : P = RingHom.ker (eval q) := by
  have hext : Ideal.Quotient.mk P = ((Ideal.Quotient.mk P).comp C).comp (eval q) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun i => ?_)
    simp only [RingHom.comp_apply, eval_X]
    exact Ideal.Quotient.eq.2 (h i)
  have hle : RingHom.ker (eval q) ≤ P := by
    intro f hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, hext]
    simp [RingHom.mem_ker.1 hf]
  have hmax : (RingHom.ker (eval q)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  exact (hmax.eq_of_le hP.ne_top hle).symm
end GroundTheory.Heights₂.Heights
