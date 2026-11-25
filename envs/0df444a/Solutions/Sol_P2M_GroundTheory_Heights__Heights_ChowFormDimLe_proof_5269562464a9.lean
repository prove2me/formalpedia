-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormDimLe_proof_5269562464a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:10.413797+00:00
-- url     : https://prove2.me/submissions/f68d7346-db4e-4017-8c28-ee53e561b1d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_coeff_zero_eq_zero_of_mem_f07820bc384c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_prime_liesOver_ad270c783d28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_ringKrullDim_eq_of_comap_8e644d83cbeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_ne_zero_common_zero_32ad9558f68b

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
open GroundTheory.Heights₂.Heights.ChowFormDimLe
namespace GroundTheory.Heights₂.Heights.ChowFormDimLe
theorem _root_.solution : ChowFormDimLe.Statement := by
  intro F _ n k I f hI hf
  by_contra hdim
  rw [not_le] at hdim
  have := hI.isPrime
  obtain ⟨P, hP, hPQ, hPI⟩ := exists_prime_liesOver (AlgebraicClosure F) I
    (fun g hg => coeff_zero_eq_zero_of_mem hI hg)
  have hdimP : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure F) ⧸ P) := by
    rw [ringKrullDim_eq_of_comap (AlgebraicClosure F) I P hPI]
    exact_mod_cast hdim
  have hall : ∀ u : Fin k × Fin n → AlgebraicClosure F, u ∈ incidence I k := by
    intro u
    obtain ⟨x, hx0, hxP, hxu⟩ := exists_ne_zero_common_zero P hPQ hdimP u
    refine ⟨x, hx0, fun g hg => ?_, hxu⟩
    have hgP : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g ∈ P := by
      rw [← hPI] at hg
      exact hg
    have := hxP _ hgP
    rwa [eval_map, ← aeval_def] at this
  apply hf.1
  apply map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective
  apply MvPolynomial.funext
  intro u
  rw [eval_map, ← aeval_def, ((hf.2 f).mpr dvd_rfl) u (hall u), map_zero, map_zero]
end GroundTheory.Heights₂.Heights.ChowFormDimLe
