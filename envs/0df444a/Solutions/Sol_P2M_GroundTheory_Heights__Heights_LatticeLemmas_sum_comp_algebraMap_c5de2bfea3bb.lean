-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_sum_comp_algebraMap_c5de2bfea3bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:22.345568+00:00
-- url     : https://prove2.me/submissions/81bc2b8e-496b-4292-a3c8-6e2902a878ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_extensions_d233ebd0ffff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (f : (K →+* ℂ) → ℝ) :
    ∑ τ : L →+* ℂ, f (τ.comp (algebraMap K L)) = Module.finrank K L * ∑ σ : K →+* ℂ, f σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : L →+* ℂ ↦ τ.comp (algebraMap K L)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_congr rfl (fun τ hτ ↦ by rw [(Finset.mem_filter.mp hτ).2]), Finset.sum_const,
    nsmul_eq_mul, ← card_extensions L σ, Nat.card_eq_fintype_card, Fintype.card_subtype]
end GroundTheory.Heights₂.Heights.LatticeLemmas
