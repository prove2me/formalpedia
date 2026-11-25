-- Prove2me | solution 1 for PI.GreenLabelSurjWork.exists_ne_zero_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:38.018849+00:00
-- url     : https://prove2.me/submissions/9b4f2c48-3f84-41c9-86e3-22eeb4eef4ae

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
namespace PI.GreenLabelSurjWork
theorem _root_.solution (hl : ∀ c, Nontrivial (lam c)) :
    ∃ v : PiTensorProduct ℂ (fun c => (lam c : Type)), v ≠ 0 := by
  classical
  choose w hw using fun c => exists_ne (0 : lam c)
  have hφ : ∀ c, ∃ φ : Module.Dual ℂ (lam c), φ (w c) ≠ 0 := fun c => by
    by_contra hc
    push_neg at hc
    exact hw c ((Module.forall_dual_apply_eq_zero_iff ℂ (w c)).mp hc)
  choose φ hφ using hφ
  refine ⟨PiTensorProduct.tprod ℂ w, fun h0 => ?_⟩
  have h1 := PiTensorProduct.dualDistrib_apply φ w
  rw [show (⨂ₜ[ℂ] i, w i) = PiTensorProduct.tprod ℂ w from rfl, h0, map_zero] at h1
  exact (Finset.prod_ne_zero_iff.mpr (fun c _ => hφ c)) h1.symm
end PI.GreenLabelSurjWork
