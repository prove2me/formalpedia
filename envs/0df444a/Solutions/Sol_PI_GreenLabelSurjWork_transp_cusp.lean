-- Prove2me | solution 1 for PI.GreenLabelSurjWork.transp_cusp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:22.31062+00:00
-- url     : https://prove2.me/submissions/cf5eb6b2-5bd6-454b-805c-b3703c255bd4

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Theorems.Thm_P2M_PI_GreenLabelSurjWork_transp___fec5525b2b85
import Theorems.Thm_PI_GreenLabelSurjWork_glEquiv_mem_unip

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
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PI.GreenLabelSurjWork
theorem _root_.solution (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (h : IsCuspidal K τ) :
    IsCuspidal K (transp e τ) := by
  intro s b hb hs v hv
  refine h s (b ∘ e) (hb.comp e.surjective) hs v (fun u hu => ?_)
  have := hv _ (glEquiv_mem_unip e b u hu)
  rwa [transp_ρ, MulEquiv.symm_apply_apply] at this
end PI.GreenLabelSurjWork
