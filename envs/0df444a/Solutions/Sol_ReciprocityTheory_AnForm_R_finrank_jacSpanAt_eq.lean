-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.finrank_jacSpanAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:20.219536+00:00
-- url     : https://prove2.me/submissions/27855c83-50bc-4608-a7ed-6583b730e42c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_grad_renC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    Module.finrank ℂ (jacSpanAt I z) =
      Module.finrank ℂ (jacSpan (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) := by
  let L : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
  have hset : grad (renPt z) '' ((I.map (renR σ : MvPolynomial σ ℂ →+* MvPolynomial (Fin (Fintype.card σ)) ℂ) :
      Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ)) : Set (MvPolynomial (Fin (Fintype.card σ)) ℂ)) =
      (L : (σ → ℂ) →ₗ[ℂ] _) '' ((fun h : MvPolynomial σ ℂ => fun j => eval z (pderiv j h)) '' (I : Set _)) := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨h, hh, rfl⟩ := (Ideal.mem_map_of_equiv (renR σ) q).1 hq
      refine ⟨_, ⟨h, hh, rfl⟩, ?_⟩
      funext j
      rw [show (renR σ) h = renC σ h from rfl, grad_renC]
      rfl
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨renR σ h, Ideal.mem_map_of_mem _ hh, ?_⟩
      funext j
      rw [show (renR σ) h = renC σ h from rfl, grad_renC]
      rfl
  unfold jacSpan jacSpanAt
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_map_eq L _).symm
end ReciprocityTheory.AnForm.R
