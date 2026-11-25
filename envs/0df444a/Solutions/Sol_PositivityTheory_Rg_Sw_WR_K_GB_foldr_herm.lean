-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.foldr_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:49.399648+00:00
-- url     : https://prove2.me/submissions/3facdc9d-97da-4310-b5f9-9ca61e209ea8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_dkl_comp_herm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_cpart_contDiffOn
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_differentiableAt_of_cdo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (τ : Fin n → Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U)
    (L : List (Fin n)) :
    L.foldr (fun k g => Dkl k (τ k) g) (fun y => F (herm y)) =
        (fun y => (L.foldr (fun k g => cpart (τ k) k g) F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (τ k) k g) F) U := by
  induction L with
  | nil => exact ⟨rfl, hF⟩
  | cons a L ih =>
    refine ⟨?_, cpart_contDiffOn _ _ hU ih.2⟩
    simp only [List.foldr_cons]
    rw [ih.1]
    funext y
    exact dkl_comp_herm a (τ a) y (differentiableAt_of_cdo hU ih.2 (hh y))
end PositivityTheory.Rg.Sw.WR.K.GB
