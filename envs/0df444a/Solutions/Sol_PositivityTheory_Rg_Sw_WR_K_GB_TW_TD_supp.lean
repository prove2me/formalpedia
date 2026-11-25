-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.TD_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:25.748925+00:00
-- url     : https://prove2.me/submissions/5b0da2a8-d105-40ad-bb90-7c9bb891d89e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_dirC_zero

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution {c : ℕ → E n → ℂ} {M : ℕ} (hM : ∀ j, M ≤ j → c j = 0) (k l : Fin n) :
    ∀ j, M + 1 ≤ j → TD k l c j = 0 := by
  intro j hj
  funext y
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : c (i + 1) = 0 := hM _ (by omega)
  have h2 : c i = 0 := hM _ (by omega)
  simp only [TD, sh, h1, h2, Dkl, dirC_zero, Pi.zero_apply, mul_zero, sub_zero]
end PositivityTheory.Rg.Sw.WR.K.GB.TW
