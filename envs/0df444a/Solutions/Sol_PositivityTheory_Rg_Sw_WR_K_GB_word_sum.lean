-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.word_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:28.169094+00:00
-- url     : https://prove2.me/submissions/280d15fa-5d19-4624-8f2a-f1c142d3a001

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_eqOn_cpart
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_word_contDiffOn
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_cpart_sum

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
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (L : List (Fin n × Fin n))
    (hU : IsOpen U) (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (word L (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * word L (f t) x) U := by
  induction L with
  | nil => intro b _; rfl
  | cons a L ih =>
    intro b hb
    have h1 := eqOn_cpart a.1 a.2 hU ih hb
    simp only [word, List.foldr_cons] at h1 ⊢
    rw [h1]
    exact cpart_sum s c (fun t => word L (f t)) a.1 a.2 hU (fun t => word_contDiffOn L hU (hf t)) hb
end PositivityTheory.Rg.Sw.WR.K.GB
