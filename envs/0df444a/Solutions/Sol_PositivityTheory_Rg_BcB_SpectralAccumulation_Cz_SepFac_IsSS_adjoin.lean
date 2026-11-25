-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:58.297423+00:00
-- url     : https://prove2.me/submissions/6f511d77-9327-4197-9194-1329816ed306

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_add
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_mul
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
namespace IsSS
theorem _root_.solution {s : Set A} (hs : ∀ x ∈ s, IsSS x) (hc : ∀ x ∈ s, ∀ y ∈ s, Commute x y) :
    ∀ y ∈ Algebra.adjoin ℂ s, IsSS y := by
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ s, ∀ y ∈ Algebra.adjoin ℂ s, Commute x y := by
    intro x hx y hy
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hc b hb a ha).symm
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap c => exact isSS_algebraMap c
  | add x y hx hy ihx ihy => exact ihx.add ihy (hcomm x hx y hy)
  | mul x y hx hy ihx ihy => exact ihx.mul ihy (hcomm x hx y hy)
end IsSS
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
