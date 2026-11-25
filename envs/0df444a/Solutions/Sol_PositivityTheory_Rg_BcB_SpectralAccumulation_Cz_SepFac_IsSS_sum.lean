-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:34.646912+00:00
-- url     : https://prove2.me/submissions/87500c53-3228-4dd8-9f40-ab128c523326

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_add
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_zero

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
theorem _root_.solution {κ : Type} (ι : Finset κ) (x : κ → A) (hx : ∀ i ∈ ι, IsSS (x i))
    (hc : ∀ i ∈ ι, ∀ j ∈ ι, Commute (x i) (x j)) : IsSS (∑ i ∈ ι, x i) := by
  classical
  induction ι using Finset.induction_on with
  | empty => simpa using isSS_zero
  | insert a ι ha ih =>
    rw [Finset.sum_insert ha]
    refine (hx a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) ?_
    exact Commute.sum_right _ _ _ fun j hj =>
      hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
end IsSS
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
