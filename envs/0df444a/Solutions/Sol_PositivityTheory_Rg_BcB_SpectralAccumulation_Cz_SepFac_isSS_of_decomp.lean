-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_of_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:45.388151+00:00
-- url     : https://prove2.me/submissions/17617092-3565-499d-85ac-d2b10c62d511

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_aeval_mul_of_mul_eq

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
theorem _root_.solution {κ : Type} {x : A} (ι : Finset κ) (e : κ → A) (c : κ → ℂ) (hsum : ∑ i ∈ ι, e i = 1)
    (hx : ∀ i ∈ ι, x * e i = c i • e i) : IsSS x := by
  classical
  refine ⟨ι.image c, ?_⟩
  calc aeval x (∏ v ∈ ι.image c, (X - C v)) = aeval x (∏ v ∈ ι.image c, (X - C v)) * ∑ i ∈ ι, e i := by
        rw [hsum, mul_one]
    _ = ∑ i ∈ ι, (∏ v ∈ ι.image c, (X - C v)).eval (c i) • e i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => aeval_mul_of_mul_eq (hx i hi) _
    _ = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [eval_prod, Finset.prod_eq_zero (Finset.mem_image_of_mem c hi) (by simp), zero_smul]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
