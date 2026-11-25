-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:24.981562+00:00
-- url     : https://prove2.me/submissions/34003c94-4e62-413d-9d9e-123a6a72b1cc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_of_decomp
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_exists_decomp

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
theorem _root_.solution {x : A} (hx : IsSS x) (c : ℂ) : IsSS (c • x) := by
  obtain ⟨s, e, hse, hxe, -⟩ := hx.exists_decomp
  refine isSS_of_decomp s e (fun v => c * v) hse fun v hv => ?_
  rw [smul_mul_assoc, hxe v hv, smul_smul]
end IsSS
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
