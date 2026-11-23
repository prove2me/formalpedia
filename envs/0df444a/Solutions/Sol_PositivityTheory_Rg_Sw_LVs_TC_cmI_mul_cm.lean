-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.cmI_mul_cm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:33.929802+00:00
-- url     : https://prove2.me/submissions/34170bc7-1171-4c16-87e5-09727efe2157

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution : CmI n * Cm n = 1 := by
  rw [Cm, CmI, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]
end PositivityTheory.Rg.Sw.LVs.TC
