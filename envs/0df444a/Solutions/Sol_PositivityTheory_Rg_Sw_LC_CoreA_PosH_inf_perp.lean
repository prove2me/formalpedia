-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.PosH.inf_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:56.301792+00:00
-- url     : https://prove2.me/submissions/ede87ea3-30bd-4d03-be5b-1bfdb8db366b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_definite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {φ : V → V → ℂ}
open PositivityTheory.Rg.Sw.LC.CoreA.PosH
variable (h : PosH φ)
include h
namespace PositivityTheory.Rg.Sw.LC.CoreA.PosH
theorem _root_.solution (W : Submodule ℂ V) : W ⊓ h.perp W = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rcases Submodule.mem_inf.1 hv with ⟨h1, h2⟩
  exact (Submodule.mem_bot ℂ).2 (h.definite v (h2 v h1))
end PositivityTheory.Rg.Sw.LC.CoreA.PosH
