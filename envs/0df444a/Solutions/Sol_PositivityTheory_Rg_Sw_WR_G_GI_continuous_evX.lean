-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GI.continuous_evX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:49.519088+00:00
-- url     : https://prove2.me/submissions/c621c7d2-1be9-46cb-b5f5-f5f9b4ca682f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G.GI
theorem _root_.solution {m n : ℕ} (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  have : Continuous fun x : Fin m → Fin n → ℂ => fx x := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [fx, h, if_true]; fun_prop
    · simp only [fx, h, if_false, Bool.false_eq_true]; fun_prop
  exact (MvPolynomial.continuous_eval P).comp this
end PositivityTheory.Rg.Sw.WR.G.GI
