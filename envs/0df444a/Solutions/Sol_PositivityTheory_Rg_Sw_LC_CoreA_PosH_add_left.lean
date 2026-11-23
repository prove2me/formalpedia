-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.PosH.add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:55.944029+00:00
-- url     : https://prove2.me/submissions/0185a1a9-2102-465b-8e4f-377eab5c62ef

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight

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
theorem _root_.solution (v₁ v₂ w : V) : φ (v₁ + v₂) w = φ v₁ w + φ v₂ w := by
  rw [h.herm w (v₁ + v₂), h.add, star_add, ← h.herm w v₁, ← h.herm w v₂]
end PositivityTheory.Rg.Sw.LC.CoreA.PosH
