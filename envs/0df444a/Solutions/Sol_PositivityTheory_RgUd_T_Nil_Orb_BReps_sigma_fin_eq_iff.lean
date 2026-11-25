-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.sigma_fin_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:28.563631+00:00
-- url     : https://prove2.me/submissions/27cce36d-e402-40dc-a5f8-2edbc6439b8e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainA

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
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution {ι : Type} {l : ι → ℕ} {b a : ι} {j : Fin (l b)} {i : Fin (l a)} :
    (⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, i⟩ ↔ b = a ∧ (j : ℕ) = i := by
  constructor
  · intro h
    cases h
    simp
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
