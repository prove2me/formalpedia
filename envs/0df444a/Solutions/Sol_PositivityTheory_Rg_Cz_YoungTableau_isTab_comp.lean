-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.isTab_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:48.525798+00:00
-- url     : https://prove2.me/submissions/e542a11e-11ca-479b-9117-a6398d871cc6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution {Y : Type} (col : X → C) (b : X → Fin n) (hT : IsTab col b) (e : Y → X)
    (he : Function.Injective e) (hcl : ∀ q y, col q = col (e y) → ∃ y', q = e y') : IsTab (col ∘ e) (b ∘ e) := by
  unfold IsTab at hT ⊢
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun p q hc hb => he (h1 _ _ hc hb), fun p i hi => ?_⟩
  obtain ⟨q, hq, hbq⟩ := h2 (e p) i hi
  obtain ⟨y', rfl⟩ := hcl q p hq
  exact ⟨y', hq, hbq⟩
end PositivityTheory.Rg.Cz.YoungTableau
