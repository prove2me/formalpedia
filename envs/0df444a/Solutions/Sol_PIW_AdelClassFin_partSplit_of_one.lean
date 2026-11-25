-- Prove2me | solution 1 for PIW.AdelClassFin.partSplit_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:34:42.008988+00:00
-- url     : https://prove2.me/submissions/1ec78c1a-f647-4fca-95a1-bec5a12383a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h : SpOne) : PartSplit := by
  unfold PartSplit
  unfold SpOne at h
  intro F E _ _ _ _ _ _ _ m k hk hHL d hd G hG hdet

  have h1 : ∀ Γ ∈ G, FinCl (SplitSet E m k d {Γ}) := fun Γ hΓ => h E m k hk hHL d hd Γ (hdet Γ hΓ)
  choose T hTfin hT using h1
  refine ⟨⋃ (Γ) (hΓ : Γ ∈ G), T Γ hΓ, hG.biUnion' hTfin, ?_⟩
  rintro p ⟨hpL, v, hv, hvG⟩
  obtain ⟨q, hq, hiso⟩ := hT _ hvG p ⟨hpL, v, hv, Set.mem_singleton _⟩
  exact ⟨q, Set.mem_iUnion₂.mpr ⟨_, hvG, hq⟩, hiso⟩
end PIW.AdelClassFin
