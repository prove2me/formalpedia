-- Prove2me | solution 1 for PIW.AdelClassFin.FinCl.union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:54.71672+00:00
-- url     : https://prove2.me/submissions/d8e82449-0a4c-4193-92a0-84da4d89cdc6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar

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
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PIW.AdelClassFin
namespace FinCl
theorem _root_.solution {m : ℕ} {S S' : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))}
    (h : FinCl S) (h' : FinCl S') : FinCl (S ∪ S') := by
  obtain ⟨T, hT, hp⟩ := h
  obtain ⟨T', hT', hp'⟩ := h'
  refine ⟨T ∪ T', hT.union hT', fun p hp0 => ?_⟩
  rcases hp0 with h1 | h1
  · obtain ⟨q, hq, hi⟩ := hp p h1
    exact ⟨q, Or.inl hq, hi⟩
  · obtain ⟨q, hq, hi⟩ := hp' p h1
    exact ⟨q, Or.inr hq, hi⟩
end FinCl
end PIW.AdelClassFin
