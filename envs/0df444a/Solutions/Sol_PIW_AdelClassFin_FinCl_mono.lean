-- Prove2me | solution 1 for PIW.AdelClassFin.FinCl.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:15:13.245243+00:00
-- url     : https://prove2.me/submissions/184d3a99-086b-4807-b226-1aafdb9e65f3

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
    (h : FinCl S') (hs : S ⊆ S') : FinCl S := by
  obtain ⟨T, hT, hp⟩ := h
  exact ⟨T, hT, fun p hp' => hp p (hs hp')⟩
end FinCl
end PIW.AdelClassFin
