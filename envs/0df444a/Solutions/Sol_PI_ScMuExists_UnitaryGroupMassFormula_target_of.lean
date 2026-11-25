-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.target_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:58.705801+00:00
-- url     : https://prove2.me/submissions/7e972852-46b9-45dc-8880-d050e7e34617

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (h5 : InstConj)
    (h6 : InstProper) : PI.ScMuExists.Target := by
  intro I r e f z hee hff hef hz hzz
  have hfr : IsFrame I e f z := ⟨hee, hff, hef, hz, hzz⟩
  obtain ⟨N, H, hNset, hHset, hN, hH, hnorm⟩ := h4 I r e f z
  obtain ⟨hNσ, hN0, hNc, hNinv, -, -⟩ := h1 I.Ginf N hN
  obtain ⟨hHσ, hH0, hHc, hHinv, -, -⟩ := h1 I.Ginf H hH
  have hconj := h5 I r e f z hfr N H hN hNset hHset
  have hprop := h6 I r e f z hfr N H hNset hHset
  obtain ⟨hSf, hSmeas, hSc, hSinv, hSpos, hScpt⟩ := h2 I.Ginf N H hN hH hnorm hconj hprop
  have := hSf
  obtain ⟨ν, hν⟩ := h3 I.Ginf (muInf I) (mulMeas (haarSub N hN) (haarSub H hH))
    ((N : Set I.Ginf) * (H : Set I.Ginf)) hSmeas hSc hSinv hSpos hScpt
  refine ⟨haarSub N hN, haarSub H hH, ν, ?_, ?_, hν⟩
  · refine ⟨hNσ, hN0, ?_, ?_⟩
    · rw [← hNset]
      exact hNc
    · intro s hs
      rw [← hNset] at hs
      exact hNinv s hs
  · refine ⟨hHσ, hH0, ?_, ?_⟩
    · rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset]
      exact hHc
    · intro s hs
      rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset] at hs
      exact hHinv s hs
end PI.ScMuExists.UnitaryGroupMassFormula
