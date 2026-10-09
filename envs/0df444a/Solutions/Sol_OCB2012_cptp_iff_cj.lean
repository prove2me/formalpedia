-- Prove2me | solution 1 for OCB2012.cptp_iff_cj
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:15:03.214934+00:00
-- url     : https://prove2.me/submissions/ba33bdc5-d7ff-429e-8706-fbe5d491ec0d

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj
import Theorems.Thm_PeresTerno_krausUpdate_completelyPositive
import Theorems.Thm_OCB2012_isTracePreserving_iff_ptrace_cj
import Theorems.Thm_OCB2012_cj_posSemidef_of_completelyPositive
import Theorems.Thm_OCB2012_exists_kraus_of_cj_posSemidef

open Matrix
open scoped Kronecker ComplexOrder

open OCB2012 in
theorem solution {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1] [DecidableEq x2]
    (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) :
    (PeresTerno.IsCompletelyPositive Φ ∧ IsTracePreserving Φ) ↔ IsCPTP_CJ (cjMatrix Φ) := by
  constructor
  · rintro ⟨hCP, hTP⟩
    exact ⟨cj_posSemidef_of_completelyPositive Φ hCP, (isTracePreserving_iff_ptrace_cj Φ).1 hTP⟩
  · rintro ⟨hJ, hpt⟩
    obtain ⟨K, hK⟩ := exists_kraus_of_cj_posSemidef Φ hJ
    have hΦ : (⇑Φ : Matrix x1 x1 ℂ → Matrix x2 x2 ℂ) = PeresTerno.krausUpdate K := funext hK
    refine ⟨?_, (isTracePreserving_iff_ptrace_cj Φ).2 hpt⟩
    rw [hΦ]
    exact PeresTerno.krausUpdate_completelyPositive K
