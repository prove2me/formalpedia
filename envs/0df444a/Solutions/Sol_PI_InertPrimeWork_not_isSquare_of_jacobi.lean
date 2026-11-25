-- Prove2me | solution 1 for PI.InertPrimeWork.not_isSquare_of_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:31.614933+00:00
-- url     : https://prove2.me/submissions/7b57e668-6518-4f51-88df-cbb5b3f01e0b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InertPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeJacobi_NotIsSquareOfJacobi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.InertPrimeWork
namespace PI.InertPrimeWork
theorem _root_.solution {d p : ℕ} (hp : p.Prime) (h : jacobiSym (-(d : ℤ)) p = -1) :
    ¬ IsSquare (((-(d : ℤ) : ℤ)) : ZMod p) := by
  haveI := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  exact (legendreSym.eq_neg_one_iff p).1 h
end PI.InertPrimeWork
