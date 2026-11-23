-- Prove2me | solution 1 for UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:30.665027+00:00
-- url     : https://prove2.me/submissions/345c1e29-002a-4584-840e-d0ceb6dd5227

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.S6
namespace UpperTheory.Reformulated.B.S6
theorem _root_.solution (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := by
    intro a
    have h : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      exact a.2
    exact h
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer hmem
  have hint : IsIntegral v.integer x := by
    obtain ⟨P, hP, hPx⟩ := hx
    refine ⟨P.map f, hP.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPx
  exact (Valuation.integer.integers v).mem_of_integral hint
end UpperTheory.Reformulated.B.S6
