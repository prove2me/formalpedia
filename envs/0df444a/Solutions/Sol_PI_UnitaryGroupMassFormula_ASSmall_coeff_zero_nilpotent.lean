-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ASSmall.coeff_zero_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:15.851283+00:00
-- url     : https://prove2.me/submissions/76859030-0b18-4882-89c1-0c88fe80f1a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_CoordPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_ExistsAsOfValLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ASSmall
open scoped NNReal
variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  (hv : v.Integers O) {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
include hv
namespace PI.UnitaryGroupMassFormula.ASSmall
theorem _root_.solution (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ N : ℕ, PreTilt.coeff 0 e ^ N = 0 := by
  by_cases h0 : PreTilt.coeff 0 e = 0
  · exact ⟨1, by rw [pow_one, h0]⟩
  have hval : PreTilt.val K v O hv p e = ModP.preVal K v O p (PreTilt.coeff 0 e) := by
    change PreTilt.valAux K v O p e = _
    rw [PreTilt.valAux_eq hv h0, pow_zero, pow_one]
  obtain ⟨E, hE⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff 0 e)
  have hE0 : (Ideal.Quotient.mk (Ideal.span {(p : O)}) E : ModP O p) ≠ 0 := by
    rw [hE]; exact h0
  have hvE : v (algebraMap O K E) < 1 := by
    rw [← ModP.preVal_mk hv hE0, hE, ← hval]; exact he
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one hp hvE
  refine ⟨N, ?_⟩
  have hEN : (Ideal.Quotient.mk (Ideal.span {(p : O)}) (E ^ N) : ModP O p) = 0 := by
    by_contra h
    have h1 := (ModP.v_p_lt_val hv).2 h
    rw [map_pow, v.map_pow] at h1
    exact lt_asymm h1 hN
  rw [← hE, ← map_pow]; exact hEN
end PI.UnitaryGroupMassFormula.ASSmall
