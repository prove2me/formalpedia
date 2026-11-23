-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.resChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:36.553976+00:00
-- url     : https://prove2.me/submissions/4c00fd89-4d6d-41f1-b116-5d5b881ed144

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel WithZero
open PI PI.PinHostLoc PI.PinHostLoc.UnitaryGroupMassFormula
namespace PI.PinHostLoc.UnitaryGroupMassFormula
theorem _root_.solution {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {n : ℕ} (hn : n.Prime) (hp : ((n : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    Formalism.MainNotions.S.Loc.resChar p = n := by
  have : Nontrivial (𝓞 F ⧸ p.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
  have h0 : ((n : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal) n]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  show ringChar (𝓞 F ⧸ p.asIdeal) = n
  exact CharP.ringChar_of_prime_eq_zero (R := 𝓞 F ⧸ p.asIdeal) hn h0
end PI.PinHostLoc.UnitaryGroupMassFormula
