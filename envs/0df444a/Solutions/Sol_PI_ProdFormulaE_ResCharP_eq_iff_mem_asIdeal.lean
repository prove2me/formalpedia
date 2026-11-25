-- Prove2me | solution 1 for PI.ProdFormulaE.ResCharP.eq_iff_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:43.975479+00:00
-- url     : https://prove2.me/submissions/0f2e2b62-828b-4b4d-b926-3cc7732c55cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open PI PI.ProdFormulaE PI.ProdFormulaE.ResCharP
namespace PI.ProdFormulaE.ResCharP
theorem _root_.solution : St.ResCharIff := by
  intro F _ _ p ℓ hℓ
  show ringChar (𝓞 F ⧸ p.asIdeal) = ℓ ↔ _
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hz : ((ℓ : 𝓞 F ⧸ p.asIdeal) = 0) ↔ (ℓ : 𝓞 F) ∈ p.asIdeal := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  rw [← hz]
  constructor
  · intro h
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  · intro h
    rcases hℓ.eq_one_or_self_of_dvd _ (ringChar.dvd h) with h1 | h1
    · exfalso
      have hc := ringChar.Nat.cast_ringChar (R := 𝓞 F ⧸ p.asIdeal)
      rw [h1, Nat.cast_one] at hc
      exact one_ne_zero hc
    · exact h1
end PI.ProdFormulaE.ResCharP
