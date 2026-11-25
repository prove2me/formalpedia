-- Prove2me | solution 1 for PI.DvRows.intVal_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:24.245325+00:00
-- url     : https://prove2.me/submissions/358ee92d-16ef-43c2-8ecd-8e5d775e10ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_mem_comap_pow
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (conjW w).intValuation a = w.intValuation (starO K a) := by
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : starO K a ≠ 0 := by
    intro h0; apply ha
    have := congrArg (starO K) h0
    rwa [starO_starO, map_zero] at this
  have key : ∀ n : ℕ, (conjW w).intValuation a ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (starO K a) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact mem_comap_pow w.asIdeal n a
  obtain ⟨m1, h1⟩ : ∃ m : ℕ, (conjW w).intValuation a = WithZero.exp (-(m : ℤ)) :=
    ⟨_, (conjW w).intValuation_eq_exp_neg_multiplicity ha⟩
  obtain ⟨m2, h2⟩ : ∃ m : ℕ, w.intValuation (starO K a) = WithZero.exp (-(m : ℤ)) :=
    ⟨_, w.intValuation_eq_exp_neg_multiplicity ha'⟩
  have k1 := (key m1).1 (le_of_eq h1)
  have k2 := (key m2).2 (le_of_eq h2)
  rw [h2, WithZero.exp_le_exp] at k1
  rw [h1, WithZero.exp_le_exp] at k2
  have : m1 = m2 := by omega
  rw [h1, h2, this]
end PI.DvRows
