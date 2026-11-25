-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.resChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:14.029072+00:00
-- url     : https://prove2.me/submissions/8e9cacff-97b4-44f6-8202-363b85602c5a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_SigRTmulOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSLocA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {E : Type} [Field E] [NumberField E] (P : Ideal (𝓞 E)) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 E) ∉ P := by
  letI := Ideal.Quotient.field P
  set p := ringChar (𝓞 E ⧸ P)
  haveI : CharP (𝓞 E ⧸ P) p := ringChar.charP _
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hmem : ((Ideal.absNorm P : ℕ) : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  have hN0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hdvd : p ∣ Ideal.absNorm P := (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p _).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hp0 : p ≠ 0 := fun h => hN0 (by rw [h] at hdvd; exact zero_dvd_iff.1 hdvd)
  have hpr : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right hp0
  refine ⟨p, hpr, fun m hm hmP => hm ?_⟩
  exact (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p m).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmP)
end PI.UnitaryGroupMassFormula.UJClassMass
