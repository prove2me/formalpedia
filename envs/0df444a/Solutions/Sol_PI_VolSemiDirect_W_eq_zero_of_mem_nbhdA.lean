-- Prove2me | solution 1 for PI.VolSemiDirect.W.eq_zero_of_mem_nbhdA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:34.47519+00:00
-- url     : https://prove2.me/submissions/de19d964-372c-4006-a782-f13e5ea2e8f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolSemiDirect.W
theorem _root_.solution (f : F) (hf : algebraMap F (AF F) f ∈ nbhdA F) : f = 0 := by
  obtain ⟨h1, h2⟩ := hf
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F f ≤ 1 := by
    intro v
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    have h3 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) f) v ∈ v.adicCompletionIntegers F := h2 v
    rw [FiniteAdeleRing.algebraMap_apply] at h3
    exact h3
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ hint
  have h4 : ‖algebraMap F (InfiniteAdeleRing F) f‖ < 1 := h1
  rw [InfiniteAdeleRing.coe_norm_eq_abs_norm] at h4
  by_contra hf0
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hf0
    rw [← hr, map_zero]
  have h5 : (1 : ℚ) ≤ |Algebra.norm ℚ ((r : 𝓞 F) : F)| := by
    have := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hr0)
    rw [← Algebra.coe_norm_int]
    exact_mod_cast this
  have h6 : ((r : 𝓞 F) : F) = f := hr
  rw [h6] at h5
  have h4' : |Algebra.norm ℚ f| < 1 := by exact_mod_cast h4
  linarith
end PI.VolSemiDirect.W
