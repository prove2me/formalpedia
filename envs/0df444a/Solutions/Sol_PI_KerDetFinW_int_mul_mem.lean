-- Prove2me | solution 1 for PI.KerDetFinW.int_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:11.934577+00:00
-- url     : https://prove2.me/submissions/ea325132-051d-4dfc-ac28-22db7b8fd08e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {k : K} (hk : k ∈ (algebraMap (𝓞 K) K).range)
    {y : E} (hy : y ∈ I) : algebraMap K E k * y ∈ I := by
  obtain ⟨z, rfl⟩ := hk
  have hz : IsIntegral ℤ (algebraMap K E (algebraMap (𝓞 K) K z)) :=
    (RingOfIntegers.isIntegral_coe z).map (algebraMap K E).toIntAlgHom
  have := (I : Submodule (𝓞 E) E).smul_mem (⟨_, hz⟩ : 𝓞 E) hy
  have e : ((⟨_, hz⟩ : 𝓞 E) • y) = algebraMap K E (algebraMap (𝓞 K) K z) * y := Algebra.smul_def _ _
  rw [← FractionalIdeal.mem_coe]
  convert this using 1
  exact e.symm
end PI.KerDetFinW
