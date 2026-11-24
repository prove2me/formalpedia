-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.low_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:09:25.500517+00:00
-- url     : https://prove2.me/submissions/e8a56099-f16a-4254-a1be-7f17cdd75238

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_nat_mult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution {M : ℕ} (L : Set (Fin M → E))
    (h5 : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L := by
  obtain ⟨c, hc, hL⟩ := h5
  obtain ⟨k, hk, c', hkc⟩ := nat_mult c hc
  refine ⟨k, hk, fun i e he => ?_⟩
  have hkF : (k : F) = (c : F) * (c' : F) := by
    have h1 := congrArg (algebraMap (𝓞 F) F) hkc
    rw [map_natCast, map_mul] at h1
    exact h1
  have he' : IsIntegral ℤ ((c' : F) • e) := by
    rw [Algebra.smul_def]
    exact (map_isIntegral_int (algebraMap F E) (RingOfIntegers.isIntegral_coe c')).mul he
  have e1 : (k : F) • e = (c : F) • ((c' : F) • e) := by
    rw [smul_smul, ← hkF]
  rw [e1]
  exact hL i _ he'
end PI.UnitaryGroupMassFormula.UJClassFin
