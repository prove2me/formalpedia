-- Prove2me | solution 1 for PI.AlgValsFin.W.pow_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:57.939823+00:00
-- url     : https://prove2.me/submissions/5eff9e4b-b9d8-41f5-a14f-02b33618c413

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_NormEqOneOfForallZpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
import Theorems.Thm_PI_AlgValsFin_W_evF_val
import Theorems.Thm_PI_AlgValsFin_W_exists_pow_close
import Theorems.Thm_PI_AlgValsFin_W_val_pow_sub_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UFin L, ∀ v ∈ S,
      Valued.v (((y ^ M : Ideles L) : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  choose N hNpos hN using fun v : HeightOneSpectrum (𝓞 L) => exists_pow_close v n
  refine ⟨∏ v ∈ S, N v, Finset.prod_pos fun v _ => hNpos v, fun y hy v hv => ?_⟩
  obtain ⟨r, hr⟩ : N v ∣ ∏ w ∈ S, N w := Finset.dvd_prod_of_mem N hv
  have hcomp : ((y ^ (∏ w ∈ S, N w) : Ideles L) : AdeleRing (𝓞 L) L).2 v =
      ((y : AdeleRing (𝓞 L) L).2 v) ^ (∏ w ∈ S, N w) := by
    rw [← evF_val, ← evF_val, map_pow, Units.val_pow_eq_pow_val]
  rw [hcomp, hr, pow_mul]
  have hy1 : Valued.v ((y : AdeleRing (𝓞 L) L).2 v) = 1 := hy.2 v
  have hx1 : Valued.v (((y : AdeleRing (𝓞 L) L).2 v) ^ N v) ≤ 1 := by
    rw [map_pow, hy1, one_pow]
  calc Valued.v ((((y : AdeleRing (𝓞 L) L).2 v) ^ N v) ^ r - 1)
      = Valued.v ((((y : AdeleRing (𝓞 L) L).2 v) ^ N v) ^ r - 1 ^ r) := by rw [one_pow]
    _ ≤ Valued.v (((y : AdeleRing (𝓞 L) L).2 v) ^ N v - 1) :=
        val_pow_sub_le v hx1 (by rw [map_one]) r
    _ ≤ WithZero.exp (-(n : ℤ)) := hN v _ hy1
end PI.AlgValsFin.W
