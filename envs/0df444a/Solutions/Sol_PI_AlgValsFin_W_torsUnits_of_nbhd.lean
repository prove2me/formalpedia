-- Prove2me | solution 1 for PI.AlgValsFin.W.torsUnits_of_nbhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:52.566026+00:00
-- url     : https://prove2.me/submissions/6dc2c6c4-35f5-406e-98bc-b27ff4d035e5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_NormEqOneOfForallZpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
import Theorems.Thm_PI_AlgValsFin_W_pow_close
import Theorems.Thm_PI_AlgValsFin_W_eq_one_of_forall_zpow
import Theorems.Thm_UpperTheory_Reformulated_B_Qk23_eq_one_of_forall_zpow


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
theorem _root_.solution (L : Type) [Field L] [NumberField L]
    (hnb : ∀ W : Set (Ideles L), IsOpen W → (1 : Ideles L) ∈ W →
      ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), ∀ x ∈ UFin L,
        (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))) → x ∈ W) :
    TorsUnits L := by
  intro χ
  set W : Set (Ideles L) := χ.1 ⁻¹' {u : ℂˣ | ‖(u : ℂ) - 1‖ < 1} with hW
  have hWo : IsOpen W := by
    refine IsOpen.preimage χ.2.1 ?_
    exact isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hW1 : (1 : Ideles L) ∈ W := by
    simp [hW]
  obtain ⟨S, n, hSn⟩ := hnb W hWo hW1
  obtain ⟨M, hM, hclose⟩ := pow_close (L := L) S n
  refine ⟨M, hM, fun x hx => ?_⟩
  have hmem : ∀ k : ℤ, (x ^ k) ^ M ∈ W := by
    intro k
    have hk : x ^ k ∈ UFin L := (ufinSub L).zpow_mem hx k
    have hkM : (x ^ k) ^ M ∈ UFin L := (ufinSub L).pow_mem hk M
    exact hSn _ hkM (fun v hv => hclose _ hk v hv)
  have hz : ((χ.1 (x ^ M) : ℂˣ) : ℂ) = 1 := by
    apply eq_one_of_forall_zpow
    intro k
    have e : ((χ.1 (x ^ M) : ℂˣ) : ℂ) ^ k = ((χ.1 ((x ^ k) ^ M) : ℂˣ) : ℂ) := by
      rw [← Units.val_zpow_eq_zpow_val, ← map_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
        ← zpow_mul, mul_comm]
    rw [e]
    exact hmem k
  rw [← map_pow]
  exact Units.ext hz
end PI.AlgValsFin.W
