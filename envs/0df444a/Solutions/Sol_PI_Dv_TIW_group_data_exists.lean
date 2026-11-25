-- Prove2me | solution 1 for PI.Dv.TIW.group_data_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:37.723279+00:00
-- url     : https://prove2.me/submissions/9fbb3afb-b88f-4685-a08b-bf030b4bf030

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GroupDataExists
import Theorems.Thm_PI_Dv_TIW_entry_bound
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_absorb_eps
import Theorems.Thm_PI_Dv_TIW_eS_central
import Theorems.Thm_PI_Dv_TIW_eS_mul_eS
import Theorems.Thm_PI_Dv_TIW_eps_idem
import Theorems.Thm_PI_Dv_TIW_finrank_le_card
import Theorems.Thm_PI_Dv_TIW_intEl_of_intR
import Theorems.Thm_PI_Dv_TIW_intR_card_eS
import Theorems.Thm_PI_Dv_TIW_intR_epsS
import Theorems.Thm_PI_Dv_TIW_intR_mul
import Theorems.Thm_PI_Dv_TIW_intR_of
import Theorems.Thm_PI_Dv_TIW_mul_eS_eq
import Theorems.Thm_PI_Dv_TIW_perS
import Theorems.Thm_PI_Dv_TIW_sandwich
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
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
namespace PI.Dv.TIW
theorem _root_.solution : GrpData := by
  intro K _ _ G _ _ T P0 P hM1
  refine ⟨eS_mul_eS T, fun s z => eS_central T s z, eps_idem P, fun s => intEl_of_intR _ (intR_card_eS T s),
    fun s => ?_⟩
  obtain ⟨g, g', Γ, hΓ, hdet, b', hb'1, hb'2⟩ := perS T P0 P hM1 s
  refine ⟨fun k => epsS P * MonoidAlgebra.of K G (g k), fun j => epsS P0 * MonoidAlgebra.of K G (g' j), Γ, hdet,
    ?_, fun i => intEl_of_intR _ (intR_mul (intR_epsS P) (intR_of _)),
    fun j => intEl_of_intR _ (intR_mul (intR_epsS P0) (intR_of _)), ?_,
    fun i => (absorb_eps T s P P0 _).symm, fun j => (absorb_eps T s P0 P _).symm, b', hb'1, hb'2⟩
  ·
    intro σ
    set ΓK := Γ.map (algebraMap (𝓞 K) K) with hΓK
    have hdetK : algebraMap (𝓞 K) K Γ.det = ΓK.det := RingHom.map_det _ _
    have hentry : ∀ j k, (InfinitePlace.mk σ).1 (ΓK j k) ≤ ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
      intro j k
      show ‖σ (ΓK j k)‖ ≤ _
      rw [hΓK, Matrix.map_apply, hΓ j k]
      exact entry_bound T s P0 P (g' j) (g k) σ
    have hdl := Matrix.det_le hentry
    rw [Fintype.card_fin] at hdl
    rw [hdetK]
    refine (show ‖σ ΓK.det‖ ≤ _ from hdl).trans ?_
    have hnG : nS T P s ≤ Fintype.card G :=
      (Submodule.finrank_le _).trans (finrank_le_card (T.tau s) (T.irr s))
    have hN : ((nS T P s).factorial * (Fintype.card G ^ 3) ^ (nS T P s) : ℕ) ≤
        Fintype.card G ^ (4 * nS T P s) := by
      calc (nS T P s).factorial * (Fintype.card G ^ 3) ^ (nS T P s)
          ≤ (nS T P s) ^ (nS T P s) * (Fintype.card G ^ 3) ^ (nS T P s) :=
            Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
        _ ≤ (Fintype.card G) ^ (nS T P s) * (Fintype.card G ^ 3) ^ (nS T P s) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnG _)
        _ = Fintype.card G ^ (4 * nS T P s) := by ring
    rw [nsmul_eq_mul]
    exact_mod_cast hN
  ·
    intro i j
    have hmul : epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0 =
        epsS P0 * (MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i))) * eps P0 := by
      simp only [mul_assoc]
    have hτ : (T.tau s).asAlgebraHom
        (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0) =
        (T.tau s).asAlgebraHom (algebraMap (𝓞 K) K (Γ j i) • eps P0) := by
      rw [hmul, sandwich (T.tau s) P0 (hM1 s), map_smul, ← mul_assoc, ← hΓ j i]
    calc epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * (eps P0 * eS T s)
        = (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0) * eS T s := by
          simp only [mul_assoc]
      _ = (algebraMap (𝓞 K) K (Γ j i) • eps P0) * eS T s := mul_eS_eq T s _ _ hτ
      _ = algebraMap (𝓞 K) K (Γ j i) • (eps P0 * eS T s) := smul_mul_assoc _ _ _
end PI.Dv.TIW
