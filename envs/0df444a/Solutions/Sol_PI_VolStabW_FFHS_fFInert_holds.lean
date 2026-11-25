-- Prove2me | solution 1 for PI.VolStabW.FFHS.fFInert_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:42:23.053442+00:00
-- url     : https://prove2.me/submissions/2a9bb6dd-1de1-4a24-afb5-01a10cef5e32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFIn
import Theorems.Thm_PI_VolStabW_FFHS_ffH_isHS
import Theorems.Thm_PI_VolStabW_FFHS_ffH_single
import Theorems.Thm_PI_VolStabW_FFHS_card_isom
import Theorems.Thm_PI_VolStabW_FFHS_frob_of_ne
import Theorems.Thm_PI_VolStabW_FFHS_card_norm_fiber
import Theorems.Thm_PI_VolStabW_FFHS_IsSq_self_fixed
import Theorems.Thm_PI_VolStabW_FFHS_card_diag
import Theorems.Thm_PI_VolStabW_FFHS_exists_orth
import Theorems.Thm_PI_VolStabW_FFHS_linIndep_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module Polynomial
namespace PI.VolStabW.FFHS
theorem _root_.solution : FFInert := by
  intro k K _ _ _ _ σ hσ h2 hne h2k M a haM J hJ hdJ T hT hdT
  classical
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hfrob := frob_of_ne σ h2 hne
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hN : ∀ d : K, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Fintype.card k + 1 :=
    fun d hd => card_norm_fiber σ hfrob h2 d hd
  have h2K : (2 : K) ≠ 0 := by
    intro h
    exact h2k ((algebraMap k K).injective (by rw [map_ofNat, map_zero]; exact h))
  have hJs := ffH_isHS hσ' J hJ hdJ
  have hTs := ffH_isHS hσ' T hT hdT
  obtain ⟨f, hf1, hf2⟩ := exists_orth h2K a (Fin a → K) (ffH (σ : K →+* K) T) hTs
    (Module.finrank_fin_fun K)
  let b := basisOfLinearIndependentOfCardEqFinrank' f (linIndep_orth hTs.toIsSq f hf1 hf2)
    (by simp)
  have e1 : Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun X => ?_))
    rw [← Matrix.ext_iff]
    simp only [ffGram, Pi.basisFun_apply, ffH_single]
  have e3 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        ffH (σ : K →+* K) T (b i) (b j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun Y => ?_))
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
    refine forall_congr' (fun i => forall_congr' (fun j => ?_))
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, hf1 i j hij]
  rw [e1, ← card_isom hTs.toIsSq hJs.toIsSq (Pi.basisFun K (Fin a)),
    card_isom hTs.toIsSq hJs.toIsSq b, e3,
    card_diag (Fintype.card k) (by omega) hK hσ' h2K hN a M haM (Fin M → K) _ hJs
      (Module.finrank_fin_fun K) _ (fun i => hTs.toIsSq.self_fixed (f i)) hf2,
    Nat.card_eq_fintype_card (α := k)]
end PI.VolStabW.FFHS
