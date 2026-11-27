-- Prove2me | solution 1 for PI.VolStabSW.FFHS.fFInert_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:17:39.219866+00:00
-- url     : https://prove2.me/submissions/5d7ae098-c3b4-4b99-80f7-e0267d124a4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Theorems.Thm_PI_VolStabSW_FFHS_ffH_isHS
import Theorems.Thm_PI_VolStabSW_FFHS_ffH_single
import Theorems.Thm_PI_VolStabSW_FFHS_card_isom
import Theorems.Thm_PI_VolStabSW_FFHS_frob_of_ne
import Theorems.Thm_PI_VolStabSW_FFHS_card_norm_fiber
import Theorems.Thm_PI_VolStabSW_FFHS_IsSq_self_fixed
import Theorems.Thm_PI_VolStabSW_FFHS_card_diag
import Theorems.Thm_PI_VolStabSW_FFHS_exists_orth
import Theorems.Thm_PI_VolStabSW_FFHS_linIndep_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module Polynomial
namespace PI.VolStabSW.FFHS
theorem _root_.solution : FFInert := by
  unfold PI.VolStabSW.FFInert
  intro k K _ _ _ _ σ hσ h2 hne h2k M a haM J hJ hdet T hT hTdet
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K := Module.finite_of_finite k
  haveI : Fintype K := Fintype.ofFinite K
  have hfrob := frob_of_ne σ h2 hne
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have h2K : (2 : K) ≠ 0 := by
    have := (algebraMap k K).injective.ne h2k
    rwa [map_ofNat, map_zero] at this
  have hK' : Fintype.card K = Fintype.card k ^ Module.finrank k K := Module.card_eq_pow_finrank
  have hK : Fintype.card K = Nat.card k ^ 2 := by
    rw [hK', h2, Nat.card_eq_fintype_card]
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1 := by
    intro d hd
    rw [Nat.card_eq_fintype_card (α := k)]
    exact card_norm_fiber σ hfrob h2 d hd
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hsV := ffH_isHS hσ' J hJ hdet
  have hsU := ffH_isHS hσ' T hT hTdet
  obtain ⟨f, horth, hnz⟩ := exists_orth h2K a (Fin a → K)
    (PI.VolStabSW.ffH (σ : K →+* K) T) hsU (Module.finrank_fin_fun K)
  have hli := linIndep_orth hsU.toIsSq f horth hnz
  have hsp : Submodule.span K (Set.range f) = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun])
  let bf := Module.Basis.mk hli hsp.ge
  have hbf : ∀ i, bf i = f i := fun i => Module.Basis.mk_apply hli hsp.ge i
  have e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabSW.ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        PI.VolStabSW.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
    simp only [Pi.basisFun_apply, ffH_single]
    constructor
    · intro h i j
      exact congrFun (congrFun h i) j
    · intro h
      ext i j
      exact h i j
  have e2 := card_isom hsU.toIsSq
    hsV.toIsSq (Pi.basisFun K (Fin a))
  have e3 := card_isom hsU.toIsSq
    hsV.toIsSq bf
  have e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        PI.VolStabSW.ffH (σ : K →+* K) T (bf i) (bf j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    have hg : ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) T (bf i) (bf j) =
        if i = j then PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i) else 0 := by
      intro i j
      simp only [hbf]
      split_ifs with hij
      · rw [hij]
      · exact horth i j hij
    refine Nat.card_congr (Equiv.subtypeEquivRight fun Y => ?_)
    simp only [hg]
  rw [e1, ← e2, e3, e4]
  exact card_diag (Nat.card k) hq0 hK hσ' h2K hN a M haM
    (Fin M → K) (PI.VolStabSW.ffH (σ : K →+* K) J) hsV (Module.finrank_fin_fun K)
    (fun i => PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i))
    (fun i => hsU.toIsSq.self_fixed (f i)) hnz
end PI.VolStabSW.FFHS
