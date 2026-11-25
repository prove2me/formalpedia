-- Prove2me | solution 1 for PI.VolStabS.FFHS.fFInert_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:39:25.535109+00:00
-- url     : https://prove2.me/submissions/66d07882-3cb0-4ff8-a95b-f1c96bb12eeb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
import Theorems.Thm_PI_VolStabS_FFHS_ffH_isHS
import Theorems.Thm_PI_VolStabS_FFHS_ffH_single
import Theorems.Thm_PI_VolStabS_FFHS_card_isom
import Theorems.Thm_PI_VolStabS_FFHS_frob_of_ne
import Theorems.Thm_PI_VolStabS_FFHS_card_norm_fiber
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_self_fixed
import Theorems.Thm_PI_VolStabS_FFHS_card_diag
import Theorems.Thm_PI_VolStabS_FFHS_exists_orth
import Theorems.Thm_PI_VolStabS_FFHS_linIndep_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabS.FFHS
open Module Polynomial
section matrix
variable {K : Type} [Field K] {σ : K →+* K}
end matrix
section field
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
private theorem card_eq_card_sq_of_finrank_two (h2 : finrank k K = 2) :
    Fintype.card K = Fintype.card k ^ 2 := by
  rw [← h2]
  exact Module.card_eq_pow_finrank
end field
end PI.VolStabS.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module Polynomial
namespace PI.VolStabS.FFHS
theorem _root_.solution : FFInert := by
  intro k K _ _ _ _ σ hσ hrank hne h2k M a haM J hJ hJdet T hT hTdet
  classical
  haveI : Module.Finite k K := Module.finite_of_finrank_eq_succ hrank
  haveI : Finite K := Module.finite_of_finite k
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype K := Fintype.ofFinite K
  have hfrob := frob_of_ne σ hrank hne
  have hσr : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have h2K : (2 : K) ≠ 0 := by
    have h2' := (algebraMap k K).injective.ne h2k
    rwa [map_ofNat, map_zero] at h2'
  have hK : Fintype.card K = Nat.card k ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact card_eq_card_sq_of_finrank_two hrank
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1 := by
    intro d hd
    rw [Nat.card_eq_fintype_card (α := k)]
    exact card_norm_fiber σ hfrob hrank d hd
  have hsV : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) J) :=
    ffH_isHS hσr J hJ hJdet
  have hsU : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) T) :=
    ffH_isHS hσr T hT hTdet
  have e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabS.ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i)
            (Pi.basisFun K (Fin a) j)} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro X
    simp only [Pi.basisFun_apply, ffH_single]
    constructor
    · intro h i j
      subst h
      rfl
    · intro h
      exact Matrix.ext fun i j => h i j
  obtain ⟨f, hf1, hf2⟩ := exists_orth h2K a (Fin a → K)
    (PI.VolStabS.ffH (σ : K →+* K) T) hsU (by simp)
  have hli := linIndep_orth hsU.toIsSq f hf1 hf2
  obtain ⟨b', hb'⟩ : ∃ b' : Basis (Fin a) K (Fin a → K), ∀ i, b' i = f i := by
    rcases isEmpty_or_nonempty (Fin a) with hE | hE
    · exact ⟨Basis.empty _, fun i => isEmptyElim i⟩
    · exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), fun i => by simp⟩
  have e2 := card_isom hsU.toIsSq hsV.toIsSq
    (Pi.basisFun K (Fin a))
  have e3 := card_isom hsU.toIsSq hsV.toIsSq b'
  have e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    have hdiag : ∀ i j, PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j) =
        if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0 := by
      intro i j
      rw [hb', hb']
      split_ifs with hij
      · subst hij
        rfl
      · exact hf1 i j hij
    simp only [hdiag]
  have key := e1.trans (e2.symm.trans (e3.trans e4))
  have final := card_diag (Nat.card k) hq0 hK hσr h2K hN a M haM (Fin M → K)
    (PI.VolStabS.ffH (σ : K →+* K) J) hsV (by simp)
    (fun i => PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i))
    (fun i => hsU.toIsSq.self_fixed (f i)) hf2
  exact (congrArg (fun n : ℕ => (n : ℝ)) key).trans final
end PI.VolStabS.FFHS
