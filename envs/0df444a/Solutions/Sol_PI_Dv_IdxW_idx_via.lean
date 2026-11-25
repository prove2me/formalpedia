-- Prove2me | solution 1 for PI.Dv.IdxW.idx_via
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:16.29347+00:00
-- url     : https://prove2.me/submissions/9872fab0-af76-4953-871f-c25ef2f313b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
import Theorems.Thm_PI_Dv_IdxW_lenS_ker_img
import Theorems.Thm_PI_Dv_IdxW_lenAt_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [Module K V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.IdxW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (M N D : Submodule (𝓞 K) V) (hDM : D ≤ M)
    (hDN : D ≤ N) (hM : lenS w.asIdeal.primeCompl M D ≠ ⊤)
    (hN : lenS w.asIdeal.primeCompl N D ≠ ⊤) :
    idxAt w M N = ((lenS w.asIdeal.primeCompl M D).toNat : ℤ) -
      (lenS w.asIdeal.primeCompl N D).toNat := by
  have lenS_zero : ∀ X Y : Submodule (𝓞 K) V, X ≤ Y → lenS w.asIdeal.primeCompl X Y = 0 := by
    intro X Y h
    unfold lenS
    rw [Module.length_eq_zero_iff]
    have : Subsingleton (↥X ⧸ Y.comap X.subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      intro x _
      exact h x.2
    constructor
    intro a b
    induction a using LocalizedModule.induction_on with
    | h m s =>
      induction b using LocalizedModule.induction_on with
      | h m' s' =>
        rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, LocalizedModule.zero_mk,
          LocalizedModule.zero_mk]
  have split : ∀ M N D : Submodule (𝓞 K) V, D ≤ M → D ≤ N →
      lenS w.asIdeal.primeCompl M D = lenS w.asIdeal.primeCompl M N +
        lenS w.asIdeal.primeCompl (M ⊓ N) D := by
    intro M N D hDM hDN
    have hk : ∀ x, x ∈ N ↔ N.mkQ x = 0 := fun x => by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have h1 := lenS_ker_img w.asIdeal.primeCompl N.mkQ N hk D M hDM
    have h2 := lenS_ker_img w.asIdeal.primeCompl N.mkQ N hk (M ⊓ N) M inf_le_left
    have hbot : ∀ E : Submodule (𝓞 K) V, E ≤ N → E.map N.mkQ = ⊥ := fun E hE => by
      refine eq_bot_iff.2 fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hE hx
    rw [inf_eq_left.2 hDN, hbot D hDN] at h1
    rw [hbot _ inf_le_right, lenS_zero _ _ (le_inf le_rfl inf_le_right), zero_add] at h2
    have hc : lenS w.asIdeal.primeCompl M N = lenS w.asIdeal.primeCompl M (M ⊓ N) := by
      have e : N.comap M.subtype = (M ⊓ N).comap M.subtype := by
        ext x
        simp [Submodule.mem_inf, x.2]
      unfold lenS
      rw [e]
    rw [h1, hc, h2, add_comm]
  have hs := split M N D hDM hDN
  have hs' := split N M D hDN hDM
  rw [inf_comm] at hs'
  unfold PI.Dv.idxAt
  rw [lenAt_eq, lenAt_eq, hs, hs']
  rw [hs] at hM
  rw [hs'] at hN
  rw [ENat.toNat_add (WithTop.add_ne_top.1 hM).1 (WithTop.add_ne_top.1 hM).2,
    ENat.toNat_add (WithTop.add_ne_top.1 hN).1 (WithTop.add_ne_top.1 hN).2]
  push_cast
  ring
end PI.Dv.IdxW
