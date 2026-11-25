-- Prove2me | solution 1 for PI.Dv.IdxW.len_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:43.751744+00:00
-- url     : https://prove2.me/submissions/0c3c1c3c-2ac6-4b2d-b7c3-0d62a310d155

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
import Theorems.Thm_PI_Dv_IdxW_lenS_ker_img
import Theorems.Thm_PI_Dv_IdxW_len_pow
import Theorems.Thm_PI_Dv_IdxW_fact
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


section
noncomputable section
namespace PI.Dv.IdxW
open NumberField IsDedekindDomain Module
section Gen
variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
end Gen
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
private lemma lenS_unit_lemma_2 {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
    (S : Submonoid R) (X Y : Submodule R W) (s : R) (hs : s ∈ S) (h : ∀ x ∈ X, s • x ∈ Y) :
    lenS S X Y = 0 := by
  unfold lenS
  rw [Module.length_eq_zero_iff]
  have hall : ∀ a : LocalizedModule S (↥X ⧸ Y.comap X.subtype), a = 0 := by
    intro a
    induction a using LocalizedModule.induction_on with
    | h m t =>
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq]
        refine ⟨⟨s, hs⟩, ?_⟩
        simp only [one_smul, smul_zero]
        rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
        exact h _ x.2
  exact ⟨fun a b => by rw [hall a, hall b]⟩
private lemma lenS_split_lemma {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
    (S : Submonoid R) (M N D : Submodule R W) (hDM : D ≤ M) (hDN : D ≤ N) :
    lenS S M D = lenS S M N + lenS S (M ⊓ N) D := by
  have hk : ∀ x, x ∈ N ↔ N.mkQ x = 0 := fun x => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have h1 := lenS_ker_img S N.mkQ N hk D M hDM
  have h2 := lenS_ker_img S N.mkQ N hk (M ⊓ N) M inf_le_left
  have hbot : ∀ E : Submodule R W, E ≤ N → E.map N.mkQ = ⊥ := fun E hE => by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hE hx
  have hz : lenS S (M ⊓ N) (M ⊓ N ⊓ N) = 0 :=
    lenS_unit_lemma_2 S _ _ 1 (Submonoid.one_mem S) (fun x hx => by
      rw [one_smul]
      exact Submodule.mem_inf.2 ⟨hx, (Submodule.mem_inf.1 hx).2⟩)
  rw [inf_eq_left.2 hDN, hbot D hDN] at h1
  rw [hbot _ inf_le_right, hz, zero_add] at h2
  have e : N.comap M.subtype = (M ⊓ N).comap M.subtype := by
    ext x
    simp [Submodule.mem_inf, x.2]
  have hc : lenS S M N = lenS S M (M ⊓ N) := by
    unfold lenS
    rw [e]
  rw [h1, hc, h2, add_comm]
end PI.Dv.IdxW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.IdxW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) (hM : M.FG) {c : 𝓞 K}
    (hc : c ≠ 0) :
    ∃ k : ℕ, Formalism.BasicNotions.vAdd w (algebraMap (𝓞 K) K c) = k ∧
      lenS w.asIdeal.primeCompl M (Ideal.span {c} • M) = ((k * Formalism.HN.rkK M : ℕ) : ℕ∞) := by
  obtain ⟨k, hk, hck, s, hs, hsy⟩ := fact w hc
  refine ⟨k, hk, ?_⟩
  have hle1 : Ideal.span {c} • M ≤ (w.asIdeal ^ k) • M :=
    Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).2 hck)
  have hle2 : (w.asIdeal ^ k) • M ≤ M := Submodule.smul_le_right
  rw [lenS_split_lemma _ M ((w.asIdeal ^ k) • M) _ (hle1.trans hle2) hle1, len_pow w M hM k]
  rw [lenS_unit_lemma_2 w.asIdeal.primeCompl _ _ s hs, add_zero]
  intro x hx
  have hx2 : x ∈ (w.asIdeal ^ k) • M := (Submodule.mem_inf.1 hx).2
  refine Submodule.smul_induction_on (p := fun x => s • x ∈ Ideal.span {c} • M) hx2
    (fun y hy z hz => ?_) (fun a b ha hb => ?_)
  · rw [← mul_smul]
    exact Submodule.smul_mem_smul (hsy y hy) hz
  · simp only [smul_add]
    exact Submodule.add_mem _ ha hb
end PI.Dv.IdxW
