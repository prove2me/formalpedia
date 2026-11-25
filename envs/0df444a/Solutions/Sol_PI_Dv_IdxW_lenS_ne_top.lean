-- Prove2me | solution 1 for PI.Dv.IdxW.lenS_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:01.011565+00:00
-- url     : https://prove2.me/submissions/afa1b529-6e3e-491e-815d-59b004c9e01d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
import Theorems.Thm_PI_Dv_IdxW_span_smul_le
import Theorems.Thm_PI_Dv_IdxW_lenS_ker_img
import Theorems.Thm_PI_Dv_IdxW_len_c
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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (X Y : Submodule (𝓞 K) V) (hX : X.FG)
    {c : 𝓞 K} (hc : c ≠ 0) (h : ∀ x ∈ X, c • x ∈ Y) : lenS w.asIdeal.primeCompl X Y ≠ ⊤ := by
  obtain ⟨k, -, hk⟩ := len_c w X hX hc
  have hD : Ideal.span {c} • X ≤ Y := span_smul_le c X Y h
  have e := lenS_split_lemma w.asIdeal.primeCompl X Y _ Submodule.smul_le_right hD
  rw [hk] at e
  intro htop
  rw [htop, top_add] at e
  exact ENat.coe_ne_top _ e
end PI.Dv.IdxW
