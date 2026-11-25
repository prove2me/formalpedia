-- Prove2me | solution 1 for PI.WGL.ioExists_of_cap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:46.752961+00:00
-- url     : https://prove2.me/submissions/a48df732-5ce6-4a4b-a9ab-6aea22d92b02

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
import Theorems.Thm_PI_WGL_io_dw_ext
import Theorems.Thm_PI_WGL_exists_capelliPolynomial_ne
import Theorems.Thm_PI_WGL_io_eig_sep
import Theorems.Thm_PI_WGL_io_sqAct_smul
import Theorems.Thm_PI_WGL_io_sqAct_zero
import Theorems.Thm_PI_WGL_io_sqAct_mem
import Theorems.Thm_PI_WGL_io_sqAct_mul
import Theorems.Thm_PI_WGL_ioSqActL_apply
import Theorems.Thm_PI_WGL_io_last_emb
import Theorems.Thm_PI_WGL_io_extremal_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) (hC : CapFacts) :
    IoExists := by
  classical
  intro n N h lam sg hI
  obtain ⟨hxi0, hxiM, hxiU, -, hxiL, -⟩ := hx n N h lam sg hI
  obtain ⟨C, hCφ, hCxi⟩ := hC n N h lam sg hI
  obtain ⟨hB1, hB2⟩ := h4 n N h lam
  let T : DomWeight n → Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := fun mu =>
    ⨆ (_ : Interlace h lam mu) (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (_ : IsEqv h mu lam φ), (nablaSq ℂ n mu).map φ
  have hT : ∀ mu, ∀ y ∈ T mu, ∀ u, C u y = capP mu u • y := by
    intro mu
    let Eig : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
      ⨅ u, LinearMap.ker (C u - capP mu u • LinearMap.id)
    have hle : T mu ≤ Eig := by
      refine iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨s, hs, rfl⟩
      simp only [Eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
      exact fun u => hCφ mu hmu φ hφ s hs u
    intro y hy u
    have hy' := hle hy
    simp only [Eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hy'
    exact hy' u
  have hxiT : xi ℂ h lam sg ∈ ⨆ mu, T mu := by
    have hm := hxiM
    rw [hB2] at hm
    exact hm
  obtain ⟨f, hfT, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp T _).mp hxiT
  have hs : ∑ i ∈ f.support, f i = xi ℂ h lam sg := hfsum
  have hsep := io_eig_sep C (fun mu u => capP mu u) sg
    (fun mu hne => exists_capelliPolynomial_ne mu sg (fun hw => hne (io_dw_ext hw))) f.support f
    (fun mu _ => hT mu (f mu) (hfT mu)) (by rw [hs]; exact hCxi)
  have hxiTsg : xi ℂ h lam sg ∈ T sg := by
    rw [← hs, hsep]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    have hi0 : i = sg := (Finset.mem_filter.mp hi).2
    rw [hi0]
    exact hfT sg
  by_cases hex : ∃ φ0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam φ0 ∧ ∃ s0 ∈ nablaSq ℂ n sg, φ0 s0 ≠ 0
  swap
  · exfalso
    apply hxi0
    have hbot : T sg = ⊥ := by
      refine eq_bot_iff.mpr (iSup_le fun _ => iSup_le fun φ => iSup_le fun hφ => ?_)
      rintro _ ⟨s, hs, rfl⟩
      rw [Submodule.mem_bot]
      by_contra hne
      exact hex ⟨φ, hφ, s, hs, hne⟩
    rw [hbot] at hxiTsg
    exact (Submodule.mem_bot ℂ).mp hxiTsg
  obtain ⟨φ0, hφ0, s0, hs0, hs0ne⟩ := hex
  have hprop : ∀ φ, IsEqv h sg lam φ → ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n sg, φ s = c • φ0 s := by
    intro φ hφ
    refine (hB1 sg φ φ0 ?_ ⟨s0, hs0, hs0ne⟩).2
    intro ψ hψ
    rcases hψ with rfl | rfl
    · exact hφ
    · exact hφ0
  have hTle : T sg ≤ (nablaSq ℂ n sg).map φ0 := by
    refine iSup_le fun _ => iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨c, hc⟩ := hprop φ hφ
    exact ⟨c • s, Submodule.smul_mem _ _ hs, by rw [map_smul, hc s hs]⟩
  obtain ⟨t, ht, hφt⟩ := hTle hxiTsg
  let K : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := nablaSq ℂ n sg ⊓ LinearMap.ker φ0
  have hKst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ K, sqAct ℂ n sg g v ∈ K := by
    intro g v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    rw [LinearMap.mem_ker] at hv2
    refine Submodule.mem_inf.mpr ⟨io_sqAct_mem sg g hv1, ?_⟩
    rw [LinearMap.mem_ker, hφ0.2 g v hv1, hv2, io_sqAct_zero]
  have hK : K = ⊥ := by
    rcases (h3 n sg).2.1 K inf_le_left hKst with hK | hK
    · exact hK
    · exfalso
      have hs0K : s0 ∈ K := by rw [hK]; exact hs0
      exact hs0ne (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hs0K).2)
  have hfix : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ n sg g t = t := by
    intro g hg1 hg2
    have hv : sqAct ℂ n sg g t - t ∈ K := by
      refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ (io_sqAct_mem sg g ht) ht, ?_⟩
      rw [LinearMap.mem_ker, map_sub, hφ0.2 g t ht, hφt, hxiU g hg1 hg2, sub_self]
    rw [hK, Submodule.mem_bot, sub_eq_zero] at hv
    exact hv
  obtain ⟨c, hc⟩ := (h3 n sg).2.2 t ht hfix
  have hext := io_extremal_mem h3 n sg
  let io0 := c • φ0
  have hE : IsEqv h sg lam io0 := by
    refine ⟨fun s hs => Submodule.smul_mem _ _ (hφ0.1 s hs), fun g s hs => ?_⟩
    simp only [io0, LinearMap.smul_apply]
    rw [hφ0.2 g s hs, io_sqAct_smul]
  have hext0 : io0 (extremal ℂ n sg) = xi ℂ h lam sg := by
    simp only [io0, LinearMap.smul_apply]
    rw [← map_smul, ← hc, hφt]
  refine ⟨io0, hE, hext0, ?_⟩
  intro a s hs
  let ψ := (ioSqActL N lam (lastGL ℂ N a)).comp io0
  have hψ : IsEqv h sg lam ψ := by
    refine ⟨fun s hs => io_sqAct_mem lam _ (hE.1 s hs), fun g s hs => ?_⟩
    simp only [ψ, LinearMap.comp_apply, ioSqActL_apply]
    rw [hE.2 g s hs, ← io_sqAct_mul, ← io_sqAct_mul, io_last_emb]
  obtain ⟨-, d, hd⟩ := hB1 sg ψ io0 (by
      intro χ hχ
      rcases hχ with rfl | rfl
      · exact hψ
      · exact hE)
    ⟨extremal ℂ n sg, hext, by rw [hext0]; exact hxi0⟩
  have h1 := hd _ hext
  simp only [ψ, LinearMap.comp_apply, ioSqActL_apply] at h1
  rw [hext0, hxiL a] at h1
  have hd' : d = ((a ^ degZ lam sg : ℂˣ) : ℂ) := by
    have h0 : (((a ^ degZ lam sg : ℂˣ) : ℂ) - d) • xi ℂ h lam sg = 0 := by rw [sub_smul, h1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hxi0)).symm
  have h2 := hd s hs
  simp only [ψ, LinearMap.comp_apply, ioSqActL_apply] at h2
  rw [h2, hd']
end PI.WGL
