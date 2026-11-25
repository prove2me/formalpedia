-- Prove2me | solution 1 for PI.WGL.gTLower_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:27:42.902709+00:00
-- url     : https://prove2.me/submissions/56fe0638-6492-40be-87e7-946143ff8d36

import Definitions.Def_Formalism_PeriodIntegrals_GTLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_Assembly
import Theorems.Thm_PI_WGL_sqAct_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution (hN : Numbers) (hX : XiFacts) (hE : IoExists) (hP4 : IoIntegral)
    (hA : AdjointBr) (hB : BrIntegral) : PI.GTLower := by
  intro n N h lam sg hI
  obtain ⟨hc0, hcB, hdeg⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, -⟩ := hX n N h lam sg hI
  obtain ⟨io0, ⟨hE1, hE2⟩, hx, hW⟩ := hE n N h lam sg hI
  let c : ℂ := ((cBr h lam sg : ℤ) : ℂ)
  let io := c • io0
  have hio : ∀ x, io x = c • io0 x := fun x => rfl
  have I2 : ∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam := fun s hs =>
    Submodule.smul_mem _ _ (hE1 s hs)
  have I3 : ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
      io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s) := by
    intro g s hs
    rw [hio, hio, hE2 g s hs, sqAct_smul]
  have I4 : io (extremal ℂ n sg) = c • xi ℂ h lam sg := by rw [hio, hx]
  have I5 : LastWeight lam sg io := by
    intro a s hs
    rw [hio, sqAct_smul, hW a s hs, smul_comm]
  have I1 : ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
      io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f := by
    intro s hs
    obtain ⟨f, hf, hf'⟩ := hP4 n N h lam sg hI io0 ⟨hE1, hE2⟩ hx hW s hs
    exact ⟨f, hf, by rw [hio, ← map_smul]; exact hf'⟩
  obtain ⟨I6, br, hrest, hT⟩ := hA n N h lam sg hI io ⟨I2, I3⟩ I4 I5
  have B1 := hB n N h lam sg hI io br I1 I2 hrest.1 hT
  exact ⟨hc0, hcB, hxi0, hdeg, io, br, ⟨I1, I2, I3, I4, I5, I6⟩, ⟨B1, hrest⟩, hT⟩
end PI.WGL
