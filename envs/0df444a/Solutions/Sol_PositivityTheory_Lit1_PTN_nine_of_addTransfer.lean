-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.nine_of_addTransfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:32.028938+00:00
-- url     : https://prove2.me/submissions/c988b4ac-a639-4dcd-b44e-526833d915b7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsAddTransfer
import Theorems.Thm_PositivityTheory_Lit1_PTN_exact_of_addTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    {B0 B1 B2 B3 B4 B5 B6 B7 BetaSesquilinearity : Type} [AddCommGroup B0] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4] [AddCommGroup B5] [AddCommGroup B6] [AddCommGroup B7] [AddCommGroup BetaSesquilinearity]
    (f0 : A0 →ₗ[ZMod N] A1) (f1 : A1 →ₗ[ZMod N] A2) (f3 : A3 →ₗ[ZMod N] A4)
    (f4 : A4 →ₗ[ZMod N] A5) (f6 : A6 →ₗ[ZMod N] A7) (f7 : A7 →ₗ[ZMod N] A8)
    (g0 : B0 →+ B1) (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (g5 : B5 →+ B6) (g6 : B6 →+ B7) (g7 : B7 →+ BetaSesquilinearity)
    (e0 : A0 ≃+ B0) (e1 : A1 ≃+ B1) (e2 : A2 ≃+ B2) (e3 : A3 ≃+ B3) (e4 : A4 ≃+ B4)
    (e5 : A5 ≃+ B5) (e6 : A6 ≃+ B6) (e7 : A7 ≃+ B7) (e8 : A8 ≃+ BetaSesquilinearity) (ε : Fin 6 → ℤˣ)
    (h0 : ∀ a, g0 (e0 a) = (ε 0 : ℤ) • e1 (f0 a)) (h1 : ∀ a, g1 (e1 a) = (ε 1 : ℤ) • e2 (f1 a))
    (h3 : ∀ a, g3 (e3 a) = (ε 2 : ℤ) • e4 (f3 a)) (h4 : ∀ a, g4 (e4 a) = (ε 3 : ℤ) • e5 (f4 a))
    (h6 : ∀ a, g6 (e6 a) = (ε 4 : ℤ) • e7 (f6 a)) (h7 : ∀ a, g7 (e7 a) = (ε 5 : ℤ) • e8 (f7 a))
    (hx : Function.Injective g0 ∧ Function.Exact g0 g1 ∧ Function.Exact g1 g2 ∧
      Function.Exact g2 g3 ∧ Function.Exact g3 g4 ∧ Function.Exact g4 g5 ∧ Function.Exact g5 g6 ∧
      Function.Exact g6 g7 ∧ Function.Surjective g7) :
    ∃ (δ₁ : A2 →ₗ[ZMod N] A3) (δ₂ : A5 →ₗ[ZMod N] A6),
      Function.Injective f0 ∧ Function.Exact f0 f1 ∧ Function.Exact f1 δ₁ ∧ Function.Exact δ₁ f3 ∧
      Function.Exact f3 f4 ∧ Function.Exact f4 δ₂ ∧ Function.Exact δ₂ f6 ∧ Function.Exact f6 f7 ∧
      Function.Surjective f7 := by
  let δ₁ : A2 →ₗ[ZMod N] A3 :=
    (e3.symm.toAddMonoidHom.comp (g2.comp e2.toAddMonoidHom)).toZModLinearMap N
  let δ₂ : A5 →ₗ[ZMod N] A6 :=
    (e6.symm.toAddMonoidHom.comp (g5.comp e5.toAddMonoidHom)).toZModLinearMap N
  have hδ₁ : ∀ a, g2 (e2 a) = ((1 : ℤˣ) : ℤ) • e3 (δ₁ a) := by
    intro a
    change g2 (e2 a) = ((1 : ℤˣ) : ℤ) • e3 (e3.symm (g2 (e2 a)))
    rw [AddEquiv.apply_symm_apply, Units.val_one, one_smul]
  have hδ₂ : ∀ a, g5 (e5 a) = ((1 : ℤˣ) : ℤ) • e6 (δ₂ a) := by
    intro a
    change g5 (e5 a) = ((1 : ℤˣ) : ℤ) • e6 (e6.symm (g5 (e5 a)))
    rw [AddEquiv.apply_symm_apply, Units.val_one, one_smul]
  obtain ⟨hi, x01, x12, x23, x34, x45, x56, x67, hs⟩ := hx
  refine ⟨δ₁, δ₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply e0.injective
    apply hi
    rw [h0, h0, hab]
  · exact PositivityTheory.Lit1.PTN.exact_of_addTransfer (map_add f0) (map_add f1) g0 g1 e0 e1 e2
      (ε 0) (ε 1) h0 h1 x01
  · exact PositivityTheory.Lit1.PTN.exact_of_addTransfer (map_add f1) (map_add δ₁) g1 g2 e1 e2 e3
      (ε 1) 1 h1 hδ₁ x12
  · exact PositivityTheory.Lit1.PTN.exact_of_addTransfer (map_add δ₁) (map_add f3) g2 g3 e2 e3 e4
      1 (ε 2) hδ₁ h3 x23
  · exact PositivityTheory.Lit1.PTN.exact_of_addTransfer (map_add f3) (map_add f4) g3 g4 e3 e4 e5
      (ε 2) (ε 3) h3 h4 x34
  · exact PositivityTheory.Lit1.PTN.exact_of_addTransfer (map_add f4) (map_add δ₂) g4 g5 e4 e5 e6
      (ε 3) 1 h4 hδ₂ x45
  · exact PositivityTheory.Lit1.PTN.exact_of_addTransfer (map_add δ₂) (map_add f6) g5 g6 e5 e6 e7
      1 (ε 4) hδ₂ h6 x56
  · exact PositivityTheory.Lit1.PTN.exact_of_addTransfer (map_add f6) (map_add f7) g6 g7 e6 e7 e8
      (ε 4) (ε 5) h6 h7 x67
  · intro y
    obtain ⟨z, hz⟩ := hs (e8 y)
    refine ⟨(ε 5 : ℤ) • e7.symm z, ?_⟩
    have hy := h7 (e7.symm z)
    rw [AddEquiv.apply_symm_apply, hz] at hy
    apply e8.injective
    rw [map_zsmul, map_zsmul, hy]
end PositivityTheory.Lit1.PTN
