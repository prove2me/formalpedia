-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.nineCmp_of_nineAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:51.489848+00:00
-- url     : https://prove2.me/submissions/02ad5fc1-8883-4672-84c6-66b81ac4e66e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsAddTransfer
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsNineAdd
import Theorems.Thm_PositivityTheory_Lit1_PTN_nine_of_addTransfer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    {f0 : A0 →ₗ[ZMod N] A1} {f1 : A1 →ₗ[ZMod N] A2} {f3 : A3 →ₗ[ZMod N] A4}
    {f4 : A4 →ₗ[ZMod N] A5} {f6 : A6 →ₗ[ZMod N] A7} {f7 : A7 →ₗ[ZMod N] A8}
    (h : NineAdd f0 f1 f3 f4 f6 f7) : NineCmp f0 f1 f3 f4 f6 f7 := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7, e0, e1, e2, e3, e4,
    e5, e6, e7, e8, ε, h0, h1, h3, h4, h6, h7, hx⟩ := h
  obtain ⟨δ₁, δ₂, x⟩ := nine_of_addTransfer f0 f1 f3 f4 f6 f7 g0 g1 g2 g3 g4 g5 g6 g7
    e0 e1 e2 e3 e4 e5 e6 e7 e8 ε h0 h1 h3 h4 h6 h7 hx
  exact ⟨ModuleCat.of (ZMod N) A0, ModuleCat.of (ZMod N) A1, ModuleCat.of (ZMod N) A2,
    ModuleCat.of (ZMod N) A3, ModuleCat.of (ZMod N) A4, ModuleCat.of (ZMod N) A5,
    ModuleCat.of (ZMod N) A6, ModuleCat.of (ZMod N) A7, ModuleCat.of (ZMod N) A8,
    f0, f1, δ₁, f3, f4, δ₂, f6, f7, LinearEquiv.refl _ _, LinearEquiv.refl _ _,
    LinearEquiv.refl _ _, LinearEquiv.refl _ _, LinearEquiv.refl _ _, LinearEquiv.refl _ _,
    LinearEquiv.refl _ _, LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ => 1,
    fun a => by simp, fun a => by simp, fun a => by simp, fun a => by simp, fun a => by simp,
    fun a => by simp, x⟩
end PositivityTheory.Lit1.PTN
