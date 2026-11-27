-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.nineAdd_intro
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:03.211846+00:00
-- url     : https://prove2.me/submissions/a2a15784-569f-4ead-b92e-b927a8467ed7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsNineAdd
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsNineAddIntro

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
    {f0 : A0 →ₗ[ZMod N] A1} {f1 : A1 →ₗ[ZMod N] A2} {f3 : A3 →ₗ[ZMod N] A4}
    {f4 : A4 →ₗ[ZMod N] A5} {f6 : A6 →ₗ[ZMod N] A7} {f7 : A7 →ₗ[ZMod N] A8}
    {B0 B1 B2 B3 B4 B5 B6 B7 BetaSesquilinearity : Type} [AddCommGroup B0] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4] [AddCommGroup B5] [AddCommGroup B6] [AddCommGroup B7] [AddCommGroup BetaSesquilinearity]
    (g0 : B0 →+ B1) (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (g5 : B5 →+ B6) (g6 : B6 →+ B7) (g7 : B7 →+ BetaSesquilinearity)
    (e0 : A0 ≃+ B0) (e1 : A1 ≃+ B1) (e2 : A2 ≃+ B2) (e3 : A3 ≃+ B3) (e4 : A4 ≃+ B4)
    (e5 : A5 ≃+ B5) (e6 : A6 ≃+ B6) (e7 : A7 ≃+ B7) (e8 : A8 ≃+ BetaSesquilinearity) (ε : Fin 6 → ℤˣ)
    (h0 : ∀ a, g0 (e0 a) = (ε 0 : ℤ) • e1 (f0 a)) (h1 : ∀ a, g1 (e1 a) = (ε 1 : ℤ) • e2 (f1 a))
    (h3 : ∀ a, g3 (e3 a) = (ε 2 : ℤ) • e4 (f3 a)) (h4 : ∀ a, g4 (e4 a) = (ε 3 : ℤ) • e5 (f4 a))
    (h6 : ∀ a, g6 (e6 a) = (ε 4 : ℤ) • e7 (f6 a)) (h7 : ∀ a, g7 (e7 a) = (ε 5 : ℤ) • e8 (f7 a))
    (i0 : Function.Injective g0) (x1 : Function.Exact g0 g1) (x2 : Function.Exact g1 g2)
    (x3 : Function.Exact g2 g3) (x4 : Function.Exact g3 g4) (x5 : Function.Exact g4 g5)
    (x6 : Function.Exact g5 g6) (x7 : Function.Exact g6 g7) (s7 : Function.Surjective g7) :
    NineAdd f0 f1 f3 f4 f6 f7 :=
  ⟨AddCommGrpCat.of B0, AddCommGrpCat.of B1, AddCommGrpCat.of B2, AddCommGrpCat.of B3,
    AddCommGrpCat.of B4, AddCommGrpCat.of B5, AddCommGrpCat.of B6, AddCommGrpCat.of B7,
    AddCommGrpCat.of BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7, e0, e1, e2, e3, e4, e5, e6, e7, e8, ε,
    h0, h1, h3, h4, h6, h7, i0, x1, x2, x3, x4, x5, x6, x7, s7⟩
end PositivityTheory.Lit1.PTN
