-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.shaHalf_of_perfectPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:42.829977+00:00
-- url     : https://prove2.me/submissions/87a4ec3a-845b-447c-b5a0-9face0aa047b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualInjectiveEquivStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsShaHalf
import Theorems.Thm_GlobalTheory_T_finite_dual_injective_equiv


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
theorem _root_.solution {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectPair (R := ZMod n) X Y) :
    Finite Y ∧ Finite X ∧ Nonempty (X ≃ₗ[ZMod n] Module.Dual (ZMod n) Y) ∧
      Nat.card Y = Nat.card X := by
  obtain ⟨hX, hY, P, hP, hP'⟩ := h
  have key := GlobalTheory.T.finite_dual_injective_equiv n Y X ⟨P, hP.1⟩ ⟨P.flip, hP'.1⟩
  exact ⟨hY, hX, key.1, key.2⟩
end PositivityTheory.Lit1.PTN
