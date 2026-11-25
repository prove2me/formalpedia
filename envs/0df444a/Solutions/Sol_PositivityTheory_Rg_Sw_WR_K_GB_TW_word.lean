-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:39.448107+00:00
-- url     : https://prove2.me/submissions/8dc6865b-d503-442e-8d20-405ea9b26e41

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_step
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_foldr_smooth
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_foldr_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution (z : ℂ) (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ) (M : ℕ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) → (∀ j, M ≤ j → c j = 0) →
    l.foldr (fun k g => Dkl k (f k) g) (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + l.length), z ^ j * (l.foldr (fun k c' => TD k (f k) c') c) j y
  | [], c, M, _, _ => by simp
  | a :: l, c, M, hc, hM => by
      rw [List.foldr_cons, solution z f l c M hc hM, List.foldr_cons, List.length_cons, ← add_assoc]
      exact step z a (f a) _ (M + l.length) (foldr_smooth f l c hc) (foldr_supp f l c M hM)
end PositivityTheory.Rg.Sw.WR.K.GB.TW
