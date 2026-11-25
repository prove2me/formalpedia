-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.foldr_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:58.331803+00:00
-- url     : https://prove2.me/submissions/853f5c3c-c8c1-442d-ba0e-8208eadf09fb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_TD_supp

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
theorem _root_.solution (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ) (M : ℕ),
    (∀ j, M ≤ j → c j = 0) → ∀ j, M + l.length ≤ j → (l.foldr (fun k c' => TD k (f k) c') c) j = 0
  | [], c, M, hM => by simpa using hM
  | a :: l, c, M, hM => by
      intro j hj
      simp only [List.foldr_cons]
      exact TD_supp (M := M + l.length) (solution f l c M hM) a (f a) j
        (by simp only [List.length_cons] at hj; omega)
end PositivityTheory.Rg.Sw.WR.K.GB.TW
