-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.list_prod_eq_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:04.706746+00:00
-- url     : https://prove2.me/submissions/0d65b38d-3997-48c3-830c-2dee2292abaf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {ρ : ℕ} (f : Fin ρ → Module.End ℂ (Fm n)) (L : List (Fin ρ)) :
    (L.map f).prod = L.foldr (fun k g => f k ∘ₗ g) LinearMap.id := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Module.End.mul_eq_comp]; rfl
end PositivityTheory.Rg.Sw.SP
