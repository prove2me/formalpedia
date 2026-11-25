-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.foldr_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:51.444628+00:00
-- url     : https://prove2.me/submissions/0e06f677-3bc9-4d50-97e7-61f7c84c16d7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution {ρ : ℕ} {M : Type} [AddCommGroup M] [Module R M] (f : Fin ρ → Module.End R M)
    (l : List (Fin ρ)) : l.foldr (fun k g => f k ∘ₗ g) LinearMap.id = (l.map f).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, List.prod_cons, ih]; rfl
end PositivityTheory.Rg.Sw.SP.Mi
