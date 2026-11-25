-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.foldr_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:37.082256+00:00
-- url     : https://prove2.me/submissions/83ffb2a2-f45b-4d03-a43c-453f1d5eeabb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_SP_Mi_opE_C_mul__198277c1a297

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R] {ρ : ℕ}
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (α : R) (r : R) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) (C r * g) =
      C r * (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_C_mul']
end PositivityTheory.Rg.Sw.SP.Mi
