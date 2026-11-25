-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.foldr_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:21.576018+00:00
-- url     : https://prove2.me/submissions/dc3fcd0c-9658-42a9-8f9c-3b6d97c269ab

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_phi

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
open PositivityTheory.Rg.Sw.SP.Mi
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ))
    (f : Pm (Polynomial ℂ) ρ) :
    (L.foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id) (phi b I J f) =
      (-(cMn s b)) ^ L.length • phi b I J ((L.foldr (fun k g => opE (alMn m b) k (σ k) ∘ₗ g) LinearMap.id) f) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, ih, map_smul, opH_phi, smul_smul, List.length_cons, pow_succ]
end PositivityTheory.Rg.Sw.SP
