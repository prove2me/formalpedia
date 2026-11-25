-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.detE_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:15.034412+00:00
-- url     : https://prove2.me/submissions/a2b990f6-3898-407b-bb85-0b94abc9b200

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_foldr_eq_prod


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
theorem _root_.solution (α : R) (ρ : ℕ) :
    detE α = ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : R) •
      ((List.finRange ρ).map (fun k => opE α k (σ k))).prod := by
  unfold detE
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [foldr_eq_prod (fun k => opE α k (σ k))]
end PositivityTheory.Rg.Sw.SP.Mi
