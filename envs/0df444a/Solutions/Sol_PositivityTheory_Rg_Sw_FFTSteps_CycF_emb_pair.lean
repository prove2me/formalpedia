-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.emb_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:03.28216+00:00
-- url     : https://prove2.me/submissions/5ef9f845-82a8-4658-920b-2b942719e0d6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (β : Bool) (a b : Fin n) :
    emb ε β (∑ i : Rw ε β, (X (Sum.inl (i, a)) : PV (Rw ε β) (Fin n) (Fin n)) * X (Sum.inr (i, b))) = Qb ε β b a := by
  simp only [map_sum, map_mul, emb, rename_X, jv, Sum.elim_inl, Sum.elim_inr, Qb]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Fin m => ε x = β)) (p := fun x => ε x = β) (by simp)]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
end PositivityTheory.Rg.Sw.FFTSteps.CycF
