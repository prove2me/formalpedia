-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.sum_invE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:14.528337+00:00
-- url     : https://prove2.me/submissions/8227376f-84bc-4036-94bf-ec8af8e35c9a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT
theorem _root_.solution (f : Fin (NN ι A B) → ℂ) (g : ι → ℂ) :
    ∑ j, f j * (invE A B j).elim 0 g = ∑ i, f (emb i) * g i := by
  rw [Fin.sum_univ_add]
  have h2 : ∑ j : Fin (Fintype.card A + Fintype.card B), f (Fin.natAdd _ j) * (invE A B (Fin.natAdd _ j)).elim 0 g = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have : invE A B (Fin.natAdd (Fintype.card ι) j) = none := by
      simp [invE]
    rw [this]; simp
  rw [h2, add_zero]
  have h1 : ∀ j : Fin (Fintype.card ι), invE A B (Fin.castAdd _ j) = some ((Fintype.equivFin ι).symm j) := by
    intro j
    simp [invE]
  simp_rw [h1]
  simp only [Option.elim]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => f (emb i) * g i)).symm.trans
    (Finset.sum_congr rfl fun j _ => by simp [emb]) |>.symm
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
