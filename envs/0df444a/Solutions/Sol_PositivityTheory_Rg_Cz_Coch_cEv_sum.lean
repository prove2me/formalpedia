-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.Coch.cEv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:30:27.010003+00:00
-- url     : https://prove2.me/submissions/67055493-7a9f-4796-a0c2-a3214ce3a375

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.Coch
variable {H V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.Cz.Coch
theorem _root_.solution {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℤ) (F : ι → (Fin N → H) → V) (A B : Fin N → H) :
    cEv (fun v => ∑ i ∈ s, c i • F i v) A B = ∑ i ∈ s, c i • cEv (F i) A B := by
  unfold cEv
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun S _ => ?_
  exact smul_comm _ _ _
end PositivityTheory.Rg.Cz.Coch
