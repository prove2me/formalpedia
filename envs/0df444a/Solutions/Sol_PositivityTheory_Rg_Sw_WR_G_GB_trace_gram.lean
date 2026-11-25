-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GB.trace_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:28.511924+00:00
-- url     : https://prove2.me/submissions/1e28a636-63ca-455d-ba57-83be9a7f2e5c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_HermTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_gramX_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GB
namespace PositivityTheory.Rg.Sw.WR.G.GB
theorem _root_.solution (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, ((sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j := by
  have L : (b * gramX ε x).trace =
      ∑ a, ∑ i, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    calc (∑ i, ∑ j, ∑ a, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)))
        = ∑ i, ∑ a, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [L]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring
end PositivityTheory.Rg.Sw.WR.G.GB
