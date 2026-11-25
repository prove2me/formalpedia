-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.Tf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:50.317314+00:00
-- url     : https://prove2.me/submissions/b1a02006-29d0-4224-a8f8-71d2b6a1ef78

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_sum_invE
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_res__ae91c244e0c8

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
theorem _root_.solution (hS : Stable) (hA : Avg) (q : PV ι A B) : Tf hA q ∈ pairAlg ι A B := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  have hP := hS (Fin (NN ι A B)) A B (by simp only [Fintype.card_fin, NN]; omega) (by simp only [Fintype.card_fin, NN]; omega) _ hs.1
  have hle : Subalgebra.map (res (ι := ι) (A := A) (B := B)) (pairAlg (Fin (NN ι A B)) A B) ≤ pairAlg ι A B := by
    rw [pairAlg, AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨(a, b), ?_⟩
    apply MvPolynomial.funext
    intro z
    simp only [res, map_sum, map_mul, aeval_X, eval_resφ, Sum.elim_inl, Sum.elim_inr]
    rw [sum_invE (fun j => (invE A B j).elim 0 fun i => z (Sum.inl (i, a))) (fun i => z (Sum.inr (i, b)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : invE A B (emb (A := A) (B := B) i) = some i := by simp [invE, emb]
    simp [this]
  exact hle ⟨_, hP, rfl⟩
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
