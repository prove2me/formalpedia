-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.pair_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:06.652545+00:00
-- url     : https://prove2.me/submissions/5f03f729-8c02-4bf2-9535-a79308002ea9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_sub


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution {q : PV ι A B} (hq : q ∈ pairAlg ι A B) : IsInv q := by
  intro u hu
  have hu' : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hle : pairAlg ι A B ≤ AlgHom.equalizer (sub u (u.map star)) (AlgHom.id ℂ (PV ι A B)) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show sub u (u.map star) _ = _
    apply MvPolynomial.funext
    intro z
    rw [eval_sub]
    simp only [map_sum, map_mul, eval_X, act, Sum.elim_inl, Sum.elim_inr, Matrix.map_apply, AlgHom.id_apply]
    have e : ∀ i, (∑ j, u i j * z (Sum.inl (j, a))) * (∑ l, star (u i l) * z (Sum.inr (l, b))) =
        ∑ j, ∑ l, (star (u i l) * u i j) * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) := by
      intro i
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have e2 : ∀ l, ∑ i, star (u i l) * u i j * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) =
        (star u * u) l j * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) := by
      intro l
      rw [Matrix.mul_apply, Finset.sum_mul]
      rfl
    simp_rw [e2, hu', Matrix.one_apply]
    simp
  exact hle hq
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
