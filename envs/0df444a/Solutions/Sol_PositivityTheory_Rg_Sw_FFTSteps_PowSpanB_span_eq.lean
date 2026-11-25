-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:23.701241+00:00
-- url     : https://prove2.me/submissions/5f43d3de-6f92-48d1-8f75-ce49b19ae150

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_add
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_single
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_pow_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_zero_mem_W
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_herm_decomp
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_core
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.FFTSteps
namespace PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)
private theorem list_prod_mul_span_prod_mem_S : ∀ l : List (PX m n), (∀ x ∈ l, x ∈ Submodule.span ℂ (W ε)) →
    ∀ q : List (PX m n), (∀ v ∈ q, v ∈ W ε) → q.prod * l.prod ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ q hq
    simpa using core ε q hq 0 (zero_mem_W ε) 0
  | cons x l ih =>
    intro hl q hq
    have hx : x ∈ Submodule.span ℂ (W ε) := hl x (by simp)
    have hl' : ∀ y ∈ l, y ∈ Submodule.span ℂ (W ε) := fun y hy => hl y (by simp [hy])
    clear hl
    rw [List.prod_cons]
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have := ih hl' (y :: q) (by
        intro v hv
        rcases List.mem_cons.mp hv with h | h
        · exact h ▸ hy
        · exact hq v h)
      rw [List.prod_cons] at this
      rw [← mul_assoc, mul_comm q.prod y]
      exact this
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_mul, mul_add]
      exact add_mem ha hb
    | smul z a _ ha =>
      rw [smul_mul_assoc, mul_smul_comm]
      exact (S ε).smul_mem z ha
end PowSpanB
end PositivityTheory.Rg.Sw.FFTSteps
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
theorem _root_.solution :
    (Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))).toSubmodule = S ε := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.mpr ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have := list_prod_mul_span_prod_mem_S ε l (by
      intro y hy
      obtain ⟨⟨a, b⟩, rfl⟩ := hl y hy
      obtain ⟨H1, H2, h1, h2, hb⟩ := herm_decomp (Matrix.single b a (1 : ℂ))
      have e : (Qp ε a b : PX m n) = lf ε H1 + Complex.I • lf ε H2 := by
        rw [← lf_single, hb, lf_add, lf_smul]
      show (Qp ε a b : PX m n) ∈ _
      rw [e]
      exact add_mem (Submodule.subset_span ⟨H1, h1, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨H2, h2, rfl⟩))) [] (by simp)
    simpa using this
  · refine Submodule.span_le.mpr ?_
    rintro R ⟨b, k, _, rfl⟩
    show _ ∈ Algebra.adjoin ℂ _
    refine Subalgebra.pow_mem _ (Subalgebra.sum_mem _ (fun i _ => Subalgebra.sum_mem _ (fun j _ => ?_))) k
    refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨(j, i), rfl⟩)
    rw [← MvPolynomial.algebraMap_eq]
    exact Subalgebra.algebraMap_mem _ _
end PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
