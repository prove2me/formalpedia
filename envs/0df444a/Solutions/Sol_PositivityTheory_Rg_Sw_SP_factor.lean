-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:18.621039+00:00
-- url     : https://prove2.me/submissions/24913ad7-0d57-419a-858c-9aeca0fe3a6d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DifferentiableClassFunctionParam
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_differentiable_class_function_param

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (hE : Ext) (hCh : Chain) (hBr : Bridge) {s : ℂ} (hs : s = 1 ∨ s = -1) (m N r : ℕ)
    (hdiv : DivZ r ((cayF (n := n) s m)^[N] 1)) (y : E n) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, (Delta^[N] (cls s z m 0 1)) y = z ^ r * q z := by
  obtain ⟨hO, hherm, han⟩ := hE n s hs
  set P : Fm n := (cayF (n := n) s m)^[N] 1 with hP
  choose d hd using hdiv
  set v : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2
    else (1 - (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2 with hv
  refine ⟨fun z => clsC s z m 0 1 (herm y) * ∑ e ∈ P.support, (d e).eval z * ∏ i ∈ e.support, v i ^ e i, ?_, ?_⟩
  · refine (differentiable_class_function_param s m 0 1 _).mul ?_
    exact Differentiable.fun_sum fun e _ => (Polynomial.differentiable _).mul (differentiable_const _)
  · intro z
    have hcls : cls s z m 0 1 = fun y : E n => clsC s z m 0 1 (herm y) := funext fun y => ((han z m 0 1).2 y).symm
    rw [hcls, hCh n (OmS s) (clsC s z m 0 1) hO hherm (han z m 0 1).1 N y, hBr n s hs m N z (herm y) (hherm y)]
    rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq]
    simp only [← hv, ← hP, Polynomial.coe_evalRingHom]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hd e, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring
end PositivityTheory.Rg.Sw.SP
