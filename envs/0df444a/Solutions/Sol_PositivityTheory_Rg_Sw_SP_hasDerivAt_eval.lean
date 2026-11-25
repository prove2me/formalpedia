-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.hasDerivAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:42.734134+00:00
-- url     : https://prove2.me/submissions/80caaf7e-2055-4605-8cdd-1582f2c6f470

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (g : ℂ → ι → ℂ) (g' : ι → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) P)
      (∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k P) * g' k) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℂ) a
  | add p q hp hq =>
    have e1 : (fun t => MvPolynomial.eval (g t) (p + q)) =
        fun t => MvPolynomial.eval (g t) p + MvPolynomial.eval (g t) q := by
      funext t; rw [map_add]
    rw [e1]
    refine (hp.add hq).congr_deriv ?_
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p k0 hp =>
    have h := hp.mul (hg k0)
    have e1 : (fun t => MvPolynomial.eval (g t) (p * MvPolynomial.X k0)) =
        fun t => MvPolynomial.eval (g t) p * g t k0 := by
      funext t; rw [map_mul, MvPolynomial.eval_X]
    rw [e1]
    refine h.congr_deriv ?_
    symm
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X,
      add_mul, Finset.sum_add_distrib]
    have e : ∑ k, MvPolynomial.eval (g 0) p * MvPolynomial.eval (g 0) ((Pi.single k (1 : MvPolynomial ι ℂ) : ι → MvPolynomial ι ℂ) k0) * g' k =
        MvPolynomial.eval (g 0) p * g' k0 := by
      rw [Finset.sum_eq_single k0]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    rw [e, Finset.sum_mul]
    have e2 : ∑ k, g 0 k0 * MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k =
        ∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k * g 0 k0 :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e2]
    ring
end PositivityTheory.Rg.Sw.SP
