-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.psi_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:56.878048+00:00
-- url     : https://prove2.me/submissions/de5b3ed6-c1ab-4af4-bfac-29d6f746849b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution (p : Sym m n) (hp : p ≠ 0) : 0 < (psi p p).re := by
  unfold psi
  rw [Finset.union_self, Complex.re_sum]
  have hterm : ∀ u, (star (p.coeff u) * p.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)).re =
      Complex.normSq (p.coeff u) * ∏ k ∈ u.support, ((u k).factorial : ℝ) := by
    intro u
    have : star (p.coeff u) * p.coeff u = (Complex.normSq (p.coeff u) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this, show (∏ k ∈ u.support, ((u k).factorial : ℂ)) = ((∏ k ∈ u.support, ((u k).factorial : ℝ) : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hp)
  refine Finset.sum_pos' (fun v _ => mul_nonneg (Complex.normSq_nonneg _)
    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)) ⟨u, hu, mul_pos ?_ (Finset.prod_pos fun _ _ => by
      exact_mod_cast Nat.factorial_pos _)⟩
  exact Complex.normSq_pos.2 (mem_support_iff.1 hu)
end PositivityTheory.Rg.Sw.LC.CoreD
