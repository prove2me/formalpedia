-- Prove2me | solution 1 for ReciprocityTheory.PGsh.sum_prod_factorial_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:13.367538+00:00
-- url     : https://prove2.me/submissions/ff29520d-4721-455b-a68e-7bcac29aeddd

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_card_fibre_cons
import Theorems.Thm_ReciprocityTheory_PGsh_sum_prod_factorial_add_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (s : ℕ) : ∀ m : ℕ,
    ∑ φ : Fin m → Fin s, ∏ k, (#{a | φ a = k}).factorial = ∏ j ∈ range m, (s + j)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, ← solution s m, Finset.sum_mul,
      ← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin s)
        (fun p => ∏ k, (#{a | (Fin.cons p.1 p.2 : Fin (m + 1) → Fin s) a = k}).factorial) _
        (fun p => rfl), Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [card_fibre_cons]
    have hsum : ∑ k, #{a | φ a = k} = m := by
      have := Finset.card_eq_sum_card_fiberwise (f := φ) (s := univ) (t := univ)
        (fun x _ => mem_univ _)
      simpa using this.symm
    rw [sum_prod_factorial_add_ite, hsum, add_comm m s]
end ReciprocityTheory.PGsh
