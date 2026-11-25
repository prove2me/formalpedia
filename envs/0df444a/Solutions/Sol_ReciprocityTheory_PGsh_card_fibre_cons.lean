-- Prove2me | solution 1 for ReciprocityTheory.PGsh.card_fibre_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:04:38.002772+00:00
-- url     : https://prove2.me/submissions/b3f18a26-ea73-463a-afc8-c8f7db99c7e8

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

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
theorem _root_.solution {s m : ℕ} (k₀ : Fin s) (φ : Fin m → Fin s) (k : Fin s) :
    #{a | (Fin.cons k₀ φ : Fin (m + 1) → Fin s) a = k} = #{a | φ a = k} + if k₀ = k then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring
end ReciprocityTheory.PGsh
