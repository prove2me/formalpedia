-- Prove2me | solution 1 for ReciprocityTheory.PGsh.cayMono_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:46.083213+00:00
-- url     : https://prove2.me/submissions/0599ab14-977f-4fbd-833c-949ac03cfd1e

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_leibniz_ofFn

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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (s : ℕ) :
    cayMono n ℤ σ (cayDet n ℤ ^ s) = ∑ φ : Fin n → Fin s, ∏ k, fibOp σ φ k (cayDet n ℤ) := by
  have h := leibniz_ofFn
    (fun i : Fin n => (pderiv (σ i, i) : Derivation ℤ (MvPolynomial (Fin n × Fin n) ℤ) _))
    (fun _ : Fin s => cayDet n ℤ)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  unfold cayMono fibOp
  rw [← List.ofFn_eq_map]
  exact h
end ReciprocityTheory.PGsh
