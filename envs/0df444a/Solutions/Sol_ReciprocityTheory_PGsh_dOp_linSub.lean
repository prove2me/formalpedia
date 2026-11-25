-- Prove2me | solution 1 for ReciprocityTheory.PGsh.dOp_linSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:21.466207+00:00
-- url     : https://prove2.me/submissions/5c9294cf-1620-4bca-8f53-0bbf5f03f4e7

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_pderiv_linSub

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
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {m : ℕ} (g : Matrix (Fin n) (Fin n) R) (r c : Fin m → Fin n)
    (q : MvPolynomial (Fin n × Fin n) R) :
    dOp r c (linSub g q) =
      ∑ τ : Fin m → Fin n, C (∏ t, g (τ t) (r t)) * linSub g (dOp τ c q) := by
  induction m with
  | zero => simp [dOp]
  | succ m ih =>
    have key : ∀ (r' c' : Fin (m + 1) → Fin n) (p : MvPolynomial (Fin n × Fin n) R),
        dOp r' c' p = pderiv (r' 0, c' 0) (dOp (fun i => r' i.succ) (fun i => c' i.succ) p) := by
      intro r' c' p
      simp only [dOp, List.ofFn_succ, List.prod_cons, Module.End.mul_apply, Derivation.coeFn_coe]
    have hce : ∀ x : Fin n × (Fin m → Fin n),
        (Fin.consEquiv fun _ => Fin n) x = Fin.cons x.1 x.2 := fun x => rfl
    rw [key, ih, map_sum, ← (Fin.consEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type]
    simp only [hce, key, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ, Derivation.leibniz,
      pderiv_C, smul_zero, smul_eq_mul, mul_zero, add_zero, pderiv_linSub, Finset.mul_sum, map_mul]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun τ _ => by ring)
end ReciprocityTheory.PGsh
