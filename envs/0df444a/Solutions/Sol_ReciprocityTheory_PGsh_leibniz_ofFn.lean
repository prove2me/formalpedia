-- Prove2me | solution 1 for ReciprocityTheory.PGsh.leibniz_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:53:06.780701+00:00
-- url     : https://prove2.me/submissions/1192027c-f704-424b-9a9d-cfa47accdbe1

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_deriv_finsetProd

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
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {m s : ℕ} (ds : Fin m → Derivation R A A) (P : Fin s → A) :
    (List.ofFn fun i => (ds i : A →ₗ[R] A)).prod (∏ k, P k) =
      ∑ φ : Fin m → Fin s,
        ∏ k, (List.ofFn fun i => if φ i = k then (ds i : A →ₗ[R] A) else 1).prod (P k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hce : ∀ x : Fin s × (Fin m → Fin s),
        (Fin.consEquiv fun _ => Fin s) x = Fin.cons x.1 x.2 := fun x => rfl
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, ih (fun i => ds i.succ), map_sum,
      ← (Fin.consEquiv fun _ => Fin s).sum_comp, Fintype.sum_prod_type]
    simp only [Derivation.coeFn_coe, deriv_finsetProd, hce, List.ofFn_succ, Fin.cons_zero,
      Fin.cons_succ, List.prod_cons, Module.End.mul_apply]
    refine Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k₀ _ => Finset.sum_congr rfl fun φ _ =>
        Finset.prod_congr rfl fun k _ => ?_)
    by_cases h : k = k₀
    · subst h; simp
    · simp [h, Ne.symm h]
end ReciprocityTheory.PGsh
