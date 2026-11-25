-- Prove2me | solution 1 for PI.WickFormula.lprod_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:06.119515+00:00
-- url     : https://prove2.me/submissions/7c2dba23-308c-4b9b-a62f-47347ad268ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
import Theorems.Thm_PI_WickFormula_add_pow_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {AA : Type} [Ring AA]
namespace PI.WickFormula
theorem _root_.solution {M : Type} [AddCommGroup M] [Module AA M] {n : ℕ} (x y : Fin n → AA)
    (e : Fin n → ℕ) (v : M) (hxy : ∀ i j, Commute (y i) (x j)) (hy : ∀ i, y i • v = 0) :
    lprod (x + y) e • v = lprod x e • v := by
  induction n with
  | zero => simp [lprod]
  | succ n ih =>
    have key : ∀ (c : Fin (n + 1) → AA), lprod c e = c 0 ^ e 0 * lprod (fun i => c i.succ) (fun i => e i.succ) := by
      intro c; simp [lprod, List.ofFn_succ]
    have ih' : lprod (fun i => (x + y) i.succ) (fun i => e i.succ) • v =
        lprod (fun i => x i.succ) (fun i => e i.succ) • v :=
      ih (fun i => x i.succ) (fun i => y i.succ) (fun i => e i.succ) (fun i j => hxy _ _) (fun i => hy _)
    rw [key, key, mul_smul, mul_smul, ih', Pi.add_apply]
    apply add_pow_smul _ _ _ (hxy 0 0)
    have hcm : Commute (y 0) (lprod (fun i => x i.succ) (fun i => e i.succ)) := by
      unfold lprod
      apply Commute.list_prod_right
      intro z hz
      rw [List.mem_ofFn] at hz
      obtain ⟨i, rfl⟩ := hz
      exact (hxy 0 i.succ).pow_right _
    rw [← mul_smul, hcm.eq, mul_smul, hy, smul_zero]
end PI.WickFormula
