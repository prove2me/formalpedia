-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.Aop_mul_mAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:35.54783+00:00
-- url     : https://prove2.me/submissions/5a97003c-7d69-4463-ae03-4f165c29c228

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_prod_split
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop K * mAt p A : Module.End ℂ (TV n M P)) = Aop (Function.update K p (K p * A)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, Aop_apply, Aop_apply]
  simp_rw [mAt_apply, Finset.smul_sum, smul_smul]
  let φ : (P → Fin n) × Fin n → (P → Fin n) × Fin n := fun x => (Function.update x.1 p x.2, x.1 p)
  have hφ : Function.Involutive φ := fun x => by
    simp only [φ, Function.update_idem, Function.update_self, Function.update_eq_self]
  let H : (P → Fin n) × Fin n → M := fun x =>
    ((∏ q, K q (I q) (Function.update x.1 p x.2 q)) * A x.2 (x.1 p)) • f x.1
  calc ∑ J : P → Fin n, ∑ j, ((∏ q, K q (I q) (J q)) * A (J p) j) • f (Function.update J p j)
      = ∑ x : (P → Fin n) × Fin n, H (φ x) := by
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [H, φ, Function.update_idem, Function.update_self, Function.update_eq_self]
    _ = ∑ x : (P → Fin n) × Fin n, H x := Equiv.sum_comp (hφ.toPerm φ) H
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [H]
        rw [← Finset.sum_smul]
        congr 1
        rw [prod_split p (fun q => Function.update K p (K p * A) q (I q) (J q))]
        simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [prod_split p (fun q => K q (I q) (Function.update J p i q))]
        simp only [Function.update_self]
        have hr : ∏ q ∈ Finset.univ.erase p, K q (I q) (Function.update J p i q) =
            ∏ q ∈ Finset.univ.erase p, Function.update K p (K p * A) q (I q) (J q) :=
          Finset.prod_congr rfl fun q hq => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]
        rw [hr]
        ring
end PositivityTheory.Rg.Cz.TGK
