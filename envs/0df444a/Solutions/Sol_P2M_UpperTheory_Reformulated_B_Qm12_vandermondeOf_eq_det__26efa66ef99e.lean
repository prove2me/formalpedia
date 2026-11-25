-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qm12_vandermondeOf_eq_det__26efa66ef99e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:23.265238+00:00
-- url     : https://prove2.me/submissions/9dbb7f66-dff7-40e3-bd9e-e7666565e62d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qm12.vandermondeOf_eq_det
theorem _root_.solution.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (v : Fin m → R),
      UpperTheory.Reformulated.B.Qm12.vandermondeOf v =
        ((Matrix.of : (Fin m → Fin m → R) → Matrix (Fin m) (Fin m) R) fun (i j : Fin m) ↦
            v i ^ (m - (1 : ℕ) - (↑j : ℕ))).det := by
  intro m R _ v
  have hM : ((Matrix.of : (Fin m → Fin m → R) → Matrix (Fin m) (Fin m) R) fun (i j : Fin m) ↦
      v i ^ (m - (1 : ℕ) - (↑j : ℕ))) = Matrix.projVandermonde (fun _ ↦ (1 : R)) v := by
    ext i j
    rw [Matrix.of_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev,
      Nat.sub_sub, Nat.add_comm]
  rw [hM, Matrix.det_projVandermonde]
  unfold UpperTheory.Reformulated.B.Qm12.vandermondeOf
  refine Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr ?_ fun j _ ↦ ?_
  · ext j
    simp
  · rw [one_mul, one_mul]
end UpperTheory.Reformulated.B.Qm12.vandermondeOf_eq_det
