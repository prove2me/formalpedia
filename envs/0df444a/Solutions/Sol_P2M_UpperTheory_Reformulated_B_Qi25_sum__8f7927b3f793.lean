-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:36.932737+00:00
-- url     : https://prove2.me/submissions/0cb472f4-94a2-4cc6-aafb-b1cb07697ea3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qi25.eval_det {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) :
    MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g)
        (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det =
      (↑g : Matrix (Fin N) (Fin N) ℂ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [UpperTheory.Reformulated.B.Qi25.ent]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qi25
theorem _root_.solution.{u_1} :
    ∀ {N : ℕ} {ι : Type u_1} (s : Finset ι) {F : ι → UpperTheory.Reformulated.B.Qi25.UG N → ℂ},
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi25.IsPD (F i)) → UpperTheory.Reformulated.B.Qi25.IsPD fun (g : UpperTheory.Reformulated.B.Qi25.UG N) ↦ ∑ i ∈ s, F i g := by
  intro N ι s F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, 0, fun g ↦ by simp⟩
  | insert a s ha ih =>
    intro h
    obtain ⟨k, P, hP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨l, Q, hQ⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨k + l,
      P * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ l
        + Q * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ k,
      fun g ↦ ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, UpperTheory.Reformulated.B.Qi25.eval_det, ← hP g, ← hQ g]
    simp only [Finset.sum_insert ha]
    ring
end UpperTheory.Reformulated.B.Qi25
