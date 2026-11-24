-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qn10_sum_r_mul_ne__f17edb41f5d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:42.896283+00:00
-- url     : https://prove2.me/submissions/a595eff5-a72f-4acd-b099-1f1e6a5b912c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne
theorem _root_.solution.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A]
    {n : ℕ} (f : MvPolynomial (Fin (n + (1 : ℕ))) A) (v w : Fin (n + (1 : ℕ)) →₀ ℕ),
    (∀ (i : Fin (n + (1 : ℕ))), (v : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
      (∀ (i : Fin (n + (1 : ℕ))), (w : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
        v ≠ w →
          ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (v : Fin (n + (1 : ℕ)) → ℕ) x ≠
            ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (w : Fin (n + (1 : ℕ)) → ℕ) x := by
  intro A _ _ n f v w hv hw hne h
  apply hne
  have key : finFunctionFinEquiv (fun i => (⟨v i, hv i⟩ : Fin (2 + f.totalDegree))) =
      finFunctionFinEquiv (fun i => (⟨w i, hw i⟩ : Fin (2 + f.totalDegree))) := by
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    simpa only [mul_comm] using h
  have hfun := finFunctionFinEquiv.injective key
  ext i
  exact congrArg Fin.val (congrFun hfun i)
end UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne
