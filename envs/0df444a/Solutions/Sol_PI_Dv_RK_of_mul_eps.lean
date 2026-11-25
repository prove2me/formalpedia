-- Prove2me | solution 1 for PI.Dv.RK.of_mul_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:06.540813+00:00
-- url     : https://prove2.me/submissions/c50b0c81-1aa8-4004-9cf1-667cfc0df944

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
namespace PI.Dv.RK
theorem _root_.solution (P : Pair K G) (h : P.H) :
    MonoidAlgebra.of K G (h : G) * eps P = ((P.chi h : Kˣ) : K) • eps P := by
  unfold eps
  rw [mul_smul_comm, smul_comm ((P.chi h : Kˣ) : K)]
  congr 1
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (h : G)) _ _ fun x => ?_
  by_cases hx : x ∈ P.H
  · have hhx : (Equiv.mulLeft (h : G)) x ∈ P.H := P.H.mul_mem h.2 hx
    rw [dif_pos hx, dif_pos hhx, mul_smul_comm, smul_smul, ← map_mul (MonoidAlgebra.of K G)]
    congr 1
    have e : P.chi ⟨(Equiv.mulLeft (h : G)) x, hhx⟩ = P.chi h * P.chi ⟨x, hx⟩ := by
      rw [← map_mul]; rfl
    rw [e]
    simp only [mul_inv_rev, Units.val_mul]
    rw [mul_left_comm, Units.mul_inv, mul_one]
  · have hhx : (Equiv.mulLeft (h : G)) x ∉ P.H := fun hm => hx (by
      have := P.H.mul_mem (P.H.inv_mem h.2) hm
      simpa using this)
    rw [dif_neg hx, dif_neg hhx, mul_zero, smul_zero]
end PI.Dv.RK
