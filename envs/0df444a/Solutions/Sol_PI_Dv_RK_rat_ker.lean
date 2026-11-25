-- Prove2me | solution 1 for PI.Dv.RK.rat_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:47.583532+00:00
-- url     : https://prove2.me/submissions/d94b1afa-b9dc-4a0d-8450-290402e934c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
import Theorems.Thm_PI_Dv_RK_L_j
import Theorems.Thm_PI_Dv_RK_L_mul
import Theorems.Thm_PI_Dv_RK_L_eG
import Theorems.Thm_PI_Dv_RK_L_zero
import Theorems.Thm_PI_Dv_RK_L_add
import Theorems.Thm_PI_Dv_RK_L_neg
import Theorems.Thm_PI_Dv_RK_L_ker
import Theorems.Thm_PI_Dv_RK_L_eps_mem

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
variable (M : GMap K σ G T EE ρE)
namespace PI.Dv.RK
theorem _root_.solution (P0 : Pair K G)
    (hF : eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P0 * b})
    (hR : M.IsRat (LinearMap.ker M.io ⊓ eigP σ P0 M.rho)) : M.IsRat (LinearMap.ker M.io) := by
  unfold GMap.IsRat at hR ⊢
  have hRN : Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io}) ≤ LinearMap.ker M.io :=
    Submodule.span_le.mpr (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have hLa : ∀ a : MonoidAlgebra K G, ∀ u ∈ LinearMap.ker M.io ⊓ eigP σ P0 M.rho,
      L M a u ∈ Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io}) := by
    intro a u hu
    rw [← hR] at hu
    have hle : Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io ⊓ eigP σ P0 M.rho}) ≤
        (Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io})).comap (L M a) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, L_j]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      show M.j _ ∈ LinearMap.ker M.io
      rw [← L_j]
      exact L_ker M a hx.1
    exact hle hu
  have hZ : ∀ v ∈ LinearMap.ker M.io,
      L M (eG T) v ∈ Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io}) := by
    refine AddSubgroup.closure_induction (p := fun z _ => ∀ v ∈ LinearMap.ker M.io,
      L M z v ∈ Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io})) ?_ ?_ ?_ ?_ hF
    · rintro z ⟨a, b, rfl⟩ v hv
      rw [L_mul, L_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact hLa a _ ⟨L_ker M _ (L_ker M b hv), L_eps_mem M P0 _⟩
    · intro v _
      rw [L_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy v hv
      rw [L_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hx v hv) (hy v hv)
    · intro x _ hx v hv
      rw [L_neg, LinearMap.neg_apply]
      exact Submodule.neg_mem _ (hx v hv)
  refine le_antisymm hRN fun v hv => ?_
  have := hZ v hv
  rwa [L_eG, Module.End.one_apply] at this
end PI.Dv.RK
