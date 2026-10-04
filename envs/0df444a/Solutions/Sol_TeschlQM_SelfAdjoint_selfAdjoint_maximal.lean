-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.selfAdjoint_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:59:07.030652+00:00
-- url     : https://prove2.me/submissions/48b8d2e7-025f-4610-8231-1f175a0bb74f

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric

set_option autoImplicit false

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B) (hAB : A ≤ B) :
    B = A := by
  have hd : Dense (A.domain : Set H) := hA.dense_domain
  have hfa : A.IsFormalAdjoint B := by
    intro x y
    have hx : (x : H) ∈ B.domain := hAB.1 x.2
    have hxe : A x = B ⟨x, hx⟩ := hAB.2 rfl
    rw [hxe]
    exact (hB.2 ⟨x, hx⟩ y).symm
  have h1 : B ≤ LinearPMap.adjoint A := hfa.le_adjoint hd
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h1
  exact le_antisymm h1 hAB
