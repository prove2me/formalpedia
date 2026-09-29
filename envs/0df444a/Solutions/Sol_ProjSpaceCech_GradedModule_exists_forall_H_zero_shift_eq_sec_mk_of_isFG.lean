-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3e8ee5bf-ec91-53a1-9b51-e4fd3f430371

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

import Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
import Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk
import Theorems.Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG
import Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG

set_option autoImplicit false

universe u

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (D : ProjSpaceCech.GradedModule R n) (hD : ProjSpaceCech.GradedModule.IsFG D) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift D d) 0,
        ∃ m : D.M, m ∈ D.grade d ∧
          ∃ hm : m ∈ (ProjSpaceCech.GradedModule.shift D d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
            ∀ s : ProjSpaceCech.Idx n 0,
              (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift D d) 0)) from c).1 s =
                ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift D d) (ProjSpaceCech.Idx.img n s)
                  ⟨0, fun _ _ => rfl, m, hm⟩ := by
  obtain ⟨σ⟩ := hD
  obtain ⟨dK, hdK⟩ := ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG σ.ker
    (ProjSpaceCech.GradedModule.Presentation.ker_isFG σ)
  obtain ⟨d₁, hd₁⟩ := ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk R n σ.d₀
  refine ⟨max dK d₁, fun d hd c => ?_⟩
  exact ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one σ d
    (hdK d ((le_max_left _ _).trans hd) 1 le_rfl) (hd₁ d ((le_max_right _ _).trans hd)) c

end S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG (solution)
