-- Prove2me | solution 1 for ZeroFreeRegions.zeta_zero_free_region_littlewood
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T23:56:14.185255+00:00
-- url     : https://prove2.me/submissions/57258191-4fa8-4a2a-96a9-b5bb18fa4a47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Theorems.Thm_GRH_grh_critical_line_iff

namespace HubZ

/-- `ζ(s) ≠ 0` for `Re s > 1/2`, from the hub (critical line for primitive characters) and the proved equivalence. -/
theorem zeta_ne_zero_of_half_lt {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · have hs1 : s ≠ 1 := fun h => by simp [h] at h1
    have h := GRH.grh_critical_line_iff.mp AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive
      1 (1 : DirichletCharacter ℂ 1) s (by exact_mod_cast hs) (fun h => hs1 h.2)
    rwa [DirichletCharacter.LFunction_modOne_eq] at h

end HubZ

theorem solution :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c * (Real.log (Real.log |ρ.im|) / Real.log |ρ.im|) := by
  refine ⟨1 / 2, 3, by norm_num, le_refl _, fun ρ hz hT => ?_⟩
  have hre : ρ.re ≤ 1 / 2 := by
    by_contra h
    exact HubZ.zeta_ne_zero_of_half_lt (by linarith) hz
  have hy : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
  have hratio : Real.log (Real.log |ρ.im|) / Real.log |ρ.im| ≤ 1 := by
    rw [div_le_one hy]
    have := Real.log_le_sub_one_of_pos hy
    linarith
  nlinarith
