-- Prove2me | solution 1 for UpperTheory.Reformulated.B.UnitaryCharacterOfReals.char_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:02.200009+00:00
-- url     : https://prove2.me/submissions/005a5e63-efb2-4549-b37e-1b19cc73d108

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.UnitaryCharacterOfReals
theorem _root_.solution :
    ∀ (f : ℝ → ℂ),
    Continuous f →
      (∀ (s t : ℝ), f (s + t) = f s * f t) →
        (∀ (s : ℝ), ‖f s‖ = (1 : ℝ)) → ∃ (b : ℝ), ∀ (s : ℝ), f s = Complex.exp ((↑(b * s) : ℂ) * Complex.I) := by
  intro f hf hadd hn
  let F : C(ℝ, Circle) :=
    ⟨fun s => ⟨f s, mem_sphere_zero_iff_norm.2 (hn s)⟩, hf.subtype_mk _⟩
  have hF : ∀ s, (F s : ℂ) = f s := fun _ => rfl
  have hFadd : ∀ s t, F (s + t) = F s * F t := fun s t => by
    apply Circle.ext
    rw [Circle.coe_mul, hF, hF, hF, hadd]
  have hF0 : F 0 = 1 := by
    have h := hFadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have cov := Circle.isCoveringMap_exp
  obtain ⟨g, ⟨hg0, hg⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts F 0 0 (by rw [hF0]; exact Circle.exp_zero)
  have hg' : ∀ s, Circle.exp (g s) = F s := fun s => congrFun hg s
  have gadd : ∀ s t, g (s + t) = g s + g t := fun s t => by
    have h := cov.eq_of_comp_eq (g₁ := fun s : ℝ => g (s + t)) (g₂ := fun s : ℝ => g s + g t)
      (by fun_prop) (by fun_prop)
      (by
        funext s
        show Circle.exp (g (s + t)) = Circle.exp (g s + g t)
        rw [Circle.exp_add, hg', hg', hg', hFadd]) 0 (by simp [hg0])
    exact congrFun h s
  let G : ℝ →+ ℝ := AddMonoidHom.mk' g gadd
  refine ⟨g 1, fun s => ?_⟩
  have hs : g s = g 1 * s := by
    have h := map_real_smul G g.continuous s 1
    simp only [smul_eq_mul, mul_one] at h
    rw [mul_comm]
    exact h
  rw [← hs, ← hF, ← hg', Circle.coe_exp]
end UpperTheory.Reformulated.B.UnitaryCharacterOfReals
