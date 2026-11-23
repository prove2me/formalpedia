-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:33.8393+00:00
-- url     : https://prove2.me/submissions/da756b0c-c3cd-4b9a-8f6b-95328ad288a2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero
theorem _root_.solution.{u_1, u_2} :
    ∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : AddCommGroup M] (ρ : Representation ℤ G M) {σ : G},
      (∀ (g : G), g ∈ Subgroup.zpowers σ) →
        ∀ {x : M}, (UpperTheory.Reformulated.B.CyclicSubtraction.cycSub ρ σ : M → M) x = (0 : M) → ∀ (g : G), ((ρ : G → M →ₗ[ℤ] M) g : M → M) x = x := by
  intro G M _ _ ρ σ hσ x hx g
  have h0 : ρ σ x - x = 0 := hx
  have h1 : ρ σ x = x := sub_eq_zero.mp h0
  let H : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by
            rw [inv_mul_cancel, map_one]
            rfl }
  have hle : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).mpr h1
  exact hle (hσ g)
end UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero
