-- Prove2me | solution 1 for Rep.finrank_invariants_res_dualTwist_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fab4f0f7-7b46-5ba9-b7f6-d84e3c7d479d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finrank_invariants_res_dualTwist_eq

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 3200000 in
theorem solution
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (Rep.res r (M.dualTwist (cycloChar p))).ρ.invariants
      = finrank (ZMod p) ((Rep.res r M).dualTwist ((cycloChar p).comp r)).ρ.invariants := by

  have key : ∀ (h : H) (f : Module.Dual (ZMod p) M),
      (Rep.res r (M.dualTwist (cycloChar p))).ρ h f = ((Rep.res r M).dualTwist ((cycloChar p).comp r)).ρ h f := by
    intro h f
    change (M.dualTwist (cycloChar p)).ρ (r h) f = _
    rw [Rep.dualTwist_ρ_apply, Rep.dualTwist_ρ_apply]
    show ((cycloChar p) (r h) : ZMod p) • (f ∘ₗ M.ρ ((r h)⁻¹)) = ((cycloChar p) (r h) : ZMod p) • (f ∘ₗ M.ρ (r (h⁻¹)))
    rw [map_inv r h]
  refine LinearEquiv.finrank_eq
    { toFun := fun f => ⟨f.1, fun h => by rw [← key]; exact f.2 h⟩
      invFun := fun f => ⟨f.1, fun h => by rw [key]; exact f.2 h⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end S_Rep_finrank_invariants_res_dualTwist_eq
end P2MW
export P2MW.S_Rep_finrank_invariants_res_dualTwist_eq (solution)
