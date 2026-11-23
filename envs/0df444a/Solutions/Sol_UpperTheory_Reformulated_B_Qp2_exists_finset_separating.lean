-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qp2.exists_finset_separating
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:29.506136+00:00
-- url     : https://prove2.me/submissions/590f3187-aaf8-4ed1-be09-21d9125c7f12

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsFinsetSeparating
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qp2.aux {X : Type} (n : ℕ) :
    ∀ (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V], Module.finrank ℂ V = n →
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hn
    by_cases hV : ∀ v ∈ V, v = 0
    · exact ⟨∅, fun v hv _ => hV v hv⟩
    · obtain ⟨w, hw⟩ := not_forall.mp hV
      obtain ⟨hwV, hw0⟩ := Classical.not_imp.mp hw
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hw0
      let U : Submodule ℂ (X → ℂ) := V ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)
      have hle : U ≤ V := inf_le_left
      have hlt : U < V := by
        refine lt_of_le_of_ne hle ?_
        intro h
        have hwU : w ∈ U := h ▸ hwV
        exact hx (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwU).2)
      haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hle
      have hr : Module.finrank ℂ U < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT⟩ := ih _ hr U rfl
      refine ⟨insert x T, fun v hv h => hT v ?_ fun y hy => h y (Finset.mem_insert_of_mem hy)⟩
      exact Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr (h x (Finset.mem_insert_self x T))⟩
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qp2
theorem _root_.solution :
    ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V],
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  intro X V _
  exact UpperTheory.Reformulated.B.Qp2.aux _ V rfl
end UpperTheory.Reformulated.B.Qp2
