-- Prove2me | solution 1 for Submodule.finrank_pi_univ_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7ad7284a-325f-5a46-b89d-a98eeaf5f4d4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_finrank_pi_univ_eq_sum

open Module

namespace Submodule p2m_export "Submodule" "pi ext mem_pi" end Submodule
p2m_open_scoped "Submodule" in
theorem Submodule.finrank_pi_univ_eq_sum
    {k : Type*} [Field k] {ι : Type*} [Fintype ι] {Φ : ι → Type*}
    [∀ v, AddCommGroup (Φ v)] [∀ v, Module k (Φ v)]
    (L : ∀ v, Submodule k (Φ v)) [∀ v, FiniteDimensional k (L v)] :
    finrank k (Submodule.pi Set.univ L) = ∑ v, finrank k (L v) := by
  set φ : (∀ v, L v) →ₗ[k] (∀ v, Φ v) :=
    LinearMap.pi (fun v => (L v).subtype ∘ₗ LinearMap.proj v) with hφ
  have happly : ∀ (x : ∀ v, L v) (v : ι), φ x v = (x v : Φ v) := fun x v => rfl
  have hinj : Function.Injective φ := fun x y hxy => by
    funext v
    exact Subtype.ext (by rw [← happly x v, ← happly y v, hxy])
  have hrange : LinearMap.range φ = Submodule.pi Set.univ L := by
    ext y
    simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨x, rfl⟩ v
      rw [happly]
      exact (x v).2
    · intro hy
      exact ⟨fun v => ⟨y v, hy v⟩, by funext v; rw [happly]⟩
  calc finrank k (Submodule.pi Set.univ L)
      = finrank k (LinearMap.range φ) := by rw [hrange]
    _ = finrank k (∀ v, L v) := ((LinearEquiv.ofInjective φ hinj).finrank_eq).symm
    _ = ∑ v, finrank k (L v) := Module.finrank_pi_fintype k

theorem solution
    {k : Type*} [Field k] {ι : Type*} [Fintype ι] {Φ : ι → Type*}
    [∀ v, AddCommGroup (Φ v)] [∀ v, Module k (Φ v)]
    (L : ∀ v, Submodule k (Φ v)) [∀ v, FiniteDimensional k (L v)] :
    finrank k (Submodule.pi Set.univ L) = ∑ v, finrank k (L v) :=
  Submodule.finrank_pi_univ_eq_sum L

end S_Submodule_finrank_pi_univ_eq_sum
end P2MW
export P2MW.S_Submodule_finrank_pi_univ_eq_sum (solution)
