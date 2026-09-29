-- Prove2me | solution 1 for QuaternionAlgebra.isOrder_toIntSubmodule_range_comp_includeRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/86b4ab60-f8f2-5969-b979-b8b9c98b19b6

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

namespace A1ix

theorem includeRight_injective (O : Type*) [Ring O] [Module.Free ℤ O] :
    Function.Injective (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) := by
  have h1 : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor O) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun x y hxy => by
      have : ((x : ℤ) : ℚ) = ((y : ℤ) : ℚ) := hxy
      exact_mod_cast this)
  have h2 : Function.Injective (TensorProduct.lid ℤ O).symm := (TensorProduct.lid ℤ O).symm.injective
  have heq : ∀ o : O, (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) o =
      ((Algebra.linearMap ℤ ℚ).rTensor O) ((TensorProduct.lid ℤ O).symm o) := fun o => by
    simp [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul]
  intro x y hxy
  rw [heq, heq] at hxy
  exact h2 (h1 hxy)

theorem span_range_includeRight (O : Type*) [Ring O] :
    Submodule.span ℚ (Set.range (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O)) = ⊤ := by
  refine top_unique fun x _ => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul q o =>
    have : q ⊗ₜ[ℤ] o = q • ((Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) o) := by
      rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨o, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

end A1ix

open A1ix in
theorem solution
    (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    {a b : ℚ} (e : ℚ ⊗[ℤ] O ≃ₐ[ℚ] ℍ[ℚ, a, b]) :
    Function.Injective
        ((e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
          (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom) ∧
      QuaternionAlgebra.IsOrder (AddSubgroup.toIntSubmodule
        ((e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
          (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom).range.toAddSubgroup) := by
  classical
  set θ : O →+* ℍ[ℚ, a, b] := (e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
      (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom with hθ
  have hθapp : ∀ o, θ o = e ((Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) o) := fun _ => rfl
  have hinj : Function.Injective θ := fun x y hxy => by
    rw [hθapp, hθapp] at hxy
    exact includeRight_injective O (e.injective hxy)
  refine ⟨hinj, ?_⟩
  set Λ : Submodule ℤ ℍ[ℚ, a, b] := AddSubgroup.toIntSubmodule θ.range.toAddSubgroup with hΛ
  have hmemΛ : ∀ x, x ∈ Λ ↔ x ∈ Set.range θ := fun x => by
    rw [hΛ]; exact ⟨fun ⟨o, ho⟩ => ⟨o, ho⟩, fun ⟨o, ho⟩ => ⟨o, ho⟩⟩

  have hΛmap : Λ = Submodule.map (θ.toIntLinearMap) ⊤ := by
    ext x
    rw [hmemΛ, Submodule.map_top, LinearMap.mem_range]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hmemΛ 1).mpr ⟨1, map_one θ⟩
  · intro x y hx hy
    obtain ⟨u, rfl⟩ := (hmemΛ x).mp hx
    obtain ⟨w, rfl⟩ := (hmemΛ y).mp hy
    exact (hmemΛ _).mpr ⟨u * w, map_mul θ u w⟩
  ·
    refine top_unique ?_
    have hsub : (e.toLinearMap : ℚ ⊗[ℤ] O →ₗ[ℚ] ℍ[ℚ, a, b]) ''
        Set.range (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O) ⊆ (Λ : Set ℍ[ℚ, a, b]) := by
      rintro _ ⟨_, ⟨o, rfl⟩, rfl⟩
      exact (hmemΛ _).mpr ⟨o, rfl⟩
    calc (⊤ : Submodule ℚ ℍ[ℚ, a, b])
        = Submodule.map (e.toLinearMap : ℚ ⊗[ℤ] O →ₗ[ℚ] ℍ[ℚ, a, b]) ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
      _ = Submodule.span ℚ ((e.toLinearMap : ℚ ⊗[ℤ] O →ₗ[ℚ] ℍ[ℚ, a, b]) ''
            Set.range (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O)) := by
          rw [← span_range_includeRight O, Submodule.map_span]
      _ ≤ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := Submodule.span_mono hsub
  · rw [hΛmap]
    exact Submodule.FG.map _ Module.Finite.fg_top

end S_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight
end P2MW
export P2MW.S_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight (solution)
