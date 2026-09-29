-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ba6a521a-0c60-5f65-a11d-7d8b9e9bfbfd

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra

open IsDedekindDomain NumberField

namespace QDiv

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem finiteAdeleBox_mono {Λ₁ Λ₂ : Submodule ℤ D} (h : Λ₁ ≤ Λ₂) :
    Submodule.finiteAdeleBox Λ₁ ≤ Submodule.finiteAdeleBox Λ₂ := by
  apply AddSubgroup.closure_mono
  rintro _ ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem finiteAdeleBox_zsmul_le (L : Submodule ℤ D) (n : ℕ) :
    Submodule.finiteAdeleBox (((n : ℕ) : ℤ) • L) ≤
      (Submodule.finiteAdeleBox L).map
        (AddMonoidHom.mulLeft ((n : ℕ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  rw [Submodule.finiteAdeleBox, AddSubgroup.closure_le]
  rintro _ ⟨z, hz, c, hc, rfl⟩
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z _ L).mp hz
  refine ⟨y ⊗ₜ[ℚ] c, AddSubgroup.subset_closure ⟨y, hy, c, hc, rfl⟩, ?_⟩
  rw [AddMonoidHom.coe_mulLeft, zsmul_eq_mul, Int.cast_natCast, Algebra.TensorProduct.natCast_def,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end QDiv

namespace QDiv

variable {a b : ℚ}

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun _ => one_mem _, Algebra.TensorProduct.one_def⟩

theorem mul_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x y : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ Submodule.finiteAdeleBox Λ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨z, hz, c, hc, rfl⟩ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hΛ.mul_mem hz hz', c * c', fun v => mul_mem (hc v) (hc' v), rfl⟩
  · intro x _
    rw [zero_mul]; exact zero_mem _
  · intro x _
    rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h h'
    rw [add_mul]; exact add_mem h h'
  · intro x y z _ _ _ h h'
    rw [mul_add]; exact add_mem h h'
  · intro x y _ _ h
    convert neg_mem h using 1
    exact neg_mul x y
  · intro x y _ _ h
    convert neg_mem h using 1
    exact mul_neg x y

end QDiv

open QDiv in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (n : ℕ) [NeZero n] :
    Submodule.ofFiniteIdele Λ (x * g) ≤ ((n : ℕ) : ℤ) • Submodule.ofFiniteIdele Λ x ↔
      (n : ℚ)⁻¹ • ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ := by
  classical
  have hfg := hΛ.fg
  have hsp := hΛ.spanTop
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)

  have hsmul_def : ∀ (c : ℚ) (w : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ), c • w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) c * w := fun c w =>
    Algebra.smul_def c w
  have hn_inv_smul : ∀ w : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ, (n : ℚ)⁻¹ • (((n : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * w) = w := fun w => by
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hn_smul_inv : ∀ w : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ, ((n : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * ((n : ℚ)⁻¹ • w) = w := fun w => by
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hn, one_smul]
  constructor
  ·
    intro hle

    have hxg : ((x * g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ (x * g)) := by
      rw [Submodule.finiteAdeleBox_ofFiniteIdele Λ hfg hsp (x * g)]
      exact ⟨1, one_mem_box hΛ, by rw [AddMonoidHom.coe_mulLeft, mul_one]⟩

    have h2 := finiteAdeleBox_zsmul_le (Submodule.ofFiniteIdele Λ x) n (finiteAdeleBox_mono hle hxg)
    rw [Submodule.finiteAdeleBox_ofFiniteIdele Λ hfg hsp x] at h2
    obtain ⟨_, ⟨lam, hlam, rfl⟩, hEq⟩ := h2
    rw [AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulLeft, Units.val_mul] at hEq

    have hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) = ((n : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * lam := by
      calc ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)
          = ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (((x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * g) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (((n : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (x * lam)) := by rw [hEq]
        _ = ((n : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * lam := by
            rw [← mul_assoc, ← (Nat.cast_commute n _).eq, mul_assoc, ← mul_assoc ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ),
              Units.inv_mul, one_mul]
    rw [hg, hn_inv_smul]
    exact hlam
  ·
    intro hmem z hz
    rw [Submodule.mem_ofFiniteIdele_iff] at hz
    obtain ⟨lam, hlam, hEq⟩ := hz
    rw [AddMonoidHom.coe_mulLeft, Units.val_mul] at hEq

    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(n : ℚ)⁻¹ • z, ?_, ?_⟩
    · rw [Submodule.mem_ofFiniteIdele_iff]
      refine ⟨((n : ℚ)⁻¹ • ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) * lam, mul_mem_box hΛ hmem hlam, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, mul_smul_comm, smul_mul_assoc, hEq]
      exact (map_smul (Algebra.TensorProduct.includeLeft : ℍ[ℚ, a, b] →ₐ[ℚ] ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ z).symm
    · rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hn, one_smul]

end S_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox (solution)
