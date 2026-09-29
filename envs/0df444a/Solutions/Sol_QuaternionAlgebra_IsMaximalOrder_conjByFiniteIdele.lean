-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.conjByFiniteIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0236c850-3f26-5617-960e-7b92917f44c3

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace W3

variable {D : Type*} [Ring D] [Algebra ℚ D]

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem finiteAdeleBox_mono {Λ₁ Λ₂ : Submodule ℤ D} (h : Λ₁ ≤ Λ₂) :
    Submodule.finiteAdeleBox Λ₁ ≤ Submodule.finiteAdeleBox Λ₂ :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, a, ha, hx⟩ => ⟨z, h hz, a, ha, hx⟩

theorem conjByFiniteIdele_mono {Λ₁ Λ₂ : Submodule ℤ D} (h : Λ₁ ≤ Λ₂) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.conjByFiniteIdele Λ₁ g ≤ Submodule.conjByFiniteIdele Λ₂ g := fun z hz => by
  rw [Submodule.mem_conjByFiniteIdele_iff] at hz ⊢
  exact AddSubgroup.map_mono (finiteAdeleBox_mono h) hz

theorem tmul_one_mem_finiteAdeleBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, 1, fun v => (v.adicCompletionIntegers ℚ).one_mem, rfl⟩

theorem le_conjByFiniteIdele_conjByFiniteIdele_inv (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hsp : Submodule.span ℚ (Λ : Set D) = ⊤) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Λ ≤ Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele Λ g) g⁻¹ := fun z hz => by
  rw [Submodule.mem_conjByFiniteIdele_iff, Submodule.finiteAdeleBox_conjByFiniteIdele Λ hfg hsp g,
    AddSubgroup.map_map]
  refine ⟨z ⊗ₜ[ℚ] (1 : 𝔸f), tmul_one_mem_finiteAdeleBox hz, ?_⟩
  simp only [inv_inv, AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
  rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]

theorem main {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (β : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    QuaternionAlgebra.IsMaximalOrder (Submodule.conjByFiniteIdele Λ β) := by
  refine ⟨QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ hΛ.isOrder β, fun Λ' hΛ' hle => ?_⟩

  have h1 : Λ ≤ Submodule.conjByFiniteIdele Λ' β⁻¹ :=
    (le_conjByFiniteIdele_conjByFiniteIdele_inv Λ hΛ.isOrder.fg hΛ.isOrder.spanTop β).trans
      (conjByFiniteIdele_mono hle β⁻¹)
  have h2 : Submodule.conjByFiniteIdele Λ' β⁻¹ = Λ :=
    hΛ.2 _ (QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ' hΛ' β⁻¹) h1

  refine le_antisymm ?_ hle
  have h3 := le_conjByFiniteIdele_conjByFiniteIdele_inv Λ' hΛ'.fg hΛ'.spanTop β⁻¹
  rwa [inv_inv, h2] at h3

end W3

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    QuaternionAlgebra.IsMaximalOrder (Submodule.conjByFiniteIdele Λ β) := by
  exact W3.main hΛ β

end S_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele (solution)
