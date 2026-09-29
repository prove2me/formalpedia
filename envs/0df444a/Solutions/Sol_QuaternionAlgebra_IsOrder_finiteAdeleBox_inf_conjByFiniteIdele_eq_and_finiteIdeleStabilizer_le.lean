-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f2e696ac-0467-5b34-aac5-a0f06e5f4b8e

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "IsDedekindDomain QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le.QuaternionAlgebra"

noncomputable section

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "IsOrder IsOrder.conjByFiniteIdele"
namespace EichlerFrameAdelic
p2m_open "QuaternionAlgebra"

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem finiteAdeleBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem tmul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) {c : 𝔸f}
    (hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_finiteAdeleBox hΛ.one_mem fun v => one_mem _

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add u w _ _ hu hw => rw [add_mul]; exact add_mem hu hw
    | neg u _ hu =>
      convert neg_mem hu using 1
      exact neg_mul u _
  | zero => rw [mul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mul_add]; exact add_mem hu hw
  | neg u _ hu =>
    convert neg_mem hu using 1
    exact mul_neg x u

theorem ratCast_smul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (n : ℕ)
    {w : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f} (hw : w ∈ Submodule.finiteAdeleBox Λ) :
    ((n : ℕ) : ℚ) • w ∈ Submodule.finiteAdeleBox Λ := by
  rw [Nat.cast_smul_eq_nsmul ℚ]
  exact AddSubgroup.nsmul_mem _ hw n

theorem mem_finiteIdeleStabilizer_of_mem_of_inv_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (hu : (u : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ)
    (hu' : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  ext z
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Units.smul_def, smul_eq_mul]
    exact mul_mem_finiteAdeleBox hΛ hu hw
  · intro hz
    refine ⟨((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * z, mul_mem_finiteAdeleBox hΛ hu' hz, ?_⟩
    rw [Units.smul_def, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]

theorem coe_mem_finiteAdeleBox_of_mem_finiteIdeleStabilizer {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O)
    {u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer O) :
    (u : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox O := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff] at hu
  have h1 : (u : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * 1 ∈ u • ((Submodule.finiteAdeleBox O : AddSubgroup _) : Set (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) :=
    Set.mem_smul_set.mpr ⟨1, one_mem_finiteAdeleBox hO, by rw [Units.smul_def, smul_eq_mul]⟩
  rw [hu, mul_one] at h1
  exact h1

theorem mem_finiteIdeleStabilizer_of_le {O Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) (hΛ' : IsOrder Λ')
    (hle : O ≤ Λ') {u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer O) :
    u ∈ Submodule.finiteIdeleStabilizer Λ' :=
  mem_finiteIdeleStabilizer_of_mem_of_inv_mem hΛ' u
    (finiteAdeleBox_mono hle (coe_mem_finiteAdeleBox_of_mem_finiteIdeleStabilizer hO hu))
    (finiteAdeleBox_mono hle (coe_mem_finiteAdeleBox_of_mem_finiteIdeleStabilizer hO (inv_mem hu)))

theorem finiteAdeleBox_inf_eq {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : IsOrder Λ₁) (h₂ : IsOrder Λ₂) :
    Submodule.finiteAdeleBox (Λ₁ ⊓ Λ₂) = Submodule.finiteAdeleBox Λ₁ ⊓ Submodule.finiteAdeleBox Λ₂ := by
  refine le_antisymm (le_inf (finiteAdeleBox_mono inf_le_left) (finiteAdeleBox_mono inf_le_right)) ?_
  rintro z ⟨hz₁, hz₂⟩
  have h₁₂ : IsOrder (Λ₁ ⊓ Λ₂) := h₁.inf h₂
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ h₁₂.fg h₁₂.spanTop]
  intro v
  rw [Submodule.localBox_inf Λ₁ Λ₂ h₁.fg h₁.spanTop h₂.fg h₂.spanTop v]
  exact ⟨(Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ h₁.fg h₁.spanTop z).mp hz₁ v,
    (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ h₂.fg h₂.spanTop z).mp hz₂ v⟩

end QuaternionAlgebra.EichlerFrameAdelic

end

open QuaternionAlgebra.EichlerFrameAdelic in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.finiteAdeleBox (Λ ⊓ Submodule.conjByFiniteIdele Λ m) =
        Submodule.finiteAdeleBox Λ ⊓
          (Submodule.finiteAdeleBox Λ).map
            ((AddMonoidHom.mulRight ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
                ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
              (AddMonoidHom.mulLeft (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) ∧
      (∀ N : ℕ,
        ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
            Submodule.finiteAdeleBox Λ →
          ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ →
        ∀ w ∈ Submodule.finiteAdeleBox Λ,
          ((N : ℕ) : ℚ) • w ∈ Submodule.finiteAdeleBox (Λ ⊓ Submodule.conjByFiniteIdele Λ m)) ∧
      Submodule.finiteIdeleStabilizer (Λ ⊓ Submodule.conjByFiniteIdele Λ m) ≤ Submodule.finiteIdeleStabilizer Λ ∧
      (∀ u ∈ Submodule.finiteIdeleStabilizer (Λ ⊓ Submodule.conjByFiniteIdele Λ m),
        m⁻¹ * u * m ∈ Submodule.finiteIdeleStabilizer Λ) := by
  set Λ₂ := Submodule.conjByFiniteIdele Λ m with hΛ₂def
  have hΛ₂ : QuaternionAlgebra.IsOrder Λ₂ := QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ hΛ m
  have hR : QuaternionAlgebra.IsOrder (Λ ⊓ Λ₂) := hΛ.inf hΛ₂
  have hbox₂ := Submodule.finiteAdeleBox_conjByFiniteIdele Λ hΛ.fg hΛ.spanTop m
  have h1 : Submodule.finiteAdeleBox (Λ ⊓ Λ₂) =
      Submodule.finiteAdeleBox Λ ⊓ (Submodule.finiteAdeleBox Λ).map
        ((AddMonoidHom.mulRight ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
          (AddMonoidHom.mulLeft (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    rw [finiteAdeleBox_inf_eq hΛ hΛ₂, ← hbox₂]
  refine ⟨h1, fun N hm₁ hmN w hw => ?_, fun u hu => mem_finiteIdeleStabilizer_of_le hR hΛ inf_le_left hu, fun u hu => ?_⟩
  ·
    rw [h1]
    refine ⟨ratCast_smul_mem_finiteAdeleBox N hw, ?_⟩
    refine ⟨(((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _)) * w *
        (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ),
      mul_mem_finiteAdeleBox hΛ (mul_mem_finiteAdeleBox hΛ hmN hw) hm₁, ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul,
      mul_assoc, Units.mul_inv, mul_one]
  ·
    have hu₂ : u ∈ Submodule.finiteIdeleStabilizer Λ₂ := mem_finiteIdeleStabilizer_of_le hR hΛ₂ inf_le_right hu
    have key : ∀ w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, w ∈ Submodule.finiteIdeleStabilizer Λ₂ →
        (((m⁻¹ * w * m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
          Submodule.finiteAdeleBox Λ := by
      intro w hw
      have hwbox := coe_mem_finiteAdeleBox_of_mem_finiteIdeleStabilizer hΛ₂ hw
      rw [hΛ₂def, hbox₂, AddSubgroup.mem_map] at hwbox
      obtain ⟨z, hz, hzw⟩ := hwbox
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at hzw
      have : (((m⁻¹ * w * m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = z := by
        rw [Units.val_mul, Units.val_mul, ← hzw]
        simp only [← mul_assoc, Units.inv_mul, one_mul]
        rw [mul_assoc, Units.inv_mul, mul_one]
      rw [this]; exact hz
    refine mem_finiteIdeleStabilizer_of_mem_of_inv_mem hΛ _ (key u hu₂) ?_
    have : (m⁻¹ * u * m)⁻¹ = m⁻¹ * u⁻¹ * m := by group
    rw [this]
    exact key u⁻¹ (inv_mem hu₂)

end S_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le (solution)
