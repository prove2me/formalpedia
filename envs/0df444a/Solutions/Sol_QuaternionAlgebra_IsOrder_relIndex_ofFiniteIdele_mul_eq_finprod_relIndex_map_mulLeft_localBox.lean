-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.relIndex_ofFiniteIdele_mul_eq_finprod_relIndex_map_mulLeft_localBox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/210ed437-8c6a-5e8c-a63e-ece4d8bf98a6

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_fg_and_span_eq_top_ofFiniteIdele
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Submodule_mem_localBox_ofFiniteIdele_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_relIndex_ofFiniteIdele_mul_eq_finprod_relIndex_map_mulLeft_localBox
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

namespace GlobalIndex

variable {a b : ℚ}

theorem mul_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ}
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

theorem localBox_ofFiniteIdele_eq_map {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox (Submodule.ofFiniteIdele Λ y) v =
      (Submodule.localBox Λ v).map
        (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
  ext z
  rw [Submodule.mem_localBox_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop y v z, AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩

end GlobalIndex

open GlobalIndex in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ) :
    (Submodule.ofFiniteIdele Λ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ x).toAddSubgroup =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft
          (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).relIndex (Submodule.localBox Λ v) := by
  classical
  have hfg := hΛ.fg
  have hsp := hΛ.spanTop

  have hle : Submodule.ofFiniteIdele Λ (x * g) ≤ Submodule.ofFiniteIdele Λ x := by
    intro z hz
    rw [Submodule.mem_ofFiniteIdele_iff] at hz ⊢
    obtain ⟨lam, hlam, hEq⟩ := hz
    refine ⟨(g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * lam, mul_mem_box hΛ hg hlam, ?_⟩
    rw [AddMonoidHom.coe_mulLeft] at hEq ⊢
    rw [← hEq, Units.val_mul, mul_assoc]
  obtain ⟨h₁fg, h₁sp⟩ := Submodule.fg_and_span_eq_top_ofFiniteIdele Λ hfg hsp x
  obtain ⟨h₂fg, h₂sp⟩ := Submodule.fg_and_span_eq_top_ofFiniteIdele Λ hfg hsp (x * g)
  rw [Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox (Submodule.ofFiniteIdele Λ x)
    (Submodule.ofFiniteIdele Λ (x * g)) h₁fg h₁sp h₂fg h₂sp hle]
  refine finprod_congr fun v => ?_
  rw [localBox_ofFiniteIdele_eq_map hΛ, localBox_ofFiniteIdele_eq_map hΛ, Units.val_mul, map_mul,
    show ∀ X G : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      AddMonoidHom.mulLeft (X * G) = (AddMonoidHom.mulLeft X).comp (AddMonoidHom.mulLeft G) from
      fun X G => by ext; simp [mul_assoc],
    ← AddSubgroup.map_map]
  refine AddSubgroup.relIndex_map_map_of_injective _ _ ?_
  have hX : IsUnit (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) := (Units.isUnit x).map _
  exact hX.mul_right_injective

end S_QuaternionAlgebra_IsOrder_relIndex_ofFiniteIdele_mul_eq_finprod_relIndex_map_mulLeft_localBox
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_relIndex_ofFiniteIdele_mul_eq_finprod_relIndex_map_mulLeft_localBox (solution)
