-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.relIndex_conjByFiniteIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a1c2e671-bb3f-54b8-831a-ad9d5f6184ad

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_relIndex_conjByFiniteIdele
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace QNIdxConj

theorem localBox_conjByFiniteIdele_eq_map {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hΛ : QuaternionAlgebra.IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox (Submodule.conjByFiniteIdele Λ g) v =
      (Submodule.localBox Λ v).map
        ((AddMonoidHom.mulRight (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
            ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).comp
          (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
            ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))) := by
  ext x
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ hΛ.fg hΛ.spanTop g v x, AddSubgroup.mem_map]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
  exact ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩⟩

end QNIdxConj

theorem solution
    {a b : ℚ} {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hΛ' : QuaternionAlgebra.IsOrder Λ') (hle : Λ' ≤ Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (Submodule.conjByFiniteIdele Λ' g).toAddSubgroup.relIndex (Submodule.conjByFiniteIdele Λ g).toAddSubgroup =
      Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup := by
  have h1 : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele Λ g) :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ hΛ g
  have h1' : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele Λ' g) :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ' hΛ' g
  have hle' : Submodule.conjByFiniteIdele Λ' g ≤ Submodule.conjByFiniteIdele Λ g := by
    intro z hz
    rw [Submodule.mem_conjByFiniteIdele_iff] at hz ⊢
    have hbox : Submodule.finiteAdeleBox Λ' ≤ Submodule.finiteAdeleBox Λ :=
      AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, hle hz, c, hc, hx⟩
    exact AddSubgroup.map_mono hbox hz
  rw [Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox (Submodule.conjByFiniteIdele Λ g)
      (Submodule.conjByFiniteIdele Λ' g) h1.fg h1.spanTop h1'.fg h1'.spanTop hle',
    Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ Λ' hΛ.fg hΛ.spanTop hΛ'.fg hΛ'.spanTop hle]
  refine finprod_congr fun v => ?_
  rw [QNIdxConj.localBox_conjByFiniteIdele_eq_map Λ hΛ g v,
    QNIdxConj.localBox_conjByFiniteIdele_eq_map Λ' hΛ' g v]
  refine AddSubgroup.relIndex_map_map_of_injective _ _ fun x y hxy => ?_
  set gv : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ :=
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) with hgv
  set gvi : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ :=
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) with hgvi
  have hgg : gv * gvi = 1 := by
    rw [hgv, hgvi, ← map_mul, Units.mul_inv, map_one]
  have hgg' : gvi * gv = 1 := by
    rw [hgv, hgvi, ← map_mul, Units.inv_mul, map_one]
  have hxy' : gv * x * gvi = gv * y * gvi := by
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight] using hxy
  calc x = (gvi * gv) * x * (gvi * gv) := by rw [hgg', one_mul, mul_one]
    _ = gvi * (gv * x * gvi) * gv := by noncomm_ring
    _ = gvi * (gv * y * gvi) * gv := by rw [hxy']
    _ = (gvi * gv) * y * (gvi * gv) := by noncomm_ring
    _ = y := by rw [hgg', one_mul, mul_one]

end S_QuaternionAlgebra_IsOrder_relIndex_conjByFiniteIdele
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_relIndex_conjByFiniteIdele (solution)
