-- Prove2me | solution 1 for PI.InvIdealIdxPiWork.map_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:36.83496+00:00
-- url     : https://prove2.me/submissions/af69a88d-f7de-4f92-99a3-52eb42a26d05

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace PI.InvIdealIdxPiWork
theorem _root_.solution (J K : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (a : 𝓞 E) (hK : Ideal.span {a} = J * K) :
    ((((J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
        Submodule (𝓞 E) E).toAddSubgroup).map (AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a)) =
      idS K := by
  have hJ0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have key : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E a) *
      (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ = (K : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← FractionalIdeal.coeIdeal_span_singleton, hK, FractionalIdeal.coeIdeal_mul,
      mul_comm (J : FractionalIdeal (𝓞 E)⁰ E), mul_assoc, mul_inv_cancel₀ hJ0, mul_one]
  ext x
  simp only [idS, Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, FractionalIdeal.mem_coe,
    AddMonoidHom.coe_mulLeft]
  rw [← key, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
end PI.InvIdealIdxPiWork
