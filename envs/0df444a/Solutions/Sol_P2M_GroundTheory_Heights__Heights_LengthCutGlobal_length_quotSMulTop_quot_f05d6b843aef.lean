-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_quot_f05d6b843aef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:52.867996+00:00
-- url     : https://prove2.me/submissions/eb8981fd-90b6-4ee0-9359-182dd9a9d931

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
omit [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution {y : C} (hmax : (P ⊔ Ideal.span {y}).IsMaximal) :
    Module.length C (QuotSMulTop y (C ⧸ P)) = 1 := by
  let g : C →ₗ[C] QuotSMulTop y (C ⧸ P) :=
    (y • (⊤ : Submodule C (C ⧸ P))).mkQ ∘ₗ Algebra.linearMap C (C ⧸ P)
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp Ideal.Quotient.mk_surjective
  have hker : LinearMap.ker g = P ⊔ Ideal.span {y} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Algebra.linearMap_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
      have hmem : x - y * c ∈ P := by
        rw [← Ideal.Quotient.eq, map_mul, ← Ideal.Quotient.algebraMap_eq, ← ht, Algebra.smul_def]
        rfl
      rw [show x = (x - y * c) + y * c by ring]
      exact Submodule.add_mem_sup hmem (Ideal.mem_span_singleton'.2 ⟨c, mul_comm c y⟩)
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Ideal.Quotient.mk P c, ?_⟩
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, mul_comm]
  rw [← (g.quotKerEquivOfSurjective hg).length_eq, hker]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.1 hmax))
end GroundTheory.Heights₂.Heights.LengthCutGlobal
