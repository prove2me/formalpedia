-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_add_583a49333333
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:44.493466+00:00
-- url     : https://prove2.me/submissions/dc6b4357-ac41-4bc5-928d-f91b6564724d

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
theorem _root_.solution (y : C) {N M Q : Type*} [AddCommGroup N] [Module C N]
    [AddCommGroup M] [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (hy : ∀ q : Q, y • q = 0 → q = 0) :
    Module.length C (QuotSMulTop y M) =
      Module.length C (QuotSMulTop y N) + Module.length C (QuotSMulTop y Q) := by
  refine Module.length_eq_add_of_exact (QuotSMulTop.map y f) (QuotSMulTop.map y g) ?_
    (QuotSMulTop.map_surjective y hg) (QuotSMulTop.map_exact y H hg)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨m, -, hm⟩ := hx
  have hgm : g m = 0 := hy _ (by rw [← map_smul, hm]; exact (H (f n)).2 ⟨n, rfl⟩)
  obtain ⟨n', rfl⟩ := (H m).1 hgm
  have hn : n = y • n' := hf (by rw [map_smul, hm])
  rw [Submodule.Quotient.mk_eq_zero, hn]
  exact Submodule.smul_mem_pointwise_smul n' y ⊤ trivial
end GroundTheory.Heights₂.Heights.LengthCutGlobal
