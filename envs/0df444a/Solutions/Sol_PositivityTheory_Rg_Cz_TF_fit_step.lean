-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.fit_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:42.167066+00:00
-- url     : https://prove2.me/submissions/89a20b6e-32ee-4b6c-bccb-29a677bef9f3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Theorems.Thm_P2M_PositivityTheory_Rg_Cz_TF_pow_mem__037d3ddb993f
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_restrict_pow_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (e : U →ₗ[ℂ] ℂ)
    (Z : Submodule ℂ U) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) (he : ∀ z ∈ Z, e (T z) = 0)
    (z0 : U) (hz0 : z0 ∈ Z) (hez : e z0 ≠ 0) : ∃ N : ℕ, ∃ a ∈ Z, (T ^ N) a = 0 ∧ e a ≠ 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_isCompl_ker_pow_range_pow (T.restrict hZ))
  have hc := hN (N + 1) (by omega)
  have hmem : (⟨z0, hz0⟩ : Z) ∈ LinearMap.ker ((T.restrict hZ) ^ (N + 1)) ⊔
      LinearMap.range ((T.restrict hZ) ^ (N + 1)) := by
    rw [hc.codisjoint.eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨w, rfl⟩ := hb
  refine ⟨N + 1, a, a.2, ?_, ?_⟩
  · rw [← restrict_pow_coe T Z hZ, LinearMap.mem_ker.1 ha]; rfl
  · have h1 : (z0 : U) = (a : U) + (T ^ (N + 1)) (w : U) := by
      rw [← restrict_pow_coe T Z hZ, ← Submodule.coe_add, hab]
    have h2 : e ((T ^ (N + 1)) (w : U)) = 0 := by
      rw [pow_succ', Module.End.mul_apply]
      exact he _ (pow_mem' T Z hZ N _ w.2)
    intro h0
    apply hez
    rw [h1, map_add, h0, h2, add_zero]
end PositivityTheory.Rg.Cz.TF
