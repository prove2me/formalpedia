-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:05.929819+00:00
-- url     : https://prove2.me/submissions/265e6cbf-b5d8-4f1f-91e7-032600368edf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] [TopologicalSpace G]
  [TopologicalSpace G₁] [TopologicalSpace G₂]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {Φ : G ≃ₜ* G₁ × G₂} {Γ : Subgroup G} {K : Subgroup G₂} {s : G₂} {x : G₁} :
    x ∈ sliceGroup Φ Γ K s ↔ ∃ γ ∈ Γ, s⁻¹ * (Φ γ).2 * s ∈ K ∧ (Φ γ).1 = x := by
  simp only [sliceGroup, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap,
    Subgroup.mem_prod, Subgroup.mem_top, true_and, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst]
  constructor
  · rintro ⟨γ, ⟨hγ, k, hk, hks⟩, rfl⟩
    refine ⟨γ, hγ, ?_, rfl⟩
    have : (Φ γ).2 = s * k * s⁻¹ := by
      have := hks.symm
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
      exact this
    rw [this]
    simpa [mul_assoc] using hk
  · rintro ⟨γ, hγ, hk, rfl⟩
    refine ⟨γ, ⟨hγ, s⁻¹ * (Φ γ).2 * s, hk, ?_⟩, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, mul_assoc,
      mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
