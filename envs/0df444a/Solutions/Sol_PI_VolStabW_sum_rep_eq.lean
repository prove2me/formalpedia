-- Prove2me | solution 1 for PI.VolStabW.sum_rep_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:10.323429+00:00
-- url     : https://prove2.me/submissions/148dd2c5-9e0a-4dfb-bd4d-f38f55a70f62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs
import Theorems.Thm_PI_VolStabW_repO_mem
import Theorems.Thm_PI_VolStabW_repO_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]
namespace PI.VolStabW
theorem _root_.solution {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by
  classical
  let F : orbS Γ y0 × (Γ ⊓ H).subgroupOf H → Γ := fun p =>
    ⟨repO Γ y0 p.1 * ((p.2 : H) : G), Γ.mul_mem (repO_mem Γ y0 p.1)
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 p.2.2)).1⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨x, δ⟩ ⟨x', δ'⟩ he
      have he' : repO Γ y0 x * ((δ : H) : G) = repO Γ y0 x' * ((δ' : H) : G) := congrArg Subtype.val he
      have hδ : ((δ : H) : G) • y0 = y0 := (hH _).1 (δ : H).2
      have hδ' : ((δ' : H) : G) • y0 = y0 := (hH _).1 (δ' : H).2
      have hx : (x : Y) = x' := by
        calc (x : Y) = repO Γ y0 x • y0 := (repO_smul Γ y0 x).symm
          _ = repO Γ y0 x • (((δ : H) : G) • y0) := by rw [hδ]
          _ = (repO Γ y0 x * ((δ : H) : G)) • y0 := (mul_smul _ _ _).symm
          _ = (repO Γ y0 x' * ((δ' : H) : G)) • y0 := by rw [he']
          _ = repO Γ y0 x' • (((δ' : H) : G) • y0) := mul_smul _ _ _
          _ = repO Γ y0 x' • y0 := by rw [hδ']
          _ = x' := repO_smul Γ y0 x'
      have hxx : x = x' := Subtype.ext hx
      subst hxx
      have e : ((δ : H) : G) = ((δ' : H) : G) := mul_left_cancel he'
      exact Prod.ext rfl (Subtype.ext (Subtype.ext e))
    · intro γ
      have hd : (repO Γ y0 ⟨(γ : G) • y0, γ, γ.2, rfl⟩)⁻¹ * γ ∈ H := by
        rw [hH, mul_smul, inv_smul_eq_iff, repO_smul]
      refine ⟨(⟨(γ : G) • y0, γ, γ.2, rfl⟩, ⟨⟨_, hd⟩, Subgroup.mem_subgroupOf.2
        (Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.inv_mem (repO_mem Γ y0 _)) γ.2, hd⟩)⟩), ?_⟩
      apply Subtype.ext
      exact mul_inv_cancel_left _ _
  calc _ = ∑' p : orbS Γ y0 × (Γ ⊓ H).subgroupOf H, u (repO Γ y0 p.1 * ((p.2 : H) : G)) :=
        (ENNReal.tsum_prod (f := fun x (δ : (Γ ⊓ H).subgroupOf H) => u (repO Γ y0 x * ((δ : H) : G)))).symm
    _ = ∑' γ : Γ, u γ := (Equiv.ofBijective F hF).tsum_eq (fun γ : Γ => u γ)
end PI.VolStabW
