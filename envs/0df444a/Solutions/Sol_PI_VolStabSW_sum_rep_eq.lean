-- Prove2me | solution 1 for PI.VolStabSW.sum_rep_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:00.803353+00:00
-- url     : https://prove2.me/submissions/c0cb38ce-b759-4894-9202-21dd879e1ae2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnfoldAbs
import Theorems.Thm_PI_VolStabSW_repO_mem
import Theorems.Thm_PI_VolStabSW_repO_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]
namespace PI.VolStabSW
theorem _root_.solution {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by
  classical
  have hstab : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) • y0 = y0 := fun δ => (hH _).mp (δ : H).2
  let e : orbS Γ y0 × (Γ ⊓ H).subgroupOf H → Γ := fun p =>
    ⟨repO Γ y0 p.1 * ((p.2 : H) : G), Γ.mul_mem (repO_mem Γ y0 p.1)
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp p.2.2)).1⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨x, δ⟩ ⟨x', δ'⟩ hxy
      have h1 : repO Γ y0 x * ((δ : H) : G) = repO Γ y0 x' * ((δ' : H) : G) := congrArg Subtype.val hxy
      have ex : (repO Γ y0 x * ((δ : H) : G)) • y0 = (x : Y) := by rw [mul_smul, hstab, repO_smul]
      have ex' : (repO Γ y0 x' * ((δ' : H) : G)) • y0 = (x' : Y) := by rw [mul_smul, hstab, repO_smul]
      have hx : x = x' := Subtype.ext (by rw [← ex, ← ex', h1])
      subst hx
      have hd : ((δ : H) : G) = ((δ' : H) : G) := mul_left_cancel h1
      exact Prod.ext rfl (Subtype.ext (Subtype.ext hd))
    · intro γ
      let x : orbS Γ y0 := ⟨(γ : G) • y0, γ, γ.2, rfl⟩
      have hmemΓ : (repO Γ y0 x)⁻¹ * γ ∈ Γ := Γ.mul_mem (Γ.inv_mem (repO_mem Γ y0 x)) γ.2
      have hmemH : (repO Γ y0 x)⁻¹ * γ ∈ H := by
        rw [hH, mul_smul, inv_smul_eq_iff, repO_smul]
      refine ⟨(x, ⟨⟨_, hmemH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hmemΓ, hmemH⟩)⟩), ?_⟩
      apply Subtype.ext
      exact mul_inv_cancel_left _ _
  rw [← ENNReal.tsum_prod]
  exact (Equiv.ofBijective e he).tsum_eq (fun γ : Γ => u γ)
end PI.VolStabSW
