-- Prove2me | solution 1 for PI.VolStabW.exists_sub_osc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:38.862869+00:00
-- url     : https://prove2.me/submissions/c24ebadc-c8ca-496e-9d25-4231652e2c91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGen
import Theorems.Thm_PI_VolStabW_HasDens_sub
import Theorems.Thm_PI_VolStabW_isOpen_inf_iInf

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
open MeasureTheory Topology Set Filter
open scoped Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace PI.VolStabW
theorem _root_.solution (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hN : ∀ x : V, {z : V | |φ (x + z) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
    intro x
    have hcx : Continuous fun z : V => |φ (x + z) - φ x| :=
      ((hc.comp (continuous_const.add continuous_id)).sub continuous_const).abs
    have : IsOpen {z : V | |φ (x + z) - φ x| < ε / 2} := isOpen_lt hcx continuous_const
    exact this.mem_nhds (by simp; linarith)
  choose L hLo hLc hLN using fun x => hNA _ (hN x)
  have hcov : tsupport φ ⊆ ⋃ x : tsupport φ, {y : V | y - (x : V) ∈ L x} := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, by simp [(L y).zero_mem]⟩
  have hopen : ∀ x : tsupport φ, IsOpen {y : V | y - (x : V) ∈ L x} := fun x =>
    (hLo x).preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := hs.isCompact.elim_finite_subcover _ hopen hcov
  have ho := isOpen_inf_iInf Λ₀ h₀o t (fun x : tsupport φ => L (x : V)) (fun x => hLo _)
  refine ⟨Λ₀ ⊓ ⨅ x ∈ t, L (x : V), ho, ?_, inf_le_left, ?_⟩
  · exact h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ ho)
      (by rw [AddSubgroup.coe_inf]; exact inter_subset_left)
  · intro x z hz
    have hz' : ∀ i ∈ t, z ∈ L (i : V) := by
      intro i hi
      have := (inf_le_right : Λ₀ ⊓ ⨅ x ∈ t, L (x : V) ≤ _) hz
      exact (AddSubgroup.mem_iInf.1 this i |> AddSubgroup.mem_iInf.1) hi
    have key : ∀ i ∈ t, x - (i : V) ∈ L (i : V) → |φ (x + z) - φ x| < ε := by
      intro i hi hxi
      have h1 := hLN (i : V) hxi
      have h2 := hLN (i : V) (show x + z - (i : V) ∈ L (i : V) by
        have := (L (i : V)).add_mem hxi (hz' i hi)
        rwa [show x - (i : V) + z = x + z - (i : V) by abel] at this)
      simp only [mem_setOf_eq, add_sub_cancel] at h1 h2
      calc |φ (x + z) - φ x| ≤ |φ (x + z) - φ i| + |φ x - φ i| := by
            rw [abs_sub_comm (φ x)]; exact abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add h2 h1
        _ = ε := by ring
    by_cases hx : x ∈ tsupport φ
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact key i hi hxi
    · by_cases hxz : x + z ∈ tsupport φ
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hxz)
        refine key i hi ?_
        have := (L (i : V)).sub_mem hxi (hz' i hi)
        rwa [show x + z - (i : V) - z = x - (i : V) by abel] at this
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]
        simpa using hε
end PI.VolStabW
