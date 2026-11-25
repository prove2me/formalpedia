-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_exists_nearest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:22:27.02499+00:00
-- url     : https://prove2.me/submissions/bfb6c924-744c-4af7-a941-ac6ff443c4d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneLeKappaMulPhase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_pack_card
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ x ∈ X.L, ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖ := by
  classical

  let S : Set (Vsp X.dim) := {y | (∃ x ∈ X.L, y = uMap I x) ∧ ‖u - y‖ ≤ ‖u‖}
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (Nat.ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I)) + 1)
    have hb := tof_pack_card P hI hP u hu (‖u‖ + 1) (by linarith [norm_nonneg u]) t
      (fun y hy => (ht (Finset.mem_coe.2 hy)).1)
      (fun y hy => le_trans (ht (Finset.mem_coe.2 hy)).2 (by linarith))
    rw [hcard] at hb
    push_cast at hb
    have hc := Nat.le_ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I))
    linarith
  have h0 : (0 : Vsp X.dim) ∈ S :=
    ⟨⟨0, X.L.zero_mem, (map_zero (uMap I)).symm⟩, by rw [sub_zero]⟩
  obtain ⟨y, hyS, hmin⟩ :=
    hfin.toFinset.exists_min_image (fun y => ‖u - y‖) ⟨0, hfin.mem_toFinset.2 h0⟩
  obtain ⟨⟨y0, hy0, rfl⟩, hyu⟩ := hfin.mem_toFinset.1 hyS
  refine ⟨y0, hy0, fun x hx => ?_⟩
  by_cases hxs : ‖u - uMap I x‖ ≤ ‖u‖
  · exact hmin _ (hfin.mem_toFinset.2 ⟨⟨x, hx, rfl⟩, hxs⟩)
  · push_neg at hxs
    linarith
end ReciprocityTheory.ChartRestriction.G.I2
