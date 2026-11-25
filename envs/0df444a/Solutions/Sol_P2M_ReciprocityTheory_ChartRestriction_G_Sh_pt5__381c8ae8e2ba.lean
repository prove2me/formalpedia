-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Sh_pt5__381c8ae8e2ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:13:20.369923+00:00
-- url     : https://prove2.me/submissions/ae50176d-c63f-4060-8227-f7ce0f44dfe5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TypicalCurveStructureConstants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_exists_average
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_type


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution : TypicalCurveStructureConstants := by
  intro C _ _ _ v p hp hv d h ty G γ hB
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (tmat γ).det = 0 := hdet
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  choose δ hδc hδlg using fun a => exists_average G hp hζ (hγ a)
  have hlcδ : ∀ a n, G.lc p (δ a) n = (p : C) • G.lc p (γ a) (n + 1) := by
    intro a n
    funext c
    simp only [LogFGL.lc, Pi.smul_apply, smul_eq_mul]
    rw [hδlg, pow_succ']
  have hδt : ∀ a, G.IsOfType p ty (ty a + 1) (δ a) := by
    intro a
    refine ⟨fun c j hj => ?_, fun n c hc => ?_⟩
    · rw [hδlg, (hγty a).1 c (p * j) (fun k hk => ?_), mul_zero]
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hk)
      · exact hj k (by rw [pow_succ'] at hk; exact Nat.eq_of_mul_eq_mul_left hp.pos hk)
    · rw [hlcδ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [(hγty a).2 (n + 1) c (by intro e; apply hc; rw [e]; push_cast; ring), mul_zero]
  refine ⟨fun s b a => ptx G p γ (δ a) s b,
    fun s b a => ptx_int G hp hγ (fun b => (hγty b).1) hdet' (δ a) (hδc a) (hδt a).1 s b,
    fun s b a hne => ?_, fun a n => ?_⟩
  · rw [ptx_type ty G hp hγ hdet' hγty (δ a) _ (hδt a) s b hne]
    ring
  · rw [← hlcδ a n, ptx_rel G p hγ hdet' (δ a) n]
    refine (Finset.sum_range_reflect _ (n + 1)).symm.trans ?_
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    dsimp only
    rw [show n + 1 - 1 - m = n - m by omega, Nat.sub_sub_self hmn]
end ReciprocityTheory.ChartRestriction.G.Sh
