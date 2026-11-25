-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.sig_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:55:08.631133+00:00
-- url     : https://prove2.me/submissions/c22bad97-1085-4756-b720-d862137a38c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_dAct_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (w0 : O) (hw : w0 + star w0 = 1) (u : Fin d → k) :
    ∑ b, C (u b) * ∑ c, sgOf k h c * C (dAct k B (star w0) c b) +
      ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * sgOf k h j = ∑ c, sgOf k h c * C (u c) := by
  have hu : ∀ c, ∑ b, C (u b) * (C (dAct k B w0 c b) + C (dAct k B (star w0) c b)) = (C (u c) : PS k 1 d) := by
    intro c
    rw [Finset.sum_eq_single c]
    · rw [← map_add, dAct_sum B w0 hw c c, if_pos rfl, map_one, mul_one]
    · intro b _ hb
      rw [← map_add, dAct_sum B w0 hw c b, if_neg (Ne.symm hb), map_zero, mul_zero]
    · intro hc; exact absurd (Finset.mem_univ c) hc
  have L1 : ∑ b, C (u b) * ∑ c, sgOf k h c * C (dAct k B (star w0) c b) =
      ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B (star w0) c b)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have L2 : ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * sgOf k h j =
      ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B w0 c b)) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have L3 : ∑ c, sgOf k h c * C (u c) = ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B w0 c b)) +
      ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B (star w0) c b)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib, ← hu c, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [L1, L2, L3]
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
