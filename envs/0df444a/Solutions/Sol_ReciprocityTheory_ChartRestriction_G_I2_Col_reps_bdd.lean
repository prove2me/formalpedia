-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.reps_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:28.976967+00:00
-- url     : https://prove2.me/submissions/d614ced5-e86d-46bc-b168-94ca504c392f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_pack_K
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_cutoff_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_uc_sep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_uc_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}
variable (hI : IsSplit P I)
include hI
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (hP : Ext.PackingCount) (C : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ X.L, ‖uc (IR I) y‖ ≤ C →
      ∃ y' ∈ X.L, uc (IR I) y' = uc (IR I) y ∧ ‖p2 (IR I) y'‖ ≤ M := by
  classical
  set F : Set (Vsp X.dim) := {u | ∃ y ∈ X.L, ‖uc (IR I) y‖ ≤ C ∧ uc (IR I) y = u} with hF
  have hb := cutoff_pos P
  set δ := Real.sqrt (b0 (E := E) P.q P.R0)
  have hδ : 0 < δ := Real.sqrt_pos.2 hb
  have hfin : F.Finite := by
    by_contra hinf
    set R := max C δ
    obtain ⟨N, hN⟩ := exists_nat_gt ((3 * R / δ) ^ (dK (IR I)))
    obtain ⟨T, hTF, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf N
    have := pack_K hP (IR I) T (fun u hu => by
        obtain ⟨y, -, -, rfl⟩ := hTF hu; exact uc_mem _ y) δ R hδ (le_max_right _ _)
      (fun u hu => by obtain ⟨y, -, hyC, rfl⟩ := hTF hu; exact hyC.trans (le_max_left _ _))
      (fun u hu v hv huv => by
        obtain ⟨y, hy, -, rfl⟩ := hTF hu
        obtain ⟨y', hy', -, rfl⟩ := hTF hv
        exact uc_sep hI hy hy' huv)
    rw [hTc] at this
    linarith
  let g : Vsp X.dim → Vsp X.dim := fun u => if h : u ∈ F then Classical.choose h else 0
  have hg : ∀ u ∈ F, g u ∈ X.L ∧ uc (IR I) (g u) = u := by
    intro u hu
    have := Classical.choose_spec hu
    simp only [g, dif_pos hu]
    exact ⟨this.1, this.2.2⟩
  refine ⟨∑ u ∈ hfin.toFinset, ‖p2 (IR I) (g u)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
    fun y hy hyC => ?_⟩
  have hu : uc (IR I) y ∈ F := ⟨y, hy, hyC, rfl⟩
  refine ⟨g (uc (IR I) y), (hg _ hu).1, (hg _ hu).2, ?_⟩
  exact Finset.single_le_sum (f := fun u => ‖p2 (IR I) (g u)‖) (fun _ _ => norm_nonneg _)
    (hfin.mem_toFinset.2 hu)
end ReciprocityTheory.ChartRestriction.G.I2.Col
