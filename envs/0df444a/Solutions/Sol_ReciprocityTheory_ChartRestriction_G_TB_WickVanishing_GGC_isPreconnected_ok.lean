-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:02.339722+00:00
-- url     : https://prove2.me/submissions/771e5793-dfb1-4bd8-92e9-f0b99cb4563c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_isPreconnected_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_det_ne_of_ok
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_ok_mask
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_ok_of_blk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_mask_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_mask_zero_blk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_continuous_mask

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
variable {p0 : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {ι : Type*} [Fintype ι] :
    IsPreconnected {y : ι → Matrix (Fin r) (Fin r) ℂ | ∀ i, Ok p0 (y i)} := by
  let V : Set (ι → Matrix (Fin r) (Fin r) ℂ) :=
    {x | ∀ i (k a : Fin r), ¬((k : ℕ) < p0 ↔ (a : ℕ) < p0) → x i k a = 0}
  have hV : ∀ a ∈ V, ∀ b ∈ V, ∀ z : ℂ, (1 - z) • a + z • b ∈ V := by
    intro a ha b hb z i k l hkl
    simp [ha i k l hkl, hb i k l hkl]
  have hBD := isPreconnected_det_ne V hV
  have hsub : {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} ⊆ {y : ι → Matrix (Fin r) (Fin r) ℂ | ∀ i, Ok p0 (y i)} :=
    fun x hx i => ok_of_blk (hx.1 i) (hx.2 i)
  have h1 : (1 : ι → Matrix (Fin r) (Fin r) ℂ) ∈ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} := by
    refine ⟨fun i k a hka => ?_, fun i => by simp⟩
    have hne : k ≠ a := by
      rintro rfl
      exact hka Iff.rfl
    simp [Matrix.one_apply_ne hne]
  refine isPreconnected_of_forall 1 fun y hy => ?_
  let γ : ℝ → ι → Matrix (Fin r) (Fin r) ℂ := fun t i => mask p0 t (y i)
  have hγc : Continuous γ := continuous_pi fun i => continuous_mask (y i)
  have hγ0 : γ 0 ∈ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} :=
    ⟨fun i k a hka => mask_zero_blk (y i) hka, fun i => det_ne_of_ok (ok_mask (hy i) le_rfl zero_le_one)⟩
  refine ⟨γ '' Set.Icc 0 1 ∪ {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0}, ?_, Or.inr (hsub h1 |> fun _ => h1),
    Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, funext fun i => mask_one (y i)⟩, ?_⟩
  · rintro x (⟨t, ⟨ht0, ht1⟩, rfl⟩ | hx)
    · exact fun i => ok_mask (hy i) ht0 ht1
    · exact hsub hx
  · exact IsPreconnected.union (γ 0) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ hγ0
      (isPreconnected_Icc.image γ hγc.continuousOn) hBD
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
