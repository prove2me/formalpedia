-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:37:40.566045+00:00
-- url     : https://prove2.me/submissions/e6bf401d-b4f9-47a7-8595-208f3988241f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {f : ℕ} {ι : Type*} (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    {R η : ℝ} (hη : 0 < η)
    (hsep2 : ∀ a, (∀ k i j, ‖x a k i j‖ ≤ R) → ∀ b, (∀ k i j, ‖x b k i j‖ ≤ R) → a ≠ b →
      ∃ k i j, 2 * η ≤ ‖x b k i j - x a k i j‖) :
    ({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard ≤
      ((Fintype.piFinset fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
        Finset.Icc (-⌈R / η⌉) ⌈R / η⌉).card : ℕ∞) := by
  classical
  let S : Set ι := {a | ∀ k i j, ‖x a k i j‖ ≤ R}
  let val : ι → Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool → ℝ := fun a t =>
    if t.2.2.2 then (x a t.1 t.2.1 t.2.2.1).re else (x a t.1 t.2.1 t.2.2.1).im
  let φ : ι → (Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool → ℤ) := fun a t => ⌊val a t / η⌋
  have hmaps : ∀ a ∈ S, φ a ∈ Fintype.piFinset (fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
      Finset.Icc (-⌈R / η⌉) ⌈R / η⌉) := by
    intro a ha
    rw [Fintype.mem_piFinset]
    intro t
    rw [Finset.mem_Icc]
    have hb := ha t.1 t.2.1 t.2.2.1
    have hv : |val a t| ≤ R := by
      simp only [val]
      split_ifs
      · exact (Complex.abs_re_le_norm _).trans hb
      · exact (Complex.abs_im_le_norm _).trans hb
    rw [abs_le] at hv
    have h1 : -(R / η) ≤ val a t / η := by rw [← neg_div]; exact div_le_div_of_nonneg_right hv.1 hη.le
    have h2 : val a t / η ≤ R / η := div_le_div_of_nonneg_right hv.2 hη.le
    constructor
    · apply Int.le_floor.2
      push_cast
      linarith [Int.le_ceil (R / η)]
    · exact Int.cast_le.1 ((Int.floor_le _).trans (h2.trans (Int.le_ceil _)))
  have hinj : Set.InjOn φ S := by
    intro a ha b hb hab
    by_contra hne
    obtain ⟨k, i, j, hsep⟩ := hsep2 a ha b hb hne
    have hre := congrFun hab (k, i, j, true)
    have him := congrFun hab (k, i, j, false)
    simp only [φ, val, if_true, Bool.false_eq_true, if_false] at hre him
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hre
    have h2 := Int.abs_sub_lt_one_of_floor_eq_floor him
    rw [← sub_div, abs_div, abs_of_pos hη, div_lt_one hη] at h1 h2
    have h3 := Complex.norm_le_abs_re_add_abs_im (x b k i j - x a k i j)
    simp only [Complex.sub_re, Complex.sub_im] at h3
    rw [abs_sub_comm] at h1 h2
    linarith
  calc S.encard = (φ '' S).encard := hinj.encard_image.symm
    _ ≤ ((Fintype.piFinset fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
          Finset.Icc (-⌈R / η⌉) ⌈R / η⌉ : Finset _) : Set _).encard :=
        Set.encard_le_encard (by rintro _ ⟨a, ha, rfl⟩; exact hmaps a ha)
    _ = _ := Set.encard_coe_eq_coe_finsetCard _
end ReciprocityTheory.ChartRestriction.G.AR.Up
