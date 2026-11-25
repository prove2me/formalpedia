-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.exists_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:11.185582+00:00
-- url     : https://prove2.me/submissions/5e319413-21d8-4ee7-8156-c316a49404c5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {K U : Set (Fin D → ℂ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∃ χ : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      cthickening δ K ⊆ U ∧ EqOn χ 1 (cthickening (δ / 2) K) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨f, hfs, hf, hfr⟩ :=
    (isOpen_thickening (δ := δ) (E := K)).exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g, hgs, hg, hgr⟩ :=
    (isClosed_cthickening (δ := δ / 2) (E := K)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hts : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (by linarith) K
  have hpos : ∀ x, 0 < f x + g x := by
    intro x
    have hf0 : 0 ≤ f x := (hfr (mem_range_self x)).1
    have hg0 : 0 ≤ g x := (hgr (mem_range_self x)).1
    by_cases hx : x ∈ cthickening (δ / 2) K
    · have : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 (Ne.symm this)) hg0
    · have : g x ≠ 0 := by rw [← Function.mem_support, hgs]; exact hx
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 (Ne.symm this))
  have hsupp : tsupport (fun x => f x / (f x + g x)) ⊆ cthickening δ K := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    rw [← hfs]
    intro h
    apply hx
    simp [h]
  refine ⟨δ, hδ, fun x => f x / (f x + g x), hf.div (hf.add hg) (fun x => (hpos x).ne'),
    (hK.cthickening).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hδU, hδU, ?_⟩
  intro x hx
  have hg0 : g x = 0 := Function.notMem_support.1 (by rw [hgs]; exact fun h => h hx)
  have hf0 : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
  simp [hg0, hf0]
end ReciprocityTheory.AnForm.A
