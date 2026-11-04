-- Prove2me | solution 1 for ThreeSum.TernaryWeightedPhysicalSources.histogram_eq_machine_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:31.811396+00:00
-- url     : https://prove2.me/submissions/1ab93db7-44c7-435e-810a-da9ddc6966e2

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWeightedPhysicalSources
open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators
variable {ι κ : Type*}
namespace ThreeSum.TernaryWeightedPhysicalSources
theorem _root_.solution {N bank n r : ℕ}
    (enumeration : ℕ → TritWord N) (key : ℕ → ℕ) (weight : ℕ → ℤ)
    (hr : r < bank) (hkey : ∀ j < n, key j < bank)
    (hinj : ∀ i j, i < bank → j < bank → enumeration i=enumeration j → i=j) :
    histogram (range n) (fun i => enumeration (key i)) weight (enumeration r)=
      LightTernaryWeightedHistogram.total key weight r n := by
  classical
  unfold histogram LightTernaryWeightedHistogram.total
  apply sum_congr rfl
  intro j hj
  have he : enumeration (key j)=enumeration r ↔ key j=r := by
    exact ⟨hinj _ _ (hkey j (mem_range.mp hj)) hr,fun h => by rw [h]⟩
  simp only [he]
end ThreeSum.TernaryWeightedPhysicalSources
