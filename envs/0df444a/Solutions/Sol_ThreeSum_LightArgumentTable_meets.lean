-- Prove2me | solution 1 for ThreeSum.LightArgumentTable.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:31.880574+00:00
-- url     : https://prove2.me/submissions/04e138c5-5c0e-4c7e-9dd4-3675cf75943b

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Theorems.Thm_ThreeSum_LightArgumentTable_stores_ends
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightArgumentTable
open Light
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightArgumentTable
theorem _root_.solution {proc N : ℕ} (hp : P[proc]?=some (stores 0 N))
    (xs : List ℤ) (hlen : xs.length=N) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : base+N≤lim.space) :
    Meets lim P proc depth ((base : ℤ)::xs) μ (5*N)
      (fun z ν => z=(base : ℤ) ∧ Seg ν base xs ∧ SameOutside μ ν base N) := by
  apply Meets.of_body hp
  have hh := stores_ends (P := P) (depth := depth) xs base 0 (frame ((base : ℤ)::xs)) μ rfl
    (fun i hi => by simp [frame]) hw (by simpa [hlen] using hspace)
  rw [hlen] at hh
  apply hh.mono le_rfl
  rintro σ ⟨hloc,hseg,hkeep⟩
  refine ⟨?_,by simpa using hseg,by simpa using hkeep⟩
  rw [hloc]
  rfl
end ThreeSum.LightArgumentTable
