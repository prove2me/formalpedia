-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentAccumulate.zero_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:53.232274+00:00
-- url     : https://prove2.me/submissions/23acbacb-0a8e-4240-9cfb-fb0931673174

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentAccumulate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentAccumulate
theorem _root_.solution {p matrix terms count : ℕ}
    (hmain : P[p]?=some fillBody) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : matrix+terms*count≤lim.space) :
    Meets lim P p d [matrix,terms*count,0] μ (fillTime (terms*count))
      (fun _ ν => (∀ k<terms, ∀ i<count, ν (matrix+k*count+i)=0) ∧
        SameOutside μ ν matrix (terms*count)) := by
  apply (fill_meets hmain hw hspace).mono (by omega)
  rintro r ν ⟨hseg,hkeep⟩
  refine ⟨?_,hkeep⟩
  intro k hk i hi
  have hm := Nat.mul_le_mul_right count (show k+1≤terms by omega)
  simp only [Nat.add_mul,one_mul] at hm
  have hj : k*count+i<terms*count := by omega
  have hv := hseg (k*count+i) (by simpa using hj)
  simpa [List.getElem_replicate,Nat.add_assoc] using hv
end ThreeSum.LightTernaryMomentAccumulate
