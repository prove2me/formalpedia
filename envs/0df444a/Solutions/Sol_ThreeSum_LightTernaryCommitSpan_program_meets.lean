-- Prove2me | solution 1 for ThreeSum.LightTernaryCommitSpan.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:20.354564+00:00
-- url     : https://prove2.me/submissions/79a352d4-1786-445e-8590-a7a4e3d8d3af

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_copy_meets
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
open ThreeSum ThreeSum.LightTernaryCommitSpan
open Light
namespace ThreeSum.LightTernaryCommitSpan
theorem _root_.solution {lim : Limits} {oldCatalog newCatalog J rows d : ℕ}
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hApart : oldCatalog+rows*J≤newCatalog)
    (hSpace : newCatalog+rows*J≤lim.space) :
    Meets lim program 0 d [newCatalog,oldCatalog,rows*J] μ (time J rows)
      (fun _ ν => (∀ k<rows, ∀ i<J,
          ν (oldCatalog+J*k+i)=μ (newCatalog+J*k+i)) ∧
        SameOutside μ ν oldCatalog (rows*J)) := by
  have hc := copy_meets (P := program) (p := 0) (d := d) (μ := μ)
    (src := newCatalog) (dst := oldCatalog) (n := rows*J) rfl hw hSpace
      (by omega) (Or.inr hApart)
  apply hc.mono le_rfl
  intro r ν hv
  refine ⟨?_,hv.2⟩
  intro k hk i hi
  have hp := Nat.mul_le_mul_left J (show k+1≤rows by omega)
  rw [Nat.mul_add,Nat.mul_one] at hp
  have hindex : J*k+i<rows*J := by nlinarith [Nat.mul_comm J rows]
  simpa only [Nat.add_assoc] using hv.1 (J*k+i) hindex
end ThreeSum.LightTernaryCommitSpan
