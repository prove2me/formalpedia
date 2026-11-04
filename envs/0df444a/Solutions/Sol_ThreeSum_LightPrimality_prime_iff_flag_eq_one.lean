-- Prove2me | solution 1 for ThreeSum.LightPrimality.prime_iff_flag_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:56.030632+00:00
-- url     : https://prove2.me/submissions/2fc884e4-791d-4717-84ba-3557e03c6d90

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
import Theorems.Thm_ThreeSum_LightPrimality_flag_eq_one_iff
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
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimality
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ flag n (n-2) = 1 := by
  rw [Nat.prime_def_lt',flag_eq_one_iff]
  constructor
  · intro h j hj
    exact h.2 (j+2) (by omega) (by omega)
  · intro h
    refine ⟨hn,?_⟩
    intro m hm2 hmn
    have hh := h (m-2) (by omega)
    simpa only [Nat.sub_add_cancel hm2] using hh
end ThreeSum.LightPrimality
