-- Prove2me | solution 1 for ThreeSum.LightPairSearch.first_pair_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:42.95946+00:00
-- url     : https://prove2.me/submissions/65eec28c-bd6c-4104-969b-4ee6c2cec83f

import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
import Theorems.Thm_ThreeSum_LightPairSearch_first_spec
import Theorems.Thm_ThreeSum_LightPairSearch_goodCode_pair


set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightPairSearch
theorem _root_.solution (q : ℕ) (hq : 0<q) (good : ℕ → ℕ → Prop) [DecidableRel good] :
    (first (goodCode q good) (q*q)=0 ↔ ∀ u<q, ∀ v<q, ¬good u v) ∧
    (∀ code, first (goodCode q good) (q*q)=code+1 →
      code/q<q ∧ code%q<q ∧ good (code/q) (code%q) ∧
      ∀ u<q, ∀ v<q, u*q+v<code → ¬good u v) := by
  have hs := first_spec (goodCode q good) (q*q)
  constructor
  · rw [hs.1]
    constructor
    · intro h u hu v hv
      have ht : u*q+v<q*q := by
        have hh := Nat.mul_le_mul_right q (show u+1≤q by omega)
        nlinarith
      exact fun hg => h _ ht ((goodCode_pair q u v hq hv good).mpr hg)
    · intro h code hc
      exact h _ ((Nat.div_lt_iff_lt_mul hq).mpr hc) _ (Nat.mod_lt _ hq)
  · intro code hc
    obtain ⟨hcode,hgood,hmin⟩ := hs.2 code hc
    refine ⟨(Nat.div_lt_iff_lt_mul hq).mpr hcode,Nat.mod_lt _ hq,hgood,?_⟩
    intro u hu v hv hlt hg
    exact hmin _ hlt ((goodCode_pair q u v hq hv good).mpr hg)
end ThreeSum.LightPairSearch
