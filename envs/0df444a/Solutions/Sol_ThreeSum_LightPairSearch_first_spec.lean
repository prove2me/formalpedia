-- Prove2me | solution 1 for ThreeSum.LightPairSearch.first_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:08.901844+00:00
-- url     : https://prove2.me/submissions/b30441db-d452-4354-886d-da255bb9d036

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
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
open ThreeSum ThreeSum.LightPairSearch
set_option maxHeartbeats 300000
namespace ThreeSum.LightPairSearch
theorem _root_.solution (good : ℕ → Prop) [DecidablePred good] : ∀ k,
    (first good k=0 ↔ ∀ i<k, ¬good i) ∧
    (∀ s, first good k=s+1 → s<k ∧ good s ∧ ∀ i<s, ¬good i) := by
  intro k
  induction k with
  | zero => simp [first]
  | succ k ih =>
    by_cases hz : first good k=0
    · by_cases hg : good k
      · simp only [first,hz,hg,and_self,ite_true]
        constructor
        · constructor
          · omega
          · intro h; exact False.elim ((h k (by omega)) hg)
        · intro s hs
          have he : s=k := by omega
          subst s
          exact ⟨by omega,hg,ih.1.mp hz⟩
      · simp only [first,hz,hg,and_false,ite_false]
        constructor
        · simp only [true_iff]
          intro i hi
          by_cases hik : i<k
          · exact ih.1.mp hz i hik
          · have he : i=k := by omega
            simpa only [he] using hg
        · intro s hs; omega
    · simp only [first,hz,false_and,ite_false]
      constructor
      · constructor
        · exact fun h => False.elim h
        · intro h; exact False.elim (hz (ih.1.mpr (fun i hi => h i (by omega))))
      · intro s hs
        obtain ⟨hlt,hgood,hmin⟩ := ih.2 s hs
        exact ⟨by omega,hgood,hmin⟩
end ThreeSum.LightPairSearch
