-- Prove2me | solution 1 for ThreeSum.LightMomentDeterminant.body_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:41.828021+00:00
-- url     : https://prove2.me/submissions/8d9e3184-f461-48e9-9278-c535003bea0b

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_wordBound_one
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_eq_zero_of_support_lt
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_support_ne_zero
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modified_det_zero_iff
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_safe
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_val
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


attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators
open FiniteMomentZeroDetector
namespace ThreeSum.LightMomentDeterminant
theorem _root_.solution (h : ℕ) {t : ℕ} (v w : Fin t → ℤ) (a : ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) (hth : t≤h)
    (atoms : ℕ → Expr) (σ : State) {lim : Limits} {P : Program} {d : ℕ}
    (U : ℤ) (hU : 0≤U)
    (hs : ∀ i, (atoms i).Safe lim σ)
    (hx : ∀ i, |(atoms i).val σ|≤U)
    (hword : wordBound U h≤lim.word)
    (hlead : ∀ k≤h, (leading k).eval (fun i => (atoms i).val σ)=(hankel v w k).det)
    (hmod : ∀ k≤h, (modified k).eval (fun i => (atoms i).val σ)=(modifiedHankel v w a k).det) :
    Ends lim P d (body atoms h) σ (time atoms h)
      (fun τ => τ.loc 0=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ τ.mem=σ.mem) := by
  classical
  induction h with
  | zero =>
    have ht : t=0 := by omega
    have hn : ¬∃ s, v s=a := by
      rintro ⟨s,hs⟩
      have := s.isLt
      omega
    unfold body time
    apply Ends.set (by change (0 : ℤ)≤lim.word; exact (by have := wordBound_one U 0; omega)) le_rfl
    simp [hn]
  | succ h ih =>
    have hwold : wordBound U h≤lim.word := (le_max_left _ _).trans hword
    have hwlead : (leading (h+1)).bound U≤lim.word :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hword)
    have hwmod : (modified (h+1)).bound U≤lim.word :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hword)
    have hslead := (leading (h+1)).compile_safe atoms σ hU hs hx hwlead
    have hsmod := (modified (h+1)).compile_safe atoms σ hU hs hx hwmod
    have hnonneg : 1≤lim.word := (wordBound_one U (h+1)).trans hword
    unfold body time
    refine Ends.iteLast ?_ ?_ ⟨hslead,by change (0 : ℤ)≤lim.word; omega⟩ (by simp [Cond.cost]; omega)
    · intro hz
      have hzero : (hankel v w (h+1)).det=0 := by
        change ((leading (h+1)).compile atoms).val σ=0 at hz
        rwa [Circuit.compile_val,hlead (h+1) (by omega)] at hz
      have hsmall : t≤h := by
        by_contra hn
        have ht : t=h+1 := by omega
        have hne := det_hankel_support_ne_zero v w hv hw
        rw [←ht] at hzero
        exact hne hzero
      exact (ih hsmall hwold (fun k hk => hlead k (by omega))
        (fun k hk => hmod k (by omega))).mono (by simp [Cond.cost]; omega) (fun τ hτ => hτ)
    · intro hnz
      have hnonzero : (hankel v w (h+1)).det≠0 := by
        change ¬((leading (h+1)).compile atoms).val σ=0 at hnz
        rwa [Circuit.compile_val,hlead (h+1) (by omega)] at hnz
      have ht : h+1=t := by
        by_contra hn
        have hlt : t<h+1 := by omega
        exact hnonzero (det_hankel_eq_zero_of_support_lt v w hlt)
      have hziff : ((modified (h+1)).compile atoms).val σ=0 ↔ ∃ s, v s=a := by
        rw [Circuit.compile_val,hmod (h+1) (by omega),ht]
        exact modified_det_zero_iff v w a hv hw
      refine Ends.iteLast ?_ ?_ ⟨hsmod,by change (0 : ℤ)≤lim.word; omega⟩ (by simp [Cond.cost]; omega)
      · intro hz
        have he : ∃ s, v s=a := hziff.mp hz
        apply Ends.set (by change (1 : ℤ)≤lim.word; omega) (by simp [Cond.cost,Expr.cost]; omega)
        simp [he]
      · intro hn
        have he : ¬∃ s, v s=a := fun he => hn (hziff.mpr he)
        apply Ends.set (by change (0 : ℤ)≤lim.word; omega) (by simp [Cond.cost,Expr.cost]; omega)
        simp [he]
end ThreeSum.LightMomentDeterminant
