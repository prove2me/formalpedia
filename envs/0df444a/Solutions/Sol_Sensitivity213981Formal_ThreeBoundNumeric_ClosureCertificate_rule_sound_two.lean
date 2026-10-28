-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.rule_sound_two
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:53:15.66914+00:00
-- url     : https://prove2.me/submissions/8134244a-d3c6-443e-8a44-e520d584a5b5

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]















theorem rejects_of_le (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (x : I → Bool) (hi : F i x = false) : F j x = false := by
  cases hj : F j x with
  | false => rfl
  | true => have hh := hF i j hij x hj; rw [hi] at hh; contradiction

theorem up_subset (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (x : I → Bool) :
    flipsTo (F j) true x ⊆ flipsTo (F i) true x := by
  classical
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF i j hij _ (Finset.mem_filter.mp ha).2⟩

theorem down_subset (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (x : I → Bool) :
    flipsTo (F i) false x ⊆ flipsTo (F j) false x := by
  classical
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    rejects_of_le F hF i j hij _ (Finset.mem_filter.mp ha).2⟩

theorem a_condition_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j : L) (hii' : i ≤  i') (v : ℕ) (h : ABound F i' j v) : ABound F i j v :=
  fun x hx => h x (rejects_of_le F hF i i' hii' x hx)

theorem a_target_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j j' : L) (hjj' : j ≤  j') (v : ℕ) (h : ABound F i j v) : ABound F i j' v :=
  fun x hx => (Finset.card_le_card (up_subset F hF j j' hjj' x)).trans (h x hx)

theorem b_target_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j : L) (hii' : i ≤  i') (v : ℕ) (h : BBound F i' j v) : BBound F i j v :=
  fun x hx => (Finset.card_le_card (down_subset F hF i i' hii' x)).trans (h x hx)

theorem b_condition_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j j' : L) (hjj' : j ≤  j') (v : ℕ) (h : BBound F i j v) : BBound F i j' v :=
  fun x hx => h x (hF j j' hjj' x hx)

theorem m_of_b (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ)
    (h : BBound F i j v) : MBound F i j k v := fun x hx _ => h x hx

theorem p_of_a (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ)
    (h : ABound F j k v) : PBound F i j k v := fun x _ hx => h x hx

theorem m_target_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j k : L) (hii' : i ≤  i') (v : ℕ)
    (h : MBound F i' j k v) : MBound F i j k v :=
  fun x hx hy => (Finset.card_le_card (down_subset F hF i i' hii' x)).trans (h x hx hy)

theorem p_target_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j k k' : L) (hkk' : k ≤  k') (v : ℕ)
    (h : PBound F i j k v) : PBound F i j k' v :=
  fun x hx hy => (Finset.card_le_card (up_subset F hF k k' hkk' x)).trans (h x hx hy)

theorem d_of_m_add_p (F : L → (I → Bool) → Bool) (i j k l : L) (m p : ℕ)
    (hm : MBound F i j k m) (hp : PBound F j k l p) : DBound F i j k l (m+p) := by
  intro x hx hy
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hm x hx hy) (hp x hx hy))

theorem d_down_target_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j k l : L) (hii' : i ≤  i') (v : ℕ)
    (h : DBound F i' j k l v) : DBound F i j k l v := by
  intro x hx hy
  apply (Finset.card_le_card (Finset.union_subset_union (down_subset F hF i i' hii' x)
    (Finset.Subset.refl _))).trans
  exact h x hx hy

theorem d_up_target_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j k l l' : L) (hll' : l ≤  l') (v : ℕ)
    (h : DBound F i j k l v) : DBound F i j k l' v := by
  intro x hx hy
  apply (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _)
    (up_subset F hF l l' hll' x))).trans
  exact h x hx hy

/-- Split the true condition into the next true state and the intervening gap. -/
theorem b_partition (F : L → (I → Bool) → Bool) (i j k : L) (b m : ℕ)
    (hb : BBound F i k b) (hm : MBound F i j k m) : BBound F i j (max b m) := by
  intro x hx
  cases hk : F k x with
  | false => exact (hm x hx hk).trans (le_max_right _ _)
  | true => exact (hb x hk).trans (le_max_left _ _)

/-- Split a false condition into the preceding false state and the intervening gap. -/
theorem a_partition (F : L → (I → Bool) → Bool) (i j k : L) (a p : ℕ)
    (ha : ABound F i k a) (hp : PBound F i j k p) : ABound F j k (max a p) := by
  intro x hx
  cases hi : F i x with
  | false => exact (ha x hi).trans (le_max_left _ _)
  | true => exact (hp x hi hx).trans (le_max_right _ _)



















end
end ThreeBoundProfiles






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]









theorem next_val (j : Fin n) (h : j.val+1 <  n) : (next j).val = j.val+1 := by
  simp [next,h]

theorem self_le_next (j : Fin n) : j ≤  next j := by
  unfold next
  split_ifs <;> simp only [Fin.le_iff_val_le_val] <;> omega

theorem prev_le_self (j : Fin n) : prev j ≤  j := by
  exact Nat.sub_le _ _

theorem next_le_of_lt (i j : Fin n) (h : i <  j) : next i ≤  j := by
  have hi : i.val+1 <  n := by have hj := j.isLt; exact lt_of_le_of_lt h hj
  change (next i).val ≤  j.val
  rw [next_val i hi]
  exact h

theorem le_prev_of_lt (i j : Fin n) (h : i <  j) : i ≤  prev j := by
  change i.val ≤  j.val-1
  have hh : i.val <  j.val := h
  omega

theorem next_lt_n_of_lt (i j : Fin n) (h : i <  j) : i.val+1 <  n :=
  lt_of_le_of_lt h j.isLt



















































end
end ThreeBoundFullProfile




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- A small trusted checker for exact closure certificates.

Each node cites either an input bound or one of the already proved semantic
closure rules, with references strictly earlier in the finite program. The
checker validates coordinates and integer inequalities. A successful check
therefore proves a semantic upper profile for every natural scaling of the
input. No executable output is used as an unverified premise. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumeric.ClosureCertificate
open ThreeBoundProfiles ThreeBoundFullProfile

variable {n : ℕ}









theorem rule_sound_two {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (r : Rule n)
    (x y : ℕ) (hx : Sem F (source₀ r) x) (hy : Sem F (source₁ r) y) :
    Sem F r.target (combine r x y) := by
  cases r with
  | aCond i j h =>
      intro _
      exact a_condition_weaken F hF i (next i) j (self_le_next i) _
        (hx (next_le_of_lt i j h))
  | aTarget i j h =>
      intro _
      exact a_target_strengthen F hF i (prev j) j (prev_le_self j) _
        (hx (le_prev_of_lt i j h))
  | bTarget i j h =>
      intro _
      exact b_target_weaken F hF i (next i) j (self_le_next i) _
        (hx (next_le_of_lt i j h))
  | bCond i j h =>
      intro _
      exact b_condition_strengthen F hF i (prev j) j (prev_le_self j) _
        (hx (le_prev_of_lt i j h))
  | mFromB i j h hn =>
      intro _ _
      exact m_of_b F i j (next j) _ (hx h)
  | mTarget i j h hn =>
      intro _ _
      exact m_target_weaken F hF i (next i) j (next j) (self_le_next i) _
        (hx (next_le_of_lt i j h) hn)
  | pFromA j l h =>
      intro _
      exact p_of_a F j (next j) l _ (hx (next_le_of_lt j l h))
  | pTarget j l h =>
      have hj : j <  prev l := by change j.val <  l.val-1; omega
      intro _
      exact p_target_strengthen F hF j (next j) (prev l) l (prev_le_self l) _ (hx hj)
  | dFromMP i j l h hl =>
      intro _ _
      exact d_of_m_add_p F i j (next j) l _ _
        (hx h (next_lt_n_of_lt j l hl)) (hy hl)
  | dDown i j l h hl =>
      intro _ _
      exact d_down_target_weaken F hF i (next i) j (next j) l (self_le_next i) _
        (hx (next_le_of_lt i j h) hl)
  | dUp i j l h hl =>
      have hj : j <  prev l := by change j.val <  l.val-1; omega
      intro _ _
      exact d_up_target_strengthen F hF i j (next j) (prev l) l (prev_le_self l) _
        (hx h hj)
  | bPartition i j h hn =>
      intro _
      exact b_partition F i j (next j) _ _
        (hx (h.trans (self_le_next j))) (hy h hn)
  | aPartition j l h =>
      intro _
      exact a_partition F j (next j) l _ _ (hx h.le) (hy h)



































end ThreeBoundNumeric.ClosureCertificate



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (r : Sensitivity213981Formal.ThreeBoundFullProfile.Rule n) (x y : Nat)
  (hx :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
      (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.source₀ n r) x)
  (hy :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
      (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.source₁ n r) y),
  @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
    (@Sensitivity213981Formal.ThreeBoundFullProfile.Rule.target n r)
    (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.combine n r x y) := @Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.rule_sound_two
