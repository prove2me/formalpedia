-- Prove2me | solution 1 for SensitivityJointCover.endpoint22_phase2_parent_bound
-- status  : ACCEPTED   (prove)
-- author  : @jennyuxi
-- created : 2026-11-13T05:13:17.378624+00:00
-- url     : https://prove2.me/submissions/6dc1fd9c-4370-4ac3-aacf-7ca773805531

import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Theorems.Thm_SensitivityJointCover_endpoint22_phase1_bound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Lean
open Sensitivity213981Formal Sensitivity213981Formal.ThreeBoundWitness
open Sensitivity213981Formal.ThreeBoundProfiles
open scoped Classical
set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

private theorem parent_iff (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent, decide_eq_true_eq, ordinaryStage,
    Bool.and_eq_true]
  constructor
  · rintro ⟨v, hc, h0, h1⟩
    refine ⟨v, ?_, hc⟩
    intro c
    cases c <;> assumption
  · rintro ⟨v, ht, hc⟩
    exact ⟨v, hc, ht false, ht true⟩

private theorem child_flip_same (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (i : I) :
    child (flip x {((w,c),i)}) w c = flip (child x w c) {i} := by
  funext j
  simp [child, _root_.OAI.Paper320.flip]

private theorem child_flip_other (x : ((V × Bool) × I) → Bool)
    (w v : V) (c d : Bool) (i : I) (h : (v,d) ≠ (w,c)) :
    child (flip x {((w,c),i)}) v d = child x v d := by
  funext j
  simp [child, _root_.OAI.Paper320.flip, h]

private theorem guard_subset_insert (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (r w : V) (c : Bool) (i : I) :
    guardFailures S F g x r ⊆
      insert w (guardFailures S F g (flip x {((w,c),i)}) r) := by
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · apply Finset.mem_insert.mpr
    right
    have hh := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hh.2.1, ?_⟩
    rw [child_flip_other x w z c (S.label r z) i (by
      intro h
      exact hzw (congrArg Prod.fst h))]
    exact hh.2.2

private theorem guard_self_unchanged (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (i : I) :
    guardFailures S F g (flip x {((w,c),i)}) w = guardFailures S F g x w := by
  ext z
  simp only [guardFailures, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hz : S.Adj w z
  · have hzw : z ≠ w := by
      intro h
      subst z
      exact S.loopless w hz
    rw [child_flip_other x w z c (S.label w z) i (by
      intro h
      exact hzw (congrArg Prod.fst h))]
  · simp [hz]

private theorem repair_shape (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t u g : L) (htu : t ≤ u)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (i : I)
    (hmid : ordinaryParent S F t g 3 x = false)
    (hnew : ordinaryParent S F u g 0 (flip x {((w,c),i)}) = true) :
    (guardFailures S F g x w).card = 0 ∧
    F t (child x w c) = false ∧
    F u (child x w (!c)) = true ∧
    F u (flip (child x w c) {i}) = true := by
  obtain ⟨r, hr, hcount⟩ := (parent_iff S F u g 0 _).1 hnew
  have hr0 : (guardFailures S F g (flip x {((w,c),i)}) r).card = 0 := by omega
  have hrw : r = w := by
    by_contra hne
    have htargets : ∀ d : Bool, F t (child x r d) = true := by
      intro d
      have hd := hr d
      rw [child_flip_other x w r c d i (by
        intro h
        exact hne (congrArg Prod.fst h))] at hd
      exact hF t u htu _ hd
    have hle := Finset.card_le_card (guard_subset_insert S F g x r w c i)
    have hins := Finset.card_insert_le w (guardFailures S F g (flip x {((w,c),i)}) r)
    have hc : (guardFailures S F g x r).card ≤ 3 := by omega
    have htrue := (parent_iff S F t g 3 x).2 ⟨r, htargets, hc⟩
    rw [hmid] at htrue
    contradiction
  subst r
  rw [guard_self_unchanged] at hr0
  have hother := hr (!c)
  rw [child_flip_other x w w c (!c) i (by cases c <;> simp)] at hother
  have hown := hr c
  rw [child_flip_same] at hown
  refine ⟨hr0, ?_, hother, hown⟩
  cases hc : F t (child x w c) with
  | false => rfl
  | true =>
    have htargets : ∀ d : Bool, F t (child x w d) = true := by
      intro d
      by_cases hd : d = c
      · simpa [hd] using hc
      · have heq : d = !c := by cases c <;> cases d <;> simp_all
        simpa [heq] using hF t u htu _ hother
    have htrue := (parent_iff S F t g 3 x).2 ⟨w, htargets, by omega⟩
    rw [hmid] at htrue
    contradiction

private def lift (v : V) (c : Bool) (T : Finset I) : Finset ((V × Bool) × I) :=
  T.map ⟨fun i => ((v,c),i), by intro i j h; exact (Prod.mk.inj h).2⟩

private theorem mem_lift (v w : V) (c d : Bool) (T : Finset I) (i : I) :
    ((w,d),i) ∈ lift v c T ↔ w = v ∧ d = c ∧ i ∈ T := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_map.mp h
    have hw := congrArg (fun p : ((V × Bool) × I) => p.1.1) he
    have hc := congrArg (fun p : ((V × Bool) × I) => p.1.2) he
    have hi := congrArg (fun p : ((V × Bool) × I) => p.2) he
    change j = i at hi
    exact ⟨hw.symm,hc.symm,hi ▸ hj⟩
  · rintro ⟨rfl,rfl,hi⟩
    exact Finset.mem_map.mpr ⟨i,hi,rfl⟩

private def cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
  (lift v false (flipsTo (F t) false (child x v false)) ∪
   lift v true (flipsTo (F t) false (child x v true))) ∪
  ((Finset.univ.filter (S.Adj v)) \ guardFailures S F g x v).biUnion fun w =>
    lift w (S.label v w) (flipsTo (F g) true (child x w (S.label v w)))

private theorem destruction_in_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (i : I)
    (hv : ordinaryRow S F t g 4 x v)
    (hnew : ordinaryParent S F t g 4 (flip x {((w,c),i)}) = false) :
    ((w,c),i) ∈ cover S F t g x v := by
  by_cases hwv : w = v
  · subst w
    have hfalse : F t (flip (child x v c) {i}) = false := by
      cases hf : F t (flip (child x v c) {i}) with
      | false => rfl
      | true =>
        have ht : ∀ d : Bool, F t (child (flip x {((v,c),i)}) v d) = true := by
          intro d
          by_cases hd : d = c
          · subst d
            simpa only [child_flip_same] using hf
          · rw [child_flip_other x v v c d i (by
              intro he
              exact hd (congrArg Prod.snd he))]
            exact hv.1 d
        have hc : (guardFailures S F g (flip x {((v,c),i)}) v).card ≤ 4 := by
          rw [guard_self_unchanged]
          exact hv.2
        have htrue := (parent_iff S F t g 4 _).2 ⟨v, ht, hc⟩
        rw [hnew] at htrue
        contradiction
    have hi : i ∈ flipsTo (F t) false (child x v c) := by
      simpa only [flipsTo, Finset.mem_filter, Finset.mem_univ, true_and] using hfalse
    apply Finset.mem_union_left
    cases c
    · exact Finset.mem_union_left _ ((mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩)
    · exact Finset.mem_union_right _ ((mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩)
  · have hextra : S.Adj v w ∧ w ∉ guardFailures S F g x v ∧
        S.label v w = c ∧ F g (flip (child x w c) {i}) = true := by
      by_contra hn
      have hsub : guardFailures S F g (flip x {((w,c),i)}) v ⊆ guardFailures S F g x v := by
        intro z hz
        have hh := (Finset.mem_filter.mp hz).2
        by_cases hzw : z = w
        · subst z
          by_cases hw : w ∈ guardFailures S F g x v
          · exact hw
          · by_cases he : S.label v w = c
            · apply False.elim
              apply hn
              refine ⟨hh.1, hw, he, ?_⟩
              have hf := hh.2
              rw [he, child_flip_same] at hf
              exact hf
            · have hf := hh.2
              rw [child_flip_other x w w c (S.label v w) i (by
                intro h
                exact he (congrArg Prod.snd h))] at hf
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1, hf⟩
        · have hf := hh.2
          rw [child_flip_other x w z c (S.label v z) i (by
            intro h
            exact hzw (congrArg Prod.fst h))] at hf
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1, hf⟩
      have ht : ∀ d : Bool, F t (child (flip x {((w,c),i)}) v d) = true := by
        intro d
        rw [child_flip_other x w v c d i (by
          intro h
          exact hwv (congrArg Prod.fst h).symm)]
        exact hv.1 d
      have htrue := (parent_iff S F t g 4 _).2 ⟨v, ht, (Finset.card_le_card hsub).trans hv.2⟩
      rw [hnew] at htrue
      contradiction
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hextra.1⟩,hextra.2.1⟩, ?_⟩
    apply (mem_lift w w (S.label v w) c _ i).2
    refine ⟨rfl, hextra.2.2.1.symm, ?_⟩
    simp only [flipsTo, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [hextra.2.2.1] using hextra.2.2.2

private theorem repair_outside_in_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t u g : L) (hgt : g ≤ t) (htu : t ≤ u)
    (htor : ∀ r z, r ≠ z → (S.Adj r z ↔ ¬ S.Adj z r))
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (i : I)
    (hv : ordinaryRow S F t g 4 x v)
    (hmid : ordinaryParent S F t g 3 x = false)
    (hnew : ordinaryParent S F u g 0 (flip x {((w,c),i)}) = true)
    (hnot : w ∉ guardFailures S F g x v) :
    ((w,c),i) ∈ cover S F t g x v := by
  obtain ⟨hz, htfalse, huother, hunew⟩ := repair_shape S F hF t u g htu x w c i hmid hnew
  have hwv : w ≠ v := by
    intro h
    subst w
    have hh := hv.1 c
    rw [htfalse] at hh
    contradiction
  have hno : ¬ S.Adj w v := by
    intro h
    have hh : v ∈ guardFailures S F g x w := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, h, hF g t hgt _ (hv.1 (S.label w v))⟩
    have hempty := Finset.card_eq_zero.mp hz
    rw [hempty] at hh
    exact Finset.notMem_empty _ hh
  have hadj := (htor v w (Ne.symm hwv)).2 hno
  have hgfalse : F g (child x w (S.label v w)) = false := by
    cases hh : F g (child x w (S.label v w)) with
    | false => rfl
    | true => exact False.elim (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,hh⟩))
  have hlab : S.label v w = c := by
    have hgother := hF g u (hgt.trans htu) _ huother
    cases c <;> cases he : S.label v w <;> simp_all
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩,hnot⟩,?_⟩
  apply (mem_lift w w (S.label v w) c _ i).2
  refine ⟨rfl,hlab.symm,?_⟩
  simp only [flipsTo, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hlab]
  exact hF g u (hgt.trans htu) _ hunew

private theorem card_biUnion_mul {A B : Type} [DecidableEq A] [DecidableEq B]
    (T : Finset A) (f : A → Finset B) (a : ℕ)
    (h : ∀ x ∈ T, (f x).card ≤ a) : (T.biUnion f).card ≤ T.card*a := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert x T hx ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hx, Nat.add_mul, Nat.one_mul]
    have h1 := h x (Finset.mem_insert_self _ _)
    have h2 := ih (fun z hz => h z (Finset.mem_insert_of_mem hz))
    have hh := Finset.card_union_le (f x) (T.biUnion f)
    omega

private theorem exceptional_row_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t u g : L) (htu : t ≤ u) (s : ℕ) (hs : ABound F t u s)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (hmid : ordinaryParent S F t g 3 x = false) :
    ((flipsTo (ordinaryParent S F u g 0) true x).filter fun p => p.1.1 = w).card ≤ s := by
  let T := (flipsTo (ordinaryParent S F u g 0) true x).filter fun p => p.1.1 = w
  by_cases hT : T.Nonempty
  · obtain ⟨⟨⟨r,c⟩,i⟩, hp⟩ := hT
    have hpr := (Finset.mem_filter.mp hp).2
    change r = w at hpr
    subst r
    have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    obtain ⟨_, hfalse, hother, _⟩ := repair_shape S F hF t u g htu x w c i hmid hn
    have hsub : T ⊆ lift w c (flipsTo (F u) true (child x w c)) := by
      rintro ⟨⟨r,d⟩,j⟩ hj
      have hr := (Finset.mem_filter.mp hj).2
      change r = w at hr
      subst r
      have hn' := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      obtain ⟨_, hfalse', _, hpost⟩ := repair_shape S F hF t u g htu x w d j hmid hn'
      have hdc : d = c := by
        by_contra hdc
        have heq : d = !c := by cases c <;> cases d <;> simp_all
        have htrue := hF t u htu _ hother
        rw [← heq,hfalse'] at htrue
        contradiction
      subst d
      apply (mem_lift w w c c _ j).2
      exact ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpost⟩⟩
    have hh := (Finset.card_le_card hsub).trans (by
      simpa only [lift,Finset.card_map] using hs (child x w c) hfalse)
    exact hh
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ s
    rw [he]
    simp

private theorem cover_card (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (degree b a : ℕ) (hb : BBound F t t b) (ha : ABound F g g a)
    (hd : ∀ v, (Finset.univ.filter (S.Adj v)).card = degree)
    (x : ((V × Bool) × I) → Bool) (v : V)
    (hv : ordinaryRow S F t g 4 x v) (heq : (guardFailures S F g x v).card = 4) :
    (cover S F t g x v).card ≤ 2*b+(degree-4)*a := by
  let B := guardFailures S F g x v
  let T := (Finset.univ.filter (S.Adj v)) \ B
  have hB : B ⊆ Finset.univ.filter (S.Adj v) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.1⟩
  have hTc : T.card = degree-4 := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset hB,hd,heq]
  have hguard : ∀ w ∈ T,
      (lift w (S.label v w) (flipsTo (F g) true (child x w (S.label v w)))).card ≤ a := by
    intro w hw
    have hn := (Finset.mem_sdiff.mp hw).2
    have hadj := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw).1).2
    have hz : F g (child x w (S.label v w)) = false := by
      cases hh : F g (child x w (S.label v w)) with
      | false => rfl
      | true => exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,hh⟩))
    simpa only [lift,Finset.card_map] using ha _ hz
  have hc := card_biUnion_mul T
    (fun w => lift w (S.label v w) (flipsTo (F g) true (child x w (S.label v w)))) a hguard
  rw [hTc] at hc
  have h0 : (lift v false (flipsTo (F t) false (child x v false))).card ≤ b := by
    simpa only [lift,Finset.card_map] using hb _ (hv.1 false)
  have h1 : (lift v true (flipsTo (F t) false (child x v true))).card ≤ b := by
    simpa only [lift,Finset.card_map] using hb _ (hv.1 true)
  have h01 := Finset.card_union_le
    (lift v false (flipsTo (F t) false (child x v false)))
    (lift v true (flipsTo (F t) false (child x v true)))
  have hsum := Finset.card_union_le
    (lift v false (flipsTo (F t) false (child x v false)) ∪
      lift v true (flipsTo (F t) false (child x v true)))
    (T.biUnion fun w => lift w (S.label v w) (flipsTo (F g) true (child x w (S.label v w))))
  change _ ≤ _ at hsum
  change (cover S F t g x v).card ≤ _
  dsimp only [cover]
  dsimp only [T,B] at hc hsum
  omega

theorem joint_cover_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t u g : L) (hgt : g ≤ t) (htu : t ≤ u)
    (htor : ∀ r z, r ≠ z → (S.Adj r z ↔ ¬ S.Adj z r))
    (degree b a s : ℕ)
    (hd : ∀ v, (Finset.univ.filter (S.Adj v)).card = degree)
    (hb : BBound F t t b) (ha : ABound F g g a) (hs : ABound F t u s)
    (x : ((V × Bool) × I) → Bool)
    (hweak : ordinaryParent S F t g 4 x = true)
    (hmid : ordinaryParent S F t g 3 x = false) :
    ((flipsTo (ordinaryParent S F t g 4) false x) ∪
      (flipsTo (ordinaryParent S F u g 0) true x)).card ≤
      2*b+(degree-4)*a+4*s := by
  obtain ⟨v,hv⟩ := (parent_iff S F t g 4 x).1 hweak
  have heq : (guardFailures S F g x v).card = 4 := by
    by_contra hne
    have htrue := (parent_iff S F t g 3 x).2 ⟨v,hv.1,by have hc := hv.2; omega⟩
    rw [hmid] at htrue
    contradiction
  let B := guardFailures S F g x v
  let P := flipsTo (ordinaryParent S F u g 0) true x
  let E := B.biUnion fun w => P.filter fun bit => bit.1.1 = w
  have hc := cover_card S F t g degree b a hb ha hd x v hv heq
  have hE : E.card ≤ 4*s := by
    have hh := card_biUnion_mul B (fun w => P.filter fun bit => bit.1.1 = w) s
      (fun w _ => exceptional_row_bound S F hF t u g htu s hs x w hmid)
    simpa only [B,E,heq] using hh
  have hsub : flipsTo (ordinaryParent S F t g 4) false x ∪ P ⊆ cover S F t g x v ∪ E := by
    rintro ⟨⟨w,c⟩,i⟩ hp
    rcases Finset.mem_union.mp hp with hM | hP
    · apply Finset.mem_union_left
      exact destruction_in_cover S F t g x v w c i hv (Finset.mem_filter.mp hM).2
    · have hn := (Finset.mem_filter.mp hP).2
      by_cases hw : w ∈ B
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨w,hw,Finset.mem_filter.mpr ⟨hP,rfl⟩⟩
      · apply Finset.mem_union_left
        exact repair_outside_in_cover S F hF t u g hgt htu htor x v w c i hv hmid hn hw
  have hcard := Finset.card_le_card hsub
  have hsum := Finset.card_union_le (cover S F t g x v) E
  change _ ≤ _ at hcard
  dsimp only [P] at hcard
  omega

end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical

private theorem parent_specialize {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]
    (S : Stage L I V) (F : L → (I → Bool) → Bool) (l t g : L) (q : ℕ)
    (hg : S.guard l = g) (hq : S.tolerance l = q)
    (ht : ∀ d y z, S.target l d y z = (F t y && F t z)) :
    parent S F l = ordinaryParent S F t g q := by
  funext x
  apply Bool.eq_iff_iff.mpr
  change parent S F l x = true ↔ ordinaryParent S F t g q x = true
  rw [parent_iff]
  change (decide (∃ v, (failed S F l x v).card ≤ S.tolerance l ∧
    S.target l (failed S F l x v).card (child x v false) (child x v true) = true)) = true ↔ _
  simp only [decide_eq_true_eq,hq,ht,Bool.and_eq_true]
  have hf (v : V) : failed S F l x v = guardFailures S F g x v := by
    simp only [failed,guardFailures,hg]
  simp only [hf]
  constructor
  · rintro ⟨v,hc,h0,h1⟩
    refine ⟨v,?_,hc⟩
    intro c
    cases c <;> assumption
  · rintro ⟨v,ht',hc⟩
    exact ⟨v,hc,ht' false,ht' true⟩

-- This statement uses the actual second-phase recipe, not a replacement family.
theorem endpoint22_phase1_joint_cover {I : Type} [Fintype I]
    (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬ Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool)
    (htor : ∀ r z, r ≠ z → (Adj r z ↔ ¬ Adj z r))
    (hd : ∀ v, (Finset.univ.filter (Adj v)).card = 2795)
    (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (b a s : ℕ) (hb : BBound F 12 12 b) (ha : ABound F 10 10 a)
    (hs : ABound F 12 13 s)
    (x : ((Fin 5591 × Bool) × I) → Bool) :
    let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (1 : Fin 4)).stage F
    let G := parent S F
    G 1 x = true → G 2 x = false →
      ((flipsTo (G 1) false x) ∪ (flipsTo (G 11) true x)).card ≤
        2*b+2791*a+4*s := by
  dsimp only
  let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (1 : Fin 4)).stage F
  have ht1 : ∀ d y z, S.target 1 d y z = (F 12 y && F 12 z) := by
    intro d y z
    change (F 12 y && F 12 z && (F 12 y || F 12 z)) = _
    cases F 12 y <;> cases F 12 z <;> rfl
  have ht2 : ∀ d y z, S.target 2 d y z = (F 12 y && F 12 z) := by
    intro d y z
    dsimp [S, MinMaxRecipe.stage,minmaxTarget,Sensitivity5591Endpoint22.recipe,
      Sensitivity5591Endpoint22.entry,Sensitivity5591Endpoint22.entries1,
      Sensitivity5591Endpoint22.Entry.threshold,Sensitivity5591Endpoint22.Entry.upper]
    cases hy : F 12 y <;> cases hz : F 12 z <;> simp [hy,hz]
  have ht11 : ∀ d y z, S.target 11 d y z = (F 13 y && F 13 z) := by
    intro d y z
    dsimp [S, MinMaxRecipe.stage,minmaxTarget,Sensitivity5591Endpoint22.recipe,
      Sensitivity5591Endpoint22.entry,Sensitivity5591Endpoint22.entries1,
      Sensitivity5591Endpoint22.Entry.threshold,Sensitivity5591Endpoint22.Entry.upper]
    cases hy : F 13 y <;> cases hz : F 13 z <;> simp [hy,hz]
  have e1 := parent_specialize S F 1 12 10 4 (by rfl) (by rfl) ht1
  have e2 := parent_specialize S F 2 12 10 3 (by rfl) (by rfl) ht2
  have e11 := parent_specialize S F 11 13 10 0 (by rfl) (by rfl) ht11
  change parent S F 1 x = true → parent S F 2 x = false → _
  rw [e1,e2,e11]
  intro h1 h2
  have H := joint_cover_bound S F hF 12 13 10 (by decide) (by decide)
    htor 2795 b a s hd hb ha hs x h1 h2
  convert H using 1 <;> congr 1 <;> ext p <;> simp only [Finset.mem_union]

end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private theorem guard2_false (S : Stage (Fin 22) I V)
    (F : Fin 22 → (I → Bool) → Bool) (x : ((V × Bool) × I) → Bool) (v w : V)
    (hv : ordinaryRow S F 17 2 0 x v) (hw : S.Adj v w) :
    F 2 (child x w (S.label v w)) = false := by
  have he : guardFailures S F 2 x v = ∅ := Finset.card_eq_zero.mp (by have hh := hv.2; omega)
  cases hf : F 2 (child x w (S.label v w)) with
  | false => rfl
  | true =>
    have hm : w ∈ guardFailures S F 2 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw,hf⟩
    rw [he] at hm
    exact False.elim (Finset.notMem_empty _ hm)

private theorem guard11_empty (S : Stage (Fin 22) I V)
    (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F 17 2 0 x v) :
    guardFailures S F 11 x v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hh := (Finset.mem_filter.mp hw).2
  have hf := hF 2 11 (by decide) _ hh.2
  rw [guard2_false S F x v w hv hh.1] at hf
  contradiction

private theorem destruction14_in_cover (S : Stage (Fin 22) I V)
    (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (weak : (((V × Bool) × I) → Bool) → Bool)
    (accept : ∀ y r, (∀ d, F 13 (child y r d) = true) →
      (∃ d, F 14 (child y r d) = true) → guardFailures S F 11 y r = ∅ → weak y = true)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (i : I)
    (hv : ordinaryRow S F 17 2 0 x v)
    (hnew : weak (flip x {((w,c),i)}) = false) :
    ((w,c),i) ∈ cover S F 13 11 x v := by
  have hempty := guard11_empty S F hF x v hv
  by_cases hwv : w = v
  · subst w
    have hf : F 13 (flip (child x v c) {i}) = false := by
      cases hh : F 13 (flip (child x v c) {i}) with
      | false => rfl
      | true =>
        have ht : ∀ d, F 13 (child (flip x {((v,c),i)}) v d) = true := by
          intro d
          by_cases hd : d = c
          · subst d; simpa only [child_flip_same] using hh
          · rw [child_flip_other x v v c d i (by intro he; exact hd (congrArg Prod.snd he))]
            exact hF 13 17 (by decide) _ (hv.1 d)
        have hu : F 14 (child (flip x {((v,c),i)}) v (!c)) = true := by
          rw [child_flip_other x v v c (!c) i (by cases c <;> simp)]
          exact hF 14 17 (by decide) _ (hv.1 (!c))
        have hg : guardFailures S F 11 (flip x {((v,c),i)}) v = ∅ := by
          rw [guard_self_unchanged,hempty]
        have htrue := accept _ v ht ⟨!c,hu⟩ hg
        rw [hnew] at htrue
        contradiction
    have hi : i ∈ flipsTo (F 13) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
    apply Finset.mem_union_left
    cases c
    · exact Finset.mem_union_left _ ((mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩)
    · exact Finset.mem_union_right _ ((mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩)
  · have ht : ∀ d, F 13 (child (flip x {((w,c),i)}) v d) = true := by
      intro d
      rw [child_flip_other x w v c d i (by intro he; exact hwv (congrArg Prod.fst he).symm)]
      exact hF 13 17 (by decide) _ (hv.1 d)
    have hu : F 14 (child (flip x {((w,c),i)}) v false) = true := by
      rw [child_flip_other x w v c false i (by intro he; exact hwv (congrArg Prod.fst he).symm)]
      exact hF 14 17 (by decide) _ (hv.1 false)
    have hne : guardFailures S F 11 (flip x {((w,c),i)}) v ≠ ∅ := by
      intro he
      have htrue := accept _ v ht ⟨false,hu⟩ he
      rw [hnew] at htrue
      contradiction
    obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hh := (Finset.mem_filter.mp hz).2
    have hzw : z = w := by
      by_contra hn
      have hf := hh.2
      rw [child_flip_other x w z c (S.label v z) i (by intro he; exact hn (congrArg Prod.fst he))] at hf
      have hm : z ∈ guardFailures S F 11 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
      rw [hempty] at hm
      exact Finset.notMem_empty _ hm
    subst z
    have hlab : S.label v w = c := by
      by_contra hn
      have hf := hh.2
      rw [child_flip_other x w w c (S.label v w) i (by intro he; exact hn (congrArg Prod.snd he))] at hf
      have hm : w ∈ guardFailures S F 11 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
      rw [hempty] at hm
      exact Finset.notMem_empty _ hm
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨w,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1⟩,by simp [hempty]⟩,?_⟩
    apply (mem_lift w w (S.label v w) c _ i).2
    refine ⟨rfl,hlab.symm,?_⟩
    simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hlab]
    simpa only [hlab,child_flip_same] using hh.2

private theorem repair20_cases (S : Stage (Fin 22) I V)
    (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (htor : ∀ r z, r ≠ z → (S.Adj r z ↔ ¬ S.Adj z r))
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (i : I)
    (hv : ordinaryRow S F 17 2 0 x v)
    (hold : ordinaryParent S F 18 1 0 x = false)
    (hnew : ordinaryParent S F 18 1 0 (flip x {((w,c),i)}) = true) :
    ((w,c),i) ∈ cover S F 13 11 x v ∨
    (w = v ∧ (guardFailures S F 1 x v).card = 0 ∧
      F 18 (child x v c) = false ∧ F 18 (child x v (!c)) = true ∧
      F 18 (flip (child x v c) {i}) = true) ∨
    (guardFailures S F 1 x v = {w} ∧ S.label v w = c ∧
      F 1 (child x w c) = true ∧ F 1 (flip (child x w c) {i}) = false) := by
  obtain ⟨r,hr,hcr⟩ := (parent_iff S F 18 1 0 _).1 hnew
  have hzero : guardFailures S F 1 (flip x {((w,c),i)}) r = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  by_cases hrw : r = w
  · subst r
    have hgold : guardFailures S F 1 x w = ∅ := by
      rw [guard_self_unchanged] at hzero
      exact hzero
    have hother := hr (!c)
    rw [child_flip_other x w w c (!c) i (by cases c <;> simp)] at hother
    have hown := hr c
    rw [child_flip_same] at hown
    have hfalse : F 18 (child x w c) = false := by
      cases hf : F 18 (child x w c) with
      | false => rfl
      | true =>
        have ht : ∀ d, F 18 (child x w d) = true := by
          intro d
          by_cases hd : d = c
          · simpa only [hd] using hf
          · have he : d = !c := by cases c <;> cases d <;> simp_all
            simpa only [he] using hother
        have hh := (parent_iff S F 18 1 0 x).2 ⟨w,ht,by rw [hgold]; simp⟩
        rw [hold] at hh
        contradiction
    by_cases hwv : w = v
    · right; left
      subst w
      exact ⟨rfl,by rw [hgold]; simp,hfalse,hother,hown⟩
    · left
      have hno : ¬ S.Adj w v := by
        intro h
        have hm : v ∈ guardFailures S F 1 x w :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hF 1 17 (by decide) _ (hv.1 (S.label w v))⟩
        rw [hgold] at hm
        exact Finset.notMem_empty _ hm
      have hadj := (htor v w (Ne.symm hwv)).2 hno
      have hf2 := guard2_false S F x v w hv hadj
      have hlab : S.label v w = c := by
        have hother2 := hF 2 18 (by decide) _ hother
        cases c <;> cases he : S.label v w <;> simp_all
      have hempty := guard11_empty S F hF x v hv
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩,by simp [hempty]⟩,?_⟩
      apply (mem_lift w w (S.label v w) c _ i).2
      refine ⟨rfl,hlab.symm,?_⟩
      simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hlab]
      exact hF 11 18 (by decide) _ hown
  · have htargets : ∀ d, F 18 (child x r d) = true := by
      intro d
      have hh := hr d
      rw [child_flip_other x w r c d i (by intro he; exact hrw (congrArg Prod.fst he))] at hh
      exact hh
    have hsub : guardFailures S F 1 x r ⊆ {w} := by
      have hh := guard_subset_insert S F 1 x r w c i
      simpa only [hzero,Finset.insert_empty] using hh
    have hwmem : w ∈ guardFailures S F 1 x r := by
      by_contra hn
      have he : guardFailures S F 1 x r = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzw := Finset.mem_singleton.mp (hsub hz)
        subst z
        exact hn hz
      have hh := (parent_iff S F 18 1 0 x).2 ⟨r,htargets,by rw [he]; simp⟩
      rw [hold] at hh
      contradiction
    have hsingle : guardFailures S F 1 x r = {w} :=
      Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hwmem)
    have hm := (Finset.mem_filter.mp hwmem).2
    have hlab : S.label r w = c := by
      by_contra hn
      have hh := hm.2
      have he := child_flip_other x w w c (S.label r w) i (by intro h; exact hn (congrArg Prod.snd h))
      have hpost : F 1 (child (flip x {((w,c),i)}) w (S.label r w)) = true := by rw [he]; exact hh
      have hmem : w ∈ guardFailures S F 1 (flip x {((w,c),i)}) r :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm.1,hpost⟩
      rw [hzero] at hmem
      exact Finset.notMem_empty _ hmem
    have hf1 := hm.2
    rw [hlab] at hf1
    have hpostfalse : F 1 (flip (child x w c) {i}) = false := by
      cases hh : F 1 (flip (child x w c) {i}) with
      | false => rfl
      | true =>
        have hmem : w ∈ guardFailures S F 1 (flip x {((w,c),i)}) r := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,hm.1,?_⟩
          rw [hlab,child_flip_same]
          exact hh
        rw [hzero] at hmem
        exact False.elim (Finset.notMem_empty _ hmem)
    by_cases hrv : r = v
    · right; right
      subst r
      exact ⟨hsingle,hlab,hf1,hpostfalse⟩
    · left
      have hno : ¬ S.Adj v r := by
        intro h
        have hh := hF 2 18 (by decide) _ (htargets (S.label v r))
        rw [guard2_false S F x v r hv h] at hh
        contradiction
      have hadj := (htor r v hrv).2 hno
      have hvfailed : v ∈ guardFailures S F 1 x r :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,hF 1 17 (by decide) _ (hv.1 (S.label r v))⟩
      rw [hsingle] at hvfailed
      have hvw := Finset.mem_singleton.mp hvfailed
      subst w
      have h13 : F 13 (flip (child x v c) {i}) = false := by
        cases hh : F 13 (flip (child x v c) {i}) with
        | false => rfl
        | true =>
          have h1 := hF 1 13 (by decide) _ hh
          rw [hpostfalse] at h1
          contradiction
      apply Finset.mem_union_left
      have hi : i ∈ flipsTo (F 13) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h13⟩
      cases c
      · exact Finset.mem_union_left _ ((mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩)
      · exact Finset.mem_union_right _ ((mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩)

end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private def cutCover (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
    (x : ((V × Bool) × I) → Bool) (v : V) (T : Finset V) : Finset ((V × Bool) × I) :=
  (lift v false (flipsTo (F 13) false (child x v false)) ∪
    lift v true (flipsTo (F 13) false (child x v true))) ∪
  T.biUnion fun w => lift w (S.label v w) (flipsTo (F 11) true (child x w (S.label v w)))

private theorem cut_card (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
    (x : ((V × Bool) × I) → Bool) (v : V) (T : Finset V)
    (hv : ordinaryRow S F 17 2 0 x v)
    (hT : T ⊆ Finset.univ.filter (S.Adj v))
    (b a : ℕ) (hb : BBound F 13 17 b) (ha : ABound F 2 11 a) :
    (cutCover S F x v T).card ≤ 2*b+T.card*a := by
  have hguard : ∀ w ∈ T,
      (lift w (S.label v w) (flipsTo (F 11) true (child x w (S.label v w)))).card ≤ a := by
    intro w hw
    have hf := guard2_false S F x v w hv (Finset.mem_filter.mp (hT hw)).2
    simpa only [lift,Finset.card_map] using ha _ hf
  have hc := card_biUnion_mul T
    (fun w => lift w (S.label v w) (flipsTo (F 11) true (child x w (S.label v w)))) a hguard
  have h0 : (lift v false (flipsTo (F 13) false (child x v false))).card ≤ b := by
    simpa only [lift,Finset.card_map] using hb _ (hv.1 false)
  have h1 : (lift v true (flipsTo (F 13) false (child x v true))).card ≤ b := by
    simpa only [lift,Finset.card_map] using hb _ (hv.1 true)
  have h01 := Finset.card_union_le
    (lift v false (flipsTo (F 13) false (child x v false)))
    (lift v true (flipsTo (F 13) false (child x v true)))
  have hsum := Finset.card_union_le
    (lift v false (flipsTo (F 13) false (child x v false)) ∪
      lift v true (flipsTo (F 13) false (child x v true)))
    (T.biUnion fun w => lift w (S.label v w) (flipsTo (F 11) true (child x w (S.label v w))))
  dsimp only [cutCover]
  omega

private theorem lift_mono (v : V) (c : Bool) {T U : Finset I} (h : T ⊆ U) :
    lift v c T ⊆ lift v c U := by
  intro p hp
  obtain ⟨i,hi,he⟩ := Finset.mem_map.mp hp
  exact Finset.mem_map.mpr ⟨i,h hi,he⟩

private theorem cover_split (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
    (hF : Nested F) (x : ((V × Bool) × I) → Bool) (v w : V)
    (hv : ordinaryRow S F 17 2 0 x v) :
    cover S F 13 11 x v ⊆
      cutCover S F x v ((Finset.univ.filter (S.Adj v)).erase w) ∪
        lift w (S.label v w)
          (flipsTo (F 1) false (child x w (S.label v w)) ∪
            flipsTo (F 11) true (child x w (S.label v w))) := by
  have he := guard11_empty S F hF x v hv
  intro p hp
  rcases Finset.mem_union.mp hp with ht | hg
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ ht)
  · obtain ⟨r,hr,hp⟩ := Finset.mem_biUnion.mp hg
    have hadj := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).2
    by_cases hrw : r = w
    · subst r
      exact Finset.mem_union_right _ (lift_mono w (S.label v w) (Finset.subset_union_right) hp)
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨r,Finset.mem_erase.mpr ⟨hrw,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩⟩,hp⟩

-- This theorem accounts for every repairing row, not only the maximal
-- two-head signature. The shared-child bound J is retained in the joint cover.
theorem parent_joint_cover (S : Stage (Fin 22) I V)
    (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (weak : (((V × Bool) × I) → Bool) → Bool)
    (accept : ∀ y r, (∀ d, F 13 (child y r d) = true) →
      (∃ d, F 14 (child y r d) = true) → guardFailures S F 11 y r = ∅ → weak y = true)
    (htor : ∀ r z, r ≠ z → (S.Adj r z ↔ ¬ S.Adj z r))
    (degree b a q J : ℕ)
    (hd : ∀ v, (Finset.univ.filter (S.Adj v)).card = degree)
    (hb : BBound F 13 17 b) (ha : ABound F 2 11 a)
    (hq : ∀ y, F 17 y = true → F 18 y = false → (flipsTo (F 18) true y).card ≤ q)
    (hJ : ∀ y, F 1 y = true → F 2 y = false →
      (flipsTo (F 1) false y ∪ flipsTo (F 11) true y).card ≤ J)
    (x : ((V × Bool) × I) → Bool)
    (hmid : ordinaryParent S F 17 2 0 x = true)
    (hstrong : ordinaryParent S F 18 1 0 x = false) :
    (flipsTo weak false x ∪ flipsTo (ordinaryParent S F 18 1 0) true x).card ≤
      max (2*b+degree*a+q) (2*b+(degree-1)*a+J) := by
  obtain ⟨v,hv⟩ := (parent_iff S F 17 2 0 x).1 hmid
  let O := Finset.univ.filter (S.Adj v)
  have he := guard11_empty S F hF x v hv
  have hcEq : cover S F 13 11 x v = cutCover S F x v O := by
    simp only [cover,cutCover,he,Finset.sdiff_empty,O]
  let P := flipsTo (ordinaryParent S F 18 1 0) true x
  by_cases hsingle : (guardFailures S F 1 x v).card = 1
  · obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hsingle
    have hwmem : w ∈ guardFailures S F 1 x v := by rw [hw]; simp
    have hadj := (Finset.mem_filter.mp hwmem).2.1
    have hgap1 := (Finset.mem_filter.mp hwmem).2.2
    have hgap2 := guard2_false S F x v w hv hadj
    let T := O.erase w
    let U := lift w (S.label v w)
      (flipsTo (F 1) false (child x w (S.label v w)) ∪
        flipsTo (F 11) true (child x w (S.label v w)))
    have hT : T.card = degree-1 := by
      dsimp only [T]
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩),hd]
    have hc := cut_card S F x v T hv (Finset.erase_subset _ _) b a hb ha
    rw [hT] at hc
    have hu : U.card ≤ J := by
      simpa only [U,lift,Finset.card_map] using hJ _ hgap1 hgap2
    have hsub : flipsTo weak false x ∪ P ⊆ cutCover S F x v T ∪ U := by
      rintro ⟨⟨r,c⟩,i⟩ hp
      rcases Finset.mem_union.mp hp with hm | hp
      · exact cover_split S F hF x v w hv
          (destruction14_in_cover S F hF weak accept x v r c i hv (Finset.mem_filter.mp hm).2)
      · have hnew := (Finset.mem_filter.mp hp).2
        rcases repair20_cases S F hF htor x v r c i hv hstrong hnew with hc | ht | hg
        · exact cover_split S F hF x v w hv hc
        · have hh := ht.2.1
          rw [hsingle] at hh
          contradiction
        · have hrw : r = w := by
            have hm : r ∈ guardFailures S F 1 x v := by rw [hg.1]; simp
            rw [hw] at hm
            exact Finset.mem_singleton.mp hm
          subst r
          apply Finset.mem_union_right
          apply (mem_lift w w (S.label v w) c _ i).2
          refine ⟨rfl,hg.2.1.symm,?_⟩
          apply Finset.mem_union_left
          simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
          rw [hg.2.1]
          exact hg.2.2.2
    have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hbound : (flipsTo weak false x ∪ P).card ≤ 2*b+(degree-1)*a+J := by omega
    exact hbound.trans (Nat.le_max_right _ _)
  · let E :=
      (if F 18 (child x v false) = false ∧ F 18 (child x v true) = true then
        lift v false (flipsTo (F 18) true (child x v false)) else ∅) ∪
      (if F 18 (child x v true) = false ∧ F 18 (child x v false) = true then
        lift v true (flipsTo (F 18) true (child x v true)) else ∅)
    have hEc : E.card ≤ q := by
      cases hf : F 18 (child x v false) <;> cases ht : F 18 (child x v true)
      · simp [E,hf,ht]
      · simpa only [E,hf,ht,Bool.false_eq_true,Bool.true_eq_false,and_false,and_true,
          and_self,if_true,if_false,Finset.union_empty,lift,Finset.card_map] using
          hq (child x v false) (hv.1 false) hf
      · simpa only [E,hf,ht,Bool.false_eq_true,Bool.true_eq_false,and_false,and_true,
          and_self,if_true,if_false,Finset.empty_union,lift,Finset.card_map] using
          hq (child x v true) (hv.1 true) ht
      · simp [E,hf,ht]
    have hc := cut_card S F x v O hv (Finset.Subset.refl _) b a hb ha
    rw [hd] at hc
    have hsub : flipsTo weak false x ∪ P ⊆ cover S F 13 11 x v ∪ E := by
      rintro ⟨⟨w,c⟩,i⟩ hp
      rcases Finset.mem_union.mp hp with hm | hp
      · exact Finset.mem_union_left _
          (destruction14_in_cover S F hF weak accept x v w c i hv (Finset.mem_filter.mp hm).2)
      · rcases repair20_cases S F hF htor x v w c i hv hstrong (Finset.mem_filter.mp hp).2 with hc | ht | hg
        · exact Finset.mem_union_left _ hc
        · rcases ht with ⟨hwv,_,hfalse,hother,hpost⟩
          subst w
          apply Finset.mem_union_right
          have hi : i ∈ flipsTo (F 18) true (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpost⟩
          cases c
          · simp only [Bool.not_false] at hother
            apply Finset.mem_union_left
            simp only [E,hfalse,hother,and_self,if_true]
            exact (mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩
          · simp only [Bool.not_true] at hother
            apply Finset.mem_union_right
            simp only [E,hfalse,hother,and_self,if_true]
            exact (mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩
        · apply False.elim
          apply hsingle
          rw [hg.1]
          simp
    have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hcEq] at hh
    have hbound : (flipsTo weak false x ∪ P).card ≤ 2*b+degree*a+q := by omega
    exact hbound.trans (Nat.le_max_left _ _)

end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical

theorem endpoint22_phase2_parent_joint {I : Type} [Fintype I]
    (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬ Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool)
    (htor : ∀ r z, r ≠ z → (Adj r z ↔ ¬ Adj z r))
    (hd : ∀ v, (Finset.univ.filter (Adj v)).card = 2795)
    (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (b a q J : ℕ) (hb : BBound F 13 17 b) (ha : ABound F 2 11 a)
    (hq : ∀ y, F 17 y = true → F 18 y = false → (flipsTo (F 18) true y).card ≤ q)
    (hJ : ∀ y, F 1 y = true → F 2 y = false →
      (flipsTo (F 1) false y ∪ flipsTo (F 11) true y).card ≤ J)
    (x : ((Fin 5591 × Bool) × I) → Bool) :
    let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (2 : Fin 4)).stage F
    let G := parent S F
    G 19 x = true → G 20 x = false →
      (flipsTo (G 14) false x ∪ flipsTo (G 20) true x).card ≤
        max (2*b+2795*a+q) (2*b+2794*a+J) := by
  dsimp only
  let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (2 : Fin 4)).stage F
  have ht19 : ∀ d y z, S.target 19 d y z = (F 17 y && F 17 z) := by
    intro d y z
    dsimp [S, MinMaxRecipe.stage,minmaxTarget,Sensitivity5591Endpoint22.recipe,
      Sensitivity5591Endpoint22.entry,Sensitivity5591Endpoint22.entries2,
      Sensitivity5591Endpoint22.Entry.threshold,Sensitivity5591Endpoint22.Entry.upper]
    cases hy : F 17 y <;> cases hz : F 17 z <;> simp [hy,hz]
  have ht20 : ∀ d y z, S.target 20 d y z = (F 18 y && F 18 z) := by
    intro d y z
    dsimp [S, MinMaxRecipe.stage,minmaxTarget,Sensitivity5591Endpoint22.recipe,
      Sensitivity5591Endpoint22.entry,Sensitivity5591Endpoint22.entries2,
      Sensitivity5591Endpoint22.Entry.threshold,Sensitivity5591Endpoint22.Entry.upper]
    cases hy : F 18 y <;> cases hz : F 18 z <;> simp [hy,hz]
  have e19 := parent_specialize S F 19 17 2 0 (by rfl) (by rfl) ht19
  have e20 := parent_specialize S F 20 18 1 0 (by rfl) (by rfl) ht20
  have accept : ∀ y r, (∀ d, F 13 (child y r d) = true) →
      (∃ d, F 14 (child y r d) = true) → guardFailures S F 11 y r = ∅ →
      parent S F 14 y = true := by
    intro y r hl hu hg
    have hf : failed S F 14 y r = ∅ := by
      change guardFailures S F 11 y r = ∅
      exact hg
    simp only [parent, decide_eq_true_eq]
    refine ⟨r,?_,?_⟩
    · rw [hf]; simp
    · rw [hf]
      change (F 13 (child y r false) && F 13 (child y r true) &&
        (F 14 (child y r false) || F 14 (child y r true))) = true
      rw [hl false,hl true]
      rcases hu with ⟨c,hc⟩
      cases c <;> simp [hc]
  change parent S F 19 x = true → parent S F 20 x = false → _
  rw [e19,e20]
  intro hm hs
  have H := parent_joint_cover S F hF (parent S F 14) accept htor
    2795 b a q J hd hb ha hq hJ x hm hs
  convert H using 1 <;> congr 1 <;> ext p <;>
    simp only [Finset.mem_union,flipsTo,Finset.mem_filter,Finset.mem_univ,true_and,S]

end
end Sensitivity213981Formal.JointCover

theorem solution {K : Type} [Fintype K]
    (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬ Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool)
    (htor : ∀ r z, r ≠ z → (Adj r z ↔ ¬ Adj z r))
    (hd : ∀ v, (Finset.univ.filter (Adj v)).card = 2795)
    (H : Fin 22 → (K → Bool) → Bool) (hH : Nested H)
    (hB : BBound H 12 12 53627300001453076)
    (hA : ABound H 10 10 914422496216727)
    (hs : ABound H 12 13 1217719417783) :
    let F := parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (1 : Fin 4)).stage H) H
    let G := parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (2 : Fin 4)).stage F) F
    Nested F → BBound F 13 17 986662590537317840 →
    ABound F 2 11 24354388355660 →
    (∀ y, F 17 y = true → F 18 y = false →
      (flipsTo (F 18) true y).card ≤ 47117605675757176) →
    ∀ x, G 19 x = true → G 20 x = false →
      (flipsTo (G 14) false x ∪ flipsTo (G 20) true x).card ≤ 4700783999961812061 := by
  dsimp only
  let F := parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (1 : Fin 4)).stage H) H
  intro hF hb ha hq x hm ht
  have hJ : ∀ y, F 1 y = true → F 2 y = false →
      (flipsTo (F 1) false y ∪ flipsTo (F 11) true y).card ≤ 2659412657821462341 := by
    intro y hy hz
    have hh := SensitivityJointCover.endpoint22_phase1_bound
      Adj loopless label htor hd H hH
      53627300001453076 914422496216727 1217719417783 hB hA hs y hy hz
    exact hh
  have bound := Sensitivity213981Formal.JointCover.endpoint22_phase2_parent_joint
    Adj loopless label htor hd F hF
    986662590537317840 24354388355660 47117605675757176 2659412657821462341
    hb ha hq (by
      intro y hy hz
      convert hJ y hy hz using 1 <;> congr 1 <;> ext p <;> simp only [Finset.mem_union]) x hm ht
  convert bound using 1 <;> congr 1 <;> ext p <;>
    simp only [Finset.mem_union,flipsTo,Finset.mem_filter,Finset.mem_univ,true_and,F]
