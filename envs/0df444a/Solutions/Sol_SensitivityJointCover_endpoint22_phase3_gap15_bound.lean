-- Prove2me | solution 1 for SensitivityJointCover.endpoint22_phase3_gap15_bound
-- status  : ACCEPTED   (prove)
-- author  : @jennyuxi
-- created : 2026-11-14T02:18:32.209929+00:00
-- url     : https://prove2.me/submissions/7ed69146-7c86-4c9f-beaa-35e12d88c5f7

import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
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

private theorem q0_repair_cases_gap15_guard0 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (i : I)
 (hold : ordinaryParent S F 21 0 0 x=false)
 (hnew : ordinaryParent S F 21 0 0 (flip x {((w,c),i)})=true) :
 (guardFailures S F 0 x w=∅ ∧ F 21 (child x w c)=false ∧
   F 21 (child x w (!c))=true ∧ F 21 (flip (child x w c) {i})=true) ∨
 (∃ r, (∀ d, F 21 (child x r d)=true) ∧ guardFailures S F 0 x r={w} ∧
   S.label r w=c ∧ F 0 (flip (child x w c) {i})=false) := by
 obtain ⟨r,hr,hcr⟩ := (parent_iff S F 21 0 0 _).1 hnew
 have hzero : guardFailures S F 0 (flip x {((w,c),i)}) r=∅ := Finset.card_eq_zero.mp (by omega)
 by_cases hrw : r=w
 · subst r
   have hg : guardFailures S F 0 x w=∅ := by rw [guard_self_unchanged] at hzero; exact hzero
   have ho := hr (!c)
   rw [child_flip_other x w w c (!c) i (by cases c <;> simp)] at ho
   have hn := hr c
   rw [child_flip_same] at hn
   have hf : F 21 (child x w c)=false := by
     cases hh : F 21 (child x w c) with
     | false => rfl
     | true =>
       have ht : ∀ d, F 21 (child x w d)=true := by
         intro d
         by_cases hd : d=c
         · simpa [hd] using hh
         · have he : d= !c := by cases c <;> cases d <;> simp_all
           simpa [he] using ho
       have hac := (parent_iff S F 21 0 0 x).2 ⟨w,ht,by rw [hg]; simp⟩
       rw [hold] at hac
       contradiction
   exact Or.inl ⟨hg,hf,ho,hn⟩
 · have ht : ∀ d, F 21 (child x r d)=true := by
     intro d
     have hh := hr d
     rw [child_flip_other x w r c d i (by intro he; exact hrw (congrArg Prod.fst he))] at hh
     exact hh
   have hsub : guardFailures S F 0 x r ⊆ {w} := by
     have hh := guard_subset_insert S F 0 x r w c i
     simpa only [hzero,Finset.insert_empty] using hh
   have hwm : w ∈ guardFailures S F 0 x r := by
     by_contra hn
     have he : guardFailures S F 0 x r=∅ := by
       apply Finset.eq_empty_iff_forall_notMem.mpr
       intro z hz
       have hzw := Finset.mem_singleton.mp (hsub hz)
       subst z; exact hn hz
     have hac := (parent_iff S F 21 0 0 x).2 ⟨r,ht,by rw [he]; simp⟩
     rw [hold] at hac
     contradiction
   have hs : guardFailures S F 0 x r={w} := Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hwm)
   have hh := (Finset.mem_filter.mp hwm).2
   have hl : S.label r w=c := by
     by_contra hn
     have ht7 := hh.2
     have hf : F 0 (child (flip x {((w,c),i)}) w (S.label r w))=true := by
       rw [child_flip_other x w w c (S.label r w) i (by intro he; exact hn (congrArg Prod.snd he))]
       exact ht7
     have hm : w ∈ guardFailures S F 0 (flip x {((w,c),i)}) r := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
     rw [hzero] at hm
     exact Finset.notMem_empty _ hm
   have hfalse : F 0 (flip (child x w c) {i})=false := by
     cases hf : F 0 (flip (child x w c) {i}) with
     | false => rfl
     | true =>
       have hm : w ∈ guardFailures S F 0 (flip x {((w,c),i)}) r := by
         apply Finset.mem_filter.mpr
         refine ⟨Finset.mem_univ _,hh.1,?_⟩
         rw [hl,child_flip_same]; exact hf
       rw [hzero] at hm
       exact False.elim (Finset.notMem_empty _ hm)
   exact Or.inr ⟨r,ht,hs,hl,hfalse⟩

end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

private theorem phase4_accept16_gap15
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h17 : ∀ c, F 21 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 0 x v=∅) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 16 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 16 x=true
 have hf : failed S F 16 x v=∅ := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,?_,?_⟩
 · rw [hf]; simp
 · rw [hf]
   change (F 21 (child x v false) && F 21 (child x v true) &&
     (F 21 (child x v false) || F 21 (child x v true)))=true
   simp [h17]

theorem phase4_gap15_witness
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 15 x=true → parent S F 16 x=false → ∃ v,
 (∀ c, F 20 (child x v c)=true) ∧ ¬(∀ c, F 21 (child x v c)=true) ∧
 guardFailures S F 0 x v=∅ := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 intro h8 h9
 change parent S F 15 x=true at h8
 simp only [parent,decide_eq_true_eq] at h8
 obtain ⟨v,hc,ht⟩ := h8
 have he : failed S F 15 x v=∅ := Finset.card_eq_zero.mp (by change _ ≤ 0 at hc; omega)
 rw [he] at ht
 change (F 20 (child x v false) && F 20 (child x v true) &&
   (F 20 (child x v false) || F 20 (child x v true)))=true at ht
 simp only [Bool.and_eq_true] at ht
 have h16 : ∀ c, F 20 (child x v c)=true := by
   intro c; cases c
   · exact ht.1.1
   · exact ht.1.2
 have hg : guardFailures S F 0 x v=∅ := he
 refine ⟨v,h16,?_,hg⟩
 intro h17
 have hac := phase4_accept16_gap15 Adj loopless label F x v h17 hg
 rw [h9] at hac
 contradiction

private theorem accept7_gap15_zero
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h15 : ∀ c, F 15 (child x v c)=true) (h16 : ∃ c, F 16 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 13 x v=∅) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 7 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 7 x=true
 have hf : failed S F 7 x v=∅ := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,?_,?_⟩
 · rw [hf]; simp
 · rw [hf]
   change (F 15 (child x v false) && F 15 (child x v true) &&
     (F 16 (child x v false) || F 16 (child x v true)))=true
   rw [h15 false,h15 true]
   rcases h16 with ⟨c,hc⟩
   cases c <;> simp [hc]

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap15_witness

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

theorem phase4_guard13_single_flip_update (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (x : ((V × Bool) × I) → Bool)
 (v w : V) (c : Bool) (i : I) (hg : guardFailures S F 13 x v=∅) :
 guardFailures S F 13 (flip x {((w,c),i)}) v =
 if S.Adj v w ∧ S.label v w=c ∧ F 13 (flip (child x w c) {i})=true then {w} else ∅ := by
 have hsub : guardFailures S F 13 (flip x {((w,c),i)}) v ⊆ {w} := by
   intro z hz
   by_cases hzw : z=w
   · exact Finset.mem_singleton.mpr hzw
   · have hh := (Finset.mem_filter.mp hz).2
     have hf := hh.2
     rw [child_flip_other x w z c (S.label v z) i (by intro he; exact hzw (congrArg Prod.fst he))] at hf
     have hm : z ∈ guardFailures S F 13 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
     rw [hg] at hm
     exact False.elim (Finset.notMem_empty _ hm)
 by_cases hc : S.Adj v w ∧ S.label v w=c ∧ F 13 (flip (child x w c) {i})=true
 · rw [if_pos hc]
   apply Finset.Subset.antisymm hsub
   apply Finset.singleton_subset_iff.mpr
   apply Finset.mem_filter.mpr
   refine ⟨Finset.mem_univ _,hc.1,?_⟩
   rw [hc.2.1,child_flip_same]
   exact hc.2.2
 · rw [if_neg hc]
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro z hz
   have hzw := Finset.mem_singleton.mp (hsub hz)
   subst z
   have hh := (Finset.mem_filter.mp hz).2
   have hlab : S.label v w=c := by
     by_contra hn
     have hf := hh.2
     rw [child_flip_other x w w c (S.label v w) i (by intro he; exact hn (congrArg Prod.snd he))] at hf
     have hm : w ∈ guardFailures S F 13 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
     rw [hg] at hm
     exact Finset.notMem_empty _ hm
   have hp := hh.2
   rw [hlab,child_flip_same] at hp
   exact hc ⟨hh.1,hlab,hp⟩

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_guard13_single_flip_update

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

private def gap15Row (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591) : Finset ((Fin 5591 × Bool) × I) :=
 lift v false (flipsTo (F 15) false (child x v false) ∪
   (if F 21 (child x v false)=false ∧ F 21 (child x v true)=true then
     flipsTo (F 21) true (child x v false) else ∅)) ∪
 lift v true (flipsTo (F 15) false (child x v true) ∪
   (if F 21 (child x v true)=false ∧ F 21 (child x v false)=true then
     flipsTo (F 21) true (child x v true) else ∅))

private def gap15Arcs (S : Stage (Fin 22) I (Fin 5591))
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591) : Finset ((Fin 5591 × Bool) × I) :=
 (Finset.univ.filter (S.Adj v)).biUnion fun w =>
   lift w (S.label v w) (flipsTo (F 13) true (child x w (S.label v w)))

private theorem gap15_down_in_row (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591) (c : Bool) (i : I)
 (hf : F 15 (flip (child x v c) {i})=false) : ((v,c),i) ∈ gap15Row F x v := by
 have hi : i ∈ flipsTo (F 15) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩
 cases c
 · apply Finset.mem_union_left
   apply (mem_lift v v false false _ i).2
   exact ⟨rfl,rfl,Finset.mem_union_left _ hi⟩
 · apply Finset.mem_union_right
   apply (mem_lift v v true true _ i).2
   exact ⟨rfl,rfl,Finset.mem_union_left _ hi⟩

private theorem gap15_row_card (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h16 : ∀ c, F 20 (child x v c)=true) (B J : ℕ) (hB : BBound F 15 20 B)
 (hJ : ∀ y, F 20 y=true → F 21 y=false →
   (flipsTo (F 15) false y ∪ flipsTo (F 21) true y).card≤J) :
 (gap15Row F x v).card≤ max (2*B) (B+J) := by
 have hb0 := hB _ (h16 false)
 have hb1 := hB _ (h16 true)
 have hc := Finset.card_union_le
   (lift v false (flipsTo (F 15) false (child x v false) ∪
     (if F 21 (child x v false)=false ∧ F 21 (child x v true)=true then
       flipsTo (F 21) true (child x v false) else ∅)))
   (lift v true (flipsTo (F 15) false (child x v true) ∪
     (if F 21 (child x v true)=false ∧ F 21 (child x v false)=true then
       flipsTo (F 21) true (child x v true) else ∅)))
 change (gap15Row F x v).card ≤ _ at hc
 simp only [lift,Finset.card_map] at hc
 cases hf : F 21 (child x v false) <;> cases ht : F 21 (child x v true)
 · simp only [hf,ht,Bool.false_eq_true,and_false,if_false,Finset.union_empty] at hc
   have hh := Nat.le_max_left (2*B) (B+J)
   omega
 · have hj := hJ _ (h16 false) hf
   simp only [hf,ht,Bool.false_eq_true,Bool.true_eq_false,and_self,and_false,if_true,if_false,Finset.union_empty] at hc
   have hh := Nat.le_max_right (2*B) (B+J)
   omega
 · have hj := hJ _ (h16 true) ht
   simp only [hf,ht,Bool.false_eq_true,Bool.true_eq_false,and_self,and_false,if_true,if_false,Finset.union_empty] at hc
   have hh := Nat.le_max_right (2*B) (B+J)
   omega
 · simp only [hf,ht,Bool.true_eq_false,false_and,if_false,Finset.union_empty] at hc
   have hh := Nat.le_max_left (2*B) (B+J)
   omega

private theorem gap15_arc_card (S : Stage (Fin 22) I (Fin 5591))
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (hg : guardFailures S F 0 x v=∅) (degree A : ℕ)
 (hd : (Finset.univ.filter (S.Adj v)).card=degree) (hA : ABound F 0 13 A) :
 (gap15Arcs S F x v).card≤degree*A := by
 have hh := card_biUnion_mul (Finset.univ.filter (S.Adj v))
   (fun w => lift w (S.label v w) (flipsTo (F 13) true (child x w (S.label v w)))) A (by
     intro w hw
     have hadj := (Finset.mem_filter.mp hw).2
     have hf : F 0 (child x w (S.label v w))=false := by
       cases hf : F 0 (child x w (S.label v w)) with
       | false => rfl
       | true =>
         have hm : w ∈ guardFailures S F 0 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,hf⟩
         rw [hg] at hm
         exact False.elim (Finset.notMem_empty _ hm)
     simpa only [lift,Finset.card_map] using hA _ hf)
 rw [hd] at hh
 exact hh

theorem phase4_gap15_destruction_cover
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h16 : ∀ c, F 20 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 0 x v=∅) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 flipsTo (parent S F 7) false x ⊆ gap15Row F x v ∪ gap15Arcs S F x v := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 have he13 : guardFailures S F 13 x v=∅ := by
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro w hw
   have hh := (Finset.mem_filter.mp hw).2
   have hm : w ∈ guardFailures S F 0 x v := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hh.1,hF 0 13 (by decide) _ hh.2⟩
   rw [hg] at hm
   exact Finset.notMem_empty _ hm
 rintro ⟨⟨w,c⟩,i⟩ hp
 have hdown := (Finset.mem_filter.mp hp).2
 by_cases hwv : w=v
 · subst w
   have hf : F 15 (flip (child x v c) {i})=false := by
     cases hh : F 15 (flip (child x v c) {i}) with
     | false => rfl
     | true =>
       have hl : ∀ d, F 15 (child (flip x {((v,c),i)}) v d)=true := by
         intro d
         by_cases hd : d=c
         · subst d; simpa only [child_flip_same] using hh
         · rw [child_flip_other x v v c d i (by intro he; exact hd (congrArg Prod.snd he))]
           exact hF 15 20 (by decide) _ (h16 d)
       have hu : ∃ d, F 16 (child (flip x {((v,c),i)}) v d)=true := by
         refine ⟨!c,?_⟩
         rw [child_flip_other x v v c (!c) i (by cases c <;> simp)]
         exact hF 16 20 (by decide) _ (h16 (!c))
       have hguard : guardFailures S F 13 (flip x {((v,c),i)}) v=∅ := by
         rw [guard_self_unchanged]; exact he13
       have hac := accept7_gap15_zero Adj loopless label F _ v hl hu hguard
       rw [hdown] at hac
       contradiction
   exact Finset.mem_union_left _ (gap15_down_in_row F x v c i hf)
 · have hl : ∀ d, F 15 (child (flip x {((w,c),i)}) v d)=true := by
     intro d
     rw [child_flip_other x w v c d i (by intro he; exact hwv (congrArg Prod.fst he).symm)]
     exact hF 15 20 (by decide) _ (h16 d)
   have hu : ∃ d, F 16 (child (flip x {((w,c),i)}) v d)=true := by
     refine ⟨false,?_⟩
     rw [child_flip_other x w v c false i (by intro he; exact hwv (congrArg Prod.fst he).symm)]
     exact hF 16 20 (by decide) _ (h16 false)
   have hne : guardFailures S F 13 (flip x {((w,c),i)}) v≠∅ := by
     intro he
     have hac := accept7_gap15_zero Adj loopless label F _ v hl hu he
     rw [hdown] at hac
     contradiction
   obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
   have hh := (Finset.mem_filter.mp hz).2
   have hzw : z=w := by
     by_contra hn
     have hf := hh.2
     rw [child_flip_other x w z c (S.label v z) i (by intro he; exact hn (congrArg Prod.fst he))] at hf
     have hm : z ∈ guardFailures S F 13 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
     rw [he13] at hm
     exact Finset.notMem_empty _ hm
   subst z
   have hlabel : S.label v w=c := by
     by_contra hn
     have hf := hh.2
     rw [child_flip_other x w w c (S.label v w) i (by intro he; exact hn (congrArg Prod.snd he))] at hf
     have hm : w ∈ guardFailures S F 13 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
     rw [he13] at hm
     exact Finset.notMem_empty _ hm
   apply Finset.mem_union_right
   apply Finset.mem_biUnion.mpr
   refine ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1⟩,?_⟩
   apply (mem_lift w w (S.label v w) c _ i).2
   refine ⟨rfl,hlabel.symm,?_⟩
   simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
   rw [hlabel]
   simpa only [hlabel,child_flip_same] using hh.2

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap15_destruction_cover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

theorem phase4_gap15_joint_bound
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (degree : ℕ) (hd : ∀ v, (Finset.univ.filter (Adj v)).card=degree)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (B A J : ℕ) (hB : BBound F 15 20 B) (hA : ABound F 0 13 A)
 (hJ : ∀ y, F 20 y=true → F 21 y=false →
   (flipsTo (F 15) false y ∪ flipsTo (F 21) true y).card≤J)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 15 x=true → parent S F 16 x=false →
 (flipsTo (parent S F 7) false x ∪ flipsTo (parent S F 16) true x).card≤ max (2*B) (B+J)+degree*A := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 intro h8 h9
 obtain ⟨v,h16,hno17,hg⟩ := phase4_gap15_witness Adj loopless label F x h8 h9
 have htarget : ∀ d y z, S.target 16 d y z=(F 21 y && F 21 z) := by
   intro d y z
   dsimp [S,MinMaxRecipe.stage,minmaxTarget,Sensitivity5591Endpoint22.recipe,
     Sensitivity5591Endpoint22.entry,Sensitivity5591Endpoint22.entries3,
     Sensitivity5591Endpoint22.Entry.threshold,Sensitivity5591Endpoint22.Entry.upper]
   cases hy : F 21 y <;> cases hz : F 21 z <;> simp [hy,hz]
 have e12 := parent_specialize S F 16 21 0 0 (by rfl) (by rfl) htarget
 have hold : ordinaryParent S F 21 0 0 x=false := by
   rw [← e12]; exact h9
 have hm := phase4_gap15_destruction_cover Adj loopless label F hF x v h16 hg
 have hc := gap15_row_card F x v h16 B J hB hJ
 have ha := gap15_arc_card S F x v hg degree A (hd v) hA
 have hs : flipsTo (parent S F 7) false x ∪ flipsTo (ordinaryParent S F 21 0 0) true x ⊆
   gap15Row F x v ∪ gap15Arcs S F x v := by
   rintro ⟨⟨z,c⟩,i⟩ hp
   rcases Finset.mem_union.mp hp with hd | hp
   · exact hm hd
   · rcases q0_repair_cases_gap15_guard0 S F x z c i hold (Finset.mem_filter.mp hp).2 with htar | hgu
     · by_cases hzv : z=v
       · subst z
         have ho17 := hF 21 21 (by decide) _ htar.2.2.1
         have hf17 : F 21 (child x v c)=false := by
           cases hh : F 21 (child x v c) with
           | false => rfl
           | true =>
             apply False.elim
             apply hno17
             intro d
             by_cases hd : d=c
             · simpa [hd] using hh
             · have he : d= !c := by cases c <;> cases d <;> simp_all
               simpa [he] using ho17
         have hi : i ∈ flipsTo (F 21) true (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,htar.2.2.2⟩
         apply Finset.mem_union_left
         cases c
         · simp only [Bool.not_false] at ho17
           apply Finset.mem_union_left
           apply (mem_lift v v false false _ i).2
           refine ⟨rfl,rfl,Finset.mem_union_right _ ?_⟩
           simp only [hf17,ho17,and_self,if_true]
           exact hi
         · simp only [Bool.not_true] at ho17
           apply Finset.mem_union_right
           apply (mem_lift v v true true _ i).2
           refine ⟨rfl,rfl,Finset.mem_union_right _ ?_⟩
           simp only [hf17,ho17,and_self,if_true]
           exact hi
       · have hnorv : ¬Adj z v := by
           intro h
           have hmem : v ∈ guardFailures S F 0 x z := Finset.mem_filter.mpr
             ⟨Finset.mem_univ _,h,hF 0 20 (by decide) _ (h16 (label z v))⟩
           rw [htar.1] at hmem
           exact Finset.notMem_empty _ hmem
         have hadj := (htor v z (Ne.symm hzv)).2 hnorv
         have hf11 : F 0 (child x z (S.label v z))=false := by
           cases hh : F 0 (child x z (S.label v z)) with
           | false => rfl
           | true =>
             have hmem : z ∈ guardFailures S F 0 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,hh⟩
             rw [hg] at hmem
             exact False.elim (Finset.notMem_empty _ hmem)
         have hlab : S.label v z=c := by
           by_contra hn
           have he : S.label v z= !c := by cases c <;> cases hl : S.label v z <;> simp_all
           have hh := hF 0 21 (by decide) _ htar.2.2.1
           rw [←he,hf11] at hh
           contradiction
         apply Finset.mem_union_right
         apply Finset.mem_biUnion.mpr
         refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩,?_⟩
         apply (mem_lift z z (S.label v z) c _ i).2
         refine ⟨rfl,hlab.symm,?_⟩
         simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
         rw [hlab]
         exact hF 13 21 (by decide) _ htar.2.2.2
     · obtain ⟨r,htr,hr,hl,hpost⟩ := hgu
       have hrv : r≠v := by
         intro he; subst r
         apply hno17
         intro d
         exact hF 21 21 (by decide) _ (htr d)
       have hno : ¬Adj v r := by
         intro hadj
         have hmem : r ∈ guardFailures S F 0 x v := Finset.mem_filter.mpr
           ⟨Finset.mem_univ _,hadj,hF 0 21 (by decide) _ (htr (label v r))⟩
         rw [hg] at hmem
         exact Finset.notMem_empty _ hmem
       have hadj := (htor r v hrv).2 hno
       have hmem : v ∈ guardFailures S F 0 x r := Finset.mem_filter.mpr
         ⟨Finset.mem_univ _,hadj,hF 0 20 (by decide) _ (h16 (label r v))⟩
       rw [hr] at hmem
       have hzv := (Finset.mem_singleton.mp hmem).symm
       subst z
       have hpost15 : F 15 (flip (child x v c) {i})=false := by
         cases hh : F 15 (flip (child x v c) {i}) with
         | false => rfl
         | true =>
           have h7 := hF 0 15 (by decide) _ hh
           rw [hpost] at h7
           contradiction
       exact Finset.mem_union_left _ (gap15_down_in_row F x v c i hpost15)
 change (flipsTo (parent S F 7) false x ∪ flipsTo (parent S F 16) true x).card≤_
 rw [e12]
 exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hc ha))

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap15_joint_bound

open Sensitivity213981Formal Sensitivity213981Formal.ThreeBoundWitness
open Sensitivity213981Formal.ThreeBoundProfiles
open scoped Classical
theorem endpoint22_phase3_gap15_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hd : ∀ v, (Finset.univ.filter (Adj v)).card=2795)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 15 20 53874150507309062240)
 (hA : ABound F 0 13 1330073126471840)
 (hJ : ∀ y, F 20 y=true → F 21 y=false →
   (flipsTo (F 15) false y ∪ flipsTo (F 21) true y).card≤56530689653409078976)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 15 x=true → parent S F 16 x=false →
 (flipsTo (parent S F 7) false x ∪ flipsTo (parent S F 16) true x).card≤114122394549206934016 := by
 have hh := Sensitivity213981Formal.JointCover.phase4_gap15_joint_bound
   Adj loopless label htor 2795 hd F hF 53874150507309062240 1330073126471840 56530689653409078976 hB hA hJ x
 exact hh
#print axioms endpoint22_phase3_gap15_bound

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
noncomputable section
open scoped Classical

private theorem gap15_joint_ordered {K : Type} [Fintype K]
 (G : Fin 22 → (K → Bool) → Bool) (hG : Nested G)
 (i l : Fin 22) (hi : i≤7) (hl : 16≤l) (x : K → Bool) (R : ℕ)
 (h : (flipsTo (G 7) false x ∪ flipsTo (G 16) true x).card≤R) :
 (flipsTo (G i) false x ∪ flipsTo (G l) true x).card≤R := by
 apply (Finset.card_le_card (show flipsTo (G i) false x ∪ flipsTo (G l) true x ⊆
   flipsTo (G 7) false x ∪ flipsTo (G 16) true x from ?_)).trans h
 intro z hz
 rcases Finset.mem_union.mp hz with hd | hu
 · apply Finset.mem_union_left
   apply Finset.mem_filter.mpr
   refine ⟨Finset.mem_univ _,?_⟩
   cases he : G 7 (flip x {z}) with
   | false => rfl
   | true =>
     have hh := hG i 7 hi _ he
     rw [(Finset.mem_filter.mp hd).2] at hh
     contradiction
 · apply Finset.mem_union_right
   apply Finset.mem_filter.mpr
   exact ⟨Finset.mem_univ _,hG 16 l hl _ (Finset.mem_filter.mp hu).2⟩

theorem phase4_gap15_closed_family {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hd : ∀ v, (Finset.univ.filter (Adj v)).card=2795)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 15 20 53874150507309062240)
 (hA : ABound F 0 13 1330073126471840)
 (hJ : ∀ y, F 20 y=true → F 21 y=false →
   (flipsTo (F 15) false y ∪ flipsTo (F 21) true y).card≤56530689653409078976)
 :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 let G := parent S F
 Nested G → ∀ (i l : Fin 22), i≤7 → 16≤l → ∀ x,
 G 15 x=true → G 16 x=false →
 (flipsTo (G i) false x ∪ flipsTo (G l) true x).card≤114122394549206934016 := by
 dsimp only
 intro hN i l hi hl x h8 h9
 have hh := endpoint22_phase3_gap15_bound Adj loopless label htor hd F hF hB hA hJ x h8 h9
 have h := gap15_joint_ordered _ hN i l hi hl x 114122394549206934016 (by
   convert hh using 1 <;> congr 1 <;> ext z <;> simp only [Finset.mem_union])
 convert h using 1 <;> congr 1 <;> ext z <;> simp only [Finset.mem_union]
end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap15_closed_family

theorem solution {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hd : ∀ v, (Finset.univ.filter (Adj v)).card=2795)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 15 20 53874150507309062240)
 (hA : ABound F 0 13 1330073126471840)
 (hJ : ∀ y, F 20 y=true → F 21 y=false →
   (flipsTo (F 15) false y ∪ flipsTo (F 21) true y).card≤56530689653409078976)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 15 x=true → parent S F 16 x=false →
 (flipsTo (parent S F 7) false x ∪ flipsTo (parent S F 16) true x).card≤114122394549206934016 := by
 exact endpoint22_phase3_gap15_bound Adj loopless label htor hd F hF hB hA hJ x
