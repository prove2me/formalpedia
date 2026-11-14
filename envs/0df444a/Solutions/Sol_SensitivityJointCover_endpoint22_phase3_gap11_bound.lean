-- Prove2me | solution 1 for SensitivityJointCover.endpoint22_phase3_gap11_bound
-- status  : ACCEPTED   (prove)
-- author  : @jennyuxi
-- created : 2026-11-14T00:37:43.987624+00:00
-- url     : https://prove2.me/submissions/f4ea2ae7-8382-42b1-a786-c05d2ed6a198

import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
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
variable {I : Type} [Fintype I]

private theorem phase4_row10
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool)
 (hx : parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 10 x = true) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 ∃ v, (∀ c, F 17 (child x v c)=true) ∧
   (∃ c, F 18 (child x v c)=true) ∧ guardFailures S F 11 x v = ∅ := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 10 x = true at hx
 simp only [parent,decide_eq_true_eq] at hx
 obtain ⟨v,hc,ht⟩ := hx
 have he : failed S F 10 x v = ∅ := Finset.card_eq_zero.mp (by change _ ≤ 0 at hc; omega)
 rw [he] at ht
 change (F 17 (child x v false) && F 17 (child x v true) &&
   (F 18 (child x v false) || F 18 (child x v true))) = true at ht
 simp only [Bool.and_eq_true,Bool.or_eq_true] at ht
 refine ⟨v,?_,?_,?_⟩
 · intro c; cases c
   · exact ht.1.1
   · exact ht.1.2
 · rcases ht.2 with hh | hh
   · exact ⟨false,hh⟩
   · exact ⟨true,hh⟩
 · exact he

private theorem accept4_zero
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h14 : ∀ c, F 14 (child x v c)=true) (h15 : ∃ c, F 15 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 13 x v=∅) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 4 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 4 x=true
 have hf : failed S F 4 x v=∅ := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,?_,?_⟩
 · rw [hf]; simp
 · rw [hf]
   change (F 14 (child x v false) && F 14 (child x v true) &&
     (F 15 (child x v false) || F 15 (child x v true)))=true
   rw [h14 false,h14 true]
   rcases h15 with ⟨c,hc⟩
   cases c <;> simp [hc]

private theorem accept4_fifteen
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h15 : ∀ c, F 15 (child x v c)=true)
 (hg : (guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 13 x v).card≤1) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 4 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 4 x=true
 have hf : (failed S F 4 x v).card≤1 := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,hf,?_⟩
 have hz : (failed S F 4 x v).card=0 ∨ (failed S F 4 x v).card=1 := by omega
 rcases hz with hz | hz
 · rw [hz]
   change (F 14 (child x v false) && F 14 (child x v true) &&
     (F 15 (child x v false) || F 15 (child x v true)))=true
   simp [h15, hF 14 15 (by decide) _ (h15 false),hF 14 15 (by decide) _ (h15 true)]
 · rw [hz]
   change (F 15 (child x v false) && F 15 (child x v true) &&
     (F 15 (child x v false) || F 15 (child x v true)))=true
   simp [h15]

private def rowDown14 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591) :=
 lift v false (flipsTo (F 14) false (child x v false)) ∪
 lift v true (flipsTo (F 14) false (child x v true))

theorem phase4_destruction_supported_at_witness
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (ht : ∀ c, F 17 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 11 x v=∅) :
 flipsTo (parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 4) false x ⊆
 rowDown14 F x v := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 have h13 : guardFailures S F 13 x v=∅ := by
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro w hw
   have hh := (Finset.mem_filter.mp hw).2
   have hm : w ∈ guardFailures S F 11 x v := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hh.1,hF 11 13 (by decide) _ hh.2⟩
   rw [hg] at hm
   exact Finset.notMem_empty _ hm
 rintro ⟨⟨w,c⟩,i⟩ hp
 have hdown := (Finset.mem_filter.mp hp).2
 by_cases hwv : w=v
 · subst w
   have hfalse : F 14 (flip (child x v c) {i})=false := by
     cases hh : F 14 (flip (child x v c) {i}) with
     | false => rfl
     | true =>
       have hlow : ∀ d, F 14 (child (flip x {((v,c),i)}) v d)=true := by
         intro d
         by_cases he : d=c
         · subst d; simpa only [child_flip_same] using hh
         · rw [child_flip_other x v v c d i (by intro h; exact he (congrArg Prod.snd h))]
           exact hF 14 17 (by decide) _ (ht d)
       have hup : ∃ d, F 15 (child (flip x {((v,c),i)}) v d)=true := by
         refine ⟨!c,?_⟩
         rw [child_flip_other x v v c (!c) i (by cases c <;> simp)]
         exact hF 15 17 (by decide) _ (ht (!c))
       have hguard : guardFailures S F 13 (flip x {((v,c),i)}) v=∅ := by
         rw [guard_self_unchanged]; exact h13
       have hac := accept4_zero Adj loopless label F _ v hlow hup hguard
       rw [hdown] at hac
       contradiction
   have hi : i ∈ flipsTo (F 14) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfalse⟩
   cases c
   · exact Finset.mem_union_left _ ((mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩)
   · exact Finset.mem_union_right _ ((mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩)
 · have htargets : ∀ d, F 15 (child (flip x {((w,c),i)}) v d)=true := by
     intro d
     rw [child_flip_other x w v c d i (by intro he; exact hwv (congrArg Prod.fst he).symm)]
     exact hF 15 17 (by decide) _ (ht d)
   have hsub := guard_subset_insert S F 13 (flip x {((w,c),i)}) v w c i
   have hsub' := guard_subset_insert S F 13 x v w c i
   have hpost : guardFailures S F 13 (flip x {((w,c),i)}) v ⊆ {w} := by
     intro z hz
     by_cases hzw : z=w
     · exact Finset.mem_singleton.mpr hzw
     · have hzold : z ∈ guardFailures S F 13 x v := by
         have hh := (Finset.mem_filter.mp hz).2
         apply Finset.mem_filter.mpr
         refine ⟨Finset.mem_univ _,hh.1,?_⟩
         rw [child_flip_other x w z c (S.label v z) i (by intro he; exact hzw (congrArg Prod.fst he))] at hh
         exact hh.2
       rw [h13] at hzold
       exact False.elim (Finset.notMem_empty _ hzold)
   have hc : (guardFailures S F 13 (flip x {((w,c),i)}) v).card≤1 :=
     (Finset.card_le_card hpost).trans (by simp)
   have hac := accept4_fifteen Adj loopless label F hF _ v htargets hc
   rw [hdown] at hac
   contradiction

end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

private theorem rowDown14_card
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (b : Fin 5591) (B : ℕ)
 (hB : BBound F 14 17 B) (ht : ∀ c, F 17 (child x b c)=true) :
 (rowDown14 F x b).card≤2*B := by
 have h0 := hB _ (ht false)
 have h1 := hB _ (ht true)
 have hh := Finset.card_union_le
   (lift b false (flipsTo (F 14) false (child x b false)))
   (lift b true (flipsTo (F 14) false (child x b true)))
 simp only [lift,Finset.card_map] at hh
 change (rowDown14 F x b).card ≤ _ at hh
 omega

end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private theorem q0_repair_cases_gap9 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (i : I)
 (hold : ordinaryParent S F 18 6 0 x=false)
 (hnew : ordinaryParent S F 18 6 0 (flip x {((w,c),i)})=true) :
 (guardFailures S F 6 x w=∅ ∧ F 18 (child x w c)=false ∧
   F 18 (child x w (!c))=true ∧ F 18 (flip (child x w c) {i})=true) ∨
 (∃ r, (∀ d, F 18 (child x r d)=true) ∧ guardFailures S F 6 x r={w} ∧
   S.label r w=c ∧ F 6 (flip (child x w c) {i})=false) := by
 obtain ⟨r,hr,hcr⟩ := (parent_iff S F 18 6 0 _).1 hnew
 have hzero : guardFailures S F 6 (flip x {((w,c),i)}) r=∅ := Finset.card_eq_zero.mp (by omega)
 by_cases hrw : r=w
 · subst r
   have hg : guardFailures S F 6 x w=∅ := by rw [guard_self_unchanged] at hzero; exact hzero
   have ho := hr (!c)
   rw [child_flip_other x w w c (!c) i (by cases c <;> simp)] at ho
   have hn := hr c
   rw [child_flip_same] at hn
   have hf : F 18 (child x w c)=false := by
     cases hh : F 18 (child x w c) with
     | false => rfl
     | true =>
       have ht : ∀ d, F 18 (child x w d)=true := by
         intro d
         by_cases hd : d=c
         · simpa [hd] using hh
         · have he : d= !c := by cases c <;> cases d <;> simp_all
           simpa [he] using ho
       have hac := (parent_iff S F 18 6 0 x).2 ⟨w,ht,by rw [hg]; simp⟩
       rw [hold] at hac
       contradiction
   exact Or.inl ⟨hg,hf,ho,hn⟩
 · have ht : ∀ d, F 18 (child x r d)=true := by
     intro d
     have hh := hr d
     rw [child_flip_other x w r c d i (by intro he; exact hrw (congrArg Prod.fst he))] at hh
     exact hh
   have hsub : guardFailures S F 6 x r ⊆ {w} := by
     have hh := guard_subset_insert S F 6 x r w c i
     simpa only [hzero,Finset.insert_empty] using hh
   have hwm : w ∈ guardFailures S F 6 x r := by
     by_contra hn
     have he : guardFailures S F 6 x r=∅ := by
       apply Finset.eq_empty_iff_forall_notMem.mpr
       intro z hz
       have hzw := Finset.mem_singleton.mp (hsub hz)
       subst z; exact hn hz
     have hac := (parent_iff S F 18 6 0 x).2 ⟨r,ht,by rw [he]; simp⟩
     rw [hold] at hac
     contradiction
   have hs : guardFailures S F 6 x r={w} := Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hwm)
   have hh := (Finset.mem_filter.mp hwm).2
   have hl : S.label r w=c := by
     by_contra hn
     have ht6 := hh.2
     have hf : F 6 (child (flip x {((w,c),i)}) w (S.label r w))=true := by
       rw [child_flip_other x w w c (S.label r w) i (by intro he; exact hn (congrArg Prod.snd he))]
       exact ht6
     have hm : w ∈ guardFailures S F 6 (flip x {((w,c),i)}) r := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hf⟩
     rw [hzero] at hm
     exact Finset.notMem_empty _ hm
   have hfalse : F 6 (flip (child x w c) {i})=false := by
     cases hf : F 6 (flip (child x w c) {i}) with
     | false => rfl
     | true =>
       have hm : w ∈ guardFailures S F 6 (flip x {((w,c),i)}) r := by
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
open CandidateCoherence ResidualCaps
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private def targetRows_gap9 (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) : Finset V :=
 Finset.univ.filter fun r => guardFailures S F 6 x r=∅ ∧
   ∃ c, F 18 (child x r c)=false ∧ F 18 (child x r (!c))=true
private def targetColor_gap9 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (r : V) : Bool :=
 if F 18 (child x r false)=false then false else true
private theorem target_color_spec_gap9 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (r : V) (hr : r ∈ targetRows_gap9 S F x) :
 guardFailures S F 6 x r=∅ ∧ F 18 (child x r (targetColor_gap9 F x r))=false ∧
 F 18 (child x r (!(targetColor_gap9 F x r)))=true := by
 obtain ⟨hg,c,hc,ho⟩ := (Finset.mem_filter.mp hr).2
 refine ⟨hg,?_⟩
 cases c
 · simpa [targetColor_gap9,hc] using And.intro hc ho
 · have hh : F 18 (child x r false)=true := ho
   simpa [targetColor_gap9,hh] using And.intro hc ho
private theorem target_label_color_gap9 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h6v : ∀ c, F 6 (child x v c)=true)
 (hg : guardFailures S F 11 x v=∅) (hvn : v ∉ targetRows_gap9 S F x)
 (r : V) (hr : r ∈ targetRows_gap9 S F x) :
 S.Adj v r ∧ S.label v r=targetColor_gap9 F x r ∧
 F 11 (child x r (targetColor_gap9 F x r))=false := by
 have hrv : r≠v := by intro he; subst r; exact hvn hr
 have hs := target_color_spec_gap9 S F x r hr
 have hnorv : ¬S.Adj r v := by
   intro hadj
   have hm : v ∈ guardFailures S F 6 x r := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hadj,h6v (S.label r v)⟩
   rw [hs.1] at hm
   exact Finset.notMem_empty _ hm
 have hadj := (htor v r (Ne.symm hrv)).2 hnorv
 have hfalse : F 11 (child x r (S.label v r))=false := by
   cases hh : F 11 (child x r (S.label v r)) with
   | false => rfl
   | true =>
     have hm : r ∈ guardFailures S F 11 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,hh⟩
     rw [hg] at hm
     exact False.elim (Finset.notMem_empty _ hm)
 have hlabel : S.label v r=targetColor_gap9 F x r := by
   by_contra hn
   have he : S.label v r= !(targetColor_gap9 F x r) := by
     cases he1 : S.label v r <;> cases he2 : targetColor_gap9 F x r <;> simp_all
   have hh := hF 11 18 (by decide) _ hs.2.2
   rw [←he,hfalse] at hh
   contradiction
 exact ⟨hadj,hlabel,by rw [←hlabel]; exact hfalse⟩

theorem phase4_all_target_rows_source_cap_gap9 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 1 19)
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h6v : ∀ c, F 6 (child x v c)=true)
 (hg : guardFailures S F 11 x v=∅) (hvn : v ∉ targetRows_gap9 S F x) :
 (targetRows_gap9 S F x).card≤18 := by
 have hd : Disjoint (targetRows_gap9 S F x) {v} := Finset.disjoint_singleton_right.mpr hvn
 have hc : ({v}:Finset V).card=1 := by simp
 have hdom : ∀ z ∈ ({v}:Finset V), ∀ r ∈ targetRows_gap9 S F x, S.Adj z r := by
   intro z hz r hr
   have hzv := Finset.mem_singleton.mp hz
   subst z
   exact (target_label_color_gap9 S F hF htor x v h6v hg hvn r hr).1
 have hzero : ∀ z ∈ targetRows_gap9 S F x ∪ ({v}:Finset V),
   (mismatch S.Adj S.label (targetRows_gap9 S F x) (targetColor_gap9 F x) z).card=0 := by
   intro z hz
   apply Finset.card_eq_zero.mpr
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro r hr
   obtain ⟨hrT,hadj,hne⟩ := Finset.mem_filter.mp hr
   have hs := target_color_spec_gap9 S F x r hrT
   have he : S.label z r= !(targetColor_gap9 F x r) := by
     cases he1 : S.label z r <;> cases he2 : targetColor_gap9 F x r <;> simp_all
   rcases Finset.mem_union.mp hz with hzT | hzV
   · have hm : r ∈ guardFailures S F 6 x z := Finset.mem_filter.mpr
       ⟨Finset.mem_univ _,hadj,by rw [he]; exact hF 6 18 (by decide) _ hs.2.2⟩
     rw [(target_color_spec_gap9 S F x z hzT).1] at hm
     exact Finset.notMem_empty _ hm
   · have hzv := Finset.mem_singleton.mp hzV
     subst z
     have hl := (target_label_color_gap9 S F hF htor x v h6v hg hvn r hrT).2.1
     exact hne hl
 have hh := hcap (targetRows_gap9 S F x) {v} (targetColor_gap9 F x) hd hc hdom hzero
 omega

private def allTargetCover_gap9 (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
 (targetRows_gap9 S F x).biUnion fun r =>
 lift r (targetColor_gap9 F x r) (flipsTo (F 18) true (child x r (targetColor_gap9 F x r)))

private theorem target_repair_in_cover_gap9 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (r : V) (c : Bool) (i : I)
 (hg : guardFailures S F 6 x r=∅) (hf : F 18 (child x r c)=false)
 (ho : F 18 (child x r (!c))=true) (hp : F 18 (flip (child x r c) {i})=true) :
 ((r,c),i) ∈ allTargetCover_gap9 S F x := by
 have hr : r ∈ targetRows_gap9 S F x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg,c,hf,ho⟩
 have he : targetColor_gap9 F x r=c := by
   cases c
   · simp [targetColor_gap9,hf]
   · have hh : F 18 (child x r false)=true := ho
     simp [targetColor_gap9,hh]
 apply Finset.mem_biUnion.mpr
 refine ⟨r,hr,?_⟩
 apply (mem_lift r r (targetColor_gap9 F x r) c _ i).2
 refine ⟨rfl,he.symm,?_⟩
 simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
 rw [he]; exact hp

private theorem all_target_cover_card_gap9 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 1 19)
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h6v : ∀ c, F 6 (child x v c)=true)
 (hg : guardFailures S F 11 x v=∅) (hvn : v ∉ targetRows_gap9 S F x)
 (s : ℕ) (hS : ABound F 11 18 s) : (allTargetCover_gap9 S F x).card≤18*s := by
 have hn := phase4_all_target_rows_source_cap_gap9 S F hF htor hcap x v h6v hg hvn
 have hh := card_biUnion_mul (targetRows_gap9 S F x)
   (fun r => lift r (targetColor_gap9 F x r) (flipsTo (F 18) true (child x r (targetColor_gap9 F x r)))) s (by
     intro r hr
     have hs := (target_label_color_gap9 S F hF htor x v h6v hg hvn r hr).2.2
     simpa only [lift,Finset.card_map] using hS _ hs)
 exact hh.trans (Nat.mul_le_mul_right s hn)

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_all_target_rows_source_cap_gap9

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

private theorem phase4_accept12
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h18 : ∀ c, F 18 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 7 x v=∅) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 12 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 12 x=true
 have hf : failed S F 12 x v=∅ := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,?_,?_⟩
 · rw [hf]; simp
 · rw [hf]
   change (F 18 (child x v false) && F 18 (child x v true) &&
     (F 18 (child x v false) || F 18 (child x v true)))=true
   simp [h18]

theorem phase4_gap11_witness
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 11 x=true → ∃ v,
 (∀ c, F 17 (child x v c)=true) ∧ (∃ c, F 18 (child x v c)=true) ∧
 guardFailures S F 9 x v=∅ := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 intro h11
 change parent S F 11 x=true at h11
 simp only [parent,decide_eq_true_eq] at h11
 obtain ⟨v,hc,ht⟩ := h11
 have he : failed S F 11 x v=∅ := Finset.card_eq_zero.mp (by change _ ≤ 0 at hc; omega)
 rw [he] at ht
 change (F 17 (child x v false) && F 17 (child x v true) &&
   (F 18 (child x v false) || F 18 (child x v true)))=true at ht
 simp only [Bool.and_eq_true,Bool.or_eq_true] at ht
 refine ⟨v,?_,?_,he⟩
 · intro c; cases c
   · exact ht.1.1
   · exact ht.1.2
 · rcases ht.2 with hh | hh
   · exact ⟨false,hh⟩
   · exact ⟨true,hh⟩

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap11_witness

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

private theorem accept3_zero
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h14 : ∀ c, F 14 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 13 x v=∅) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 3 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 3 x=true
 have hf : failed S F 3 x v=∅ := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,?_,?_⟩
 · rw [hf]; simp
 · rw [hf]
   change (F 14 (child x v false) && F 14 (child x v true) &&
     (F 14 (child x v false) || F 14 (child x v true)))=true
   simp [h14]

private theorem accept3_fifteen
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h15 : ∀ c, F 15 (child x v c)=true)
 (hg : (guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 13 x v).card≤1) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 3 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 3 x=true
 have hf : (failed S F 3 x v).card≤1 := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,by change _ ≤ 2; omega,?_⟩
 have hz : (failed S F 3 x v).card=0 ∨ (failed S F 3 x v).card=1 := by omega
 rcases hz with hz | hz
 · rw [hz]
   change (F 14 (child x v false) && F 14 (child x v true) &&
     (F 14 (child x v false) || F 14 (child x v true)))=true
   simp [hF 14 15 (by decide) _ (h15 false),hF 14 15 (by decide) _ (h15 true)]
 · rw [hz]
   change (F 14 (child x v false) && F 14 (child x v true) &&
     (F 15 (child x v false) || F 15 (child x v true)))=true
   simp [h15,hF 14 15 (by decide) _ (h15 false),hF 14 15 (by decide) _ (h15 true)]

theorem phase4_gap11_destruction
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (ht : ∀ c, F 17 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 9 x v=∅) :
 flipsTo (parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 3) false x ⊆
 rowDown14 F x v := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 have h13 : guardFailures S F 13 x v=∅ := by
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro w hw
   have hh := (Finset.mem_filter.mp hw).2
   have hm : w ∈ guardFailures S F 9 x v := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hh.1,hF 9 13 (by decide) _ hh.2⟩
   rw [hg] at hm
   exact Finset.notMem_empty _ hm
 rintro ⟨⟨w,c⟩,i⟩ hp
 have hdown := (Finset.mem_filter.mp hp).2
 by_cases hwv : w=v
 · subst w
   have hfalse : F 14 (flip (child x v c) {i})=false := by
     cases hh : F 14 (flip (child x v c) {i}) with
     | false => rfl
     | true =>
       have hlow : ∀ d, F 14 (child (flip x {((v,c),i)}) v d)=true := by
         intro d
         by_cases he : d=c
         · subst d; simpa only [child_flip_same] using hh
         · rw [child_flip_other x v v c d i (by intro h; exact he (congrArg Prod.snd h))]
           exact hF 14 17 (by decide) _ (ht d)
       have hup : ∃ d, F 15 (child (flip x {((v,c),i)}) v d)=true := by
         refine ⟨!c,?_⟩
         rw [child_flip_other x v v c (!c) i (by cases c <;> simp)]
         exact hF 15 17 (by decide) _ (ht (!c))
       have hguard : guardFailures S F 13 (flip x {((v,c),i)}) v=∅ := by
         rw [guard_self_unchanged]; exact h13
       have hac := accept3_zero Adj loopless label F _ v hlow hguard
       rw [hdown] at hac
       contradiction
   have hi : i ∈ flipsTo (F 14) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfalse⟩
   cases c
   · exact Finset.mem_union_left _ ((mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩)
   · exact Finset.mem_union_right _ ((mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩)
 · have htargets : ∀ d, F 15 (child (flip x {((w,c),i)}) v d)=true := by
     intro d
     rw [child_flip_other x w v c d i (by intro he; exact hwv (congrArg Prod.fst he).symm)]
     exact hF 15 17 (by decide) _ (ht d)
   have hsub := guard_subset_insert S F 13 (flip x {((w,c),i)}) v w c i
   have hsub' := guard_subset_insert S F 13 x v w c i
   have hpost : guardFailures S F 13 (flip x {((w,c),i)}) v ⊆ {w} := by
     intro z hz
     by_cases hzw : z=w
     · exact Finset.mem_singleton.mpr hzw
     · have hzold : z ∈ guardFailures S F 13 x v := by
         have hh := (Finset.mem_filter.mp hz).2
         apply Finset.mem_filter.mpr
         refine ⟨Finset.mem_univ _,hh.1,?_⟩
         rw [child_flip_other x w z c (S.label v z) i (by intro he; exact hzw (congrArg Prod.fst he))] at hh
         exact hh.2
       rw [h13] at hzold
       exact False.elim (Finset.notMem_empty _ hzold)
   have hc : (guardFailures S F 13 (flip x {((w,c),i)}) v).card≤1 :=
     (Finset.card_le_card hpost).trans (by simp)
   have hac := accept3_fifteen Adj loopless label F hF _ v htargets hc
   rw [hdown] at hac
   contradiction


end
end Sensitivity213981Formal.JointCover

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
open CandidateCoherence ResidualCaps
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private theorem target_label_outside_gap11 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h6v : ∀ c, F 6 (child x v c)=true) (hg : guardFailures S F 9 x v=∅)
 (r : V) (hr : r ∈ targetRows_gap9 S F x) (hrv : r≠v) :
 S.Adj v r ∧ S.label v r=targetColor_gap9 F x r ∧
 F 9 (child x r (targetColor_gap9 F x r))=false := by
 have hs := target_color_spec_gap9 S F x r hr
 have hnorv : ¬S.Adj r v := by
   intro hadj
   have hm : v ∈ guardFailures S F 6 x r := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hadj,h6v (S.label r v)⟩
   rw [hs.1] at hm
   exact Finset.notMem_empty _ hm
 have hadj := (htor v r (Ne.symm hrv)).2 hnorv
 have hfalse : F 9 (child x r (S.label v r))=false := by
   cases hh : F 9 (child x r (S.label v r)) with
   | false => rfl
   | true =>
     have hm : r ∈ guardFailures S F 9 x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,hh⟩
     rw [hg] at hm
     exact False.elim (Finset.notMem_empty _ hm)
 have hlabel : S.label v r=targetColor_gap9 F x r := by
   by_contra hn
   have he : S.label v r= !(targetColor_gap9 F x r) := by
     cases he1 : S.label v r <;> cases he2 : targetColor_gap9 F x r <;> simp_all
   have hh := hF 9 18 (by decide) _ hs.2.2
   rw [←he,hfalse] at hh
   contradiction
 exact ⟨hadj,hlabel,by rw [←hlabel]; exact hfalse⟩

theorem phase4_gap11_outside_target_cap (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 1 19)
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h6v : ∀ c, F 6 (child x v c)=true) (hg : guardFailures S F 9 x v=∅) :
 ((targetRows_gap9 S F x).erase v).card≤18 := by
 let T := (targetRows_gap9 S F x).erase v
 have hd : Disjoint T {v} := Finset.disjoint_singleton_right.mpr (by simp [T])
 have hc : ({v}:Finset V).card=1 := by simp
 have hdom : ∀ z ∈ ({v}:Finset V), ∀ r ∈ T, S.Adj z r := by
   intro z hz r hr
   have hzv := Finset.mem_singleton.mp hz
   subst z
   have hh := Finset.mem_erase.mp hr
   exact (target_label_outside_gap11 S F hF htor x v h6v hg r hh.2 hh.1).1
 have hzero : ∀ z ∈ T ∪ ({v}:Finset V),
   (mismatch S.Adj S.label T (targetColor_gap9 F x) z).card=0 := by
   intro z hz
   apply Finset.card_eq_zero.mpr
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro r hr
   obtain ⟨hrT,hadj,hne⟩ := Finset.mem_filter.mp hr
   have hr' := Finset.mem_erase.mp hrT
   have hs := target_color_spec_gap9 S F x r hr'.2
   have he : S.label z r= !(targetColor_gap9 F x r) := by
     cases he1 : S.label z r <;> cases he2 : targetColor_gap9 F x r <;> simp_all
   rcases Finset.mem_union.mp hz with hzT | hzV
   · have hm : r ∈ guardFailures S F 6 x z := Finset.mem_filter.mpr
       ⟨Finset.mem_univ _,hadj,by rw [he]; exact hF 6 18 (by decide) _ hs.2.2⟩
     rw [(target_color_spec_gap9 S F x z (Finset.mem_erase.mp hzT).2).1] at hm
     exact Finset.notMem_empty _ hm
   · have hzv := Finset.mem_singleton.mp hzV
     subst z
     have hl := (target_label_outside_gap11 S F hF htor x v h6v hg r hr'.2 hr'.1).2.1
     exact hne hl
 have hh := hcap T {v} (targetColor_gap9 F x) hd hc hdom hzero
 change T.card≤18
 omega

private def outsideTargetCover_gap11 (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
 ((targetRows_gap9 S F x).erase v).biUnion fun r =>
 lift r (targetColor_gap9 F x r) (flipsTo (F 18) true (child x r (targetColor_gap9 F x r)))

private theorem target_repair_outside_gap11 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (v r : V) (c : Bool) (i : I) (hrv : r≠v)
 (hg : guardFailures S F 6 x r=∅) (hf : F 18 (child x r c)=false)
 (ho : F 18 (child x r (!c))=true) (hp : F 18 (flip (child x r c) {i})=true) :
 ((r,c),i) ∈ outsideTargetCover_gap11 S F x v := by
 have hr : r ∈ targetRows_gap9 S F x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg,c,hf,ho⟩
 have he : targetColor_gap9 F x r=c := by
   cases c
   · simp [targetColor_gap9,hf]
   · have hh : F 18 (child x r false)=true := ho
     simp [targetColor_gap9,hh]
 apply Finset.mem_biUnion.mpr
 refine ⟨r,Finset.mem_erase.mpr ⟨hrv,hr⟩,?_⟩
 apply (mem_lift r r (targetColor_gap9 F x r) c _ i).2
 refine ⟨rfl,he.symm,?_⟩
 simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
 rw [he]; exact hp

private theorem outside_target_cover_card_gap11 (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 1 19)
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h6v : ∀ c, F 6 (child x v c)=true) (hg : guardFailures S F 9 x v=∅)
 (s : ℕ) (hS : ABound F 9 18 s) : (outsideTargetCover_gap11 S F x v).card≤18*s := by
 have hn := phase4_gap11_outside_target_cap S F hF htor hcap x v h6v hg
 have hh := card_biUnion_mul ((targetRows_gap9 S F x).erase v)
   (fun r => lift r (targetColor_gap9 F x r) (flipsTo (F 18) true (child x r (targetColor_gap9 F x r)))) s (by
     intro r hr
     have hr' := Finset.mem_erase.mp hr
     have hs := (target_label_outside_gap11 S F hF htor x v h6v hg r hr'.2 hr'.1).2.2
     simpa only [lift,Finset.card_map] using hS _ hs)
 exact hh.trans (Nat.mul_le_mul_right s hn)

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap11_outside_target_cap

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

theorem phase4_gap11_self_candidate_iff
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h18 : ∃ c, F 18 (child x v c)=true)
 (h12 : parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 12 x=false) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 v ∈ targetRows_gap9 S F x ↔ guardFailures S F 6 x v=∅ := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 simp only [targetRows_gap9,Finset.mem_filter,Finset.mem_univ,true_and]
 constructor
 · intro hv; exact hv.1
 · intro hg
   have he7 : guardFailures S F 7 x v=∅ := by
     apply Finset.eq_empty_iff_forall_notMem.mpr
     intro r hr
     have hh := (Finset.mem_filter.mp hr).2
     have hm : r ∈ guardFailures S F 6 x v := Finset.mem_filter.mpr
       ⟨Finset.mem_univ _,hh.1,hF 6 7 (by decide) _ hh.2⟩
     rw [hg] at hm
     exact Finset.notMem_empty _ hm
   obtain ⟨c,hc⟩ := h18
   have ho : F 18 (child x v (!c))=false := by
     cases hh : F 18 (child x v (!c)) with
     | false => rfl
     | true =>
       have ht : ∀ d, F 18 (child x v d)=true := by
         intro d
         by_cases hd : d=c
         · simpa [hd] using hc
         · have he : d= !c := by cases c <;> cases d <;> simp_all
           simpa [he] using hh
       have hac := phase4_accept12 Adj loopless label F x v ht he7
       rw [h12] at hac
       contradiction
   refine ⟨hg,!c,ho,?_⟩
   simpa using hc

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap11_self_candidate_iff

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
open CandidateCoherence ResidualCaps
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

theorem phase4_gap11_joint_bound
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (B g s q : ℕ) (hB : BBound F 14 17 B) (hG : ∀ y, F 7 y=true → F 9 y=false → (flipsTo (F 6) false y).card≤g) (hS : ABound F 9 18 s)
 (hQ : ∀ y, F 17 y=true → F 18 y=false → (flipsTo (F 18) true y).card≤q)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 11 x=true → parent S F 12 x=false →
 (flipsTo (parent S F 3) false x ∪ flipsTo (parent S F 13) true x).card≤2*B+18*s+max g q := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 intro h11 h12
 obtain ⟨v,h17,h18,hg⟩ := phase4_gap11_witness Adj loopless label F x h11
 have h6v : ∀ c, F 6 (child x v c)=true := fun c => hF 6 17 (by decide) _ (h17 c)
 have htarget : ∀ d y z, S.target 13 d y z=(F 18 y && F 18 z) := by
   intro d y z
   dsimp [S,MinMaxRecipe.stage,minmaxTarget,Sensitivity5591Endpoint22.recipe,
     Sensitivity5591Endpoint22.entry,Sensitivity5591Endpoint22.entries3,
     Sensitivity5591Endpoint22.Entry.threshold,Sensitivity5591Endpoint22.Entry.upper]
   cases hy : F 18 y <;> cases hz : F 18 z <;> simp [hy,hz]
 have e13 := parent_specialize S F 13 18 6 0 (by rfl) (by rfl) htarget
 have hold : ordinaryParent S F 18 6 0 x=false := by
   cases hh : ordinaryParent S F 18 6 0 x with
   | false => rfl
   | true =>
     obtain ⟨r,hrt,hrg⟩ := (parent_iff S F 18 6 0 x).1 hh
     have he6 : guardFailures S F 6 x r=∅ := Finset.card_eq_zero.mp (by omega)
     have he7 : guardFailures S F 7 x r=∅ := by
       apply Finset.eq_empty_iff_forall_notMem.mpr
       intro z hz
       have hz' := (Finset.mem_filter.mp hz).2
       have hm : z ∈ guardFailures S F 6 x r := Finset.mem_filter.mpr
         ⟨Finset.mem_univ _,hz'.1,hF 6 7 (by decide) _ hz'.2⟩
       rw [he6] at hm
       exact Finset.notMem_empty _ hm
     have hac := phase4_accept12 Adj loopless label F x r hrt he7
     rw [h12] at hac
     contradiction

 have hm : flipsTo (parent S F 3) false x ⊆ rowDown14 F x v :=
   phase4_gap11_destruction Adj loopless label F hF x v h17 hg
 have hc := rowDown14_card F x v B hB h17
 have ht := outside_target_cover_card_gap11 S F hF htor (by
   intro A M color hd hc hdom hz
   apply hcap A M color hd hc hdom
   intro z hzmem
   apply hz z
   simpa only [Finset.mem_union] using hzmem) x v h6v hg s hS
 have guard_location (r z : Fin 5591)
   (htr : ∀ c, F 18 (child x r c)=true) (hr : guardFailures S F 6 x r={z}) :
   r=v ∨ z=v := by
   by_cases hrv : r=v
   · exact Or.inl hrv
   · right
     have hno : ¬Adj v r := by
       intro hadj
       have hh : r ∈ guardFailures S F 9 x v := Finset.mem_filter.mpr
         ⟨Finset.mem_univ _,hadj,hF 9 18 (by decide) _ (htr (label v r))⟩
       rw [hg] at hh
       exact Finset.notMem_empty _ hh
     have hrvAdj := (htor r v hrv).2 hno
     have hh : v ∈ guardFailures S F 6 x r := Finset.mem_filter.mpr
       ⟨Finset.mem_univ _,hrvAdj,h6v (label r v)⟩
     rw [hr] at hh
     exact (Finset.mem_singleton.mp hh).symm
 have post6_in_row (c : Bool) (i : I) (hf : F 6 (flip (child x v c) {i})=false) :
   ((v,c),i) ∈ rowDown14 F x v := by
   have h14 : F 14 (flip (child x v c) {i})=false := by
     cases hh : F 14 (flip (child x v c) {i}) with
     | false => rfl
     | true =>
       have h6 := hF 6 14 (by decide) _ hh
       rw [hf] at h6
       contradiction
   have hi : i ∈ flipsTo (F 14) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h14⟩
   cases c
   · exact Finset.mem_union_left _ ((mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩)
   · exact Finset.mem_union_right _ ((mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩)
 have externalGap (z : Fin 5591) (htr : ∀ c, F 18 (child x v c)=true)
   (hr : guardFailures S F 6 x v={z}) :
   F 7 (child x z (S.label v z))=true ∧ F 9 (child x z (S.label v z))=false := by
   have hne : guardFailures S F 7 x v≠∅ := by
     intro he
     have hac := phase4_accept12 Adj loopless label F x v htr he
     rw [h12] at hac
     contradiction
   obtain ⟨r,hm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
   have hh := (Finset.mem_filter.mp hm).2
   have hm6 : r ∈ guardFailures S F 6 x v := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hh.1,hF 6 7 (by decide) _ hh.2⟩
   rw [hr] at hm6
   have hrz := Finset.mem_singleton.mp hm6
   subst r
   refine ⟨hh.2,?_⟩
   cases hf : F 9 (child x z (S.label v z)) with
   | false => rfl
   | true =>
     have hm9 : z ∈ guardFailures S F 9 x v := Finset.mem_filter.mpr
       ⟨Finset.mem_univ _,hh.1,hf⟩
     rw [hg] at hm9
     exact False.elim (Finset.notMem_empty _ hm9)
 change (flipsTo (parent S F 3) false x ∪ flipsTo (parent S F 13) true x).card≤_
 rw [e13]
 by_cases hz : (guardFailures S F 6 x v).card=0
 · have hzero : guardFailures S F 6 x v=∅ := Finset.card_eq_zero.mp hz
   let E :=
     (if F 18 (child x v false)=false ∧ F 18 (child x v true)=true then
       lift v false (flipsTo (F 18) true (child x v false)) else ∅) ∪
     (if F 18 (child x v true)=false ∧ F 18 (child x v false)=true then
       lift v true (flipsTo (F 18) true (child x v true)) else ∅)
   have he : E.card≤q := by
     cases hf : F 18 (child x v false) <;> cases ht' : F 18 (child x v true)
     · simp [E,hf,ht']
     · simpa [E,hf,ht',lift] using hQ _ (h17 false) hf
     · simpa [E,hf,ht',lift] using hQ _ (h17 true) ht'
     · simp [E,hf,ht']
   have hs : flipsTo (parent S F 3) false x ∪ flipsTo (ordinaryParent S F 18 6 0) true x ⊆
     rowDown14 F x v ∪ (outsideTargetCover_gap11 S F x v ∪ E) := by
     rintro ⟨⟨z,c⟩,i⟩ hp
     rcases Finset.mem_union.mp hp with hd | hp
     · exact Finset.mem_union_left _ (hm hd)
     · rcases q0_repair_cases_gap9 S F x z c i hold (Finset.mem_filter.mp hp).2 with htar | hgu
       · by_cases hzv : z=v
         · subst z
           have hf := htar.2.1
           have ho := htar.2.2.1
           have hi : i ∈ flipsTo (F 18) true (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,htar.2.2.2⟩
           apply Finset.mem_union_right
           apply Finset.mem_union_right
           cases c
           · simp only [Bool.not_false] at ho
             apply Finset.mem_union_left
             simp only [E,hf,ho,and_self,if_true]
             exact (mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩
           · simp only [Bool.not_true] at ho
             apply Finset.mem_union_right
             simp only [E,hf,ho,and_self,if_true]
             exact (mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩
         · exact Finset.mem_union_right _ (Finset.mem_union_left _
             (target_repair_outside_gap11 S F x v z c i hzv htar.1 htar.2.1 htar.2.2.1 htar.2.2.2))
       · obtain ⟨r,htr,hr,hl,hpost⟩ := hgu
         rcases guard_location r z htr hr with hrv | hzv
         · subst r; rw [hzero] at hr
           have hh : z ∈ (∅:Finset (Fin 5591)) := by rw [hr]; simp
           exact False.elim (Finset.notMem_empty _ hh)
         · subst z
           exact Finset.mem_union_left _ (post6_in_row c i hpost)
   have hb1 := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
   have hb2 := Finset.card_union_le (outsideTargetCover_gap11 S F x v) E
   have hqmax := Nat.le_max_right g q
   omega
 · by_cases hs1 : (guardFailures S F 6 x v).card=1
   · obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hs1
     let E := if F 7 (child x w (S.label v w))=true ∧ F 9 (child x w (S.label v w))=false then
       lift w (S.label v w) (flipsTo (F 6) false (child x w (S.label v w))) else ∅
     have he : E.card≤g := by
       by_cases hh : F 7 (child x w (S.label v w))=true ∧ F 9 (child x w (S.label v w))=false
       · simpa only [E,hh,and_self,if_true,lift,Finset.card_map] using hG _ hh.1 hh.2
       · simp [E,hh]
     have hs : flipsTo (parent S F 3) false x ∪ flipsTo (ordinaryParent S F 18 6 0) true x ⊆
       rowDown14 F x v ∪ (outsideTargetCover_gap11 S F x v ∪ E) := by
       rintro ⟨⟨z,c⟩,i⟩ hp
       rcases Finset.mem_union.mp hp with hd | hp
       · exact Finset.mem_union_left _ (hm hd)
       · rcases q0_repair_cases_gap9 S F x z c i hold (Finset.mem_filter.mp hp).2 with htar | hgu
         · have hzv : z≠v := by intro he; subst z; apply hz; rw [htar.1]; simp
           exact Finset.mem_union_right _ (Finset.mem_union_left _
             (target_repair_outside_gap11 S F x v z c i hzv htar.1 htar.2.1 htar.2.2.1 htar.2.2.2))
         · obtain ⟨r,htr,hr,hl,hpost⟩ := hgu
           rcases guard_location r z htr hr with hrv | hzv
           · subst r
             have hzw : z=w := by
               have hmem : z ∈ guardFailures S F 6 x v := by rw [hr]; simp
               rw [hw] at hmem
               exact Finset.mem_singleton.mp hmem
             subst z
             have hgapw := externalGap w htr hr
             apply Finset.mem_union_right
             apply Finset.mem_union_right
             change ((w,c),i) ∈ E
             dsimp only [E]
             rw [if_pos hgapw]
             apply (mem_lift w w (S.label v w) c _ i).2
             refine ⟨rfl,hl.symm,?_⟩
             simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
             rw [hl]; exact hpost
           · subst z
             exact Finset.mem_union_left _ (post6_in_row c i hpost)
     have hb1 := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
     have hb2 := Finset.card_union_le (outsideTargetCover_gap11 S F x v) E
     have hgmax := Nat.le_max_left g q
     omega
   · have hs : flipsTo (parent S F 3) false x ∪ flipsTo (ordinaryParent S F 18 6 0) true x ⊆
       rowDown14 F x v ∪ outsideTargetCover_gap11 S F x v := by
       rintro ⟨⟨z,c⟩,i⟩ hp
       rcases Finset.mem_union.mp hp with hd | hp
       · exact Finset.mem_union_left _ (hm hd)
       · rcases q0_repair_cases_gap9 S F x z c i hold (Finset.mem_filter.mp hp).2 with htar | hgu
         · have hzv : z≠v := by intro he; subst z; apply hz; rw [htar.1]; simp
           exact Finset.mem_union_right _
             (target_repair_outside_gap11 S F x v z c i hzv htar.1 htar.2.1 htar.2.2.1 htar.2.2.2)
         · obtain ⟨r,htr,hr,hl,hpost⟩ := hgu
           rcases guard_location r z htr hr with hrv | hzv
           · subst r; apply False.elim; apply hs1; rw [hr]; simp
           · subst z
             exact Finset.mem_union_left _ (post6_in_row c i hpost)
     have hb1 := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
     omega

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap11_joint_bound

open Sensitivity213981Formal Sensitivity213981Formal.ThreeBoundWitness
open Sensitivity213981Formal.ThreeBoundProfiles
open scoped Classical

theorem endpoint22_phase3_gap11_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : Sensitivity213981Formal.ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 17 2041395696528705380)
 (hM7 : ∀ y, F 7 y=true → F 8 y=false → (flipsTo (F 6) false y).card≤150358948041692066811)
 (hM8 : ∀ y, F 8 y=true → F 9 y=false → (flipsTo (F 6) false y).card≤146185162351149245833)
 (hS : ABound F 9 18 98368454968486)
 (hQ : ∀ y, F 17 y=true → F 18 y=false → (flipsTo (F 18) true y).card≤2871710707230501566)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 11 x=true → parent S F 12 x=false →
 (flipsTo (parent S F 3) false x ∪ flipsTo (parent S F 13) true x).card≤154443510066938910319 := by
 have hG : ∀ y, F 7 y=true → F 9 y=false →
   (flipsTo (F 6) false y).card≤150358948041692066811 := by
   intro y h7 h9
   cases h8 : F 8 y with
   | false => exact hM7 y h7 h8
   | true => exact (hM8 y h8 h9).trans (by decide +kernel)
 have hh := Sensitivity213981Formal.JointCover.phase4_gap11_joint_bound
   Adj loopless label htor hcap F hF
   2041395696528705380 150358948041692066811 98368454968486 2871710707230501566 hB hG hS hQ x
 exact hh

#print axioms endpoint22_phase3_gap11_bound

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
noncomputable section
open scoped Classical

private theorem gap11_joint_ordered {K : Type} [Fintype K]
 (G : Fin 22 → (K → Bool) → Bool) (hG : Nested G)
 (i l : Fin 22) (hi : i≤3) (hl : 13≤l) (x : K → Bool) (R : ℕ)
 (h : (flipsTo (G 3) false x ∪ flipsTo (G 13) true x).card≤R) :
 (flipsTo (G i) false x ∪ flipsTo (G l) true x).card≤R := by
 apply (Finset.card_le_card (show flipsTo (G i) false x ∪ flipsTo (G l) true x ⊆
   flipsTo (G 3) false x ∪ flipsTo (G 13) true x from ?_)).trans h
 intro z hz
 rcases Finset.mem_union.mp hz with hd | hu
 · apply Finset.mem_union_left
   apply Finset.mem_filter.mpr
   refine ⟨Finset.mem_univ _,?_⟩
   cases he : G 3 (flip x {z}) with
   | false => rfl
   | true =>
     have hh := hG i 3 hi _ he
     rw [(Finset.mem_filter.mp hd).2] at hh
     contradiction
 · apply Finset.mem_union_right
   apply Finset.mem_filter.mpr
   exact ⟨Finset.mem_univ _,hG 13 l hl _ (Finset.mem_filter.mp hu).2⟩

theorem phase4_gap11_closed_family {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 17 2041395696528705380)
 (hM7 : ∀ y, F 7 y=true → F 8 y=false → (flipsTo (F 6) false y).card≤150358948041692066811)
 (hM8 : ∀ y, F 8 y=true → F 9 y=false → (flipsTo (F 6) false y).card≤146185162351149245833)
 (hS : ABound F 9 18 98368454968486)
 (hQ : ∀ y, F 17 y=true → F 18 y=false → (flipsTo (F 18) true y).card≤2871710707230501566) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 let G := parent S F
 Nested G → ∀ (i l : Fin 22), i≤3 → 13≤l → ∀ x,
 G 11 x=true → G 12 x=false →
 (flipsTo (G i) false x ∪ flipsTo (G l) true x).card≤154443510066938910319 := by
 dsimp only
 intro hN i l hi hl x h11 h12
 have hh := endpoint22_phase3_gap11_bound Adj loopless label htor hcap F hF hB hM7 hM8 hS hQ x h11 h12
 have h := gap11_joint_ordered _ hN i l hi hl x 154443510066938910319 (by
   convert hh using 1 <;> congr 1 <;> ext z <;> simp only [Finset.mem_union])
 convert h using 1 <;> congr 1 <;> ext z <;> simp only [Finset.mem_union]

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_gap11_closed_family

theorem solution {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : Sensitivity213981Formal.ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 17 2041395696528705380)
 (hM7 : ∀ y, F 7 y=true → F 8 y=false → (flipsTo (F 6) false y).card≤150358948041692066811)
 (hM8 : ∀ y, F 8 y=true → F 9 y=false → (flipsTo (F 6) false y).card≤146185162351149245833)
 (hS : ABound F 9 18 98368454968486)
 (hQ : ∀ y, F 17 y=true → F 18 y=false → (flipsTo (F 18) true y).card≤2871710707230501566)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 11 x=true → parent S F 12 x=false →
 (flipsTo (parent S F 3) false x ∪ flipsTo (parent S F 13) true x).card≤154443510066938910319 := by
 exact endpoint22_phase3_gap11_bound Adj loopless label htor hcap F hF hB hM7 hM8 hS hQ x
