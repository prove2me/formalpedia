-- Prove2me | solution 1 for SensitivityJointCover.endpoint22_phase3_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @jennyuxi
-- created : 2026-11-13T06:31:33.749315+00:00
-- url     : https://prove2.me/submissions/2226e2bc-9dd2-4a92-a2a3-b3e24cda2f83

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

theorem phase4_two_heads_force_sink
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ r z, r≠z → (Adj r z ↔ ¬Adj z r))
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (a b : Fin 5591) (hab : Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 10 x=true → parent S F 11 x=false →
 (guardFailures S F 0 x a).card=1 → (guardFailures S F 0 x b).card=1 →
 (∀ c, F 17 (child x b c)=true) ∧ guardFailures S F 11 x b=∅ ∧
 ∃ w, guardFailures S F 0 x b={w} ∧
   F 9 (child x w (label b w))=true ∧ F 11 (child x w (label b w))=false := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 intro h10 h11 hca hcb
 change (guardFailures S F 0 x a).card=1 at hca
 change (guardFailures S F 0 x b).card=1 at hcb
 obtain ⟨v,h17,h18,hg⟩ := phase4_row10 Adj loopless label F x h10
 have nohead (r : Fin 5591) (hr : ∀ c, F 21 (child x r c)=true) : ¬Adj v r := by
   intro h
   have hm : r ∈ guardFailures S F 11 x v := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,h,hF 11 21 (by decide) _ (hr (label v r))⟩
   rw [hg] at hm
   exact Finset.notMem_empty _ hm
 have hva : v≠a := by
   intro h
   apply nohead b htb
   simpa [h] using hab
 have hav := (htor a v (Ne.symm hva)).2 (nohead a hta)
 have hmb : b ∈ guardFailures S F 0 x a := Finset.mem_filter.mpr
   ⟨Finset.mem_univ _,hab,hF 0 21 (by decide) _ (htb (label a b))⟩
 have hmv : v ∈ guardFailures S F 0 x a := Finset.mem_filter.mpr
   ⟨Finset.mem_univ _,hav,hF 0 17 (by decide) _ (h17 (label a v))⟩
 have hvb := (Finset.card_le_one.mp (by omega : (guardFailures S F 0 x a).card≤1)) v hmv b hmb
 subst v
 obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hcb
 have h9nonempty : guardFailures S F 9 x b ≠ ∅ := by
   intro he
   have hf : failed S F 11 x b=∅ := he
   have hp : parent S F 11 x=true := by
     simp only [parent,decide_eq_true_eq]
     refine ⟨b,?_,?_⟩
     · rw [hf]; simp
     · rw [hf]
       change (F 17 (child x b false) && F 17 (child x b true) &&
         (F 18 (child x b false) || F 18 (child x b true)))=true
       rw [h17 false,h17 true]
       rcases h18 with ⟨c,hc⟩
       cases c <;> simp [hc]
   rw [h11] at hp
   contradiction
 obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr h9nonempty
 have hh := (Finset.mem_filter.mp hz).2
 have hm0 : z ∈ guardFailures S F 0 x b := Finset.mem_filter.mpr
   ⟨Finset.mem_univ _,hh.1,hF 0 9 (by decide) _ hh.2⟩
 rw [hw] at hm0
 have hzw := Finset.mem_singleton.mp hm0
 subst z
 have hnot11 : F 11 (child x w (label b w))=false := by
   cases ht : F 11 (child x w (label b w)) with
   | false => rfl
   | true =>
     have hm : w ∈ guardFailures S F 11 x b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,ht⟩
     rw [hg] at hm
     exact False.elim (Finset.notMem_empty _ hm)
 exact ⟨h17,hg,w,hw,hh.2,hnot11⟩

private theorem phase4_repair_at_sink_in_cover
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ r z, r≠z → (Adj r z ↔ ¬Adj z r))
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (b : Fin 5591)
 (htb : ∀ c, F 21 (child x b c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 11 x b=∅)
 (hb : (guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 0 x b).card=1)
 (c : Bool) (i : I)
 (hnew : parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 21 (flip x {((b,c),i)})=true) :
 ((b,c),i) ∈ rowDown14 F x b := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 21 (flip x {((b,c),i)})=true at hnew
 simp only [parent,decide_eq_true_eq] at hnew
 obtain ⟨r,hcard,ht⟩ := hnew
 have he : failed S F 21 (flip x {((b,c),i)}) r=∅ :=
   Finset.card_eq_zero.mp (by change _ ≤ 0 at hcard; omega)
 have hg0 : guardFailures S F 0 (flip x {((b,c),i)}) r=∅ := he
 have hrb : r≠b := by
   intro h; subst r
   rw [guard_self_unchanged] at hg0
   rw [hg0] at hb
   simp at hb
 rw [he] at ht
 change (F 21 (child (flip x {((b,c),i)}) r false) && F 21 (child (flip x {((b,c),i)}) r true) &&
   (F 21 (child (flip x {((b,c),i)}) r false) || F 21 (child (flip x {((b,c),i)}) r true)))=true at ht
 simp only [Bool.and_eq_true] at ht
 have htr : ∀ d, F 21 (child x r d)=true := by
   intro d
   have hh : F 21 (child (flip x {((b,c),i)}) r d)=true := by
     cases d
     · exact ht.1.1
     · exact ht.1.2
   rw [child_flip_other x b r c d i (by intro heq; exact hrb (congrArg Prod.fst heq))] at hh
   exact hh
 have hno : ¬Adj b r := by
   intro h
   have hm : r ∈ guardFailures S F 11 x b := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,h,hF 11 21 (by decide) _ (htr (label b r))⟩
   rw [hg] at hm
   exact Finset.notMem_empty _ hm
 have hrbAdj := (htor r b hrb).2 hno
 have hpost0 : F 0 (child (flip x {((b,c),i)}) b (label r b))=false := by
   cases hh : F 0 (child (flip x {((b,c),i)}) b (label r b)) with
   | false => rfl
   | true =>
     have hm : b ∈ guardFailures S F 0 (flip x {((b,c),i)}) r :=
       Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrbAdj,hh⟩
     rw [hg0] at hm
     exact False.elim (Finset.notMem_empty _ hm)
 have hlab : label r b=c := by
   by_contra hn
   rw [child_flip_other x b b c (label r b) i (by intro heq; exact hn (congrArg Prod.snd heq))] at hpost0
   have hh := hF 0 21 (by decide) _ (htb (label r b))
   rw [hpost0] at hh
   contradiction
 rw [hlab,child_flip_same] at hpost0
 have hpost14 : F 14 (flip (child x b c) {i})=false := by
   cases hh : F 14 (flip (child x b c) {i}) with
   | false => rfl
   | true =>
     have h0 := hF 0 14 (by decide) _ hh
     rw [hpost0] at h0
     contradiction
 have hi : i ∈ flipsTo (F 14) false (child x b c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpost14⟩
 cases c
 · exact Finset.mem_union_left _ ((mem_lift b b false false _ i).2 ⟨rfl,rfl,hi⟩)
 · exact Finset.mem_union_right _ ((mem_lift b b true true _ i).2 ⟨rfl,rfl,hi⟩)

theorem phase4_two_head_joint_cover
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ r z, r≠z → (Adj r z ↔ ¬Adj z r))
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (a b : Fin 5591) (hab : Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 10 x=true → parent S F 11 x=false →
 (guardFailures S F 0 x a).card=1 → (guardFailures S F 0 x b).card=1 →
 let P := flipsTo (parent S F 21) true x
 flipsTo (parent S F 4) false x ∪ P ⊆
 rowDown14 F x b ∪ P.filter (fun z => z.1.1≠b) := by
 dsimp only
 intro h10 h11 ha hb
 obtain ⟨h17,hg,w,hw,h9,hnot11⟩ := phase4_two_heads_force_sink
   Adj loopless label htor F hF x a b hab hta htb h10 h11 ha hb
 have hd := phase4_destruction_supported_at_witness Adj loopless label F hF x b h17 hg
 rintro ⟨⟨v,c⟩,i⟩ hp
 rcases Finset.mem_union.mp hp with hm | hp
 · exact Finset.mem_union_left _ (hd hm)
 · by_cases hvb : v=b
   · subst v
     apply Finset.mem_union_left
     exact phase4_repair_at_sink_in_cover Adj loopless label htor F hF x b htb hg hb c i
       (Finset.mem_filter.mp hp).2
   · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hvb⟩)

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_two_heads_force_sink
#print axioms Sensitivity213981Formal.JointCover.phase4_two_head_joint_cover

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

theorem phase4_maximal_case_counted_cover
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ r z, r≠z → (Adj r z ↔ ¬Adj z r))
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (a b : Fin 5591) (hab : Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true)
 (B : ℕ) (hB : BBound F 14 17 B) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 10 x=true → parent S F 11 x=false →
 (guardFailures S F 0 x a).card=1 → (guardFailures S F 0 x b).card=1 →
 let P := flipsTo (parent S F 21) true x
 (flipsTo (parent S F 4) false x ∪ P).card ≤
   2*B + (P.filter (fun z => z.1.1≠b)).card := by
 dsimp only
 intro h10 h11 ha hb
 have hsub := phase4_two_head_joint_cover Adj loopless label htor F hF x a b hab hta htb h10 h11 ha hb
 have ht : ∀ c, F 17 (child x b c)=true := fun c => hF 17 21 (by decide) _ (htb c)
 have hc := rowDown14_card F x b B hB ht
 exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hc _))

theorem phase4_equality_forces_full_row_cover
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (b : Fin 5591)
 (ht : ∀ c, F 17 (child x b c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 11 x b=∅)
 (B : ℕ) (hB : BBound F 14 17 B)
 (heq : (flipsTo (parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 4) false x).card=2*B) :
 flipsTo (parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 4) false x = rowDown14 F x b := by
 apply Finset.eq_of_subset_of_card_le
 · exact phase4_destruction_supported_at_witness Adj loopless label F hF x b ht hg
 · rw [heq]
   exact rowDown14_card F x b B hB ht

theorem phase4_joint_overlap_credit
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ r z, r≠z → (Adj r z ↔ ¬Adj z r))
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((Fin 5591 × Bool) × I) → Bool) (a b : Fin 5591) (hab : Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true)
 (B : ℕ) (hB : BBound F 14 17 B) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 10 x=true → parent S F 11 x=false →
 (guardFailures S F 0 x a).card=1 → (guardFailures S F 0 x b).card=1 →
 let P := flipsTo (parent S F 21) true x
 (flipsTo (parent S F 4) false x ∪ P).card +
   (P.filter (fun z => z.1.1=b)).card ≤ 2*B + P.card := by
 dsimp only
 intro h10 h11 ha hb
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 let P := flipsTo (parent S F 21) true x
 have hc := phase4_maximal_case_counted_cover Adj loopless label htor F hF x a b hab hta htb B hB h10 h11 ha hb
 have hp : (P.filter (fun z => z.1.1=b)).card +
     (P.filter (fun z => z.1.1≠b)).card = P.card := by
   convert Finset.card_filter_add_card_filter_not (s:=P) (fun z => z.1.1=b) using 1 <;>
     congr 1 <;> ext z <;> simp only [Finset.mem_filter]
 dsimp only [P,S] at hp
 change _ + _ ≤ _
 omega

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_maximal_case_counted_cover
#print axioms Sensitivity213981Formal.JointCover.phase4_equality_forces_full_row_cover

#print axioms Sensitivity213981Formal.JointCover.phase4_joint_overlap_credit

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
open CandidateCoherence ResidualCaps
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private def negRows (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) : Finset V :=
 Finset.univ.filter fun r => guardFailures S F 0 x r=∅ ∧
   ∃ c, F 0 (child x r c)=false ∧ F 21 (child x r (!c))=true

private def negColor (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (r : V) : Bool :=
 if F 0 (child x r false)=false then false else true

private theorem neg_color_spec (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((V × Bool) × I) → Bool) (r : V) (hr : r ∈ negRows S F x) :
 guardFailures S F 0 x r=∅ ∧ F 0 (child x r (negColor F x r))=false ∧
   F 21 (child x r (!(negColor F x r)))=true := by
 obtain ⟨hg,c,hc,ho⟩ := (Finset.mem_filter.mp hr).2
 refine ⟨hg,?_⟩
 cases c
 · simpa [negColor,hc] using And.intro hc ho
 · have hf : F 0 (child x r false)=true := hF 0 21 (by decide) _ ho
   simpa [negColor,hf] using And.intro hc ho

private theorem neg_mismatch_implies_failure (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((V × Bool) × I) → Bool) (v r : V)
 (hr : r ∈ mismatch S.Adj S.label (negRows S F x) (negColor F x) v) :
 r ∈ guardFailures S F 0 x v := by
 obtain ⟨hN,hadj,hn⟩ := Finset.mem_filter.mp hr
 have hs := neg_color_spec S F hF x r hN
 have he : S.label v r = !(negColor F x r) := by
   cases he1 : S.label v r <;> cases he2 : negColor F x r <;> simp_all
 exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,by rw [he]; exact hF 0 21 (by decide) _ hs.2.2⟩

private theorem neg_not_high (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((V × Bool) × I) → Bool) (r : V) (hr : r ∈ negRows S F x)
 (ht : ∀ c, F 0 (child x r c)=true) : False := by
 have hs := neg_color_spec S F hF x r hr
 have hh := ht (negColor F x r)
 rw [hs.2.1] at hh
 contradiction

private theorem high_dominates_neg (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (x : ((V × Bool) × I) → Bool) (a r : V)
 (hta : ∀ c, F 0 (child x a c)=true) (hr : r ∈ negRows S F x) : S.Adj a r := by
 have har : a≠r := by
   intro he; subst a
   exact neg_not_high S F hF x r hr hta
 apply (htor a r har).2
 intro hra
 have hg := (neg_color_spec S F hF x r hr).1
 have hm : a ∈ guardFailures S F 0 x r :=
   Finset.mem_filter.mpr ⟨Finset.mem_univ _,hra,hta (S.label r a)⟩
 rw [hg] at hm
 exact Finset.notMem_empty _ hm

private theorem external_not_negative (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (x : ((V × Bool) × I) → Bool) (b w : V)
 (h9 : F 9 (child x w (S.label b w))=true)
 (h11 : F 11 (child x w (S.label b w))=false) : w ∉ negRows S F x := by
 intro hw
 have hs := neg_color_spec S F hF x w hw
 have hn : S.label b w ≠ negColor F x w := by
   intro he
   have hh := hF 0 9 (by decide) _ h9
   rw [he,hs.2.1] at hh
   contradiction
 have he : S.label b w = !(negColor F x w) := by
   cases he1 : S.label b w <;> cases he2 : negColor F x w <;> simp_all
 have hh := hF 11 21 (by decide) _ hs.2.2
 rw [←he,h11] at hh
 contradiction

theorem phase4_two_head_negative_cap (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 2 17)
 (x : ((V × Bool) × I) → Bool) (a b w : V) (hab : S.Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true)
 (ha : guardFailures S F 0 x a={b}) (hb : guardFailures S F 0 x b={w})
 (h9 : F 9 (child x w (S.label b w))=true)
 (h11 : F 11 (child x w (S.label b w))=false) :
 (negRows S F x).card≤16 := by
 have habne : a≠b := by intro he; subst a; exact S.loopless b hab
 have h0a : ∀ c, F 0 (child x a c)=true := fun c => hF 0 21 (by decide) _ (hta c)
 have h0b : ∀ c, F 0 (child x b c)=true := fun c => hF 0 21 (by decide) _ (htb c)
 have han : a ∉ negRows S F x := fun hh => neg_not_high S F hF x a hh h0a
 have hbn : b ∉ negRows S F x := fun hh => neg_not_high S F hF x b hh h0b
 have hwn := external_not_negative S F hF x b w h9 h11
 have hd : Disjoint (negRows S F x) {a,b} := by
   apply Finset.disjoint_left.mpr
   intro r hr hm
   simp only [Finset.mem_insert,Finset.mem_singleton] at hm
   rcases hm with he | he
   · subst r; exact han hr
   · subst r; exact hbn hr
 have hc : ({a,b} : Finset V).card=2 := by simp [habne]
 have hdom : ∀ v ∈ ({a,b}:Finset V), ∀ r ∈ negRows S F x, S.Adj v r := by
   intro v hv r hr
   simp only [Finset.mem_insert,Finset.mem_singleton] at hv
   rcases hv with he | he
   · subst v; exact high_dominates_neg S F hF htor x a r h0a hr
   · subst v; exact high_dominates_neg S F hF htor x b r h0b hr
 have hzero : ∀ v ∈ negRows S F x ∪ ({a,b}:Finset V),
   (mismatch S.Adj S.label (negRows S F x) (negColor F x) v).card=0 := by
   intro v hv
   apply Finset.card_eq_zero.mpr
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro r hr
   have hf := neg_mismatch_implies_failure S F hF x v r hr
   have hrN := (Finset.mem_filter.mp hr).1
   rcases Finset.mem_union.mp hv with hvN | hvH
   · have he := (neg_color_spec S F hF x v hvN).1
     rw [he] at hf
     exact Finset.notMem_empty _ hf
   · simp only [Finset.mem_insert,Finset.mem_singleton] at hvH
     rcases hvH with he | he
     · subst v; rw [ha] at hf
       have he := Finset.mem_singleton.mp hf
       subst r; exact hbn hrN
     · subst v; rw [hb] at hf
       have he := Finset.mem_singleton.mp hf
       subst r; exact hwn hrN
 have hh := hcap (negRows S F x) {a,b} (negColor F x) hd hc hdom hzero
 omega

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_two_head_negative_cap

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private theorem q0_repair_cases (S : Stage (Fin 22) I V)
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
     have ht0 := hh.2
     have hf : F 0 (child (flip x {((w,c),i)}) w (S.label r w))=true := by
       rw [child_flip_other x w w c (S.label r w) i (by intro he; exact hn (congrArg Prod.snd he))]
       exact ht0
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
open CandidateCoherence ResidualCaps
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private def negRepairCover (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
 (negRows S F x).biUnion fun r =>
   lift r (negColor F x r) (flipsTo (F 21) true (child x r (negColor F x r)))

private theorem guard_repair_outside_is_sink (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (x : ((V × Bool) × I) → Bool) (a b r z : V) (hab : S.Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true)
 (ha : guardFailures S F 0 x a={b}) (hg : guardFailures S F 11 x b=∅)
 (htr : ∀ c, F 21 (child x r c)=true) (hr : guardFailures S F 0 x r={z})
 (hzb : z≠b) : r=b := by
 have habne : a≠b := by intro he; subst a; exact S.loopless b hab
 by_contra hrb
 have hra : r≠a := by
   intro he; subst r
   have hh : ({b}:Finset V)={z} := ha.symm.trans hr
   have hzm : z ∈ ({b}:Finset V) := by rw [hh]; simp
   exact hzb (Finset.mem_singleton.mp hzm)
 have hno : ¬ S.Adj b r := by
   intro hadj
   have hm : r ∈ guardFailures S F 11 x b := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hadj,hF 11 21 (by decide) _ (htr (S.label b r))⟩
   rw [hg] at hm
   exact Finset.notMem_empty _ hm
 have hrbAdj := (htor r b hrb).2 hno
 have hnoar : ¬ S.Adj a r := by
   intro hadj
   have hm : r ∈ guardFailures S F 0 x a := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hadj,hF 0 21 (by decide) _ (htr (S.label a r))⟩
   rw [ha] at hm
   exact hrb (Finset.mem_singleton.mp hm)
 have hraAdj := (htor r a hra).2 hnoar
 have hma : a ∈ guardFailures S F 0 x r := Finset.mem_filter.mpr
   ⟨Finset.mem_univ _,hraAdj,hF 0 21 (by decide) _ (hta (S.label r a))⟩
 have hmb : b ∈ guardFailures S F 0 x r := Finset.mem_filter.mpr
   ⟨Finset.mem_univ _,hrbAdj,hF 0 21 (by decide) _ (htb (S.label r b))⟩
 rw [hr] at hma hmb
 exact habne ((Finset.mem_singleton.mp hma).trans (Finset.mem_singleton.mp hmb).symm)

theorem phase4_maximal_outside_cover (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (x : ((V × Bool) × I) → Bool) (a b w : V) (hab : S.Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true)
 (ha : guardFailures S F 0 x a={b}) (hb : guardFailures S F 0 x b={w})
 (hg : guardFailures S F 11 x b=∅)
 (hold : ordinaryParent S F 21 0 0 x=false) :
 (flipsTo (ordinaryParent S F 21 0 0) true x).filter (fun z => z.1.1≠b) ⊆
 lift w (S.label b w) (flipsTo (F 0) false (child x w (S.label b w))) ∪ negRepairCover S F x := by
 rintro ⟨⟨z,c⟩,i⟩ hp
 obtain ⟨hp,hzb⟩ := Finset.mem_filter.mp hp
 have hn := (Finset.mem_filter.mp hp).2
 rcases q0_repair_cases S F x z c i hold hn with ht | hgR
 · have hfalse0 : F 0 (child x z c)=false := by
     cases hh : F 0 (child x z c) with
     | false => rfl
     | true =>
       have h0both : ∀ d, F 0 (child x z d)=true := by
         intro d
         by_cases hd : d=c
         · simpa [hd] using hh
         · have he : d= !c := by cases c <;> cases d <;> simp_all
           rw [he]; exact hF 0 21 (by decide) _ ht.2.2.1
       have hza : z≠a := by
         intro he; subst z
         have hac := hta c
         rw [ht.2.1] at hac
         contradiction
       have hno : ¬S.Adj z a := by
         intro hadj
         have hm : a ∈ guardFailures S F 0 x z := Finset.mem_filter.mpr
           ⟨Finset.mem_univ _,hadj,hF 0 21 (by decide) _ (hta (S.label z a))⟩
         rw [ht.1] at hm
         exact Finset.notMem_empty _ hm
       have haz := (htor a z (Ne.symm hza)).2 hno
       have hm : z ∈ guardFailures S F 0 x a := Finset.mem_filter.mpr
         ⟨Finset.mem_univ _,haz,h0both (S.label a z)⟩
       rw [ha] at hm
       exact False.elim (hzb (Finset.mem_singleton.mp hm))
   have hzN : z ∈ negRows S F x := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,ht.1,c,hfalse0,ht.2.2.1⟩
   have hcol : negColor F x z=c := by
     cases c
     · simp [negColor,hfalse0]
     · have hh : F 0 (child x z false)=true := hF 0 21 (by decide) _ ht.2.2.1
       simp [negColor,hh]
   apply Finset.mem_union_right
   apply Finset.mem_biUnion.mpr
   refine ⟨z,hzN,?_⟩
   apply (mem_lift z z (negColor F x z) c _ i).2
   refine ⟨rfl,hcol.symm,?_⟩
   simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
   rw [hcol]
   exact ht.2.2.2
 · obtain ⟨r,htr,hr,hl,hfalse⟩ := hgR
   have hrb := guard_repair_outside_is_sink S F hF htor x a b r z hab hta htb ha hg htr hr hzb
   subst r
   have hzw : z=w := by
     have hm : z ∈ guardFailures S F 0 x b := by rw [hr]; simp
     rw [hb] at hm
     exact Finset.mem_singleton.mp hm
   subst z
   apply Finset.mem_union_left
   apply (mem_lift w w (S.label b w) c _ i).2
   refine ⟨rfl,hl.symm,?_⟩
   simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
   rw [hl]
   exact hfalse

theorem phase4_maximal_outside_bound (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 2 17)
 (x : ((V × Bool) × I) → Bool) (a b w : V) (hab : S.Adj a b)
 (hta : ∀ c, F 21 (child x a c)=true) (htb : ∀ c, F 21 (child x b c)=true)
 (ha : guardFailures S F 0 x a={b}) (hb : guardFailures S F 0 x b={w})
 (hg : guardFailures S F 11 x b=∅)
 (h9 : F 9 (child x w (S.label b w))=true)
 (h11 : F 11 (child x w (S.label b w))=false)
 (hold : ordinaryParent S F 21 0 0 x=false)
 (g s : ℕ) (hG : BBound F 0 9 g) (hS : ABound F 0 21 s) :
 ((flipsTo (ordinaryParent S F 21 0 0) true x).filter (fun z => z.1.1≠b)).card ≤ g+16*s := by
 have hsub := phase4_maximal_outside_cover S F hF htor x a b w hab hta htb ha hb hg hold
 have hn := phase4_two_head_negative_cap S F hF htor hcap x a b w hab hta htb ha hb h9 h11
 have hext : (lift w (S.label b w) (flipsTo (F 0) false (child x w (S.label b w)))).card ≤ g := by
   simpa only [lift,Finset.card_map] using hG _ h9
 have hneg : (negRepairCover S F x).card ≤ 16*s := by
   have hh := card_biUnion_mul (negRows S F x)
     (fun r => lift r (negColor F x r) (flipsTo (F 21) true (child x r (negColor F x r)))) s (by
       intro r hr
       have hs := neg_color_spec S F hF x r hr
       simpa only [lift,Finset.card_map] using hS _ hs.2.1)
   exact hh.trans (Nat.mul_le_mul_right s hn)
 exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hext hneg))

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_maximal_outside_bound

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
open CandidateCoherence ResidualCaps
noncomputable section
open scoped Classical
variable {I V : Type} [Fintype I] [Fintype V]

private def targetRows (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) : Finset V :=
 Finset.univ.filter fun r => guardFailures S F 0 x r=∅ ∧
   ∃ c, F 21 (child x r c)=false ∧ F 21 (child x r (!c))=true
private def targetColor (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (r : V) : Bool :=
 if F 21 (child x r false)=false then false else true
private theorem target_color_spec (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (r : V) (hr : r ∈ targetRows S F x) :
 guardFailures S F 0 x r=∅ ∧ F 21 (child x r (targetColor F x r))=false ∧
 F 21 (child x r (!(targetColor F x r)))=true := by
 obtain ⟨hg,c,hc,ho⟩ := (Finset.mem_filter.mp hr).2
 refine ⟨hg,?_⟩
 cases c
 · simpa [targetColor,hc] using And.intro hc ho
 · have hh : F 21 (child x r false)=true := ho
   simpa [targetColor,hh] using And.intro hc ho
private theorem target_label_color (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h0v : ∀ c, F 0 (child x v c)=true)
 (hg : guardFailures S F 11 x v=∅) (hvn : v ∉ targetRows S F x)
 (r : V) (hr : r ∈ targetRows S F x) :
 S.Adj v r ∧ S.label v r=targetColor F x r ∧
 F 11 (child x r (targetColor F x r))=false := by
 have hrv : r≠v := by intro he; subst r; exact hvn hr
 have hs := target_color_spec S F x r hr
 have hnorv : ¬S.Adj r v := by
   intro hadj
   have hm : v ∈ guardFailures S F 0 x r := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hadj,h0v (S.label r v)⟩
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
 have hlabel : S.label v r=targetColor F x r := by
   by_contra hn
   have he : S.label v r= !(targetColor F x r) := by
     cases he1 : S.label v r <;> cases he2 : targetColor F x r <;> simp_all
   have hh := hF 11 21 (by decide) _ hs.2.2
   rw [←he,hfalse] at hh
   contradiction
 exact ⟨hadj,hlabel,by rw [←hlabel]; exact hfalse⟩

theorem phase4_all_target_rows_source_cap (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 1 19)
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h0v : ∀ c, F 0 (child x v c)=true)
 (hg : guardFailures S F 11 x v=∅) (hvn : v ∉ targetRows S F x) :
 (targetRows S F x).card≤18 := by
 have hd : Disjoint (targetRows S F x) {v} := Finset.disjoint_singleton_right.mpr hvn
 have hc : ({v}:Finset V).card=1 := by simp
 have hdom : ∀ z ∈ ({v}:Finset V), ∀ r ∈ targetRows S F x, S.Adj z r := by
   intro z hz r hr
   have hzv := Finset.mem_singleton.mp hz
   subst z
   exact (target_label_color S F hF htor x v h0v hg hvn r hr).1
 have hzero : ∀ z ∈ targetRows S F x ∪ ({v}:Finset V),
   (mismatch S.Adj S.label (targetRows S F x) (targetColor F x) z).card=0 := by
   intro z hz
   apply Finset.card_eq_zero.mpr
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro r hr
   obtain ⟨hrT,hadj,hne⟩ := Finset.mem_filter.mp hr
   have hs := target_color_spec S F x r hrT
   have he : S.label z r= !(targetColor F x r) := by
     cases he1 : S.label z r <;> cases he2 : targetColor F x r <;> simp_all
   rcases Finset.mem_union.mp hz with hzT | hzV
   · have hm : r ∈ guardFailures S F 0 x z := Finset.mem_filter.mpr
       ⟨Finset.mem_univ _,hadj,by rw [he]; exact hF 0 21 (by decide) _ hs.2.2⟩
     rw [(target_color_spec S F x z hzT).1] at hm
     exact Finset.notMem_empty _ hm
   · have hzv := Finset.mem_singleton.mp hzV
     subst z
     have hl := (target_label_color S F hF htor x v h0v hg hvn r hrT).2.1
     exact hne hl
 have hh := hcap (targetRows S F x) {v} (targetColor F x) hd hc hdom hzero
 omega

private def allTargetCover (S : Stage (Fin 22) I V) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
 (targetRows S F x).biUnion fun r =>
 lift r (targetColor F x r) (flipsTo (F 21) true (child x r (targetColor F x r)))

private theorem target_repair_in_cover (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool)
 (x : ((V × Bool) × I) → Bool) (r : V) (c : Bool) (i : I)
 (hg : guardFailures S F 0 x r=∅) (hf : F 21 (child x r c)=false)
 (ho : F 21 (child x r (!c))=true) (hp : F 21 (flip (child x r c) {i})=true) :
 ((r,c),i) ∈ allTargetCover S F x := by
 have hr : r ∈ targetRows S F x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg,c,hf,ho⟩
 have he : targetColor F x r=c := by
   cases c
   · simp [targetColor,hf]
   · have hh : F 21 (child x r false)=true := ho
     simp [targetColor,hh]
 apply Finset.mem_biUnion.mpr
 refine ⟨r,hr,?_⟩
 apply (mem_lift r r (targetColor F x r) c _ i).2
 refine ⟨rfl,he.symm,?_⟩
 simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
 rw [he]; exact hp

private theorem all_target_cover_card (S : Stage (Fin 22) I V)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (htor : ∀ v r, v≠r → (S.Adj v r ↔ ¬ S.Adj r v))
 (hcap : DominatorCardBound S.Adj S.label 1 19)
 (x : ((V × Bool) × I) → Bool) (v : V)
 (h0v : ∀ c, F 0 (child x v c)=true)
 (hg : guardFailures S F 11 x v=∅) (hvn : v ∉ targetRows S F x)
 (s : ℕ) (hS : ABound F 11 21 s) : (allTargetCover S F x).card≤18*s := by
 have hn := phase4_all_target_rows_source_cap S F hF htor hcap x v h0v hg hvn
 have hh := card_biUnion_mul (targetRows S F x)
   (fun r => lift r (targetColor F x r) (flipsTo (F 21) true (child x r (targetColor F x r)))) s (by
     intro r hr
     have hs := (target_label_color S F hF htor x v h0v hg hvn r hr).2.2
     simpa only [lift,Finset.card_map] using hS _ hs)
 exact hh.trans (Nat.mul_le_mul_right s hn)

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_all_target_rows_source_cap

namespace Sensitivity213981Formal.JointCover
open _root_.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundConditional
open CandidateCoherence ResidualCaps
noncomputable section
open scoped Classical
variable {I : Type} [Fintype I]

private theorem phase4_accept11
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool) (F : Fin 22 → (I → Bool) → Bool)
 (x : ((Fin 5591 × Bool) × I) → Bool) (v : Fin 5591)
 (h17 : ∀ c, F 17 (child x v c)=true) (h18 : ∃ c, F 18 (child x v c)=true)
 (hg : guardFailures ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 9 x v=∅) :
 parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F) F 11 x=true := by
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 change parent S F 11 x=true
 have hf : failed S F 11 x v=∅ := hg
 simp only [parent,decide_eq_true_eq]
 refine ⟨v,?_,?_⟩
 · rw [hf]; simp
 · rw [hf]
   change (F 17 (child x v false) && F 17 (child x v true) &&
     (F 18 (child x v false) || F 18 (child x v true)))=true
   rw [h17 false,h17 true]
   rcases h18 with ⟨c,hc⟩
   cases c <;> simp [hc]

theorem phase4_global_joint_cover_bound
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (B g s : ℕ) (hB : BBound F 14 17 B) (hG : BBound F 0 9 g) (hS : ABound F 11 21 s)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 10 x=true → parent S F 11 x=false →
 (flipsTo (parent S F 4) false x ∪ flipsTo (parent S F 21) true x).card≤2*B+g+18*s := by
 dsimp only
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 intro h10 h11
 obtain ⟨v,h17,h18,hg⟩ := phase4_row10 Adj loopless label F x h10
 have h0v : ∀ c, F 0 (child x v c)=true := fun c => hF 0 17 (by decide) _ (h17 c)
 have h9ne : guardFailures S F 9 x v≠∅ := by
   intro hz
   have hh := phase4_accept11 Adj loopless label F x v h17 h18 hz
   rw [h11] at hh
   contradiction
 have hvn : v ∉ targetRows S F x := by
   intro hv
   have he := (target_color_spec S F x v hv).1
   apply h9ne
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro w hw
   have hh := (Finset.mem_filter.mp hw).2
   have hm : w ∈ guardFailures S F 0 x v := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hh.1,hF 0 9 (by decide) _ hh.2⟩
   rw [he] at hm
   exact Finset.notMem_empty _ hm
 have ht21 : ∀ d y z, S.target 21 d y z=(F 21 y && F 21 z) := by
   intro d y z
   dsimp [S,MinMaxRecipe.stage,minmaxTarget,Sensitivity5591Endpoint22.recipe,
     Sensitivity5591Endpoint22.entry,Sensitivity5591Endpoint22.entries3,
     Sensitivity5591Endpoint22.Entry.threshold,Sensitivity5591Endpoint22.Entry.upper]
   cases hy : F 21 y <;> cases hz : F 21 z <;> simp [hy,hz]
 have e21 := parent_specialize S F 21 21 0 0 (by rfl) (by rfl) ht21
 have hold : ordinaryParent S F 21 0 0 x=false := by
   cases hh : ordinaryParent S F 21 0 0 x with
   | false => rfl
   | true =>
     obtain ⟨r,hrt,hrg⟩ := (parent_iff S F 21 0 0 x).1 hh
     have he0 : guardFailures S F 0 x r=∅ := Finset.card_eq_zero.mp (by omega)
     have he9 : guardFailures S F 9 x r=∅ := by
       apply Finset.eq_empty_iff_forall_notMem.mpr
       intro z hz
       have hz' := (Finset.mem_filter.mp hz).2
       have hm : z ∈ guardFailures S F 0 x r := Finset.mem_filter.mpr
         ⟨Finset.mem_univ _,hz'.1,hF 0 9 (by decide) _ hz'.2⟩
       rw [he0] at hm
       exact Finset.notMem_empty _ hm
     have hh := phase4_accept11 Adj loopless label F x r
       (fun c => hF 17 21 (by decide) _ (hrt c))
       ⟨false,hF 18 21 (by decide) _ (hrt false)⟩ he9
     rw [h11] at hh
     contradiction
 have hm : flipsTo (parent S F 4) false x ⊆ rowDown14 F x v :=
   phase4_destruction_supported_at_witness Adj loopless label F hF x v h17 hg
 have hc := rowDown14_card F x v B hB h17
 have ht := all_target_cover_card S F hF htor (by
   intro A M color hd hc hdom hz
   apply hcap A M color hd hc hdom
   intro z hzmem
   apply hz z
   simpa only [Finset.mem_union] using hzmem) x v h0v hg hvn s hS
 have guard_location (r z : Fin 5591)
   (htr : ∀ c, F 21 (child x r c)=true) (hr : guardFailures S F 0 x r={z}) :
   r=v ∨ z=v := by
   by_cases hrv : r=v
   · exact Or.inl hrv
   · right
     have hno : ¬Adj v r := by
       intro hadj
       have hh : r ∈ guardFailures S F 11 x v := Finset.mem_filter.mpr
         ⟨Finset.mem_univ _,hadj,hF 11 21 (by decide) _ (htr (label v r))⟩
       rw [hg] at hh
       exact Finset.notMem_empty _ hh
     have hrvAdj := (htor r v hrv).2 hno
     have hh : v ∈ guardFailures S F 0 x r := Finset.mem_filter.mpr
       ⟨Finset.mem_univ _,hrvAdj,h0v (label r v)⟩
     rw [hr] at hh
     exact (Finset.mem_singleton.mp hh).symm
 have post0_in_row (c : Bool) (i : I) (hf : F 0 (flip (child x v c) {i})=false) :
   ((v,c),i) ∈ rowDown14 F x v := by
   have h14 : F 14 (flip (child x v c) {i})=false := by
     cases hh : F 14 (flip (child x v c) {i}) with
     | false => rfl
     | true =>
       have h0 := hF 0 14 (by decide) _ hh
       rw [hf] at h0
       contradiction
   have hi : i ∈ flipsTo (F 14) false (child x v c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h14⟩
   cases c
   · exact Finset.mem_union_left _ ((mem_lift v v false false _ i).2 ⟨rfl,rfl,hi⟩)
   · exact Finset.mem_union_right _ ((mem_lift v v true true _ i).2 ⟨rfl,rfl,hi⟩)
 change (flipsTo (parent S F 4) false x ∪ flipsTo (parent S F 21) true x).card ≤ _
 rw [e21]
 by_cases hs : (guardFailures S F 0 x v).card=1
 · obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hs
   obtain ⟨r,hr⟩ := Finset.nonempty_iff_ne_empty.mpr h9ne
   have hh := (Finset.mem_filter.mp hr).2
   have hm0 : r ∈ guardFailures S F 0 x v := Finset.mem_filter.mpr
     ⟨Finset.mem_univ _,hh.1,hF 0 9 (by decide) _ hh.2⟩
   rw [hw] at hm0
   have hrw := Finset.mem_singleton.mp hm0
   subst r
   let E := lift w (S.label v w) (flipsTo (F 0) false (child x w (S.label v w)))
   have he : E.card≤g := by simpa only [E,lift,Finset.card_map] using hG _ hh.2
   have hsub : flipsTo (parent S F 4) false x ∪ flipsTo (ordinaryParent S F 21 0 0) true x ⊆
     rowDown14 F x v ∪ (E ∪ allTargetCover S F x) := by
     rintro ⟨⟨z,c⟩,i⟩ hp
     rcases Finset.mem_union.mp hp with hd | hp
     · exact Finset.mem_union_left _ (hm hd)
     · rcases q0_repair_cases S F x z c i hold (Finset.mem_filter.mp hp).2 with htar | hgu
       · exact Finset.mem_union_right _ (Finset.mem_union_right _
           (target_repair_in_cover S F x z c i htar.1 htar.2.1 htar.2.2.1 htar.2.2.2))
       · obtain ⟨r,htr,hr,hl,hpost⟩ := hgu
         rcases guard_location r z htr hr with hrv | hzv
         · subst r
           have hzw : z=w := by
             have hm : z ∈ guardFailures S F 0 x v := by rw [hr]; simp
             rw [hw] at hm
             exact Finset.mem_singleton.mp hm
           subst z
           apply Finset.mem_union_right
           apply Finset.mem_union_left
           apply (mem_lift w w (S.label v w) c _ i).2
           refine ⟨rfl,hl.symm,?_⟩
           simp only [flipsTo,Finset.mem_filter,Finset.mem_univ,true_and]
           rw [hl]; exact hpost
         · subst z
           exact Finset.mem_union_left _ (post0_in_row c i hpost)
   have hb1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
   have hb2 := Finset.card_union_le E (allTargetCover S F x)
   omega
 · have hsub : flipsTo (parent S F 4) false x ∪ flipsTo (ordinaryParent S F 21 0 0) true x ⊆
     rowDown14 F x v ∪ allTargetCover S F x := by
     rintro ⟨⟨z,c⟩,i⟩ hp
     rcases Finset.mem_union.mp hp with hd | hp
     · exact Finset.mem_union_left _ (hm hd)
     · rcases q0_repair_cases S F x z c i hold (Finset.mem_filter.mp hp).2 with htar | hgu
       · exact Finset.mem_union_right _
           (target_repair_in_cover S F x z c i htar.1 htar.2.1 htar.2.2.1 htar.2.2.2)
       · obtain ⟨r,htr,hr,hl,hpost⟩ := hgu
         rcases guard_location r z htr hr with hrv | hzv
         · subst r
           apply False.elim
           apply hs
           rw [hr]; simp
         · subst z
           exact Finset.mem_union_left _ (post0_in_row c i hpost)
   have hb1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
   omega

end
end Sensitivity213981Formal.JointCover
#print axioms Sensitivity213981Formal.JointCover.phase4_global_joint_cover_bound

theorem solution {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : Sensitivity213981Formal.ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 17 2041395696528705380)
 (hG : BBound F 0 9 3056915546137949758)
 (hS : ABound F 11 21 98368454968486)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 10 x=true → parent S F 11 x=false →
 (flipsTo (parent S F 4) false x ∪ flipsTo (parent S F 21) true x).card≤7141477571384793266 := by
 have hh := Sensitivity213981Formal.JointCover.phase4_global_joint_cover_bound
   Adj loopless label htor hcap F hF
   2041395696528705380 3056915546137949758 98368454968486 hB hG hS x
 exact hh
