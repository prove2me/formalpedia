-- Prove2me | solution 2 for SensitivityCampaign.endpoint22_joint_profile_rate
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T12:35:27.458097+00:00
-- url     : https://prove2.me/submissions/f64876c0-bb14-46ab-afee-70ce635e8851

import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Hybrid_upper_scaled_from_seeds
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_records_complete
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_closure_complete
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_numerical_complete
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_NatTable_dominates_sound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_NatTable_lowerCheck_sound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_oneBit_upper
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundProfiles_sensitivity_le_diagonal_max
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_blockSensitivity_lower_of_indexed_blocks
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_sensitivity_reindex
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_tower_common_witnesses
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_dCore_bound
import Theorems.Thm_SensitivityJointCover_endpoint22_phase1_bound

/- Uses the Apache-2.0 Prove2Me proofs of the exact four-stage rate (cda6a452-93c8-49ec-b0a1-22a9f1d2fb20), the joint cover of the second phase (6dc1fd9c-4370-4ac3-aacf-7ca773805531), core homogeneity, and endpoint recipe matching from the published 22-state construction. The propagation of the joint estimate into the critical final gap and the resulting reset are new. -/
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

namespace Sensitivity213981Formal.ThreeBoundNumeric
open ThreeBoundFullProfile
theorem Expr.eval_homogeneous {n : ℕ} (e : Expr n) (v : Profile n) (c : ℕ) :
    e.eval (fun i => c * v i) = c * e.eval v := by
  induction e with
  | zero => simp [eval]
  | var i => rfl
  | add a b ha hb => simp only [eval, ha, hb, Nat.mul_add]
  | scale k a ha => simp only [eval, ha]; ring
  | sub a b ha hb => simp only [eval, ha, hb, Nat.mul_sub_left_distrib]
  | min a b ha hb => simp only [eval, ha, hb, Nat.mul_min_mul_left]
  | max a b ha hb => simp only [eval, ha, hb, Nat.mul_max_mul_left]

end Sensitivity213981Formal.ThreeBoundNumeric

namespace Sensitivity213981Formal.ThreeBoundMinmaxNumeric
open ThreeBoundNumeric ThreeBoundFullProfile
theorem dCore_homogeneous (n degree : ℕ) (v : Profile n) (i j k l : Entry) (first c : ℕ) :
    dCore n degree (scale c v) i j k l (c*first)=c*dCore n degree v i j k l first := by
  have he (e : Expr n) : e.eval (scale c v)=c*e.eval v := Expr.eval_homogeneous e v c
  dsimp only [dCore]
  split_ifs <;> simp only [he,Nat.mul_left_comm degree c,Nat.mul_left_comm (degree-1) c,
    ← Nat.mul_add,Nat.mul_max_mul_left,Nat.mul_min_mul_left,Nat.mul_zero,
    Nat.max_zero,Nat.zero_max,Nat.min_zero,Nat.zero_min]

end Sensitivity213981Formal.ThreeBoundMinmaxNumeric

namespace Sensitivity213981Formal.ThreeBoundEndpoint22Pairs
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting ThreeBoundMinmaxTransfer ThreeBoundMinmaxNumeric
variable {I : Type} [Fintype I]
theorem numeric_lower (p : Fin 4) (l : Fin 22) (d : ℕ)
    (hd : d ≤  (Sensitivity5591Endpoint22.entry p l).tolerance) :
    ((Sensitivity5591Endpoint22.entry p l).threshold d).val=
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).lowerAt d := by
  have hd9 : d< 9 := by have hh := Sensitivity5591Endpoint22.entry_tolerance_bound p l; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint22.recipe,ThreeBoundMinmaxNumeric.Entry.lowerAt,Array.getD,hd9]

theorem numeric_upper (p : Fin 4) (l : Fin 22) (d : ℕ)
    (hd : d ≤  (Sensitivity5591Endpoint22.entry p l).tolerance) :
    ((Sensitivity5591Endpoint22.entry p l).upper d).val=
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).upperAt d := by
  have hd9 : d< 9 := by have hh := Sensitivity5591Endpoint22.entry_tolerance_bound p l; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint22.recipe,ThreeBoundMinmaxNumeric.Entry.upperAt,Array.getD,hd9]

theorem entryMatch (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ w, ¬Adj w w)
    (label : Fin 5591 → Fin 5591 → Bool) (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool)
    (i j : Fin 22) (hij : i ≤  j) :
    EntryMatch ((Sensitivity5591Endpoint22.recipe Adj loopless label p).stage F) F i j
      (pairData Adj loopless label p F i j hij) (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i)
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j) where
  weakTolerance := rfl
  strongTolerance := rfl
  weakGuard := rfl
  strongGuard := rfl
  weakLower := numeric_lower p i
  weakUpper := numeric_upper p i
  strongLower := numeric_lower p j
  strongUpper := numeric_upper p j

end Sensitivity213981Formal.ThreeBoundEndpoint22Pairs
/- The structural lemmas and unrolling of the four stages below follow the published
   Prove2Me proofs by yousofy for ThreeBoundMinmaxNumeric.Endpoint22.periodic_upper_hybrid
   and ThreeBoundEndpoint22CampaignComplete.seeds (Sensitivity213981Formal).
   The exact reset, rounded induction, and passage to its real logarithmic
   endpoint are given in ExactFourStageBound. -/
namespace Sensitivity213981Formal
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320

variable {L I V : Type}

theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]

/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/

end ThreeBoundWitness

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

theorem sem_mono (F : Fin n → (I → Bool) → Bool) (c : Coord n) (a b : ℕ)
    (hab : a ≤  b) (ha : Sem F c a) : Sem F c b := by
  cases c with
  | a i j => exact fun hij x hx => (ha hij x hx).trans hab
  | b i j => exact fun hij x hx => (ha hij x hx).trans hab
  | m i j => exact fun hij hn x hx hy => (ha hij hn x hx hy).trans hab
  | p j l => exact fun hjl x hx hy => (ha hjl x hx hy).trans hab
  | d i j l => exact fun hij hjl x hx hy => (ha hij hjl x hx hy).trans hab

theorem upper_mono (F : Fin n → (I → Bool) → Bool) (v w : Profile n)
    (hvw : ∀ c, v c ≤  w c) (hv : Upper F v) : Upper F w :=
  fun c => sem_mono F c _ _ (hvw c) (hv c)

end
end ThreeBoundFullProfile

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace ThreeBoundNesting
open ThreeBoundWitness ThreeBoundProfiles

variable {L I V : Type} [Preorder L] [Fintype V]

theorem failed_subset (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (r.stage F) F i x v ⊆ failed (r.stage F) F j x v := by
  classical
  intro w hw
  change w ∈ Finset.univ.filter (fun z =>
    r.Adj v z ∧ F (r.guard i) (child x z (r.label v z)) = true) at hw
  change w ∈ Finset.univ.filter (fun z =>
    r.Adj v z ∧ F (r.guard j) (child x z (r.label v z)) = true)
  have hh := (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1,
    hF _ _ (hr.guard hij) _ hh.2⟩

theorem target_mono (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (a b : ℕ) (hab : a ≤  b)
    (hb : b ≤  r.tolerance j) (x y : I → Bool)
    (h : minmaxTarget F r.lower r.upper j b x y = true) :
    minmaxTarget F r.lower r.upper i a x y = true := by
  have ht : r.lower i a ≤  r.lower j b :=
    (hr.lower_mono i hab).trans (hr.lower_order i j hij b hb)
  have hu : r.upper i a ≤  r.upper j b :=
    (hr.upper_mono i hab).trans (hr.upper_order i j hij b hb)
  simp only [minmaxTarget, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  refine ⟨⟨hF _ _ ht x h.1.1, hF _ _ ht y h.1.2⟩, ?_⟩
  rcases h.2 with hx | hy
  · exact Or.inl (hF _ _ hu x hx)
  · exact Or.inr (hF _ _ hu y hy)

/-- The concrete parent construction used by the witness recursion preserves
nested families for every ordered min/max recipe. -/
theorem parent_nested (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F) :
    Nested (parent (r.stage F) F) := by
  intro i j hij x hj
  obtain ⟨v, hv, ht⟩ := (parent_true_iff (r.stage F) F j x).mp hj
  have hc := Finset.card_le_card (failed_subset r hr F hF i j hij x v)
  apply (parent_true_iff (r.stage F) F i x).mpr
  refine ⟨v, hc.trans (hv.trans (hr.tolerance hij)), ?_⟩
  exact target_mono r hr F hF i j hij _ _ hc hv _ _ ht

/-- Nesting holds at every depth of the actual arbitrary-depth construction. -/
theorem tower_nested (r : ℕ → MinMaxRecipe L V)
    (hr : ∀ n, OrderedRecipe (r n)) (n : ℕ) :
    Nested (towerFamily r n) := by
  induction n with
  | zero => exact fun _ _ _ _ h => h
  | succ n ih => exact parent_nested (r n) (hr n) _ ih

end ThreeBoundNesting

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual third-endpoint recipes, certificate SHA256 c706e403ddef113743f0dacc0a95d97dd3a2f32de032f35972f7ef045be6425f.
The tournament and edge labeling remain explicit parameters until the selected
order-5591 labeling is instantiated. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Sensitivity5591Endpoint22
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting

theorem family_nested (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool) (n : ℕ) : Nested (family Adj loopless label n) :=
  tower_nested (periodicRecipe Adj loopless label) (fun k => recipe_ordered Adj loopless label _) n

end Sensitivity5591Endpoint22

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The fully proved Paley geometry fixes an unconditional third-endpoint family. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundEndpoint22Selected
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNumeric ThreeBoundFullProfile
open Sensitivity5591Labeling.Labeling5591

theorem family_nested (n : ℕ) : Nested (family n) :=
  Sensitivity5591Endpoint22.family_nested Adj irreflexive label n

end ThreeBoundEndpoint22Selected

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile

theorem base_ab_table:NatTable.lowerCheck 1 initialABTable=true:=by decide +kernel

theorem base_ab_indices:∀i j:Fin 22,flatIndex (Coord.a i j)< 506∧flatIndex (Coord.b i j)< 506:=by decide +kernel

theorem base_positive:BasePositive profile0:=by
  have htable:=NatTable.lowerCheck_sound 1 initialABTable base_ab_table
  intro i j hij
  constructor
  · change 1≤ (if flatIndex (Coord.a i j)< 506 then initialABTable.get (flatIndex (.a i j)) else _)
    rw [if_pos (base_ab_indices i j).1]
    exact htable _
  · change 1≤ (if flatIndex (Coord.b i j)< 506 then initialABTable.get (flatIndex (.b i j)) else _)
    rw [if_pos (base_ab_indices i j).2]
    exact htable _

theorem ordered0:Ordered profile0:=by decide +kernel

theorem ordered1:Ordered profile1:=by decide +kernel

theorem ordered2:Ordered profile2:=by decide +kernel

theorem ordered3:Ordered profile3:=by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Four exact scaled stages and reset give the third endpoint's infinite family. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness
open ThreeBoundEndpoint22Selected

theorem input_ordered (p : Fin 4) : Ordered (input p) := by
  fin_cases p
  · exact ordered0
  · exact ordered1
  · exact ordered2
  · exact ordered3

theorem actual_base_upper : Upper (ThreeBoundEndpoint22Selected.family 0) profile0 :=
  oneBit_upper profile0 base_positive

theorem family_succ_phase (d : ℕ) (p : Fin 4) (hp : d%4=p.val) :
    ThreeBoundEndpoint22Selected.family (d+1) =
      parent ((ThreeBoundEndpoint22Selected.recipe p).stage
        (ThreeBoundEndpoint22Selected.family d)) (ThreeBoundEndpoint22Selected.family d) := by
  have he : (⟨d%4,Nat.mod_lt d (by decide)⟩ : Fin 4)=p := Fin.ext hp
  simp only [ThreeBoundEndpoint22Selected.family,ThreeBoundEndpoint22Selected.recipe,
    Sensitivity5591Endpoint22.family,towerFamily,Sensitivity5591Endpoint22.periodicRecipe,he]
  rfl

end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The essential-entry numerical certificate yields the same periodic family. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness
open ThreeBoundMinmaxHybrid ThreeBoundEndpoint22Hybrid

theorem stage_from_hybrid {I : Type} [Fintype I]
    (records : List (List ℕ)) (hrecords : ∀ xs ∈ ThreeBoundQ3.records, xs ∈ records)
    (seeds : Fin 4 → List (Fin 22 × Fin 22))
    (numerical : HybridNumericalBounds records seeds) (closure : ClosureBounds)
    (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F) (c : ℕ)
    (hv : Upper F (scale c (input p))) :
    Upper (parent ((ThreeBoundEndpoint22Selected.recipe p).stage F) F) (scale c (output p)) := by
  let G := parent ((ThreeBoundEndpoint22Selected.recipe p).stage F) F
  have hG : Nested G := ThreeBoundNesting.parent_nested _
    (Sensitivity5591Endpoint22.recipe_ordered Sensitivity5591Labeling.Labeling5591.Adj
      Sensitivity5591Labeling.Labeling5591.irreflexive ThreeBoundEndpoint22Selected.label p) F hF
  have hh := upper_scaled_from_seeds records hrecords p F hF (input p) (rawInput p) (seeds p)
    (numerical p).1 (numerical p).2.1 (numerical p).2.2 (input_ordered p) c hv
  exact closure p ((Fin 5591 × Bool) × I) G hG c hh

end ThreeBoundMinmaxNumeric.Endpoint22
end
end Sensitivity213981Formal
namespace Sensitivity213981Formal
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320

variable {L I V : Type}

/-- An injectively indexed family of sensitive coordinates bounds the campaign measure. -/
theorem sensitivity_lower_of_indexed_bits [Fintype I] {A : Type} [Fintype A]
    (f : (I → Bool) → Bool) (x : I → Bool) (e : A ↪ I)
    (he : ∀ a, f (_root_.OAI.Paper320.flip x {e a}) ≠ f x) : Fintype.card A ≤  _root_.OAI.Paper320.sensitivity f := by
  classical
  have hsub : (Finset.univ.map e) ⊆
      Finset.univ.filter (fun i => f (_root_.OAI.Paper320.flip x {i}) ≠ f x) := by
    intro i hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he a⟩
  have hat : Fintype.card A ≤  _root_.OAI.Paper320.sensitivityAt f x := by
    simpa only [_root_.OAI.Paper320.sensitivityAt, Finset.card_map, Finset.card_univ]
      using Finset.card_le_card hsub
  exact hat.trans (Finset.le_sup (Finset.mem_univ x))

/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/

end ThreeBoundWitness

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Concrete arbitrary-depth graded/min-max constructions and their lower bounds.
Every recipe sequence below defines total Boolean functions.  No sensitivity
upper bound is claimed; the finite sensitivity-profile soundness remains a
separate obligation for the requested separation exponents.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundWitness
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320

theorem tower_lower_bounds {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) (v : V) (n : ℕ) (l : L) :
    2^n ≤  _root_.OAI.Paper320.sensitivity (towerFamily r n l) ∧
      (Fintype.card V)^n ≤  _root_.OAI.Paper320.blockSensitivity (towerFamily r n l) := by
  obtain ⟨w⟩ := tower_common_witnesses r v n
  constructor
  · have h := sensitivity_lower_of_indexed_bits (towerFamily r n l) w.positive
      w.positiveBits (fun a => by rw [w.positive_off a l, w.positive_accepts l]; decide)
    simpa only [card_iterProd, Fintype.card_bool] using h
  · have h := blockSensitivity_lower_of_indexed_blocks (towerFamily r n l) w.zero
      w.blocks w.blocks_nonempty w.blocks_disjoint
      (fun a => by rw [w.blocks_on a l, w.zero_rejects l]; decide)
    simpa only [card_iterProd] using h

end ThreeBoundWitness

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual third-endpoint finite Boolean functions and their growing disjoint
block witnesses.  The periodic upper profile is the final transfer invariant. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint22Seeds
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundFullProfile
open Sensitivity5591Endpoint22

variable (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ w, ¬Adj w w)
  (label : Fin 5591 → Fin 5591 → Bool)

theorem finiteFamily_sensitivity (n : ℕ) (l : Fin 22) :
    _root_.OAI.Paper320.sensitivity (finiteFamily Adj loopless label n l)=_root_.OAI.Paper320.sensitivity (family Adj loopless label n l) :=
  sensitivity_reindex (coordinates n) (family Adj loopless label n l)

theorem finiteFamily_lower (n : ℕ) (l : Fin 22) :
    2^n ≤  _root_.OAI.Paper320.sensitivity (finiteFamily Adj loopless label n l) ∧
      5591^n ≤  _root_.OAI.Paper320.blockSensitivity (finiteFamily Adj loopless label n l) := by
  classical
  constructor
  · rw [finiteFamily_sensitivity]
    exact (tower_lower_bounds (periodicRecipe Adj loopless label) (0 : Fin 5591) n l).1
  · obtain ⟨w⟩ := tower_common_witnesses (periodicRecipe Adj loopless label) (0 : Fin 5591) n
    let w' := w.reindex (coordinates n)
    have h := blockSensitivity_lower_of_indexed_blocks
      (reindex (coordinates n) (towerFamily (periodicRecipe Adj loopless label) n l))
      w'.zero w'.blocks w'.blocks_nonempty w'.blocks_disjoint
      (fun a => by rw [w'.blocks_on a l,w'.zero_rejects l]; decide)
    simpa only [card_iterProd,Fintype.card_fin,finiteFamily,family] using h

theorem finiteFamily_four_stage_lower (m : ℕ) (l : Fin 22) :
    16^m ≤  _root_.OAI.Paper320.sensitivity (finiteFamily Adj loopless label (4*m) l) ∧
      (5591^4)^m ≤  _root_.OAI.Paper320.blockSensitivity (finiteFamily Adj loopless label (4*m) l) := by
  simpa only [pow_mul,show (2 : ℕ)^4=16 from rfl] using finiteFamily_lower Adj loopless label (4*m) l

private theorem upper_at_scale (W : Profile 22) (m k : ℕ)
    (hupper : Upper (family Adj loopless label (4*m)) (scale (k) W)) :
    _root_.OAI.Paper320.sensitivity (finiteFamily Adj loopless label (4*m) 0) ≤  prefactor W*k := by
  rw [finiteFamily_sensitivity]
  have ha := hupper (.a 0 0) (le_refl (0 : Fin 22))
  have hb := hupper (.b 0 0) (le_refl (0 : Fin 22))
  have h := sensitivity_le_diagonal_max (family Adj loopless label (4*m)) 0 _ _ ha hb
  have hh : _root_.OAI.Paper320.sensitivity (family Adj loopless label (4*m) 0) ≤ 
      max (W (.a 0 0)) (W (.b 0 0))*k := by
    simpa only [scale,← Nat.mul_max_mul_left,Nat.mul_comm] using h
  exact hh.trans (Nat.mul_le_mul_right _ (le_max_right _ _))

end ThreeBoundEndpoint22Seeds
end
end Sensitivity213981Formal

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Sensitivity213981Formal
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness
open ThreeBoundMinmaxNumeric.Endpoint22 ThreeBoundEndpoint22Records

namespace ExactFourStageBound

open Sensitivity5591Labeling.Labeling5591
open scoped Classical

private noncomputable abbrev phaseStep {I : Type} [Fintype I] (p : Fin 4)
    (F : Fin 22 → (I → Bool) → Bool) :=
  parent ((ThreeBoundEndpoint22Selected.recipe p).stage F) F

private def revised3 (c : Coord 22) : ℕ :=
  if c = .d 14 19 20 then 4700783999961812061 else profile3 c

private def revised4 : Profile 22
  | .d i j l => if i ≤ 3 ∧ j = 14 ∧ l = 15 then 10459734084979310241 else profile4 (.d i j l)
  | z => profile4 z

private theorem phase_three_upper {I : Type} [Fintype I] (H : Fin 22 → (I → Bool) → Bool)
    (c : ℕ) (hH : Nested H) (h₁ : Upper H (scale c profile1))
    (hF : Nested (phaseStep 1 H)) (h₂ : Upper (phaseStep 1 H) (scale c profile2))
    (h₃ : Upper (phaseStep 2 (phaseStep 1 H)) (scale c profile3)) :
    Upper (phaseStep 2 (phaseStep 1 H)) (scale c revised3) := by
  classical
  let F := phaseStep 1 H
  let G := phaseStep 2 F
  have hbH : BBound H 12 12 (c*53627300001453076) := h₁ (.b 12 12) (by decide)
  have haH : ABound H 10 10 (c*914422496216727) := h₁ (.a 10 10) (by decide)
  have hsH : ABound H 12 13 (c*1217719417783) := h₁ (.a 12 13) (by decide)
  have hb : BBound F 13 17 (c*986662590537317840) := h₂ (.b 13 17) (by decide)
  have ha : ABound F 2 11 (c*24354388355660) := h₂ (.a 2 11) (by decide)
  have hq : PBound F 17 18 18 (c*47117605675757176) := h₂ (.p 17 18) (by decide)
  have htor : ∀ r z, r ≠ z → (Adj r z ↔ ¬ Adj z r) := edge_compl
  have hd : ∀ v, (Finset.univ.filter (Adj v)).card = 2795 := outdegree
  have hJ : DBound F 1 1 2 11 (c*2659412657821462341) := by
    intro y hy hz
    have h := SensitivityJointCover.endpoint22_phase1_bound
      Adj irreflexive ThreeBoundEndpoint22Selected.label htor hd H hH _ _ _ hbH haH hsH y hy hz
    have bound : 2*(c*53627300001453076)+2791*(c*914422496216727)+4*(c*1217719417783) =
        c*2659412657821462341 := by omega
    rw [bound] at h
    first | exact h | convert h using 1 <;> congr 1 <;> ext p <;> simp only [Finset.mem_union] <;> exact Iff.rfl
  have hD : DBound G 14 19 20 20 (c*4700783999961812061) := by
    intro x hx hy
    have h := JointCover.endpoint22_phase2_parent_joint
      Adj irreflexive ThreeBoundEndpoint22Selected.label htor hd F hF
      (c*986662590537317840) (c*24354388355660) (c*47117605675757176) (c*2659412657821462341)
      hb ha hq (by
        intro y hm hs
        convert hJ y hm hs using 1 <;> congr 1 <;> ext b <;> simp only [Finset.mem_union]) x hx hy
    have hnum : max (2*(c*986662590537317840)+2795*(c*24354388355660)+c*47117605675757176)
        (2*(c*986662590537317840)+2794*(c*24354388355660)+c*2659412657821462341) ≤
        c*4700783999961812061 := by apply max_le <;> omega
    first | exact h.trans hnum | convert h.trans hnum using 1 <;> congr 1 <;> ext p <;> simp only [Finset.mem_union] <;> exact Iff.rfl
  intro z
  by_cases hz : z = .d 14 19 20
  · subst z
    simpa only [scale,revised3,if_pos rfl,if_true] using
      (show Sem G (.d 14 19 20) (c*4700783999961812061) from fun _ _ => hD)
  · simpa only [scale,revised3,if_neg hz] using h₃ z

private theorem down_mono {I : Type} [Fintype I] (F : Fin 22 → (I → Bool) → Bool)
    (hF : Nested F) (i : Fin 22) (hi : i ≤ 3) (u : ℕ) (hu : DBound F 3 14 15 15 u) :
    DBound F i 14 15 15 u := by
  classical
  intro x hx hy
  apply (Finset.card_le_card _).trans (hu x hx hy)
  apply Finset.union_subset_union_left
  intro b hb
  obtain ⟨_,hfalse⟩ := Finset.mem_filter.mp hb
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  cases he : F 3 (_root_.OAI.Paper320.flip x {b}) with
  | false => rfl
  | true =>
    have h := hF i 3 hi _ he
    rw [h] at hfalse
    contradiction

private theorem final_core_check :
    let r := ThreeBoundMinmaxNumeric.Endpoint22.recipe (3 : Fin 4)
    ThreeBoundMinmaxNumeric.dCore 22 2795 revised3 (r 3) (r 14) (r 15) (r 15)
      10461023712484042305 ≤ 10459734084979310241 := by decide +kernel

private theorem phase_four_upper {I : Type} [Fintype I] (G : Fin 22 → (I → Bool) → Bool)
    (c : ℕ) (hG : Nested G) (h₃ : Upper G (scale c revised3))
    (hW : Nested (phaseStep 3 G)) (h₄ : Upper (phaseStep 3 G) (scale c profile4)) :
    Upper (phaseStep 3 G) (scale c revised4) := by
  let S := (ThreeBoundEndpoint22Selected.recipe 3).stage G
  let r : Fin 22 → ThreeBoundMinmaxNumeric.Entry := ThreeBoundMinmaxNumeric.Endpoint22.recipe 3
  let P := ThreeBoundEndpoint22Pairs.pairData Adj irreflexive ThreeBoundEndpoint22Selected.label 3 G
  let hm := ThreeBoundEndpoint22Pairs.entryMatch Adj irreflexive ThreeBoundEndpoint22Selected.label 3 G
  have old : DBound (phaseStep 3 G) 3 14 15 15 (c * 10461023712484042305) :=
    h₄ (.d 3 14 15) (by decide) (by decide)
  have hc := ThreeBoundMinmaxNumeric.dCore_bound S
    ⟨irreflexive,edge_compl⟩
    G hG r 3 14 15 15 (P 3 14 (by decide)) (P 14 15 (by decide)) (P 15 15 le_rfl)
    (hm 3 14 (by decide)) (hm 14 15 (by decide)) (hm 15 15 le_rfl)
    2795 (c * 10461023712484042305)
    (fun w => outdegree w)
    (scale c revised3) h₃ old
  rw [ThreeBoundMinmaxNumeric.dCore_homogeneous] at hc
  have strong : DBound (phaseStep 3 G) 3 14 15 15 (c*10459734084979310241) :=
    fun x hx hy => (hc x hx hy).trans (Nat.mul_le_mul_left c final_core_check)
  intro z
  cases z with
  | a i j => exact h₄ (.a i j)
  | b i j => exact h₄ (.b i j)
  | m i j => exact h₄ (.m i j)
  | p j l => exact h₄ (.p j l)
  | d i j l =>
    by_cases h : i ≤ 3 ∧ j = 14 ∧ l = 15
    · obtain ⟨hi,rfl,rfl⟩ := h
      simp only [scale,revised4,hi,and_self,if_true,eq_self]
      exact fun _ _ => down_mono _ hW i hi _ strong
    · simpa only [scale,revised4,if_neg h] using h₄ (.d i j l)

private theorem profile_le (z : Coord 22) (hz : valid z) :
    712440234061 * revised4 z ≤ 7211267676808970194 * profile0 z := by
  cases z with
  | a i j => exact (by decide +kernel : ∀ i j : Fin 22, valid (.a i j) →
      712440234061 * revised4 (.a i j) ≤ 7211267676808970194 * profile0 (.a i j)) i j hz
  | b i j => exact (by decide +kernel : ∀ i j : Fin 22, valid (.b i j) →
      712440234061 * revised4 (.b i j) ≤ 7211267676808970194 * profile0 (.b i j)) i j hz
  | m i j => exact (by decide +kernel : ∀ i j : Fin 22, valid (.m i j) →
      712440234061 * revised4 (.m i j) ≤ 7211267676808970194 * profile0 (.m i j)) i j hz
  | p j l => exact (by decide +kernel : ∀ j l : Fin 22, valid (.p j l) →
      712440234061 * revised4 (.p j l) ≤ 7211267676808970194 * profile0 (.p j l)) j l hz
  | d i j l => exact (by decide +kernel : ∀ i j l : Fin 22, valid (.d i j l) →
      712440234061 * revised4 (.d i j l) ≤ 7211267676808970194 * profile0 (.d i j l)) i j l hz

private theorem sem_of_invalid {I : Type} [Fintype I] (F : Fin 22 → (I → Bool) → Bool)
    (z : Coord 22) (h : ¬valid z) (k : ℕ) : Sem F z k := by
  cases z with
  | a i j => exact fun hij => (h hij).elim
  | b i j => exact fun hij => (h hij).elim
  | m i j => exact fun hij hn => (h ⟨hij,hn⟩).elim
  | p j l => exact fun hjl => (h hjl).elim
  | d i j l => exact fun hij hjl => (h ⟨hij,hjl⟩).elim
/-- Real growth per period, with integer profile bounds at each finite depth. -/
private noncomputable def rate : ℝ := 7211267676808970194 / 712440234061

private theorem two_le_rate : (2 : ℝ) ≤ rate := by norm_num [rate]

private noncomputable def cap : ℕ → ℕ
  | 0 => 1
  | m + 1 => ⌈rate * (cap m : ℝ)⌉₊

private theorem cap_step (m : ℕ) (coord : Coord 22) (hz : valid coord) :
    cap m * revised4 coord ≤ cap (m + 1) * profile0 coord := by
  have h : (712440234061 : ℝ) * (revised4 coord : ℝ) ≤
      7211267676808970194 * (profile0 coord : ℝ) := by
    exact_mod_cast profile_le coord hz
  have hp : (revised4 coord : ℝ) ≤ rate * (profile0 coord : ℝ) := by
    dsimp [rate]
    linarith only [h]
  have hc : rate * (cap m : ℝ) ≤ (cap (m + 1) : ℝ) := Nat.le_ceil _
  have hh : (cap m : ℝ) * (revised4 coord : ℝ) ≤
      (cap (m + 1) : ℝ) * (profile0 coord : ℝ) := calc
    _ ≤ (cap m : ℝ) * (rate * (profile0 coord : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = (rate * (cap m : ℝ)) * (profile0 coord : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
  exact_mod_cast hh

private theorem cap_bound (m : ℕ) : (cap m : ℝ) ≤ 2 * rate ^ m - 1 := by
  have hr := two_le_rate
  have hr0 : 0 ≤ rate := by linarith
  induction m with
  | zero => norm_num [cap]
  | succ m ih =>
    have h : (cap (m + 1) : ℝ) < rate * (cap m : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hr0 (Nat.cast_nonneg _))
    have h' := mul_le_mul_of_nonneg_left ih hr0
    rw [pow_succ]
    nlinarith only [h, h', hr]

private theorem periodic (m : ℕ) :
    Upper (ThreeBoundEndpoint22Selected.family (4*m)) (scale (cap m) profile0) := by
  induction m with
  | zero =>
      change Upper (ThreeBoundEndpoint22Selected.family 0) (fun coord => 1*profile0 coord)
      simpa only [one_mul] using actual_base_upper
  | succ m ih =>
      let c := cap m
      have h₁ : Upper (ThreeBoundEndpoint22Selected.family (4*m+1)) (scale c profile1) := by
        rw [family_succ_phase (4*m) 0 (by omega)]
        exact stage_from_hybrid records records_complete essentialSeeds numerical_complete
          closure_complete 0 _ (ThreeBoundEndpoint22Selected.family_nested (4*m)) c ih
      have h₂ : Upper (ThreeBoundEndpoint22Selected.family (4*m+2)) (scale c profile2) := by
        rw [show 4*m+2=(4*m+1)+1 by omega,family_succ_phase (4*m+1) 1 (by omega)]
        exact stage_from_hybrid records records_complete essentialSeeds numerical_complete
          closure_complete 1 _ (ThreeBoundEndpoint22Selected.family_nested (4*m+1)) c h₁
      have h₃ : Upper (ThreeBoundEndpoint22Selected.family (4*m+3)) (scale c profile3) := by
        rw [show 4*m+3=(4*m+2)+1 by omega,family_succ_phase (4*m+2) 2 (by omega)]
        exact stage_from_hybrid records records_complete essentialSeeds numerical_complete
          closure_complete 2 _ (ThreeBoundEndpoint22Selected.family_nested (4*m+2)) c h₂
      have h₄ : Upper (ThreeBoundEndpoint22Selected.family (4*m+4)) (scale c profile4) := by
        rw [show 4*m+4=(4*m+3)+1 by omega,family_succ_phase (4*m+3) 3 (by omega)]
        exact stage_from_hybrid records records_complete essentialSeeds numerical_complete
          closure_complete 3 _ (ThreeBoundEndpoint22Selected.family_nested (4*m+3)) c h₃
      have e₂ := family_succ_phase (4*m+1) 1 (by omega)
      have e₃ := family_succ_phase (4*m+2) 2 (by omega)
      have e₄ := family_succ_phase (4*m+3) 3 (by omega)
      have n₂ := ThreeBoundEndpoint22Selected.family_nested (4*m+2)
      have n₃ := ThreeBoundEndpoint22Selected.family_nested (4*m+3)
      have n₄ := ThreeBoundEndpoint22Selected.family_nested (4*m+4)
      have improved : Upper (ThreeBoundEndpoint22Selected.family (4*m+4)) (scale c revised4) := by
        rw [e₂] at h₂ n₂
        rw [e₃,e₂] at h₃ n₃
        rw [e₄,e₃,e₂] at h₄ n₄ ⊢
        exact phase_four_upper _ c n₃ (phase_three_upper _ c
          (ThreeBoundEndpoint22Selected.family_nested (4*m+1)) h₁ n₂ h₂ h₃) n₄ h₄
      have hf : Upper (ThreeBoundEndpoint22Selected.family (4*m+4))
          (scale (cap (m+1)) profile0) := by
        intro z
        by_cases hz : valid z
        · exact sem_mono _ z _ _ (cap_step m z hz) (improved z)
        · exact sem_of_invalid _ z hz _
      simpa only [Nat.mul_succ] using hf

open ThreeBoundEndpoint22Seeds
open Sensitivity5591Labeling.Labeling5591

private theorem actual_seeds (m : ℕ) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
        16^m ≤ _root_.OAI.Paper320.sensitivity f ∧
        (_root_.OAI.Paper320.sensitivity f : ℝ) ≤
          (2 * (prefactor profile0 : ℝ)) * rate^m ∧
        (5591^4)^m ≤ _root_.OAI.Paper320.blockSensitivity f := by
  let label := ThreeBoundEndpoint22Selected.label
  let f := finiteFamily Adj irreflexive label (4*m) 0
  have hlow := finiteFamily_four_stage_lower Adj irreflexive label m 0
  obtain ⟨hs0, hb⟩ := hlow
  refine ⟨11182^(4*m), f, hs0, ?_, hb⟩
  have hu : _root_.OAI.Paper320.sensitivity f ≤ prefactor profile0 * cap m := by
    exact upper_at_scale Adj irreflexive label profile0 m (cap m) (periodic m)
  have hcast : (_root_.OAI.Paper320.sensitivity f : ℝ) ≤
      (prefactor profile0 : ℝ) * (cap m : ℝ) := by exact_mod_cast hu
  have hcap : (cap m : ℝ) ≤ 2 * rate^m := by linarith only [cap_bound m]
  calc
    _ ≤ (prefactor profile0 : ℝ) * (cap m : ℝ) := hcast
    _ ≤ (prefactor profile0 : ℝ) * (2 * rate ^ m) :=
      mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg _)
    _ = _ := by ring

open _root_.OAI.Paper320

private theorem endpoint :
    SensitivityCampaign.AchievesExponent (Real.log ((5591 : ℝ)^4) / Real.log rate) := by
  let g : ℝ := (5591 : ℝ)^4
  let c : ℝ := 2 * (prefactor profile0 : ℝ)
  have hc0 : (2 : ℕ) ≤ prefactor profile0 := le_max_left _ _
  have hc2 : (2 : ℝ) ≤ (prefactor profile0 : ℝ) := by exact_mod_cast hc0
  have hc : 0 < c := by dsimp [c]; linarith
  have hr1 : 1 < rate := by linarith only [two_le_rate]
  have hr := lt_trans (by norm_num : (0:ℝ) < 1) hr1
  have hg1 : 1 < g := by norm_num [g]
  have hg := lt_trans (by norm_num : (0:ℝ) < 1) hg1
  have hlg := Real.log_pos hg1
  have hlr := Real.log_pos hr1
  let a := Real.log g / Real.log rate
  have ha : 0 < a := div_pos hlg hlr
  intro ε hε S hS
  let b := max 0 (a - ε)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hba : b < a := max_lt ha (by linarith)
  let δ := Real.log g - b * Real.log rate
  have hδ : 0 < δ := sub_pos.mpr ((lt_div_iff₀ hlr).mp hba)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (S : ℝ) (b * Real.log c / δ))
  have hmS : S < m := by exact_mod_cast ((le_max_left _ _).trans_lt hm)
  have hgap : b * Real.log c < (m : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨n, f, hs0, hs, hbs⟩ := actual_seeds m
  have hSle : S ≤ sensitivity f :=
    hmS.le.trans ((Nat.lt_pow_self (by decide : 1 < 16)).le.trans hs0)
  have hbase : (1 : ℝ) ≤ sensitivity f := by
    exact_mod_cast (show 1 ≤ sensitivity f by omega)
  refine ⟨n, f, hSle, ?_⟩
  have hp : (c * rate^m)^b ≤ g^m := by
    apply (Real.rpow_le_iff_le_log (mul_pos hc (pow_pos hr m)) (pow_pos hg m)).2
    rw [Real.log_mul hc.ne' (pow_pos hr m).ne', Real.log_pow, Real.log_pow]
    dsimp only [δ] at hgap
    nlinarith only [hgap]
  calc
    (sensitivity f : ℝ)^(a-ε) ≤ (sensitivity f : ℝ)^b :=
      Real.rpow_le_rpow_of_exponent_le hbase (le_max_right _ _)
    _ ≤ (c * rate^m)^b := Real.rpow_le_rpow (Nat.cast_nonneg _) hs hb0
    _ ≤ g^m := hp
    _ ≤ (blockSensitivity f : ℝ) := by
      dsimp only [g]
      exact_mod_cast hbs

end ExactFourStageBound
end Sensitivity213981Formal

theorem solution : SensitivityCampaign.AchievesExponent
    (Real.log ((5591 : ℝ) ^ 4) / Real.log ((7211267676808970194 : ℝ) / 712440234061)) := by
  exact Sensitivity213981Formal.ExactFourStageBound.endpoint
