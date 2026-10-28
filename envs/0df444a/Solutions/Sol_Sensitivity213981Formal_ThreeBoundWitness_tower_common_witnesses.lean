-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundWitness.tower_common_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:40:14.69141+00:00
-- url     : https://prove2.me/submissions/f2d99c24-d59c-430b-a823-17fc7edffe48

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RecursiveLowerBounds
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_common_positive_lift


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
open OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]

theorem parent_false_of_targets_false [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool)
    (h : ∀ v : V,
      S.target l (failed S F l x v).card (child x v false) (child x v true) = false) :
    parent S F l x = false := by
  classical
  simp only [parent, decide_eq_false_iff_not]
  rintro ⟨v, _, hv⟩
  rw [h v] at hv
  contradiction







@[simp] theorem child_planted_same (z p : I → Bool) (v : V) (c : Bool) :
    child (planted z p v) v c = p := by
  classical
  funext i
  simp [child, planted]

theorem child_planted_other (z p : I → Bool) (v w : V) (c : Bool) (hw : w ≠ v) :
    child (planted z p v) w c = z := by
  classical
  funext i
  simp [child, planted, hw]

theorem planted_failed_empty [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (v : V) (l : L) :
    failed S F l (planted z p v) v = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro w _ hw
  have hwv : w ≠ v := by
    intro he
    subst w
    exact S.loopless v hw.1
  rw [child_planted_other z p v w (S.label v w) hwv, hz] at hw
  exact Bool.noConfusion hw.2

theorem parent_accepts_planted [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (hp : ∀ l, F l p = true)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true) (v : V) (l : L) :
    parent S F l (planted z p v) = true := by
  apply (parent_true_iff S F l _).2
  refine ⟨v, ?_, ?_⟩
  · simp [planted_failed_empty S F z p hz v l]
  · simpa only [planted_failed_empty S F z p hz v l, Finset.card_empty,
      child_planted_same] using haccept l p p hp hp

theorem parent_rejects_replicated [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z : I → Bool)
    (hz : ∀ l, F l z = false)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (l : L) : parent S F l (replicate z) = false := by
  apply parent_false_of_targets_false
  intro v
  exact hreject l _ z z (Or.inl hz)











@[simp] theorem mem_pairedBlock (v w : V) (c : Bool) (i : I) (B : Finset I) :
    ((w,c),i) ∈ pairedBlock v B ↔ w = v ∧ i ∈ B := by
  classical
  unfold pairedBlock
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨b,j⟩, hj, heq⟩
    change ((v,b),j) = ((w,c),i) at heq
    cases heq
    exact ⟨rfl, (Finset.mem_product.mp hj).2⟩
  · rintro ⟨rfl, hi⟩
    exact ⟨(c,i), Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

theorem pairedBlock_nonempty (v : V) (B : Finset I) (hB : B.Nonempty) :
    (pairedBlock v B).Nonempty := by
  obtain ⟨i, hi⟩ := hB
  exact ⟨((v,false),i), (mem_pairedBlock v v false i B).2 ⟨rfl,hi⟩⟩

theorem pairedBlock_disjoint {A : Type} (B : A → Finset I)
    (hB : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (v w : V) (a b : A) (h : (v,a) ≠ (w,b)) :
    Disjoint (pairedBlock v (B a)) (pairedBlock w (B b)) := by
  classical
  apply Finset.disjoint_left.mpr
  rintro ⟨⟨u,c⟩,i⟩ hi hj
  obtain ⟨huv, hia⟩ := (mem_pairedBlock v u c i (B a)).1 hi
  obtain ⟨huw, hib⟩ := (mem_pairedBlock w u c i (B b)).1 hj
  have hvw : v = w := huv.symm.trans huw
  have hab : a ≠ b := by
    intro he
    exact h (Prod.ext hvw he)
  exact (Finset.disjoint_left.mp (hB a b hab)) hia hib

theorem flip_replicate_pairedBlock (z : I → Bool) (v : V) (B : Finset I) :
    _root_.OAI.Paper320.flip (replicate z) (pairedBlock v B) = planted z (_root_.OAI.Paper320.flip z B) v := by
  classical
  funext q
  rcases q with ⟨⟨w,c⟩,i⟩
  by_cases hw : w = v <;> by_cases hi : i ∈ B <;>
    simp [_root_.OAI.Paper320.flip, replicate, planted, hw, hi]

/-- The common zero-input block witness multiplies its index set by V. -/
theorem common_blocks_lift [Fintype V] {A : Type}
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (z : I → Bool) (hz : ∀ l, F l z = false)
    (B : A → Finset I) (hne : ∀ a, (B a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hflip : ∀ a l, F l (_root_.OAI.Paper320.flip z (B a)) = true)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false) :
    ∃ (z' : ((V × Bool) × I) → Bool) (B' : (V × A) → Finset ((V × Bool) × I)),
      (∀ l, parent S F l z' = false) ∧
      (∀ a, (B' a).Nonempty) ∧
      (∀ a b, a ≠ b → Disjoint (B' a) (B' b)) ∧
      (∀ a l, parent S F l (_root_.OAI.Paper320.flip z' (B' a)) = true) := by
  let B' : (V × A) → Finset ((V × Bool) × I) := fun a => pairedBlock a.1 (B a.2)
  refine ⟨replicate z, B', ?_, ?_, ?_, ?_⟩
  · exact fun l => parent_rejects_replicated S F z hz hreject l
  · exact fun a => pairedBlock_nonempty a.1 (B a.2) (hne a.2)
  · exact fun a b h => pairedBlock_disjoint B hdis a.1 b.1 a.2 b.2 h
  · intro a l
    change parent S F l (_root_.OAI.Paper320.flip (replicate z) (pairedBlock a.1 (B a.2))) = true
    rw [flip_replicate_pairedBlock]
    exact parent_accepts_planted S F z (_root_.OAI.Paper320.flip z (B a.2)) hz (hflip a.2) haccept a.1 l









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
open OAI.Paper320













theorem minmax_accepts {L I V : Type} (r : MinMaxRecipe L V)
    (F : L → (I → Bool) → Bool) (l : L) (x y : I → Bool)
    (hx : ∀ a, F a x = true) (hy : ∀ a, F a y = true) :
    (r.stage F).target l 0 x y = true := by
  simp [MinMaxRecipe.stage, minmaxTarget, hx, hy]

theorem minmax_rejects {L I V : Type} (r : MinMaxRecipe L V)
    (F : L → (I → Bool) → Bool) (l : L) (d : ℕ) (x y : I → Bool)
    (h : (∀ a, F a x = false) ∨ (∀ a, F a y = false)) :
    (r.stage F).target l d x y = false := by
  rcases h with hx | hy
  · simp [MinMaxRecipe.stage, minmaxTarget, hx]
  · simp [MinMaxRecipe.stage, minmaxTarget, hy]









theorem common_witnesses_lift {L I V A B : Type} [Fintype V]
    (r : MinMaxRecipe L V) (F : L → (I → Bool) → Bool)
    (w : CommonWitnesses F A B) (v : V) :
    Nonempty (CommonWitnesses (parent (r.stage F) F) (Bool × A) (V × B)) := by
  obtain ⟨p', e', hp', he'⟩ := common_positive_lift (r.stage F) F
    w.zero w.positive w.zero_rejects w.positive_accepts w.positiveBits w.positive_off
    (minmax_accepts r F) (minmax_rejects r F) v
  obtain ⟨z', B', hz', hne', hdis', hflip'⟩ := common_blocks_lift (r.stage F) F
    w.zero w.zero_rejects w.blocks w.blocks_nonempty w.blocks_disjoint w.blocks_on
    (minmax_accepts r F) (minmax_rejects r F)
  exact ⟨⟨z', p', e', B', hz', hp', he', hne', hdis', hflip'⟩⟩

theorem tower_common_witnesses {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) (v : V) (n : ℕ) :
    Nonempty (CommonWitnesses (towerFamily r n) (IterProd Bool n) (IterProd V n)) := by
  classical
  induction n with
  | zero =>
      refine ⟨{
        zero := fun _ => false
        positive := fun _ => true
        positiveBits := Function.Embedding.refl Unit
        blocks := fun _ => {()}
        zero_rejects := fun _ => rfl
        positive_accepts := fun _ => rfl
        positive_off := ?_
        blocks_nonempty := ?_
        blocks_disjoint := ?_
        blocks_on := ?_ }⟩
      · intro a l
        cases a
        change (_root_.OAI.Paper320.flip (fun _ : Unit => true) {()}) () = false
        simp [_root_.OAI.Paper320.flip]
      · intro a
        exact Finset.singleton_nonempty ()
      · intro a b h
        cases a
        cases b
        exact False.elim (h rfl)
      · intro a l
        change (_root_.OAI.Paper320.flip (fun _ : Unit => false) {()}) () = true
        simp [_root_.OAI.Paper320.flip]
  | succ n ih =>
      obtain ⟨w⟩ := ih
      exact common_witnesses_lift (r n) (towerFamily r n) w v











end ThreeBoundWitness








end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L V : Type} [inst : Fintype.{0} V] (r : Nat → Sensitivity213981Formal.ThreeBoundWitness.MinMaxRecipe L V) (v : V)
  (n : Nat),
  Nonempty.{1}
    (@Sensitivity213981Formal.ThreeBoundWitness.CommonWitnesses L
      (Sensitivity213981Formal.ThreeBoundWitness.IterProd (Prod.{0, 0} V Bool) n)
      (@Sensitivity213981Formal.ThreeBoundWitness.towerFamily L V inst r n)
      (Sensitivity213981Formal.ThreeBoundWitness.IterProd Bool n)
      (Sensitivity213981Formal.ThreeBoundWitness.IterProd V n)) := @Sensitivity213981Formal.ThreeBoundWitness.tower_common_witnesses
