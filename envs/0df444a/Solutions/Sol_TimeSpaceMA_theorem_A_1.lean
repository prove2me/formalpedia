-- Prove2me | solution 1 for TimeSpaceMA.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T19:40:51.218385+00:00
-- url     : https://prove2.me/submissions/93cc8f35-1db4-434e-b6c0-39fc1ae8ab31

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
import Definitions.Def_TimeSpaceMA_TUZExtractor
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_TimeSpaceMA_constantLossFlatExtractor
import Theorems.Thm_TimeSpaceMA_widthListComputable_to_coinFreeRAM

open scoped BigOperators

namespace TimeSpaceMA

section
variable {Input Seed Out : Type} [Fintype Seed] [Fintype Out] [DecidableEq Out]

/-- Statistical closeness implies support coverage for every finite flat input source. -/
theorem support_of_flatExtractorEvents (E : Input → Seed → Out) (S : Finset Input)
    (hS : 0 < S.card) (hseed : 0 < Fintype.card Seed) (hout : 0 < Fintype.card Out)
    (ε : ℝ) (hE : FlatExtractorEvents E S ε) :
    (1-ε) * (Fintype.card Out : ℝ) ≤
      (S.biUnion (fun x => Finset.univ.image (E x))).card := by
  classical
  let U := S.biUnion (fun x => Finset.univ.image (E x))
  have hfilter : ((S ×ˢ Finset.univ).filter (fun p : Input × Seed => E p.1 p.2 ∈ U)) =
      S ×ˢ Finset.univ := by
    apply Finset.filter_true_of_mem
    rintro ⟨x,s⟩ hp
    exact Finset.mem_biUnion.mpr ⟨x, (Finset.mem_product.mp hp).1,
      Finset.mem_image_of_mem _ (Finset.mem_univ s)⟩
  have hden : (S.card : ℝ) * (Fintype.card Seed : ℝ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hS)) (by exact_mod_cast (Nat.ne_of_gt hseed))
  have hEU := hE U
  rw [hfilter, Finset.card_product, Finset.card_univ, Nat.cast_mul, div_self hden] at hEU
  have hratio : 1-ε ≤ (U.card : ℝ) / (Fintype.card Out : ℝ) := by linarith
  exact (le_div_iff₀ (by exact_mod_cast hout)).mp hratio

end

section Composition
variable {Prefix Suffix Seed₁ Seed₂ Right : Type}
variable [Fintype Seed₁] [Fintype Seed₂] [Fintype Right]
variable [DecidableEq Seed₂] [DecidableEq Right]

/-- For a flat prefix set with sufficiently rich suffix fibers, first use each fiber
to cover most of the seed space, then apply an extractor to the prefixes. The resulting
support covers a `1-δ-ε` fraction of the final universe. -/
theorem support_compose_extractors
    (E₁ : Prefix → Suffix → Seed₁ → Seed₂) (E₂ : Prefix → Seed₂ → Right)
    (A : Finset Prefix) (B : Prefix → Finset Suffix)
    (hA : 0 < A.card) (hseed : 0 < Fintype.card Seed₂) (hR : 0 < Fintype.card Right)
    (δ ε : ℝ)
    (h₁ : ∀ a ∈ A, (1-δ) * (Fintype.card Seed₂ : ℝ) ≤
      ((B a).biUnion fun b => Finset.univ.image (E₁ a b)).card)
    (h₂ : FlatExtractorEvents E₂ A ε) :
    (1-δ-ε) * (Fintype.card Right : ℝ) ≤
      (A.biUnion (fun a => (B a).biUnion fun b =>
        Finset.univ.image (fun t => E₂ a (E₁ a b t)))).card := by
  classical
  let K := fun a => (B a).biUnion fun b => Finset.univ.image (E₁ a b)
  let U := A.biUnion (fun a => (B a).biUnion fun b => Finset.univ.image (fun t => E₂ a (E₁ a b t)))
  let G := (A ×ˢ Finset.univ).filter (fun p : Prefix × Seed₂ => E₂ p.1 p.2 ∈ U)
  let T := fun a => Finset.univ.filter (fun y : Seed₂ => E₂ a y ∈ U)
  have hsub (a : Prefix) (ha : a ∈ A) : K a ⊆ T a := by
    intro y hy
    obtain ⟨b,hb,hby⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hby
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr
      ⟨a,ha,Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_image_of_mem _ (Finset.mem_univ t)⟩⟩⟩
  have hcard : G.card = ∑ a ∈ A, (T a).card := by
    rw [Finset.card_filter]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    exact (Finset.card_filter _ _).symm
  have hreal : (G.card : ℝ) = ∑ a ∈ A, ((T a).card : ℝ) := by exact_mod_cast hcard
  have hlower : (1-δ) * ((A.card : ℝ) * (Fintype.card Seed₂ : ℝ)) ≤ (G.card : ℝ) := by
    rw [hreal]
    calc
      _ = ∑ _a ∈ A, (1-δ) * (Fintype.card Seed₂ : ℝ) := by simp [nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun a ha => (h₁ a ha).trans (by exact_mod_cast Finset.card_le_card (hsub a ha)))
  have hden : 0 < (A.card : ℝ) * (Fintype.card Seed₂ : ℝ) := by
    have hcA : 0 < (A.card : ℝ) := by exact_mod_cast hA
    have hcSeed : 0 < (Fintype.card Seed₂ : ℝ) := by exact_mod_cast hseed
    exact mul_pos hcA hcSeed
  have hratio := (le_div_iff₀ hden).2 hlower
  have hdist := h₂ U
  change (G.card : ℝ) / ((A.card : ℝ) * (Fintype.card Seed₂ : ℝ)) -
    (U.card : ℝ) / (Fintype.card Right : ℝ) ≤ ε at hdist
  have hgoal : 1-δ-ε ≤ (U.card : ℝ) / (Fintype.card Right : ℝ) := by linarith
  exact (le_div_iff₀ (by exact_mod_cast hR)).1 hgoal

end Composition

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA

/-- Words in the support extending the specified prefix at the specified depth. -/
def wordsWithPrefix (A : Finset (List Bool)) (i : ℕ) (p : List Bool) : Finset (List Bool) :=
  A.filter fun x => x.take i = p

/-- The full set of prefixes with at least `B` support extensions at this depth. -/
def heavyPrefixes (A : Finset (List Bool)) (B i : ℕ) : Finset (List Bool) :=
  (A.image (List.take i)).filter fun p => B ≤ (wordsWithPrefix A i p).card

/-- Some depth has many heavy prefixes. Charge every support word to its last heavy prefix.
The charged words at each prefix lie in at most two light child fibers. -/
theorem exists_many_heavyPrefixes (A : Finset (List Bool)) (B n : ℕ)
    (hn : ∀ x ∈ A, x.length = n) (hB : 2 ≤ B) (hAB : B ≤ A.card) :
    ∃ i < n, A.card ≤ n * (2 * (B - 1)) * (heavyPrefixes A B i).card := by
  classical
  have hnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  have hlast (x : List Bool) (hx : x ∈ A) : (wordsWithPrefix A n (x.take n)).card < B := by
    have hsub : wordsWithPrefix A n (x.take n) ⊆ {x} := by
      intro y hy
      obtain ⟨hy, hp⟩ := Finset.mem_filter.mp hy
      rw [← hn x hx, List.take_length, hn x hx, ← hn y hy, List.take_length] at hp
      simpa using hp
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  have hex (x : List Bool) (hx : x ∈ A) :
      ∃ m, (wordsWithPrefix A m (x.take m)).card < B := ⟨n, hlast x hx⟩
  let firstLight (x : List Bool) : ℕ :=
    if hx : x ∈ A then Nat.find (hex x hx) else 0
  have hroot (x : List Bool) : wordsWithPrefix A 0 (x.take 0) = A := by
    simp [wordsWithPrefix]
  have firstBounds (x : List Bool) (hx : x ∈ A) :
      0 < firstLight x ∧ firstLight x ≤ n := by
    have hspec := Nat.find_spec (hex x hx)
    have hle := Nat.find_min' (hex x hx) (hlast x hx)
    simp only [firstLight, dif_pos hx]
    refine ⟨Nat.pos_of_ne_zero (fun heq => ?_), hle⟩
    rw [heq, hroot] at hspec
    exact (not_lt_of_ge hAB) hspec
  let depth (x : List Bool) := firstLight x - 1
  have hdepth (x : List Bool) (hx : x ∈ A) : depth x < n := by
    have := firstBounds x hx
    dsimp [depth]
    omega
  have hdepth_succ (x : List Bool) (hx : x ∈ A) : depth x + 1 = firstLight x := by
    have := (firstBounds x hx).1
    dsimp [depth]
    omega
  have lastHeavy (x : List Bool) (hx : x ∈ A) :
      B ≤ (wordsWithPrefix A (depth x) (x.take (depth x))).card := by
    apply Nat.le_of_not_gt
    apply Nat.find_min (hex x hx)
    have h := (firstBounds x hx).1
    simpa only [depth, firstLight, dif_pos hx] using
      (show firstLight x - 1 < firstLight x by omega)
  have firstLight_lt (x : List Bool) (hx : x ∈ A) :
      (wordsWithPrefix A (depth x + 1) (x.take (depth x + 1))).card < B := by
    rw [hdepth_succ x hx]
    simpa only [firstLight, dif_pos hx] using Nat.find_spec (hex x hx)
  let atDepth (i : ℕ) := A.filter fun x => depth x = i
  have allAtDepth (i : ℕ) (hi : i < n) :
      (atDepth i).card ≤ (heavyPrefixes A B i).card * (2 * (B-1)) := by
    let fibers (p : List Bool) := (atDepth i).filter fun x => x.take i = p
    have hmap : Set.MapsTo (List.take i) (↑(atDepth i) : Set (List Bool))
        (↑(heavyPrefixes A B i) : Set (List Bool)) := by
      intro x hx
      obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp (show x ∈ atDepth i from hx)
      have hh := lastHeavy x hx
      rw [hxi] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hx, hh⟩
    have hlocal (p : List Bool) (b : Bool) :
        ((fibers p).filter fun x => x.take (i+1) = p ++ [b]).card ≤ B-1 := by
      let assigned := (fibers p).filter fun x => x.take (i+1) = p ++ [b]
      by_cases he : assigned.Nonempty
      · obtain ⟨y, hy⟩ := he
        obtain ⟨hy, hnext⟩ := Finset.mem_filter.mp hy
        obtain ⟨hy, _⟩ := Finset.mem_filter.mp hy
        obtain ⟨hy, hdepthy⟩ := Finset.mem_filter.mp hy
        have hlight : (wordsWithPrefix A (i+1) (p ++ [b])).card < B := by
          simpa only [hdepthy, hnext] using firstLight_lt y hy
        have hsub : assigned ⊆ wordsWithPrefix A (i+1) (p ++ [b]) := by
          intro z hz
          obtain ⟨hz, hzpre⟩ := Finset.mem_filter.mp hz
          obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, hzpre⟩
        have := Finset.card_le_card hsub
        change assigned.card ≤ B - 1
        omega
      · have hz : assigned = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        change assigned.card ≤ _
        simp [hz]
    have hfiber (p : List Bool) : (fibers p).card ≤ 2*(B-1) := by
      let S₀ := (fibers p).filter fun x => x.take (i+1) = p ++ [false]
      let S₁ := (fibers p).filter fun x => x.take (i+1) = p ++ [true]
      have hsub : fibers p ⊆ S₀ ∪ S₁ := by
        intro x hx
        obtain ⟨hxd, hxp⟩ := Finset.mem_filter.mp hx
        have hxA := (Finset.mem_filter.mp hxd).1
        have hxi : i < x.length := by rw [hn x hxA]; exact hi
        have hnext := List.take_succ_eq_append_getElem hxi
        rw [hxp] at hnext
        apply Finset.mem_union.mpr
        cases hb : x[i] with
        | false => exact .inl (Finset.mem_filter.mpr ⟨hx, by simpa only [hb] using hnext⟩)
        | true => exact .inr (Finset.mem_filter.mpr ⟨hx, by simpa only [hb] using hnext⟩)
      have hsum := (Finset.card_le_card hsub).trans (Finset.card_union_le S₀ S₁)
      have hl := hlocal p false
      have hr := hlocal p true
      change S₀.card ≤ _ at hl
      change S₁.card ≤ _ at hr
      omega
    calc
      (atDepth i).card = ∑ p ∈ heavyPrefixes A B i, (fibers p).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _ ∈ heavyPrefixes A B i, 2*(B-1) := Finset.sum_le_sum fun p _ => hfiber p
      _ = _ := by simp [Nat.nsmul_eq_mul]
  have hmaps : Set.MapsTo depth (↑A : Set (List Bool)) (↑(Finset.range n) : Set ℕ) :=
    fun x hx => Finset.mem_range.mpr (hdepth x hx)
  have hrange : (Finset.range n).Nonempty := by
    obtain ⟨x,hx⟩ := hnonempty
    exact ⟨depth x, hmaps hx⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range n)
    (fun j => (heavyPrefixes A B j).card) hrange
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  calc
    A.card = ∑ j ∈ Finset.range n, (atDepth j).card := Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _ ∈ Finset.range n, (heavyPrefixes A B i).card * (2*(B-1)) :=
      Finset.sum_le_sum fun j hj => (allAtDepth j (Finset.mem_range.mp hj)).trans
        (Nat.mul_le_mul_right _ (hmax j hj))
    _ = _ := by rw [Finset.sum_const, Finset.card_range]; simp only [Nat.nsmul_eq_mul]; ac_rfl


/-- The suffix words extending a prefix, with the prefix removed. -/
def suffixFiber (A : Finset (List Bool)) (i : ℕ) (p : List Bool) : Finset (List Bool) :=
  (wordsWithPrefix A i p).image (List.drop i)

@[simp]
theorem card_suffixFiber (A : Finset (List Bool)) (i : ℕ) (p : List Bool) :
    (suffixFiber A i p).card = (wordsWithPrefix A i p).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hdrop
  have hxp := (Finset.mem_filter.mp hx).2
  have hyp := (Finset.mem_filter.mp hy).2
  rw [← List.take_append_drop i x, ← List.take_append_drop i y, hxp, hyp, hdrop]

theorem append_mem_of_suffixFiber {A : Finset (List Bool)} {i : ℕ} {p b : List Bool}
    (hb : b ∈ suffixFiber A i p) : p ++ b ∈ A := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hxA, hxp⟩ := Finset.mem_filter.mp hx
  simpa only [← hxp, List.take_append_drop] using hxA

theorem length_of_suffixFiber {A : Finset (List Bool)} {n i : ℕ} {p b : List Bool}
    (hn : ∀ x ∈ A, x.length = n) (hb : b ∈ suffixFiber A i p) : b.length = n-i := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  rw [List.length_drop, hn x (Finset.mem_filter.mp hx).1]

theorem length_of_heavyPrefix {A : Finset (List Bool)} {B n i : ℕ} {p : List Bool}
    (hn : ∀ x ∈ A, x.length = n) (hi : i ≤ n) (hp : p ∈ heavyPrefixes A B i) :
    p.length = i := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp).1
  rw [List.length_take, hn x hx, Nat.min_eq_left hi]

/-- A support with enough words has a cut with at least `H` distinct prefixes, each extending
at least `B` distinct suffixes. These prefix and suffix sets are actual parts of the support. -/
theorem exists_prefix_split (A : Finset (List Bool)) (B H n : ℕ)
    (hn : ∀ x ∈ A, x.length = n) (hB : 2 ≤ B) (hAB : B ≤ A.card)
    (hsize : n * (2*(B-1)) * H ≤ A.card) :
    ∃ i < n, ∃ P : Finset (List Bool), H ≤ P.card ∧
      ∀ p ∈ P, p.length = i ∧ B ≤ (suffixFiber A i p).card ∧
      ∀ b ∈ suffixFiber A i p, b.length = n-i ∧ p ++ b ∈ A := by
  obtain ⟨i, hi, hcard⟩ := exists_many_heavyPrefixes A B n hn hB hAB
  refine ⟨i, hi, heavyPrefixes A B i, ?_, ?_⟩
  · have hpos : 0 < n * (2*(B-1)) := Nat.mul_pos (by omega) (Nat.mul_pos (by decide) (by omega))
    exact Nat.le_of_mul_le_mul_left (hsize.trans hcard) hpos
  · intro p hp
    refine ⟨length_of_heavyPrefix hn hi.le hp, ?_, ?_⟩
    · rw [card_suffixFiber]
      exact (Finset.mem_filter.mp hp).2
    · intro b hb
      exact ⟨length_of_suffixFiber hn hb, append_mem_of_suffixFiber hb⟩

end TimeSpaceMA

namespace TimeSpaceMA

/-- Package a cut and seed as a single edge index, retaining the seed as the low-order digit. -/
def tuzCoordinateGraph {α : Type} {Rows Seeds R : ℕ}
    (E : α → Fin Rows → Fin Seeds → Fin R) : α → Fin (Rows * Seeds) → Fin R :=
  fun x i =>
    let p : Fin Rows × Fin Seeds := finProdFinEquiv.symm i
    E x p.1 p.2

@[simp] theorem tuzCoordinateGraph_encode {α : Type} {Rows Seeds R : ℕ}
    (E : α → Fin Rows → Fin Seeds → Fin R) (x : α) (c : Fin Rows) (t : Fin Seeds) :
    tuzCoordinateGraph E x (finProdFinEquiv (c,t)) = E x c t := by
  simp [tuzCoordinateGraph]

/-- The exact right-neighbor set is the union over the cut and seed coordinates. -/
theorem tuzCoordinateGraph_neighbors {α : Type} {Rows Seeds R : ℕ}
    (E : α → Fin Rows → Fin Seeds → Fin R) (D : Finset α) :
    D.biUnion (fun x => Finset.univ.image (tuzCoordinateGraph E x)) =
      D.biUnion (fun x => Finset.univ.image (fun p : Fin Rows × Fin Seeds => E x p.1 p.2)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr
      ⟨finProdFinEquiv.symm i, Finset.mem_univ _, rfl⟩⟩
  · intro hy
    obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨⟨c,t⟩,_,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr
      ⟨finProdFinEquiv (c,t), Finset.mem_univ _, tuzCoordinateGraph_encode E x c t⟩⟩

/-- If the inputs `join a b` lie in a larger source, support from a single chosen cut
contributes to the complete graph's neighborhood. -/
theorem tuzCoordinateGraph_support_ge {α Prefix Suffix : Type} {Rows Seeds R : ℕ}
    (E : α → Fin Rows → Fin Seeds → Fin R) (D : Finset α) (c : Fin Rows)
    (A : Finset Prefix) (B : Prefix → Finset Suffix) (join : Prefix → Suffix → α)
    (hjoin : ∀ a ∈ A, ∀ b ∈ B a, join a b ∈ D) :
    (A.biUnion (fun a => (B a).biUnion fun b => Finset.univ.image (E (join a b) c))).card ≤
      (D.biUnion (fun x => Finset.univ.image (tuzCoordinateGraph E x))).card := by
  apply Finset.card_le_card
  intro y hy
  obtain ⟨a,ha,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨b,hb,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_biUnion.mpr ⟨join a b, hjoin a ha b hb,
    Finset.mem_image.mpr ⟨finProdFinEquiv (c,t), Finset.mem_univ _, tuzCoordinateGraph_encode E (join a b) c t⟩⟩

/-- The preceding coverage argument applies to a fixed coordinate in the final graph
that composes the inner and outer extractors on a suitable collection of fibers. -/
theorem tuzCoordinateGraph_extractors_ge
    {α Prefix Suffix : Type} {Rows Seeds₁ Seeds₂ R : ℕ}
    (E : α → Fin Rows → Fin Seeds₁ → Fin R) (D : Finset α) (c : Fin Rows)
    (A : Finset Prefix) (B : Prefix → Finset Suffix) (join : Prefix → Suffix → α)
    (hjoin : ∀ a ∈ A, ∀ b ∈ B a, join a b ∈ D)
    (E₁ : Prefix → Suffix → Fin Seeds₁ → Fin Seeds₂) (E₂ : Prefix → Fin Seeds₂ → Fin R)
    (hcomp : ∀ a ∈ A, ∀ b ∈ B a, ∀ t, E (join a b) c t = E₂ a (E₁ a b t))
    (hA : 0 < A.card) (hseed : 0 < Seeds₂) (hR : 0 < R) (δ ε : ℝ)
    (h₁ : ∀ a ∈ A, (1-δ) * (Seeds₂ : ℝ) ≤
      ((B a).biUnion fun b => Finset.univ.image (E₁ a b)).card)
    (h₂ : FlatExtractorEvents E₂ A ε) :
    (1-δ-ε) * (R : ℝ) ≤ (D.biUnion (fun x => Finset.univ.image (tuzCoordinateGraph E x))).card := by
  have hin := support_compose_extractors E₁ E₂ A B hA
    (by simpa using hseed) (by simpa using hR) δ ε (by simpa using h₁) h₂
  have hle : (A.biUnion (fun a => (B a).biUnion fun b =>
      Finset.univ.image (fun t => E₂ a (E₁ a b t)))).card ≤
      (D.biUnion (fun x => Finset.univ.image (tuzCoordinateGraph E x))).card := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨a,ha,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨b,hb,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨join a b, hjoin a ha b hb,
      Finset.mem_image.mpr ⟨finProdFinEquiv (c,t), Finset.mem_univ _,
        (tuzCoordinateGraph_encode E (join a b) c t).trans (hcomp a ha b hb t)⟩⟩
  exact (by simpa using hin : (1-δ-ε) * (R : ℝ) ≤
    (A.biUnion (fun a => (B a).biUnion fun b =>
      Finset.univ.image (fun t => E₂ a (E₁ a b t)))).card).trans (by exact_mod_cast hle)

end TimeSpaceMA

namespace TimeSpaceMA

section
variable {Input Larger Seed Out : Type} [Fintype Seed] [Fintype Out] [DecidableEq Out]

/-- Transport a flat-source extractor guarantee along any embedding of the input labels. -/
theorem FlatExtractorEvents.comapInput
    (E : Larger → Seed → Out) (S : Finset Input) (f : Input ↪ Larger) (ε : ℝ)
    (h : FlatExtractorEvents E (S.map f) ε) :
    FlatExtractorEvents (fun x => E (f x)) S ε := by
  classical
  intro A
  let F : (Input × Seed) ↪ (Larger × Seed) :=
    ⟨fun p => (f p.1,p.2), fun p q hpq =>
      Prod.ext (f.injective (congrArg Prod.fst hpq)) (congrArg (fun v : Larger × Seed => v.2) hpq)⟩
  have heq : (S.map f ×ˢ Finset.univ).filter (fun p : Larger × Seed => E p.1 p.2 ∈ A) =
      ((S ×ˢ Finset.univ).filter (fun p : Input × Seed => E (f p.1) p.2 ∈ A)).map F := by
    ext p
    obtain ⟨y,t⟩ := p
    constructor
    · intro hp
      obtain ⟨hs, ht⟩ := Finset.mem_filter.mp hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp (Finset.mem_product.mp hs).1
      exact Finset.mem_map.mpr ⟨(x,t), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx,Finset.mem_univ _⟩, ht⟩, rfl⟩
    · intro hp
      obtain ⟨⟨x,u⟩, hp, he⟩ := Finset.mem_map.mp hp
      change (f x,u) = (y,t) at he
      cases he
      obtain ⟨hs, ht⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_map.mpr ⟨x, (Finset.mem_product.mp hs).1,rfl⟩, Finset.mem_univ _⟩,ht⟩
  have hA := h A
  rw [heq, Finset.card_map, Finset.card_map] at hA
  exact hA

end

/-- Taking a suffix is injective on the fiber of a fixed prefix. -/
theorem drop_injOn_of_fixed_take {α : Type} (i : ℕ) (p : List α) :
    Set.InjOn (List.drop i) {x | x.take i = p} := by
  intro a ha b hb hdrop
  change a.take i = p at ha
  change b.take i = p at hb
  calc
    a = a.take i ++ a.drop i := (List.take_append_drop _ _).symm
    _ = b.take i ++ b.drop i := by rw [ha, hb, hdrop]
    _ = b := List.take_append_drop _ _

/-- Extract suffixes from a fixed prefix fiber without changing its cardinality. -/
theorem card_suffixes_of_prefix (D : Finset (List Bool)) (i : ℕ) (p : List Bool) :
    ((D.filter fun x => x.take i = p).image (List.drop i)).card =
      (D.filter fun x => x.take i = p).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  apply drop_injOn_of_fixed_take i p
  · exact (Finset.mem_filter.mp ha).2
  · exact (Finset.mem_filter.mp hb).2
  · exact he

/-- Prefixes and suffixes extracted from a set can be joined inside the original set. -/
theorem append_mem_of_prefix_suffix (D : Finset (List Bool)) (i : ℕ) (p s : List Bool)
    (hs : s ∈ (D.filter fun x => x.take i = p).image (List.drop i)) : p++s ∈ D := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hm,hpre⟩ := Finset.mem_filter.mp hx
  rwa [← hpre, List.take_append_drop]

/-- A fixed-length input universe broken into `i`-bit prefixes has all suffixes of length `n-i`. -/
theorem length_suffix_of_prefix (D : Finset (List Bool)) (i n : ℕ) (p s : List Bool)
    (hn : ∀ x ∈ D, x.length = n)
    (hs : s ∈ (D.filter fun x => x.take i = p).image (List.drop i)) : s.length = n-i := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
  rw [List.length_drop, hn x (Finset.mem_filter.mp hx).1]

end TimeSpaceMA

namespace TimeSpaceMA

/-- The cut-and-seed graph that first extracts from the suffix and then extracts from the
prefix using those bits as its second seed. -/
def prefixSplitNeighbor {n Seeds₁ Seeds₂ R : ℕ}
    (E₁ : Fin n → List Bool → Fin Seeds₁ → Fin Seeds₂)
    (E₂ : Fin n → List Bool → Fin Seeds₂ → Fin R) :
    List Bool → Fin n → Fin Seeds₁ → Fin R :=
  fun w i t => E₂ i (w.take i.val) (E₁ i (w.drop i.val) t)

/-- The high-entropy graph gets large support from the coordinate supplied by the
heavy-prefix lemma. The bound counts all cut-and-seed pairs as graph edges. -/
theorem prefixSplitGraph_coverage {n Seeds₁ Seeds₂ R : ℕ}
    (E₁ : Fin n → List Bool → Fin Seeds₁ → Fin Seeds₂)
    (E₂ : Fin n → List Bool → Fin Seeds₂ → Fin R)
    (D : Finset (List Bool)) (B H : ℕ) (δ ε : ℝ)
    (hn : ∀ w ∈ D, w.length = n) (hB : 2 ≤ B) (hBD : B ≤ D.card) (hH : 0 < H)
    (hsize : n * (2*(B-1)) * H ≤ D.card)
    (hseed₁ : 0 < Seeds₁) (hseed₂ : 0 < Seeds₂) (hR : 0 < R)
    (h₁ : ∀ (i : Fin n) (S : Finset (List Bool)),
      (∀ w ∈ S, w.length = n-i.val) → B ≤ S.card → FlatExtractorEvents (E₁ i) S δ)
    (h₂ : ∀ (i : Fin n) (S : Finset (List Bool)),
      (∀ w ∈ S, w.length = i.val) → H ≤ S.card → FlatExtractorEvents (E₂ i) S ε) :
    (1-δ-ε) * (R : ℝ) ≤
      (D.biUnion (fun w => Finset.univ.image (tuzCoordinateGraph (prefixSplitNeighbor E₁ E₂) w))).card := by
  obtain ⟨j, hj, A, hA, hp⟩ := exists_prefix_split D B H n hn hB hBD hsize
  let i : Fin n := ⟨j,hj⟩
  let fibers := suffixFiber D j
  have hjA : ∀ p ∈ A, ∀ b ∈ fibers p, p ++ b ∈ D :=
    fun p ha b hb => ((hp p ha).2.2 b hb).2
  have hinner : ∀ p ∈ A, (1-δ) * (Seeds₂ : ℝ) ≤
      ((fibers p).biUnion fun b => Finset.univ.image (E₁ i b)).card := by
    intro p ha
    have hf := (hp p ha).2.1
    have hlen : ∀ b ∈ fibers p, b.length = n-i.val := fun b hb => ((hp p ha).2.2 b hb).1
    have hpos : 0 < (fibers p).card := (show 0 < B by omega).trans_le hf
    have h := support_of_flatExtractorEvents (E₁ i) (fibers p) hpos
      (by simpa using hseed₁) (by simpa using hseed₂) δ (h₁ i (fibers p) hlen hf)
    simpa using h
  have houter := h₂ i A (fun p ha => (hp p ha).1) hA
  apply tuzCoordinateGraph_extractors_ge (prefixSplitNeighbor E₁ E₂) D i A fibers
    List.append hjA (fun _ b t => E₁ i b t) (E₂ i) ?_ (hH.trans_le hA) hseed₂ hR δ ε hinner houter
  intro p ha b _ t
  have hlen : p.length = i.val := (hp p ha).1
  change E₂ i ((p ++ b).take i.val) (E₁ i ((p ++ b).drop i.val) t) = _
  rw [← hlen, List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil, List.drop_left]


/-- The power-of-two min-entropy form of prefix splitting. One additional bit beyond
`log₂ n` accounts for the cut selection and the two light children per prefix. -/
theorem prefixSplitGraph_entropy_coverage {n Seeds₁ Seeds₂ R : ℕ}
    (E₁ : Fin n → List Bool → Fin Seeds₁ → Fin Seeds₂)
    (E₂ : Fin n → List Bool → Fin Seeds₂ → Fin R)
    (D : Finset (List Bool)) (k k₁ k₂ s : ℕ) (δ ε : ℝ)
    (hn : ∀ w ∈ D, w.length = n) (hk₁ : 1 ≤ k₁) (hD : 2^k ≤ D.card)
    (hs : 2*n ≤ 2^s) (hbudget : k₁+k₂+s ≤ k)
    (hseed₁ : 0 < Seeds₁) (hseed₂ : 0 < Seeds₂) (hR : 0 < R)
    (h₁ : ∀ (i : Fin n) (S : Finset (List Bool)),
      (∀ w ∈ S, w.length = n-i.val) → 2^k₁ ≤ S.card → FlatExtractorEvents (E₁ i) S δ)
    (h₂ : ∀ (i : Fin n) (S : Finset (List Bool)),
      (∀ w ∈ S, w.length = i.val) → 2^k₂ ≤ S.card → FlatExtractorEvents (E₂ i) S ε) :
    (1-δ-ε) * (R : ℝ) ≤
      (D.biUnion (fun w => Finset.univ.image (tuzCoordinateGraph (prefixSplitNeighbor E₁ E₂) w))).card := by
  apply prefixSplitGraph_coverage E₁ E₂ D (2^k₁) (2^k₂) δ ε hn _ _ _ _ hseed₁ hseed₂ hR h₁ h₂
  · simpa using (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk₁)
  · exact (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)).trans hD
  · exact Nat.pow_pos (by decide)
  · calc
      n * (2 * (2^k₁ - 1)) * 2^k₂ ≤ n * (2 * 2^k₁) * 2^k₂ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
      _ = (2*n)*2^k₁*2^k₂ := by ac_rfl
      _ ≤ 2^s*2^k₁*2^k₂ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs)
      _ = (2:ℕ)^(k₁+k₂+s) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hbudget
      _ ≤ D.card := hD

end TimeSpaceMA

namespace TimeSpaceMA

open Cslib.BitString

/-- View a natural vertex label as an exactly `n`-bit big-endian word. -/
def fixedWordEmbedding (n : ℕ) : Fin (2^n) ↪ List Bool :=
  ⟨fun x => binaryWord n x.val, fun a b h => Fin.ext (by
    have hv := congrArg binaryValue h
    simpa using hv)⟩

@[simp] theorem fixedWordEmbedding_length (n : ℕ) (x : Fin (2^n)) :
    (fixedWordEmbedding n x).length = n := length_binaryWord x.isLt

@[simp] theorem fixedWordEmbedding_value (n : ℕ) (x : Fin (2^n)) :
    binaryValue (fixedWordEmbedding n x) = x.val := binaryValue_binaryWord n x.val

/-- Encode any word and clip to the designated number of bits on out-of-range inputs. -/
def fitWord (n : ℕ) (x : List Bool) : Fin (2^n) :=
  ⟨binaryValue x % 2^n, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

/-- Clipping leaves every word of the supported width unchanged. -/
@[simp] theorem fitWord_value_of_length_le {n : ℕ} {x : List Bool} (h : x.length ≤ n) :
    (fitWord n x).val = binaryValue x :=
  Nat.mod_eq_of_lt ((binaryValue_lt_two_pow x).trans_le (Nat.pow_le_pow_right (by decide) h))

/-- Fixed-length words embed by numerical value into a larger padded binary universe. -/
def fixedBitsEmbedding (n w : ℕ) (h : w ≤ n) : {x : List Bool // x.length = w} ↪ Fin (2^n) :=
  ⟨fun x => fitWord n x.val, fun a b hab => Subtype.ext (by
    have av : a.val.length ≤ n := a.property.le.trans h
    have bv : b.val.length ≤ n := b.property.le.trans h
    have hv := congrArg Fin.val hab
    exact binaryValue_injective_of_length_eq (a.property.trans b.property.symm) (by
      simpa only [fitWord_value_of_length_le av, fitWord_value_of_length_le bv] using hv))⟩

@[simp] theorem fixedBitsEmbedding_apply (n w : ℕ) (h : w ≤ n)
    (x : {x : List Bool // x.length = w}) : fixedBitsEmbedding n w h x = fitWord n x.val := rfl

@[simp] theorem fitWord_fixedWordEmbedding (n : ℕ) (x : Fin (2^n)) :
    fitWord n (fixedWordEmbedding n x) = x := by
  apply Fin.ext
  rw [fitWord_value_of_length_le (fixedWordEmbedding_length n x).le, fixedWordEmbedding_value]

@[simp] theorem fixedWordEmbedding_fitWord (n : ℕ) (x : List Bool) (hx : x.length = n) :
    fixedWordEmbedding n (fitWord n x) = x := by
  apply binaryValue_injective_of_length_eq
  · rw [fixedWordEmbedding_length, hx]
  · rw [fixedWordEmbedding_value, fitWord_value_of_length_le hx.le]

/-- Neighbor sets are preserved exactly when the left vertex labels are embedded. -/
theorem biUnion_image_map_left {α β γ ι : Type} [Fintype ι] [DecidableEq γ]
    (f : α ↪ β) (E : β → ι → γ) (D : Finset α) :
    (D.map f).biUnion (fun x => Finset.univ.image (E x)) =
      D.biUnion (fun x => Finset.univ.image (E (f x))) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_biUnion.mpr ⟨a,ha,hy⟩
  · intro hy
    obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨f x,Finset.mem_map.mpr ⟨x,hx,rfl⟩,hy⟩

/-- Transport word-based neighborhood coverage back to labels in `Fin (2^n)`. -/
theorem tuzCoordinateGraph_fixedWord_support {Rows Seeds R n : ℕ}
    (E : List Bool → Fin Rows → Fin Seeds → Fin R) (D : Finset (Fin (2^n))) :
    ((D.map (fixedWordEmbedding n)).biUnion (fun x => Finset.univ.image (tuzCoordinateGraph E x))).card =
      (D.biUnion (fun x => Finset.univ.image
        (tuzCoordinateGraph (fun a => E (fixedWordEmbedding n a)) x))).card := by
  rw [biUnion_image_map_left]
  rfl

/-- Concatenation shifts the prefix by the number of bits of the suffix. -/
theorem binaryValue_append (p s : List Bool) :
    binaryValue (p ++ s) = binaryValue p * 2^s.length + binaryValue s := by
  induction s using List.reverseRecOn with
  | nil => simp [binaryValue]
  | append_singleton s b ih =>
    rw [← List.append_assoc, binaryValue_snoc, ih, binaryValue_snoc]
    simp only [List.length_append, List.length_singleton, Nat.pow_succ]
    ring

/-- The binary value of the prefix is the quotient, and that of the suffix the remainder. -/
theorem binaryValue_take_drop (x : List Bool) (i : ℕ) :
    binaryValue (x.take i) = binaryValue x / 2^(x.length-i) ∧
      binaryValue (x.drop i) = binaryValue x % 2^(x.length-i) := by
  have h := binaryValue_append (x.take i) (x.drop i)
  rw [List.take_append_drop, List.length_drop] at h
  have hmod : binaryValue (x.drop i) < 2^(x.length-i) := by
    simpa using binaryValue_lt_two_pow (x.drop i)
  have hpos : 0 < (2:ℕ)^(x.length-i) := Nat.pow_pos (by decide)
  constructor
  · conv_rhs => rw [h]
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hmod, Nat.zero_add]
  · conv_rhs => rw [h]
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmod]

end TimeSpaceMA

namespace TimeSpaceMA

section
variable {Seed Out : Type} [Fintype Seed] [Fintype Out] [DecidableEq Out]

/-- A flat-source extractor guarantee on numeric labels restricts to words of any one
length at most the label width. -/
theorem FlatExtractorEvents.of_fixed_word_length
    {n w threshold : ℕ} (hw : w ≤ n) (E : Fin (2^n) → Seed → Out)
    (ε : ℝ) (hE : ∀ T : Finset (Fin (2^n)), threshold ≤ T.card → FlatExtractorEvents E T ε)
    (S : Finset (List Bool)) (hS : ∀ x ∈ S, x.length = w) (hcard : threshold ≤ S.card) :
    FlatExtractorEvents (fun x => E (fitWord n x)) S ε := by
  classical
  let e : {x : List Bool // x ∈ S} ↪ Fin (2^n) :=
    ⟨fun x => fixedBitsEmbedding n w hw ⟨x.val, hS x.val x.property⟩,
      fun x y he => Subtype.ext (congrArg (fun z : {x : List Bool // x.length = w} => z.val)
        ((fixedBitsEmbedding n w hw).injective he))⟩
  have hcard' : threshold ≤ (S.attach.map e).card := by simpa using hcard
  have hsub := FlatExtractorEvents.comapInput E S.attach e ε (hE _ hcard')
  intro A
  let f : ({x : List Bool // x ∈ S} × Seed) ↪ (List Bool × Seed) :=
    ⟨fun p => (p.1.val,p.2), fun p q he => Prod.ext
      (Subtype.ext (congrArg (fun z : List Bool × Seed => z.1) he))
      (congrArg (fun z : List Bool × Seed => z.2) he)⟩
  have heq : ((S.attach ×ˢ Finset.univ).filter
      (fun p : {x : List Bool // x ∈ S} × Seed => E (e p.1) p.2 ∈ A)).map f =
        (S ×ˢ Finset.univ).filter (fun p : List Bool × Seed => E (fitWord n p.1) p.2 ∈ A) := by
    ext p
    obtain ⟨x,t⟩ := p
    constructor
    · intro hp
      obtain ⟨⟨y,u⟩,hy,he⟩ := Finset.mem_map.mp hp
      change (y.val,u) = (x,t) at he
      cases he
      obtain ⟨_,hyE⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨y.property,Finset.mem_univ _⟩,hyE⟩
    · intro hp
      obtain ⟨hprod,hxE⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_map.mpr ⟨(⟨x,(Finset.mem_product.mp hprod).1⟩,t),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_attach _ _,Finset.mem_univ _⟩,hxE⟩,rfl⟩
  have h := hsub A
  rw [← heq, Finset.card_map]
  simpa only [Finset.card_attach] using h

end

end TimeSpaceMA

namespace TimeSpaceMA

section
variable {Input Seed Extra Out : Type} [Fintype Seed] [Fintype Extra] [Fintype Out]
variable [DecidableEq Extra] [DecidableEq Out]

end

section Relabel
variable {Input Seed Seed' Out Out' : Type} [Fintype Seed] [Fintype Seed'] [Fintype Out] [Fintype Out']
variable [DecidableEq Out] [DecidableEq Out']

/-- Relabel seeds and outputs by arbitrary bijections without changing the extractor error. -/
theorem FlatExtractorEvents.equivSeedOutput
    (E : Input → Seed → Out) (S : Finset Input) (ε : ℝ)
    (eS : Seed' ≃ Seed) (eO : Out ≃ Out') (hE : FlatExtractorEvents E S ε) :
    FlatExtractorEvents (fun x t => eO (E x (eS t))) S ε := by
  classical
  intro A
  let B := A.map eO.symm.toEmbedding
  let f : (Input × Seed') ↪ (Input × Seed) := (Equiv.prodCongr (Equiv.refl Input) eS).toEmbedding
  let X := (S ×ˢ Finset.univ).filter (fun p : Input × Seed' => eO (E p.1 (eS p.2)) ∈ A)
  let Y := (S ×ˢ Finset.univ).filter (fun p : Input × Seed => E p.1 p.2 ∈ B)
  have hB (y : Out) : y ∈ B ↔ eO y ∈ A := by
    change y ∈ A.map eO.symm.toEmbedding ↔ eO y ∈ A
    constructor
    · intro hy
      obtain ⟨u,hu,he⟩ := Finset.mem_map.mp hy
      change eO.symm u = y at he
      simpa [← he] using hu
    · intro h
      exact Finset.mem_map.mpr ⟨_,h,eO.symm_apply_apply y⟩
  have hXY : X.map f = Y := by
    ext p
    obtain ⟨x,t⟩ := p
    constructor
    · intro hp
      obtain ⟨⟨u,s⟩,hu,he⟩ := Finset.mem_map.mp hp
      change (u,eS s) = (x,t) at he
      cases he
      obtain ⟨hm,hy⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm).1,
        Finset.mem_univ _⟩,(hB _).2 hy⟩
    · intro hp
      obtain ⟨hm,hy⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_map.mpr ⟨(x,eS.symm t),Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm).1,Finset.mem_univ _⟩,?_⟩,?_⟩
      · simpa using (hB _).1 hy
      · change (x,eS (eS.symm t)) = (x,t)
        rw [eS.apply_symm_apply]
  have hcard : X.card = Y.card := by rw [← hXY, Finset.card_map]
  change (X.card : ℝ) / ((S.card : ℝ) * (Fintype.card Seed' : ℝ)) -
    (A.card : ℝ) / (Fintype.card Out' : ℝ) ≤ ε
  rw [hcard, Fintype.card_congr eS, ← Fintype.card_congr eO]
  have h := hE B
  change (Y.card : ℝ) / ((S.card : ℝ) * (Fintype.card Seed : ℝ)) -
    (B.card : ℝ) / (Fintype.card Out : ℝ) ≤ ε at h
  simpa [B] using h

end Relabel

/-- Changing a seed's finite carrier by an index equality preserves the extractor property. -/
theorem FlatExtractorEvents.comapSeedCast {Input Out : Type} {s t : ℕ}
    [Fintype Out] [DecidableEq Out] {E : Input → Fin t → Out}
    {S : Finset Input} {ε : ℝ} (h : s = t) (hE : FlatExtractorEvents E S ε) :
    FlatExtractorEvents (fun x i => E x (Fin.cast h i)) S ε := by
  exact FlatExtractorEvents.equivSeedOutput E S ε (finCongr h) (Equiv.refl Out) hE

/-- Casting all right vertex indices along equality preserves the cardinal of each neighborhood. -/
theorem finCast_neighbor_card {Input Seed : Type} {r r' : ℕ} [Fintype Seed]
    (h : r = r') (E : Input → Seed → Fin r) (S : Finset Input) :
    (S.biUnion (fun x => Finset.univ.image (fun i => Fin.cast h (E x i)))).card =
      (S.biUnion (fun x => Finset.univ.image (E x))).card := by
  subst r'
  rfl

end TimeSpaceMA

namespace TimeSpaceMA

/-- The heavy-prefix argument loses one bit in addition to the length of a binary
encoding of the input width. The upper bound controls the disperser's entropy loss. -/
theorem tuz_splitLoss_bounds {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ (2 : ℕ)^(n.size + 1) ∧ (2 : ℕ)^(n.size + 1) ≤ 4 * n := by
  have hw : 0 < n.size := Nat.size_pos.mpr hn
  have hlo : (2 : ℕ)^(n.size-1) ≤ n := Nat.lt_size.mp (by omega)
  have hhi := Nat.lt_size_self n
  constructor
  · rw [pow_succ]
    omega
  · rw [show n.size+1 = (n.size-1)+2 by omega, pow_add]
    omega

/-- A polynomial clock absorbs the number of seeds at every positive input width. -/
theorem tuz_seed_degree_bound (B : ℕ) :
    ∃ e : ℕ, ∀ n : ℕ, 1 ≤ n → n * (2 : ℕ)^(B * n.size) ≤ n^e + e := by
  refine ⟨max (2*B+1) ((2 : ℕ)^B), ?_⟩
  intro n hn
  have hPow : (2 : ℕ)^n.size ≤ 2*n := by
    have h := (tuz_splitLoss_bounds hn).2
    rw [pow_succ] at h
    omega
  have hD : n * 2^(B*n.size) ≤ 2^B * n^(B+1) := by
    calc
      _ = n * (2^n.size)^B := by rw [← pow_mul, Nat.mul_comm B]
      _ ≤ n * (2*n)^B := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hPow _)
      _ = _ := by rw [mul_pow, pow_succ]; ac_rfl
  by_cases h1 : n = 1
  · subst n
    exact hD.trans (by simp only [one_pow, Nat.mul_one]; omega)
  · have h2 : 2 ≤ n := by omega
    have hPB := Nat.pow_le_pow_left h2 B
    have hE : 2*B+1 ≤ max (2*B+1) ((2 : ℕ)^B) := Nat.le_max_left .. 
    calc
      _ ≤ 2^B * n^(B+1) := hD
      _ ≤ n^B * n^(B+1) := Nat.mul_le_mul_right _ hPB
      _ = n^(2*B+1) := by rw [← pow_add]; congr 1; omega
      _ ≤ n^(max (2*B+1) ((2 : ℕ)^B)) := Nat.pow_le_pow_right (by omega) hE
      _ ≤ _ := Nat.le_add_right ..

private theorem tuz_loss_inequality
    {s m k t n Δ d : ℕ} (hn : 1 ≤ n)
    (hd : d ≤ n * 2^t)
    (hsize : m + s + 2*Δ = k+t)
    (hseed : (2 : ℕ)^s ≤ 4*n) :
    ((2 : ℝ)^k * (d : ℝ)) /
      ((4 * (2 : ℝ)^(2*Δ)) * (n : ℝ)^3) ≤ (2 : ℝ)^m := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp (j : ℕ) : 0 < (2 : ℝ)^j := by positivity
  have hdR : (d : ℝ) ≤ n * (2 : ℝ)^t := by exact_mod_cast hd
  have hseedR : (2 : ℝ)^s ≤ 4 * n := by exact_mod_cast hseed
  have hpow : (2 : ℝ)^k * (2 : ℝ)^t =
      (2 : ℝ)^m * (2 : ℝ)^s * (2 : ℝ)^(2*Δ) := by
    rw [← pow_add, ← pow_add, ← pow_add, hsize]
  have hn3 : (n : ℝ)^2 ≤ n^3 := by
    rw [show (3 : ℕ) = 2+1 by decide, pow_add, pow_one]
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hnR (show 0 ≤ (n : ℝ)^2 by positivity))
  apply (div_le_iff₀ (by positivity)).2
  calc
    _ ≤ (2:ℝ)^k * ((n:ℝ)*2^t) := mul_le_mul_of_nonneg_left hdR (hp k).le
    _ = ((2:ℝ)^k * 2^t) * n := by ring
    _ = ((2:ℝ)^m * 2^s * 2^(2*Δ)) * n := by rw [hpow]
    _ = 2^s * ((2:ℝ)^m * 2^(2*Δ) * n) := by ring
    _ ≤ (4*n) * ((2:ℝ)^m * 2^(2*Δ) * n) := mul_le_mul_of_nonneg_right hseedR (by positivity)
    _ = n^2 * (4 * (2:ℝ)^m * 2^(2*Δ)) := by ring
    _ ≤ n^3 * (4 * (2:ℝ)^m * 2^(2*Δ)) := mul_le_mul_of_nonneg_right hn3 (by positivity)
    _ = _ := by ring

/-- The high branch pays for all n cut positions and still meets the cubic entropy loss. -/
theorem tuz_high_loss_bound {n k t Δ : ℕ} (hn : 1 ≤ n)
    (ht : Δ ≤ t) (hk : n.size+1+Δ ≤ k) :
    let m := k+t-(n.size+1)-2*Δ
    let d := n*2^t
    (1 / (4*(2:ℝ)^(2*Δ))) * (2:ℝ)^k * (d:ℝ) / (n:ℝ)^3 ≤ (2:ℝ)^m := by
  dsimp only
  have h := tuz_loss_inequality (n := n) (k := k) (t := t) (s := n.size+1)
    (m := k+t-(n.size+1)-2*Δ) (Δ := Δ) hn (le_refl (n*2^t))
    (by omega) (tuz_splitLoss_bounds hn).2
  convert h using 1
  ring

/-- The lower-entropy branch has constant entropy loss and meets the same uniform constant. -/
theorem tuz_low_loss_bound {n k t Δ : ℕ} (hn : 1 ≤ n) (ht : Δ ≤ t) :
    let m := k+t-Δ
    let d := 2^t
    (1 / (4*(2:ℝ)^(2*Δ))) * (2:ℝ)^k * (d:ℝ) / (n:ℝ)^3 ≤ (2:ℝ)^m := by
  dsimp only
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (1 : ℝ) ≤ (n:ℝ)^3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hnR 3
  have hTwo : (2 : ℝ)^Δ ≤ 4*(2:ℝ)^(2*Δ) := by
    have hpow : (2 : ℝ)^Δ ≤ 2^(2*Δ) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpos : 0 ≤ (2 : ℝ)^(2*Δ) := by positivity
    linarith
  have hden : (2 : ℝ)^Δ ≤ (4*(2:ℝ)^(2*Δ))*(n:ℝ)^3 := by
    apply hTwo.trans
    simpa using mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 4*(2:ℝ)^(2*Δ) by positivity)
  have heq : (2:ℝ)^k * 2^t = 2^(k+t-Δ) * 2^Δ := by
    rw [← pow_add, ← pow_add, Nat.sub_add_cancel (show Δ ≤ k+t by omega)]
  have hd₁ : 0 < (4*(2:ℝ)^(2*Δ)) := by positivity
  have hd₂ : 0 < (n:ℝ)^3 := by positivity
  rw [show (1/(4*(2:ℝ)^(2*Δ)))*2^k*2^t/(n:ℝ)^3 =
       (2^k*2^t)/((4*2^(2*Δ))*(n:ℝ)^3) by ring]
  apply (div_le_iff₀ (mul_pos hd₁ hd₂)).2
  rw [heq]
  exact mul_le_mul_of_nonneg_left hden (by positivity)


/-- The fourth power of a binary-encoding width is bounded by a fixed linear function
of the underlying positive integer. -/
private theorem tuz_size_four_le {n : ℕ} (hn : 0 < n) : n.size^4 ≤ 1296 * n := by
  have hh (t : ℕ) (ht : t ≥ 1) : t^4 ≤ 1296 * (2 : ℕ)^(t-1) := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht6 : t < 6
      · have hb := Nat.pow_le_pow_left (show t+1 ≤ 6 by omega) 4
        have hp : 1 ≤ (2 : ℕ)^(t+1-1) := Nat.pow_pos (by decide)
        calc
          _ ≤ 6^4 := hb
          _ ≤ _ := by norm_num at *; omega
      · have h₁ : t^2 ≥ 36 := Nat.pow_le_pow_left (show 6 ≤ t by omega) 2
        have h₂ : 6*t^2 ≤ t^3 := by
          rw [show t^3 = t^2 * t by ring, Nat.mul_comm 6]
          exact Nat.mul_le_mul_left _ (by omega)
        have h₃ : 6*t^3 ≤ t^4 := by
          rw [show t^4 = t^3 * t by ring, Nat.mul_comm 6]
          exact Nat.mul_le_mul_left _ (by omega)
        have h4 : (t+1)^4 ≤ 2*t^4 := by
          have hlow : 6*t^2 + 4*t + 1 ≤ 2*t^3 := by nlinarith
          nlinarith
        calc
          _ ≤ 2*t^4 := h4
          _ ≤ 2*(1296*2^(t-1)) := Nat.mul_le_mul_left _ (ih (by omega))
          _ = _ := by
            rw [show t+1-1 = (t-1)+1 by omega, pow_succ]
            ac_rfl
  have hsize := Nat.size_pos.mpr hn
  have hpow : (2 : ℕ)^(n.size-1) ≤ n := Nat.lt_size.mp (by omega)
  exact (hh n.size hsize).trans (Nat.mul_le_mul_left _ hpow)

private theorem tuz_size_mul_le (a b : ℕ) : (a*b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)

private theorem tuz_size_pow_four (a : ℕ) : (a^4).size ≤ 4*a.size := by
  calc
    _ = (a*a*(a*a)).size := by congr 1; ring
    _ ≤ (a*a).size + (a*a).size := tuz_size_mul_le _ _
    _ ≤ _ := by
      have h := tuz_size_mul_le a a
      omega

private theorem tuz_size_le_self (a : ℕ) : a.size ≤ a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    apply Nat.size_le.mpr
    have h := Nat.lt_size_self a
    have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ih
    have hpos : 0 < (2 : ℕ)^a := Nat.pow_pos (by decide)
    rw [pow_succ]
    omega

/-- One linear seed budget in `n.size` pays for all extractor calls whose entropy
parameter is at most the low/high branch threshold. The same budget absorbs the
constant entropy loss. -/
theorem tuz_short_seed_budget (A Δ : ℕ) :
    ∃ B : ℕ, Δ ≤ B ∧ ∀ n k : ℕ, 1 ≤ n →
      k ≤ A*(n.size+n.size^4)+Δ+(n.size+1)+Δ →
      A*(n.size+k.size^4) ≤ B*n.size := by
  let C := 2*A + 2*Δ + 3
  let B := Δ + A*(1 + 1296*((C.size+4)^4))
  refine ⟨B, Nat.le_add_right .., ?_⟩
  intro n k hn hk
  let q := n.size
  have hq : 0 < q := Nat.size_pos.mpr hn
  have hq4 : q ≤ q^4 := by
    calc
      q = q^1 := by simp
      _ ≤ q^4 := Nat.pow_le_pow_right hq (by decide)
  have hq41 : 1 ≤ q^4 := hq.trans_le hq4
  have hkC : k ≤ C*q^4 := by
    change k ≤ A*(q+q^4)+Δ+(q+1)+Δ at hk
    have hA := Nat.mul_le_mul_left A (show q+q^4 ≤ 2*q^4 by omega)
    have hD := Nat.mul_le_mul_left (2*Δ+3) hq41
    dsimp [C]
    nlinarith
  have hkSize : k.size ≤ (C.size+4)*q.size := by
    calc
      _ ≤ (C*q^4).size := Nat.size_le_size hkC
      _ ≤ C.size + (q^4).size := tuz_size_mul_le _ _
      _ ≤ C.size + 4*q.size := Nat.add_le_add_left (tuz_size_pow_four q) _
      _ ≤ _ := by
        have hh : 1 ≤ q.size := Nat.size_pos.mpr hq
        rw [Nat.add_mul]
        simpa using Nat.add_le_add_right (Nat.mul_le_mul_left C.size hh) (4*q.size)
  have hkk : k.size^4 ≤ (C.size+4)^4*(1296*q) := by
    calc
      _ ≤ ((C.size+4)*q.size)^4 := Nat.pow_le_pow_left hkSize _
      _ = (C.size+4)^4*q.size^4 := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (tuz_size_four_le hq)
  change A*(q+k.size^4) ≤ B*q
  calc
    _ ≤ A*(q+(C.size+4)^4*(1296*q)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left hkk _)
    _ ≤ _ := by
      dsimp only [B]
      have hΔ : 0 ≤ Δ*q := Nat.zero_le _
      nlinarith


/-- The padded seed of the second extractor is exactly the first extractor's output
width. In the high branch all entropy and output parameters are admissible. -/
theorem tuz_high_seed_compatible (A Δ n k t₁ : ℕ)
    (hkn : k ≤ n)
    (hhigh : A*(n.size+n.size^4)+Δ+(n.size+1)+Δ ≤ k) :
    let t₂ := A*(n.size+n.size^4)
    let k₁ := t₂+Δ
    let k₂ := k-k₁-(n.size+1)
    k₁ ≤ n ∧ k₂ ≤ n ∧ Δ ≤ k₁+t₁ ∧ Δ ≤ k₂+(t₂+t₁) ∧
      A*(n.size+k₂.size^4) ≤ t₂+t₁ ∧
      k₁+t₁-Δ = t₂+t₁ ∧
      k₂+(t₂+t₁)-Δ = k+t₁-(n.size+1)-2*Δ ∧
      k₁+k₂+(n.size+1) = k := by
  dsimp only
  have hlow : k - (A*(n.size+n.size^4)+Δ) - (n.size+1) ≤ n := by omega
  have hsize := Nat.pow_le_pow_left (Nat.size_le_size hlow) 4
  have hbudget := Nat.mul_le_mul_left A (Nat.add_le_add_left hsize n.size)
  refine ⟨by omega, hlow, by omega, by omega, ?_, by omega, by omega, by omega⟩
  omega

end TimeSpaceMA

namespace TimeSpaceMA

/-- Enumerate all cut and seed pairs in the high branch, and just the seeds in the low branch.
The entropy threshold is capped at the input width before the binary output powers are formed. -/
def tuzNeighborLabels (extract : ExtractorInput → ℕ) (A Δ B : ℕ)
    (n k v : ℕ) : List ℕ :=
  let k := min k n
  let t₁ := B*n.size
  let t₂ := A*(n.size+n.size^4)
  let k₁ := t₂+Δ
  let s := n.size+1
  let k₂ := k-k₁-s
  let d := (2 : ℕ)^t₁
  if k₁+s+Δ ≤ k then
    (List.range (n*d)).map fun i =>
      let block := (2 : ℕ)^(n-i/d)
      let x₁ := v/block
      let x₂ := v%block
      let z := extract (n,k₁,t₁,x₂,i%d) % (2 : ℕ)^(t₂+t₁)
      extract (n,k₂,t₂+t₁,x₁,z) % (2 : ℕ)^(k+t₁-s-2*Δ)
  else
    (List.range d).map fun i => extract (n,k,t₁,v,i) % (2 : ℕ)^(k+t₁-Δ)

end TimeSpaceMA

namespace TimeSpaceMA

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

private abbrev ListingQuery := ℕ × ℕ × ℕ
private abbrev listingEncoding : ListingQuery ↪ List Bool := encPair encUnary (encPair encNat encNat)

private theorem tidy_size_unary {α : Type} {input : α ↪ List Bool} {value : α → ℕ}
    (hv : ComputableTidilyInPolyTime value input encUnary) :
    ComputableTidilyInPolyTime (fun x => (value x).size) input encUnary :=
  ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hv)

private theorem tidy_clamp_to_unary {α : Type} {input : α ↪ List Bool} {bound value : α → ℕ}
    (hb : ComputableTidilyInPolyTime bound input encUnary)
    (hv : ComputableTidilyInPolyTime value input encNat) :
    ComputableTidilyInPolyTime (fun x => min (bound x) (value x)) input encUnary :=
  (ComputableInPolyTime.binary_min_unary' hb.computableInPolyTime hv.computableInPolyTime).tidy

private theorem tidy_seedWidth {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n input encUnary) (B : ℕ) :
    ComputableTidilyInPolyTime (fun x => B * (n x).size) input encUnary :=
  unary_mul.comp ((const B).prod (tidy_size_unary hn))

private theorem tidy_seedCount {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n input encUnary) (B : ℕ) :
    ComputableTidilyInPolyTime (fun x => 2^(B * (n x).size)) input encUnary := by
  refine binary_to_unary_bounded (binary_two_pow.comp (tidy_seedWidth hn B))
    ((unary_pow B).comp (unary_mul.comp ((const 2).prod (unary_add.comp (hn.prod (const 1))))))
    ?_
  intro x
  have hbase : (2 : ℕ)^(n x).size ≤ 2*(n x + 1) := by
    cases he : (n x).size with
    | zero => simp; omega
    | succ m =>
      have hpow : (2:ℕ)^m ≤ n x := Nat.lt_size.mp (by omega)
      rw [pow_succ]
      omega
  calc
    _ = ((2:ℕ)^(n x).size)^B := by rw [← pow_mul, Nat.mul_comm B]
    _ ≤ _ := Nat.pow_le_pow_left hbase _


private theorem tidy_longSeedWidth {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n input encUnary) (A : ℕ) :
    ComputableTidilyInPolyTime (fun x => A * ((n x).size + (n x).size^4)) input encUnary :=
  let hs := tidy_size_unary hn
  unary_mul.comp ((const A).prod (unary_add.comp (hs.prod ((unary_pow 4).comp hs))))

/-- The schedule and the label computation preserve polynomial time when the supplied
extractor does. Widths and enumeration counts are constructed in unary only after bounding
them polynomially in the input width. -/
theorem tuzNeighborLabels_polytime (extract : ExtractorInput → ℕ) (A Δ B : ℕ)
    (hExtract : ComputableInPolyTime extract encExtractorInput encNat) :
    ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ => tuzNeighborLabels extract A Δ B x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair encNat encNat)) (encList encNat) := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let input := listingEncoding
  let n := fun x : ListingQuery => x.1
  let kraw := fun x : ListingQuery => x.2.1
  let v := fun x : ListingQuery => x.2.2
  have hn : ComputableTidilyInPolyTime n input encUnary := fst _ _
  have hkr : ComputableTidilyInPolyTime kraw input encNat := (snd _ _).fst'
  have hv : ComputableTidilyInPolyTime v input encNat := (snd _ _).snd'
  let k := fun x => min (kraw x) (n x)
  have hku : ComputableTidilyInPolyTime k input encUnary := by
    simpa only [k, min_comm] using tidy_clamp_to_unary hn hkr
  have hk : ComputableTidilyInPolyTime k input encNat := unary_to_binary.comp hku
  let t₁ := fun x => B*(n x).size
  have ht₁ : ComputableTidilyInPolyTime t₁ input encUnary := tidy_seedWidth hn B
  let t₂ := fun x => A*((n x).size+(n x).size^4)
  have ht₂ : ComputableTidilyInPolyTime t₂ input encUnary := tidy_longSeedWidth hn A
  let combined := fun x => t₂ x + t₁ x
  have hcombined : ComputableTidilyInPolyTime combined input encUnary := unary_add.comp (ht₂.prod ht₁)
  let k₁ := fun x => t₂ x + Δ
  have hk₁u : ComputableTidilyInPolyTime k₁ input encUnary := unary_add.comp (ht₂.prod (const Δ))
  have hk₁ : ComputableTidilyInPolyTime k₁ input encNat := unary_to_binary.comp hk₁u
  let s := fun x => (n x).size + 1
  have hs : ComputableTidilyInPolyTime s input encUnary :=
    unary_add.comp ((tidy_size_unary hn).prod (const 1))
  let k₂ := fun x => k x-k₁ x-s x
  have hk₂u : ComputableTidilyInPolyTime k₂ input encUnary :=
    unary_sub.comp ((unary_sub.comp (hku.prod hk₁u)).prod hs)
  have hk₂ : ComputableTidilyInPolyTime k₂ input encNat := unary_to_binary.comp hk₂u
  let d := fun x => (2:ℕ)^(t₁ x)
  have hd : ComputableTidilyInPolyTime d input encNat := binary_two_pow.comp ht₁
  have hdu : ComputableTidilyInPolyTime d input encUnary := tidy_seedCount hn B
  have hndl : ComputableTidilyInPolyTime (fun x => List.range (n x*d x)) input (encList encUnary) :=
    range.comp (unary_mul.comp (hn.prod hdu))
  have hdl : ComputableTidilyInPolyTime (fun x => List.range (d x)) input (encList encUnary) :=
    range.comp hdu
  let extended := encPair input encUnary
  have hquery : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => x.1) extended input := fst _ _
  have hi : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => x.2) extended encNat :=
    unary_to_binary.comp (snd _ _)
  let block := fun (x : ListingQuery) (i : ℕ) => (2:ℕ)^(n x-i/d x)
  have hblock : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => block x.1 x.2) extended encNat := by
    have hcut := binary_div' hi (hd.comp hquery)
    have hwidth := hn.comp hquery
    have hbounded := tidy_clamp_to_unary hwidth hcut
    have h := binary_two_pow.comp (unary_sub.comp (hwidth.prod hbounded))
    apply h.of_enc_eq
    intro x
    dsimp [block, Function.comp_def]
    by_cases hle : n x.1 ≤ x.2 / d x.1
    · rw [min_eq_left hle, Nat.sub_self, Nat.sub_eq_zero_of_le hle]
    · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hle))]
  let x₁ := fun x i => v x / block x i
  let x₂ := fun x i => v x % block x i
  have hx₁ : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => x₁ x.1 x.2) extended encNat :=
    binary_div' (hv.comp hquery) hblock
  have hx₂ : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => x₂ x.1 x.2) extended encNat :=
    binary_mod' (hv.comp hquery) hblock
  let ri := fun x i => i % d x
  have hri : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => ri x.1 x.2) extended encNat :=
    binary_mod' hi (hd.comp hquery)
  let z := fun x i => extract (n x,k₁ x,t₁ x,x₂ x i,ri x i) % (2:ℕ)^(combined x)
  have hz : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => z x.1 x.2) extended encNat := by
    have hraw := hExtract.tidy.comp ((hn.comp hquery).prod
      ((hk₁.comp hquery).prod ((ht₁.comp hquery).prod (hx₂.prod hri))))
    exact binary_mod' hraw (binary_two_pow.comp (hcombined.comp hquery))
  let highMod := fun x => (2:ℕ)^(k x+t₁ x-s x-2*Δ)
  have highModPoly : ComputableTidilyInPolyTime highMod input encNat :=
    binary_two_pow.comp (unary_sub.comp
      ((unary_sub.comp ((unary_add.comp (hku.prod ht₁)).prod hs)).prod (const (2*Δ))))
  let high := fun x i => extract (n x,k₂ x,combined x,x₁ x i,z x i) % highMod x
  have highPoly : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => high x.1 x.2) extended encNat := by
    have hraw := hExtract.tidy.comp ((hn.comp hquery).prod
      ((hk₂.comp hquery).prod ((hcombined.comp hquery).prod (hx₁.prod hz))))
    exact binary_mod' hraw (highModPoly.comp hquery)
  let lowMod := fun x => (2:ℕ)^(k x+t₁ x-Δ)
  have lowModPoly : ComputableTidilyInPolyTime lowMod input encNat :=
    binary_two_pow.comp (unary_sub.comp ((unary_add.comp (hku.prod ht₁)).prod (const Δ)))
  let low := fun x i => extract (n x,k x,t₁ x,v x,i) % lowMod x
  have lowPoly : ComputableTidilyInPolyTime (fun x : ListingQuery × ℕ => low x.1 x.2) extended encNat := by
    have hraw := hExtract.tidy.comp ((hn.comp hquery).prod
      ((hk.comp hquery).prod ((ht₁.comp hquery).prod ((hv.comp hquery).prod hi))))
    exact binary_mod' hraw (lowModPoly.comp hquery)
  let guard := fun x => k₁ x+s x+Δ ≤ k x
  have hg : ComputableTidilyInPolyTime (fun x => decide (guard x)) input encBool :=
    unary_le' (unary_add.comp ((unary_add.comp (hk₁u.prod hs)).prod (const Δ))) hku
  apply (hg.ite_decide (mapWithInput hndl highPoly) (mapWithInput hdl lowPoly)).of_enc_eq
  intro x
  rfl

end TimeSpaceMA

namespace TimeSpaceMA

open Turing.MultiTapeTM Cslib.BitString

private theorem tuz_high_graph
    (extract : ExtractorInput → ℕ) (Δ n k k₁ k₂ t₁ t₂ : ℕ)
    (he₁ : k₁+t₁-Δ = t₂+t₁)
    (he₂ : k₂+(t₂+t₁)-Δ = k+t₁-(n.size+1)-2*Δ)
    (hk₁ : 1 ≤ k₁) (hk : k₁+k₂+(n.size+1) ≤ k)
    (hn : 1 ≤ n) (δ : ℝ)
    (h₁ : ∀ S : Finset (Fin (2^n)), 2^k₁ ≤ S.card →
      FlatExtractorEvents (extractorEdge extract Δ n k₁ t₁) S δ)
    (h₂ : ∀ S : Finset (Fin (2^n)), 2^k₂ ≤ S.card →
      FlatExtractorEvents (extractorEdge extract Δ n k₂ (t₂+t₁)) S δ) :
    ∃ Γ : Fin (2^n) → Fin (n*2^t₁) → Fin (2^(k+t₁-(n.size+1)-2*Δ)),
      (∀ D : Finset (Fin (2^n)), 2^k ≤ D.card →
        (1-δ-δ) * (2:ℝ)^(k+t₁-(n.size+1)-2*Δ) ≤
          (D.biUnion fun v => Finset.univ.image (Γ v)).card) ∧
      ∀ v i, (Γ v i).val =
        extract (n,k₂,t₂+t₁, v.val / 2^(n-i.val/2^t₁),
          extract (n,k₁,t₁,v.val % 2^(n-i.val/2^t₁),i.val % 2^t₁) % 2^(t₂+t₁)) %
          2^(k+t₁-(n.size+1)-2*Δ) := by
  classical
  let E₁ : Fin n → List Bool → Fin (2^t₁) → Fin (2^(k₁+t₁-Δ)) :=
    fun _ x => extractorEdge extract Δ n k₁ t₁ (fitWord n x)
  let E₂ : Fin n → List Bool → Fin (2^(k₁+t₁-Δ)) → Fin (2^(k₂+(t₂+t₁)-Δ)) :=
    fun _ x y => extractorEdge extract Δ n k₂ (t₂+t₁) (fitWord n x)
      (Fin.cast (congrArg (fun z : ℕ => 2^z) he₁) y)
  let E := prefixSplitNeighbor E₁ E₂
  let Γ := fun (v : Fin (2^n)) (i : Fin (n*2^t₁)) =>
    Fin.cast (congrArg (fun z : ℕ => 2^z) he₂)
      (tuzCoordinateGraph E (fixedWordEmbedding n v) i)
  refine ⟨Γ, ?_, ?_⟩
  · intro D hD
    let words := D.map (fixedWordEmbedding n)
    have hwords : 2^k ≤ words.card := by simpa [words] using hD
    have hfsize : ∀ w ∈ words, w.length = n := by
      intro w hw
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hw
      exact fixedWordEmbedding_length _ _
    have hinner (i : Fin n) (S : Finset (List Bool))
        (hlen : ∀ w ∈ S, w.length = n-i.val) (hS : 2^k₁ ≤ S.card) :
        FlatExtractorEvents (E₁ i) S δ :=
      FlatExtractorEvents.of_fixed_word_length (Nat.sub_le ..) _ δ h₁ S hlen hS
    have houter (i : Fin n) (S : Finset (List Bool))
        (hlen : ∀ w ∈ S, w.length = i.val) (hS : 2^k₂ ≤ S.card) :
        FlatExtractorEvents (E₂ i) S δ := by
      have h := FlatExtractorEvents.of_fixed_word_length i.isLt.le _ δ h₂ S hlen hS
      exact FlatExtractorEvents.comapSeedCast (congrArg (fun z : ℕ => 2^z) he₁) h
    have h := prefixSplitGraph_entropy_coverage E₁ E₂ words k k₁ k₂ (n.size+1) δ δ
      hfsize hk₁ hwords (tuz_splitLoss_bounds hn).1 hk (by positivity) (by positivity)
      (by positivity) hinner houter
    rw [tuzCoordinateGraph_fixedWord_support] at h
    have hcast := finCast_neighbor_card (congrArg (fun z : ℕ => 2^z) he₂)
      (fun v => tuzCoordinateGraph E (fixedWordEmbedding n v)) D
    change _ ≤ ((D.biUnion fun v => Finset.univ.image (Γ v)).card : ℝ)
    unfold Γ
    rw [hcast]
    have hh := h
    conv at hh => lhs; rw [he₂]
    exact_mod_cast hh
  · intro v i
    let w := fixedWordEmbedding n v
    let p : Fin n × Fin (2^t₁) := finProdFinEquiv.symm i
    have hp₁ : p.1.val = i.val / 2^t₁ := rfl
    have hp₂ : p.2.val = i.val % 2^t₁ := rfl
    have hsplit := binaryValue_take_drop w p.1.val
    have hprefix : (fitWord n (w.take p.1.val)).val = v.val / 2^(n-p.1.val) := by
      rw [fitWord_value_of_length_le (by simp [w])]
      simpa [w] using hsplit.1
    have hsuffix : (fitWord n (w.drop p.1.val)).val = v.val % 2^(n-p.1.val) := by
      rw [fitWord_value_of_length_le (by simp [w])]
      simpa [w] using hsplit.2
    change (extractorEdge extract Δ n k₂ (t₂+t₁) (fitWord n (w.take p.1.val))
      (Fin.cast _ (extractorEdge extract Δ n k₁ t₁ (fitWord n (w.drop p.1.val)) p.2))).val = _
    simp only [extractorEdge, Fin.val_cast, he₁, he₂]
    rw [hprefix, hsuffix, hp₁, hp₂]

end TimeSpaceMA

namespace TimeSpaceMA

open Turing.MultiTapeTM

theorem tuz_from_extractors (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ) (e : ℕ) (P : Program), 0 < c ∧ P.CoinFree ∧
      ∀ n k : ℕ, 1 ≤ n → k ≤ n →
        ∃ (d R : ℕ) (Γ : Fin (2 ^ n) → Fin d → Fin R),
          1 ≤ d ∧ d ≤ n ^ e + e ∧
          c * (2 : ℝ) ^ k * (d : ℝ) / (n : ℝ) ^ 3 ≤ (R : ℝ) ∧
          (∀ D : Finset (Fin (2 ^ n)), 2 ^ k ≤ D.card →
            (1 - ε) * (R : ℝ) ≤ ((D.biUnion fun v => Finset.univ.image (Γ v)).card : ℝ)) ∧
          ∀ v : Fin (2 ^ n),
            ∃ st, P.RunsTo zeroTape (memOf [n, k, v.val]) st ∧ st.work ≤ n ^ e + e ∧
              st.mem 0 = d ∧ ∀ i : Fin d, st.mem (1 + i.val) = (Γ v i).val := by
  let δ : ℝ := min (ε/2) (1/4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ' : δ ≤ 1/4 := min_le_right _ _
  have hδε : 2*δ ≤ ε := by
    have hd : δ ≤ ε/2 := min_le_left _ _
    linarith
  obtain ⟨A, Δ, extract, hA, hext, hflat⟩ := constantLossFlatExtractor δ hδ hδ'
  obtain ⟨B, hB, hshort⟩ := tuz_short_seed_budget A Δ
  obtain ⟨eD, hD⟩ := tuz_seed_degree_bound B
  let f : ℕ × ℕ × ℕ → List ℕ := fun x => tuzNeighborLabels extract A Δ B x.1 x.2.1 x.2.2
  obtain ⟨eP, P, hP, hrun⟩ := widthListComputable_to_coinFreeRAM f
    (tuzNeighborLabels_polytime extract A Δ B hext)
  let e := max eD eP
  let c : ℝ := 1 / (4 * (2 : ℝ)^(2*Δ))
  refine ⟨c, e, P, by dsimp [c]; positivity, hP, ?_⟩
  intro n k hn hk
  let t₁ := B*n.size
  let t₂ := A*(n.size+n.size^4)
  let k₁ := t₂+Δ
  let s := n.size+1
  let k₂ := k-k₁-s
  let d₀ := (2 : ℕ)^t₁
  have hq : 1 ≤ n.size := Nat.size_pos.mpr hn
  have ht₁ : Δ ≤ t₁ := hB.trans (by simpa [t₁] using Nat.mul_le_mul_left B hq)
  have hd₀ : 0 < d₀ := Nat.pow_pos (by decide)
  have hlenD : n*d₀ ≤ n^e+e := (hD n hn).trans
    (Nat.add_le_add (Nat.pow_le_pow_right hn (le_max_left _ _)) (le_max_left _ _))
  have hclock : n^eP+eP ≤ n^e+e :=
    Nat.add_le_add (Nat.pow_le_pow_right hn (le_max_right _ _)) (le_max_right _ _)
  have liftRuns (d R : ℕ) (Γ : Fin (2 ^ n) → Fin d → Fin R)
      (hlength : ∀ v : Fin (2^n), (f (n,k,v.val)).length = d)
      (houtput : ∀ (v : Fin (2^n)) (i : Fin d),
        (f (n,k,v.val))[i.val]'(by rw [hlength]; exact i.isLt) = (Γ v i).val) :
      ∀ v : Fin (2 ^ n),
        ∃ st, P.RunsTo zeroTape (memOf [n, k, v.val]) st ∧ st.work ≤ n ^ e + e ∧
          st.mem 0 = d ∧ ∀ i : Fin d, st.mem (1 + i.val) = (Γ v i).val := by
    intro v
    obtain ⟨st, hr, hw, hd, ho⟩ := hrun n k v.val hn hk v.isLt
    refine ⟨st, hr, hw.trans hclock, hd.trans (hlength v), ?_⟩
    intro i
    let j : Fin (f (n,k,v.val)).length := ⟨i.val, by rw [hlength]; exact i.isLt⟩
    exact (ho j).trans (houtput v i)
  by_cases hhigh : k₁+s+Δ ≤ k
  · let m := k+t₁-s-2*Δ
    obtain ⟨hk₁, hk₂, hΔ₁, hΔ₂, hseed₂, he₁, he₂, hbudget⟩ :=
      tuz_high_seed_compatible A Δ n k t₁ hk hhigh
    have hseed₁ : A*(n.size+k₁.size^4) ≤ t₁ :=
      hshort n k₁ hn (by dsimp [k₁, t₂]; omega)
    have hk₁positive : 1 ≤ k₁ := by
      have hlong : 0 < t₂ := Nat.mul_pos hA (by omega)
      dsimp only [k₁]
      omega
    obtain ⟨Γ, hcoverage, hvalue⟩ := tuz_high_graph extract Δ n k k₁ k₂ t₁ t₂ he₁ he₂
      hk₁positive (by exact hbudget.le) hn δ
      (hflat n k₁ t₁ hn hk₁ hseed₁ hΔ₁)
      (hflat n k₂ (t₂+t₁) hn hk₂ hseed₂ hΔ₂)
    refine ⟨n*d₀, 2^m, Γ, Nat.mul_pos hn hd₀, hlenD, ?_, ?_, ?_⟩
    · have h : n.size+1+Δ ≤ k := by dsimp [s] at hhigh; omega
      simpa only [c, m, s, d₀, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        tuz_high_loss_bound hn ht₁ h
    · intro D hDS
      have h := hcoverage D hDS
      apply le_trans (b := (1-δ-δ) * ((2^m : ℕ) : ℝ))
      · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      · exact_mod_cast h
    · have hlength : ∀ v : Fin (2^n), (f (n,k,v.val)).length = n*d₀ := by
        intro v
        have hg : A*(n.size+n.size^4)+Δ+(n.size+1)+Δ ≤ k := hhigh
        simp only [f, tuzNeighborLabels, Nat.min_eq_left hk, if_pos hg,
          List.length_map, List.length_range, d₀, t₁]
      apply liftRuns _ _ Γ hlength
      intro v i
      rw [hvalue]
      have hg : A*(n.size+n.size^4)+Δ+(n.size+1)+Δ ≤ k := hhigh
      simp only [f, tuzNeighborLabels, Nat.min_eq_left hk, if_pos hg,
        List.getElem_map, List.getElem_range, k₁, k₂, t₁, t₂, s]
  · let m := k+t₁-Δ
    let Γ := extractorEdge extract Δ n k t₁
    have hseed : A*(n.size+k.size^4) ≤ t₁ :=
      hshort n k hn (by dsimp [k₁, t₂, s] at hhigh; omega)
    have hΔk : Δ ≤ k+t₁ := by omega
    refine ⟨d₀, 2^m, Γ, hd₀, ?_, ?_, ?_, ?_⟩
    · apply le_trans _ hlenD
      simpa using Nat.mul_le_mul_right d₀ hn
    · simpa only [c, m, d₀, Nat.cast_pow, Nat.cast_ofNat] using
        tuz_low_loss_bound hn (k := k) ht₁
    · intro D hDS
      have h := support_of_flatExtractorEvents Γ D ((Nat.pow_pos (by decide)).trans_le hDS)
        (by simpa using hd₀) (by simp) δ (hflat n k t₁ hn hk hseed hΔk D hDS)
      simp only [Fintype.card_fin] at h
      exact (mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans h
    · have hlength : ∀ v : Fin (2^n), (f (n,k,v.val)).length = d₀ := by
        intro v
        have hg : ¬ A*(n.size+n.size^4)+Δ+(n.size+1)+Δ ≤ k := hhigh
        simp only [f, tuzNeighborLabels, Nat.min_eq_left hk, if_neg hg,
          List.length_map, List.length_range, d₀, t₁]
      apply liftRuns _ _ Γ hlength
      intro v i
      have hg : ¬ A*(n.size+n.size^4)+Δ+(n.size+1)+Δ ≤ k := hhigh
      simp only [f, tuzNeighborLabels, Nat.min_eq_left hk, if_neg hg,
        List.getElem_map, List.getElem_range, Γ, extractorEdge, t₁]

end TimeSpaceMA

open TimeSpaceMA

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ) (e : ℕ) (P : Program), 0 < c ∧ P.CoinFree ∧
      ∀ n k : ℕ, 1 ≤ n → k ≤ n →
        ∃ (d R : ℕ) (Γ : Fin (2 ^ n) → Fin d → Fin R),
          1 ≤ d ∧ d ≤ n ^ e + e ∧
          c * (2 : ℝ) ^ k * (d : ℝ) / (n : ℝ) ^ 3 ≤ (R : ℝ) ∧
          (∀ D : Finset (Fin (2 ^ n)), 2 ^ k ≤ D.card →
            (1 - ε) * (R : ℝ) ≤ ((D.biUnion fun v => Finset.univ.image (Γ v)).card : ℝ)) ∧
          ∀ v : Fin (2 ^ n),
            ∃ st, P.RunsTo zeroTape (memOf [n, k, v.val]) st ∧ st.work ≤ n ^ e + e ∧
              st.mem 0 = d ∧ ∀ i : Fin d, st.mem (1 + i.val) = (Γ v i).val :=
  tuz_from_extractors ε hε
