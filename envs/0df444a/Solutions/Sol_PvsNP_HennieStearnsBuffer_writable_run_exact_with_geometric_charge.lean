-- Prove2me | solution 1 for PvsNP.HennieStearnsBuffer.writable_run_exact_with_geometric_charge
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T17:19:05.037537+00:00
-- url     : https://prove2.me/submissions/a13e34e3-7deb-451b-a234-dbed34b75096

import Definitions.Def_HennieStearnsWritableBuffer
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace PvsNP.HennieStearnsBuffer

open scoped BigOperators

private theorem atLeast_cons (i j : ℕ) (tail : List ℕ) :
    atLeast i (j::tail) = atLeast i tail + (if i ≤ j then 1 else 0) := by
  by_cases h : i ≤ j <;> simp [atLeast,h]

private theorem count_credit (orders : List ℕ) (ready : ℕ → Bool) (i : ℕ)
    (valid : legal ready orders) : atLeast (i+1) orders ≤ orders.count i + (ready i).toNat := by
  induction orders generalizing ready with
  | nil => simp [atLeast]
  | cons j tail ih =>
    obtain ⟨first,rest⟩ := valid
    have later := ih (after ready j) rest
    rw [atLeast_cons,List.count_cons]
    rcases lt_trichotomy j i with small | equal | large
    · have notLarge : ¬i+1 ≤ j := by omega
      have neq : j ≠ i := by omega
      have notLess : ¬i < j := by omega
      have reverseNeq : i ≠ j := Ne.symm neq
      simp [after,notLess,reverseNeq] at later
      simpa only [if_neg notLarge,beq_eq_false_iff_ne.mpr neq,Bool.false_eq_true,
        if_false,Nat.add_zero] using later
    · subst j
      have reusable : atLeast (i+1) tail ≤ tail.count i+1 := by simpa [after] using later
      have notLarge : ¬i+1 ≤ i := by omega
      simp only [if_neg notLarge,beq_self_eq_true,if_true,Nat.add_zero]
      omega
    · have charged : ready i = true := first i large
      have big : i+1 ≤ j := by omega
      have neq : j ≠ i := by omega
      have laterBound : atLeast (i+1) tail ≤ tail.count i := by simpa [after,large] using later
      simp only [if_pos big,beq_eq_false_iff_ne.mpr neq,Bool.false_eq_true,
        if_false,Nat.add_zero,charged,Bool.toNat_true]
      omega

private theorem atLeast_split (orders : List ℕ) (i : ℕ) :
    atLeast i orders = orders.count i + atLeast (i+1) orders := by
  induction orders with
  | nil => rfl
  | cons j tail ih =>
    rw [atLeast_cons,atLeast_cons,List.count_cons,ih]
    rcases lt_trichotomy j i with small | equal | large
    · have h₁ : ¬i ≤ j := by omega
      have h₂ : ¬i+1 ≤ j := by omega
      have h₃ : j ≠ i := by omega
      simp only [if_neg h₁,if_neg h₂,beq_eq_false_iff_ne.mpr h₃,
        Bool.false_eq_true,if_false,Nat.add_zero]
    · subst j
      have h₂ : ¬i+1 ≤ i := by omega
      simp only [if_pos le_rfl,if_neg h₂,beq_self_eq_true,if_true,Nat.add_zero]
      omega
    · have h₁ : i ≤ j := by omega
      have h₂ : i+1 ≤ j := by omega
      have h₃ : j ≠ i := by omega
      simp only [if_pos h₁,if_pos h₂,beq_eq_false_iff_ne.mpr h₃,
        Bool.false_eq_true,if_false,Nat.add_zero]
      omega

/-- Larger cleanups are geometrically rare, even when their directions and
the times at which cleanups are requested are arbitrary. -/
theorem order_frequency (orders : List ℕ) (valid : legal (fun _ => false) orders) (i : ℕ) :
    atLeast i orders * 2^i ≤ orders.length := by
  induction i with
  | zero => simp [atLeast]
  | succ i ih =>
    have credit := count_credit orders (fun _ => false) i valid
    have halves : 2*atLeast (i+1) orders ≤ atLeast i orders := by
      simp only [Bool.toNat_false,Nat.add_zero] at credit
      rw [atLeast_split orders i]
      omega
    rw [pow_succ]
    calc
      _ = (2*atLeast (i+1) orders)*2^i := by ring
      _ ≤ _ := (Nat.mul_le_mul_right _ halves).trans ih

private theorem count_le_atLeast (orders : List ℕ) (i : ℕ) :
    orders.count i ≤ atLeast i orders := by
  rw [atLeast_split]
  exact Nat.le_add_right _ _

private theorem atLeast_of_mem (orders : List ℕ) {i : ℕ} (present : i ∈ orders) :
    0 < atLeast i orders :=
  (List.count_pos_iff.mpr present).trans_le (count_le_atLeast orders i)

private theorem level_lt_size (orders : List ℕ) (valid : legal (fun _ => false) orders)
    {i : ℕ} (present : i ∈ orders) : i < orders.length.size := by
  apply Nat.lt_size.mpr
  exact (Nat.le_mul_of_pos_left _ (atLeast_of_mem orders present)).trans
    (order_frequency orders valid i)

/-- Sum of nominal work across all cleanup levels. It takes only the
geometric separation invariant, independently of the tape layout. -/
theorem bill_le (orders : List ℕ) (valid : legal (fun _ => false) orders) :
    bill orders ≤ orders.length*orders.length.size := by
  rw [bill,Finset.sum_list_map_count]
  have subset : orders.toFinset ⊆ Finset.range orders.length.size := by
    intro i present
    exact Finset.mem_range.mpr (level_lt_size orders valid (List.mem_toFinset.mp present))
  calc
    (∑ i ∈ orders.toFinset, orders.count i • 2^i) ≤
        ∑ i ∈ orders.toFinset, orders.length := by
      apply Finset.sum_le_sum
      intro i _
      change orders.count i * 2^i ≤ orders.length
      exact (Nat.mul_le_mul_right (2^i) (count_le_atLeast orders i)).trans
          (order_frequency orders valid i)
    _ = orders.toFinset.card*orders.length := by simp
    _ ≤ orders.length.size*orders.length := by
      apply Nat.mul_le_mul_right
      simpa using Finset.card_le_card subset
    _ = _ := Nat.mul_comm _ _

@[simp] theorem below_sum (i : ℕ) : (below i).sum = 2^i-1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [below,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,ih,pow_succ]
    have positive : 0 < (2:ℕ)^i := by positivity
    omega

theorem shelve_flatten {A : Type} (sizes : List ℕ) (w : List A) :
    (shelve sizes w).1.flatten ++ (shelve sizes w).2 = w := by
  induction sizes generalizing w with
  | nil => rfl
  | cons n ns ih =>
    simp only [shelve,List.flatten_cons,List.append_assoc,ih,List.take_append_drop]

theorem shelve_lengths {A : Type} (sizes : List ℕ) (w : List A)
    (enough : sizes.sum ≤ w.length) :
    (shelve sizes w).1.map List.length = sizes ∧
      (shelve sizes w).2.length = w.length-sizes.sum := by
  induction sizes generalizing w with
  | nil => simp [shelve]
  | cons n ns ih =>
    simp only [List.sum_cons] at enough
    have small : n ≤ w.length := by omega
    have fits : ns.sum ≤ (w.drop n).length := by
      simp only [List.length_drop]
      omega
    obtain ⟨first,last⟩ := ih (w.drop n) fits
    constructor
    · simp [shelve,List.length_take,small,first]
    · simp only [shelve,last,List.length_drop,List.sum_cons]
      omega

private theorem place_words {A : Type} {ls rs : List (List A)}
    (length : ls.length = rs.length) :
    leftWord (place ls rs) = ls.flatten ∧ rightWord (place ls rs) = rs.flatten := by
  induction ls generalizing rs with
  | nil =>
    have empty : rs = [] := List.length_eq_zero_iff.mp length.symm
    subst rs
    exact ⟨rfl,rfl⟩
  | cons l ls ih =>
    cases rs with
    | nil => simp at length
    | cons r rs =>
      have shorter : ls.length = rs.length := by simpa using length
      obtain ⟨left,right⟩ := ih shorter
      constructor
      · simpa only [place,leftWord,List.zip_cons_cons,List.map_cons,List.flatten_cons]
          using congrArg (l ++ ·) left
      · simpa only [place,rightWord,List.zip_cons_cons,List.map_cons,List.flatten_cons]
          using congrArg (r ++ ·) right

/-- The rearrangement preserves represented word order exactly. The lower
areas are balanced again and the selected area still holds two blocks. -/
theorem slideLeft_verifies {A : Type} (i : ℕ) (center : A) (near : List (Layer A))
    (selected : Layer A) (noLeft : leftWord near = [])
    (nearRight : (rightWord near).length = 2*(2^i-1))
    (upper : selected.fits (2^i)) (nonempty : selected.left ≠ []) :
    let out := slideLeft i center near selected
    out.center :: (leftWord out.near ++ out.selected.left) =
        leftWord near ++ selected.left ∧
      rightWord out.near ++ out.selected.right =
        center :: (rightWord near ++ selected.right) ∧
      out.near.map (fun level => level.left.length) = below i ∧
      out.near.map (fun level => level.right.length) = below i ∧
      out.selected.fits (2^i) := by
  let b : ℕ := 2^i
  have bPositive : 0 < b := by dsimp [b]; positivity
  let front := selected.left.take b
  let left := shelve (below i) front.tail
  let right := shelve (below i) (center::rightWord near)
  have oldLeft : selected.left.length = b ∨ selected.left.length = 2*b := by
    rcases upper.1 with none | one | two
    · exact False.elim (nonempty (List.length_eq_zero_iff.mp none))
    · exact Or.inl one
    · exact Or.inr two
  have capacity : b ≤ selected.left.length := by rcases oldLeft with e | e <;> omega
  have frontLength : front.length = b := by simp [front,capacity]
  have tailLength : front.tail.length = b-1 := by simp [frontLength]
  have sizes : (below i).sum = b-1 := below_sum i
  obtain ⟨ll,remL⟩ := shelve_lengths (below i) front.tail (by omega)
  have rightLength : (center::rightWord near).length = 2*(b-1)+1 := by
    simp only [List.length_cons,nearRight,b]
  obtain ⟨rl,remR⟩ := shelve_lengths (below i) (center::rightWord near) (by omega)
  change left.1.map List.length = below i at ll
  change left.2.length = _ at remL
  change right.1.map List.length = below i at rl
  change right.2.length = _ at remR
  have eqLen : left.1.length = right.1.length := by
    simpa only [List.length_map] using congrArg List.length (ll.trans rl.symm)
  obtain ⟨placedL,placedR⟩ := place_words eqLen
  have leftFlat : left.1.flatten ++ left.2 = front.tail := shelve_flatten _ _
  have rightFlat : right.1.flatten ++ right.2 = center::rightWord near := shelve_flatten _ _
  have none : left.2 = [] := List.length_eq_zero_iff.mp (by omega)
  have leftNear : leftWord (place left.1 right.1) = front.tail := by
    simpa only [none,List.append_nil,placedL] using leftFlat
  have nextSize : right.2.length = b := by omega
  have frontForm : front.headD center::front.tail = front := by
    cases eq : front with
    | nil =>
      rw [eq] at frontLength
      simp only [List.length_nil] at frontLength
      omega
    | cons a w => rfl
  change (front.headD center :: (leftWord (place left.1 right.1) ++
    (left.2 ++ selected.left.drop b)) = leftWord near ++ selected.left) ∧
    (rightWord (place left.1 right.1) ++ (right.2 ++ selected.right) =
      center :: (rightWord near ++ selected.right)) ∧
    (place left.1 right.1).map (fun level => level.left.length) = below i ∧
    (place left.1 right.1).map (fun level => level.right.length) = below i ∧
    (Layer.mk (left.2 ++ selected.left.drop b) (right.2 ++ selected.right)).fits b
  have planned : ∀ {ls rs : List (List A)}, ls.length = rs.length →
      (place ls rs).map (fun level => level.left.length) = ls.map List.length ∧
      (place ls rs).map (fun level => level.right.length) = rs.map List.length := by
    intro ls
    induction ls with
    | nil => intro rs same; have eq : rs = [] := List.length_eq_zero_iff.mp same.symm; simp [place,eq]
    | cons l ls ih =>
      intro rs same
      cases rs with
      | nil => simp at same
      | cons r rs =>
        have shorter : ls.length = rs.length := by simpa using same
        obtain ⟨p,q⟩ := ih shorter
        constructor
        · simpa only [place,List.zip_cons_cons,List.map_cons] using congrArg (l.length :: ·) p
        · simpa only [place,List.zip_cons_cons,List.map_cons] using congrArg (r.length :: ·) q
  obtain ⟨leftPlan,rightPlan⟩ := planned eqLen
  refine ⟨?_,?_,leftPlan.trans ll,rightPlan.trans rl,?_⟩
  · rw [leftNear,none,List.nil_append,noLeft,List.nil_append,← List.cons_append,frontForm]
    exact List.take_append_drop b selected.left
  · rw [placedR,← List.append_assoc,rightFlat,List.cons_append]
  · obtain ⟨_,sum⟩ := upper
    constructor
    · simp only [none,List.nil_append,List.length_drop]
      rcases oldLeft with one | two
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
    · simp only [none,List.nil_append,List.length_drop,List.length_append,nextSize]
      omega

private theorem legal_of_physical {physical charged : ℕ → Bool}
    {events : List (ℕ × Bool)}
    (follows : physicalSchedule physical events)
    (dominates : ∀ j, physical j = true → charged j = true) :
    legal charged (events.map Prod.fst) := by
  induction events generalizing physical charged with
  | nil => trivial
  | cons event events ih =>
    obtain ⟨i,remains⟩ := event
    obtain ⟨ready,remaining⟩ := follows
    refine ⟨fun j earlier => dominates j (ready j earlier),ih remaining (fun j used => ?_)⟩
    by_cases smaller : j < i
    · simp [physicalAfter,smaller] at used
    · by_cases same : j = i
      · simp [after,same]
      · simp [physicalAfter,smaller,same] at used
        simpa [after,smaller,same] using dominates j used

/-- Either rule for the selected level gets the same exact aggregate bound. -/
theorem physical_schedule_bill (events : List (ℕ × Bool))
    (follows : physicalSchedule (fun _ => false) events) :
    bill (events.map Prod.fst) ≤ events.length*events.length.size := by
  simpa only [List.length_map] using bill_le _ (legal_of_physical follows (fun _ h => h))

/-- An empty storage area on the side being read from forces both levels
on the opposite side to be full. It is therefore eligible for clearing
when a larger storage area must be reached. -/
theorem empty_side_forces_full {A : Type} {size : ℕ} {level : Layer A}
    (fits : level.fits size) (empty : level.left = []) :
    level.right.length = 2*size := by
  simpa only [empty,List.length_nil,Nat.zero_add] using fits.2

@[simp] theorem sizesFrom_length (base n : ℕ) :
    (sizesFrom base n).length = n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp [sizesFrom,ih]

private theorem sizesFrom_snoc (base n : ℕ) :
    sizesFrom base (n+1) = sizesFrom base n ++ [2^(base+n)] := by
  induction n generalizing base with
  | zero => simp [sizesFrom]
  | succ n ih =>
    change 2^base :: sizesFrom (base+1) (n+1) =
      (2^base :: sizesFrom (base+1) n) ++ [2^(base+(n+1))]
    rw [ih,List.cons_append,show base+1+n = base+(n+1) by omega]

theorem below_eq_sizes (i : ℕ) : below i = sizesFrom 0 i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [below,ih,sizesFrom_snoc,Nat.zero_add]

@[simp] theorem below_length (i : ℕ) : (below i).length = i := by
  rw [below_eq_sizes,sizesFrom_length]

theorem fits_append {A : Type} (base : ℕ) (left right : List (Layer A)) :
    FitsFrom base (left++right) ↔
      FitsFrom base left ∧ FitsFrom (base+left.length) right := by
  induction left generalizing base with
  | nil => simp [FitsFrom]
  | cons a ls ih =>
    simp only [List.cons_append,FitsFrom,List.length_cons,ih,and_assoc]
    rw [show base+1+ls.length = base+(ls.length+1) by omega]

theorem leftWord_append {A : Type} (l r : List (Layer A)) :
    leftWord (l++r) = leftWord l ++ leftWord r := by simp [leftWord]

theorem rightWord_append {A : Type} (l r : List (Layer A)) :
    rightWord (l++r) = rightWord l ++ rightWord r := by simp [rightWord]

theorem all_left_nil {A : Type} {l : List (Layer A)}
    (empty : ∀ a ∈ l, a.left = []) : leftWord l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have first := empty a (by simp)
    have remaining : ∀ b ∈ l, b.left = [] := fun b h => empty b (by simp [h])
    have tail := ih remaining
    change a.left ++ leftWord l = []
    rw [first,tail]
    rfl

private theorem rightLength_empty_left {A : Type} (base : ℕ) (l : List (Layer A))
    (fit : FitsFrom base l) (empty : ∀ a ∈ l, a.left = []) :
    (l.map fun a => a.right.length) = (sizesFrom base l.length).map (2*·) := by
  induction l generalizing base with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨head,tail⟩ := fit
    have first := empty a (by simp)
    have full := empty_side_forces_full head first
    have remaining : ∀ b ∈ l, b.left = [] := fun b h => empty b (by simp [h])
    simp only [List.map_cons,List.length_cons,sizesFrom,full,ih (base+1) tail remaining]

theorem full_right_prefix {A : Type} (l : List (Layer A))
    (fit : FitsFrom 0 l) (empty : ∀ a ∈ l, a.left = []) :
    (rightWord l).length = 2*(2^l.length-1) := by
  unfold rightWord
  rw [List.length_flatten,List.map_map]
  have lengths := rightLength_empty_left 0 l fit empty
  change (l.map (fun a => a.right.length)).sum = _
  rw [lengths,← below_eq_sizes,List.sum_map_mul_left]
  simp

private theorem fits_balanced_sizes {A : Type} (base : ℕ) (l : List (Layer A))
    (lSize : l.map (fun a => a.left.length) = sizesFrom base l.length)
    (rSize : l.map (fun a => a.right.length) = sizesFrom base l.length) :
    FitsFrom base l := by
  induction l generalizing base with
  | nil => trivial
  | cons a l ih =>
    simp only [List.map_cons,List.length_cons,sizesFrom,List.cons.injEq] at lSize rSize
    exact ⟨⟨Or.inr (Or.inl lSize.1),by rw [lSize.1,rSize.1,two_mul]⟩,
      ih (base+1) lSize.2 rSize.2⟩

theorem splitLeft_ok {A : Type} (layers : List (Layer A)) :
    let s := splitLeft layers
    s.1++s.2 = layers ∧ (∀ a ∈ s.1, a.left = []) ∧
      (∀ a, s.2.head? = some a → a.left ≠ []) := by
  induction layers with
  | nil => simp [splitLeft]
  | cons l layers ih =>
    by_cases empty : l.left.isEmpty
    · have nilLeft : l.left = [] := List.isEmpty_iff.mp empty
      obtain ⟨part,first,rest⟩ := ih
      simp only [splitLeft,if_pos empty,List.cons_append,part,true_and]
      exact ⟨fun a h => (List.mem_cons.mp h).elim (fun e => e ▸ nilLeft) (first a),rest⟩
    · simp only [splitLeft,if_neg empty,List.nil_append,List.not_mem_nil,false_implies,
        implies_true,List.head?_cons,Option.some.injEq,true_and]
      intro a same
      subst a
      exact fun h => empty (List.isEmpty_iff.mpr h)

theorem blankLayer_fits {A : Type} (blank : A) (i : ℕ) : (blankLayer blank i).fits (2^i) := by
  simp [blankLayer,Layer.fits,two_mul]

theorem chooseLeft_ok {A : Type} (blank : A) {old : List (Layer A)} (valid : FitsFrom 0 old) :
    let sel := chooseLeft blank old
    FitsFrom 0 sel.near ∧ (∀ a ∈ sel.near, a.left = []) ∧
      sel.selected.fits (2^sel.near.length) ∧ sel.selected.left ≠ [] ∧
      FitsFrom (sel.near.length+1) sel.far ∧
      (sel.layers = old ∨ (sel.near = old ∧ sel.far = [] ∧
        sel.selected = blankLayer blank old.length)) := by
  obtain ⟨parts,nearEmpty,next⟩ := splitLeft_ok old
  generalize eq : splitLeft old = pair at parts nearEmpty next ⊢
  rcases pair with ⟨near,far⟩
  change near++far = old at parts
  have sizes := (fits_append 0 near far).mp (parts.symm ▸ valid)
  cases far with
  | nil =>
    have nearOld : near = old := by simpa using parts
    have newNonempty : (blankLayer blank near.length).left ≠ [] := by
      intro h
      have len := congrArg List.length h
      simp only [blankLayer,List.length_replicate,List.length_nil] at len
      exact (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) len
    have chosen : chooseLeft blank old = ⟨near,blankLayer blank near.length,[]⟩ := by
      simp [chooseLeft,eq]
    dsimp only
    rw [chosen]
    exact ⟨sizes.1,nearEmpty,blankLayer_fits _ _,newNonempty,trivial,Or.inr
      ⟨nearOld,rfl,by rw [nearOld]⟩⟩
  | cons a far =>
    obtain ⟨head,tail⟩ := sizes.2
    have chosen : chooseLeft blank old = ⟨near,a,far⟩ := by simp [chooseLeft,eq]
    dsimp only
    rw [chosen]
    exact ⟨sizes.1,nearEmpty,by simpa using head,next _ rfl,by simpa using tail,Or.inl parts⟩

theorem slide_left_layout {A : Type} (blank : A) (tape : TapeBuffer A)
    (valid : FitsFrom 0 tape.layers) :
    let s := chooseLeft blank tape.layers
    let moved := moveLeft blank tape
    FitsFrom 0 moved.tape.layers ∧
      moved.tape.center :: leftWord moved.tape.layers = leftWord s.layers ∧
      rightWord moved.tape.layers = tape.center :: rightWord s.layers := by
  let s := chooseLeft blank tape.layers
  let z := slideLeft s.near.length tape.center s.near s.selected
  obtain ⟨fit,empty,head,nonempty,far,_⟩ := chooseLeft_ok blank valid
  obtain ⟨left,right,sizeL,sizeR,select⟩ := slideLeft_verifies s.near.length tape.center
    s.near s.selected (all_left_nil empty) (full_right_prefix _ fit empty) head nonempty
  have zlen : z.near.length = s.near.length := by
    have lengths := congrArg List.length sizeL
    simpa only [List.length_map,below_length] using lengths
  have balanced : FitsFrom 0 z.near := by
    apply fits_balanced_sizes 0
    · simpa only [zlen,← below_eq_sizes] using sizeL
    · simpa only [zlen,← below_eq_sizes] using sizeR
  refine ⟨?_,?_,?_⟩
  · change FitsFrom 0 (z.near++z.selected::s.far)
    apply (fits_append _ _ _).mpr
    refine ⟨balanced,?_⟩
    rw [Nat.zero_add,zlen]
    exact ⟨select,far⟩
  · change z.center::leftWord (z.near++z.selected::s.far) = leftWord (s.near++s.selected::s.far)
    simp only [leftWord_append]
    change z.center::(leftWord z.near ++ (z.selected.left++leftWord s.far)) =
      leftWord s.near ++ (s.selected.left++leftWord s.far)
    rw [← List.append_assoc,← List.append_assoc,← List.cons_append,left]
  · change rightWord (z.near++z.selected::s.far) =
      tape.center::rightWord (s.near++s.selected::s.far)
    simp only [rightWord_append]
    change rightWord z.near ++ (z.selected.right++rightWord s.far) =
      tape.center::(rightWord s.near ++ (s.selected.right++rightWord s.far))
    rw [← List.append_assoc,← List.append_assoc,right,List.cons_append]

theorem wordAt_extend {A : Type} (blank : A) (word : List A) (count i : ℕ) :
    wordAt blank (word++List.replicate count blank) i = wordAt blank word i := by
  by_cases inside : i < word.length
  · simp only [wordAt,List.getElem?_append_left inside]
  · rw [wordAt,List.getElem?_append_right (Nat.le_of_not_gt inside),
      List.getElem?_replicate,wordAt,List.getElem?_eq_none (Nat.le_of_not_gt inside)]
    split <;> rfl

private theorem glimpse_selected {A : Type} (blank : A) (tape : TapeBuffer A)
    (valid : FitsFrom 0 tape.layers) :
    glimpse blank ⟨tape.center,(chooseLeft blank tape.layers).layers⟩ = glimpse blank tape := by
  obtain ⟨_,_,_,_,_,same | grown⟩ := chooseLeft_ok blank valid
  · simp [glimpse,same]
  · obtain ⟨left,far,atSelected⟩ := grown
    have extension : (chooseLeft blank tape.layers).layers =
        tape.layers++[blankLayer blank tape.layers.length] := by
      simp [Selection.layers,left,far,atSelected]
    apply Snapshot.ext
    · rfl
    · funext i
      simp only [glimpse,extension,leftWord_append]
      simpa [leftWord,blankLayer] using wordAt_extend blank (leftWord tape.layers) (2^tape.layers.length) i
    · funext i
      simp only [glimpse,extension,rightWord_append]
      simpa [rightWord,blankLayer] using wordAt_extend blank (rightWord tape.layers) (2^tape.layers.length) i

/-- Allocating a fresh blank superblock when required and doing the cleanup
have exactly the effect of one move on a tape with an infinite blank tail. -/
theorem moveLeft_glimpse {A : Type} (blank : A) (tape : TapeBuffer A)
    (valid : FitsFrom 0 tape.layers) :
    FitsFrom 0 (moveLeft blank tape).tape.layers ∧
      glimpse blank (moveLeft blank tape).tape = (glimpse blank tape).shiftLeft := by
  obtain ⟨nextFits,readLeft,readRight⟩ := slide_left_layout blank tape valid
  refine ⟨nextFits,?_⟩
  let s := chooseLeft blank tape.layers
  let u := (moveLeft blank tape).tape
  rw [← glimpse_selected blank tape valid]
  apply Snapshot.ext
  · exact congrArg (fun w => wordAt blank w 0) readLeft
  · funext i
    exact congrArg (fun w => wordAt blank w (i+1)) readLeft
  · funext i
    change wordAt blank (rightWord u.layers) i =
      (Snapshot.shiftLeft (glimpse blank ⟨tape.center,s.layers⟩)).right i
    rw [readRight]
    cases i <;> rfl

theorem Layer.fits_flip {A : Type} {size : ℕ} {l : Layer A} (h : l.fits size) :
    l.flip.fits size := by
  obtain ⟨values,total⟩ := h
  constructor
  · change l.right.length = 0 ∨ l.right.length = size ∨ l.right.length = 2*size
    rcases values with v | v | v
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  · change l.right.length+l.left.length = 2*size
    omega

theorem fits_flip {A : Type} (base : ℕ) (levels : List (Layer A)) (fit : FitsFrom base levels) :
    FitsFrom base (levels.map Layer.flip) := by
  induction levels generalizing base with
  | nil => exact fit
  | cons a rest ih => exact ⟨Layer.fits_flip fit.1,ih (base+1) fit.2⟩

theorem glimpse_flip {A : Type} (blank : A) (tape : TapeBuffer A) :
    glimpse blank tape.flip = (glimpse blank tape).flip := by
  simp only [glimpse,TapeBuffer.flip,Snapshot.flip,leftWord,rightWord,List.map_map]
  rfl

theorem moveRight_glimpse {A : Type} (blank : A) (tape : TapeBuffer A)
    (valid : FitsFrom 0 tape.layers) :
    FitsFrom 0 (moveRight blank tape).tape.layers ∧
      glimpse blank (moveRight blank tape).tape = (glimpse blank tape).shiftRight := by
  obtain ⟨size,read⟩ := moveLeft_glimpse blank tape.flip (fits_flip 0 _ valid)
  refine ⟨fits_flip 0 _ size,?_⟩
  change glimpse blank (moveLeft blank tape.flip).tape.flip = _
  rw [glimpse_flip,read,glimpse_flip]
  rfl

@[simp] theorem levelFlags_length {A : Type} (base : ℕ) (areas : List (Layer A)) :
    (levelFlags base areas).length = areas.length := by
  induction areas generalizing base with
  | nil => rfl
  | cons a areas ih => simp [levelFlags,ih]

private theorem flags_append {A : Type} (base : ℕ) (l r : List (Layer A)) :
    levelFlags base (l++r) = levelFlags base l ++ levelFlags (base+l.length) r := by
  induction l generalizing base with
  | nil => simp [levelFlags]
  | cons a rest ih =>
    simp only [List.cons_append,levelFlags,ih,List.length_cons]
    rw [show base+1+rest.length = base+(rest.length+1) by omega]

private theorem flags_empty_left {A : Type} (base : ℕ) (l : List (Layer A))
    (empty : ∀ a ∈ l, a.left = []) :
    levelFlags base l = List.replicate l.length true := by
  induction l generalizing base with
  | nil => rfl
  | cons h l ih =>
    have no : h.left = [] := empty h (by simp)
    have rest : ∀ a ∈ l, a.left = [] := fun a here => empty a (by simp [here])
    have positive : 0 < (2:ℕ)^base := by positivity
    simp [levelFlags,no,ih _ rest,ne_of_lt positive,List.replicate_succ]

private theorem flags_balanced {A : Type} (base : ℕ) (l : List (Layer A))
    (sizes : l.map (fun a => a.left.length) = sizesFrom base l.length) :
    levelFlags base l = List.replicate l.length false := by
  induction l generalizing base with
  | nil => rfl
  | cons h l ih =>
    simp only [List.map_cons,List.length_cons,sizesFrom,List.cons.injEq] at sizes
    simp [levelFlags,sizes.1,ih _ sizes.2,List.replicate_succ]

private theorem ready_selected {A : Type} (blank : A) (tape : TapeBuffer A)
    (valid : FitsFrom 0 tape.layers) :
    readyAt ⟨tape.center,(chooseLeft blank tape.layers).layers⟩ = readyAt tape := by
  obtain ⟨_,_,_,_,_,same | extension⟩ := chooseLeft_ok blank valid
  · simp [readyAt,same]
  · obtain ⟨near,far,selected⟩ := extension
    have grow : (chooseLeft blank tape.layers).layers =
        tape.layers++[blankLayer blank tape.layers.length] := by
      simp [Selection.layers,near,far,selected]
    funext j
    simp only [readyAt,grow,flags_append,Nat.zero_add]
    have tail : levelFlags tape.layers.length [blankLayer blank tape.layers.length] =
        List.replicate 1 false := by simp [levelFlags,blankLayer]
    rw [tail,wordAt_extend]

private theorem prefix_ready (i : ℕ) (b : Bool) (rest : List Bool) :
    ∀ j < i, wordAt false (List.replicate i true ++ b::rest) j = true := by
  intro j earlier
  rw [wordAt,List.getElem?_append_left (by simpa using earlier)]
  simp [earlier]

private theorem prefix_after (i : ℕ) (b next : Bool) (rest : List Bool) :
    wordAt false (List.replicate i false ++ next::rest) =
      physicalAfter (wordAt false (List.replicate i true ++ b::rest)) i next := by
  funext j
  by_cases earlier : j < i
  · rw [physicalAfter,if_pos earlier,wordAt,List.getElem?_append_left (by simpa using earlier)]
    simp [earlier]
  · have reaches : i ≤ j := by omega
    rw [physicalAfter,if_neg earlier]
    by_cases here : j=i
    · subst j
      simp only [wordAt,List.getElem?_append_right (by simp :
        (List.replicate i false).length ≤ i),List.length_replicate,Nat.sub_self,
        List.getElem?_cons_zero,Option.getD_some,if_true]
    · have positive : 0 < j-i := by omega
      have first : (List.replicate i false).length ≤ j := by simpa using reaches
      have other : (List.replicate i true).length ≤ j := by simpa using reaches
      simp only [if_neg here,wordAt,List.getElem?_append_right first,
        List.getElem?_append_right other,List.length_replicate]
      obtain ⟨d,eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      rw [eq]
      rfl

/-- The selected level is found from actual occupancies. Every lower level
was ready to pay for this cleanup, and it becomes unready after it. -/
theorem moveLeft_event {A : Type} (blank : A) (tape : TapeBuffer A) (fit : FitsFrom 0 tape.layers) :
    let r := moveLeft blank tape
    (∀ j < r.order, readyAt tape j = true) ∧
      readyAt r.tape = physicalAfter (readyAt tape) r.order r.remains := by
  let s := chooseLeft blank tape.layers
  let i := s.near.length
  let z := slideLeft i tape.center s.near s.selected
  obtain ⟨nearFit,empty,selFit,nonempty,_,_⟩ := chooseLeft_ok blank fit
  have blankNear : leftWord s.near = [] := all_left_nil empty
  obtain ⟨_,_,sizeL,_,_⟩ := slideLeft_verifies i tape.center s.near s.selected
    blankNear (full_right_prefix _ nearFit empty) selFit nonempty
  have zlen : z.near.length = i := by
    have lengths := congrArg List.length sizeL
    simpa only [List.length_map,below_length] using lengths
  have fixed := flags_balanced 0 z.near (by simpa only [zlen,← below_eq_sizes] using sizeL)
  have warm := flags_empty_left 0 s.near empty
  let b := decide (s.selected.left.length ≠ 2^i)
  let next := decide (z.selected.left.length ≠ 2^i)
  let far := levelFlags (i+1) s.far
  have before : readyAt tape = wordAt false (List.replicate i true ++ b::far) := by
    rw [← ready_selected blank tape fit]
    change wordAt false (levelFlags 0 (s.near++s.selected::s.far)) = _
    rw [flags_append,Nat.zero_add,warm]
    rfl
  have later : readyAt (moveLeft blank tape).tape =
      wordAt false (List.replicate i false ++ next::far) := by
    change wordAt false (levelFlags 0 (z.near++z.selected::s.far)) = _
    rw [flags_append,Nat.zero_add,fixed,zlen]
    rfl
  change (∀ j < i, readyAt tape j = true) ∧
    readyAt (moveLeft blank tape).tape = physicalAfter (readyAt tape) i next
  rw [before,later]
  exact ⟨prefix_ready i b far,prefix_after i b next far⟩

private theorem flags_flip {A : Type} (base : ℕ) (l : List (Layer A)) (fit : FitsFrom base l) :
    levelFlags base (l.map Layer.flip) = levelFlags base l := by
  induction l generalizing base with
  | nil => rfl
  | cons h l ih =>
    obtain ⟨head,tail⟩ := fit
    have sum := head.2
    have same : (h.right.length ≠ 2^base) ↔ (h.left.length ≠ 2^base) := by omega
    simp [levelFlags,Layer.flip,ih _ tail,same]

private theorem ready_flip {A : Type} (tape : TapeBuffer A) (fit : FitsFrom 0 tape.layers) :
    readyAt tape.flip = readyAt tape := by
  simp [readyAt,TapeBuffer.flip,flags_flip 0 _ fit]

theorem moveRight_event {A : Type} (blank : A) (tape : TapeBuffer A) (fit : FitsFrom 0 tape.layers) :
    let r := moveRight blank tape
    (∀ j < r.order, readyAt tape j = true) ∧
      readyAt r.tape = physicalAfter (readyAt tape) r.order r.remains := by
  have flipped := fits_flip 0 _ fit
  obtain ⟨first,later⟩ := moveLeft_event blank tape.flip flipped
  have nextFit := (moveLeft_glimpse blank tape.flip flipped).1
  simpa only [moveRight,Moved.flip,ready_flip tape fit,
    ready_flip (moveLeft blank tape.flip).tape nextFit] using And.intro first later

theorem stepBuffer_spec {A : Type} (blank : A) (tape : TapeBuffer A) (a : A)
    (dir : Turn) (fit : FitsFrom 0 tape.layers) :
    let step := stepBuffer blank tape a dir
    FitsFrom 0 step.1.layers ∧
      glimpse blank step.1 = snapshotStep (glimpse blank tape) a dir ∧
      (∀ tail, physicalSchedule (readyAt step.1) tail →
        physicalSchedule (readyAt tape) (step.2++tail)) ∧ step.2.length ≤ 1 := by
  let written := {tape with center := a}
  have sizes : FitsFrom 0 written.layers := fit
  cases dir with
  | stay => exact ⟨fit,rfl,fun _ h => h,by simp [stepBuffer]⟩
  | left =>
    obtain ⟨sz,view⟩ := moveLeft_glimpse blank written sizes
    obtain ⟨lower,outside⟩ := moveLeft_event blank written sizes
    refine ⟨sz,view,fun rest schedule => ⟨lower,?_⟩,by simp [stepBuffer]⟩
    change physicalSchedule (physicalAfter (readyAt written)
      (moveLeft blank written).order (moveLeft blank written).remains) rest
    rw [← outside]
    exact schedule
  | right =>
    obtain ⟨sz,view⟩ := moveRight_glimpse blank written sizes
    obtain ⟨lower,outside⟩ := moveRight_event blank written sizes
    refine ⟨sz,view,fun rest schedule => ⟨lower,?_⟩,by simp [stepBuffer]⟩
    change physicalSchedule (physicalAfter (readyAt written)
      (moveRight blank written).order (moveRight blank written).remains) rest
    rw [← outside]
    exact schedule

/-- Writable replay at the represented-tape level, including arbitrary
reversals and head motions that expose previously unallocated blank cells. -/
theorem runBuffer_spec {A : Type} (blank : A) (tape : TapeBuffer A)
    (instructions : List (A × Turn)) (fit : FitsFrom 0 tape.layers) :
    let run := runBuffer blank tape instructions
    FitsFrom 0 run.1.layers ∧
      glimpse blank run.1 = runSnapshot (glimpse blank tape) instructions ∧
      physicalSchedule (readyAt tape) run.2 ∧ run.2.length ≤ instructions.length := by
  induction instructions generalizing tape with
  | nil => exact ⟨fit,rfl,trivial,by simp [runBuffer]⟩
  | cons move rest ih =>
    rcases move with ⟨a,dir⟩
    let next := stepBuffer blank tape a dir
    obtain ⟨hasFit,meaning,schedule,length⟩ := stepBuffer_spec blank tape a dir fit
    obtain ⟨tailFit,tailMeaning,tailSchedule,tailLength⟩ := ih next.1 hasFit
    refine ⟨tailFit,?_,schedule _ tailSchedule,?_⟩
    · change glimpse blank (runBuffer blank next.1 rest).1 =
        runSnapshot (snapshotStep (glimpse blank tape) a dir) rest
      rw [tailMeaning,meaning]
    · change (next.2++(runBuffer blank next.1 rest).2).length ≤ rest.length+1
      rw [List.length_append]
      change next.2.length ≤ 1 at length
      change (runBuffer blank next.1 rest).2.length ≤ rest.length at tailLength
      omega

/-- The actual occupancy-driven execution generates a legal physical
cleanup schedule. This accounts for the aggregate geometric work,
before implementing the storage scans on a Turing machine. -/
theorem runBuffer_geometric_bound {A : Type} (blank : A) (instructions : List (A × Turn)) :
    let run := runBuffer blank (blankBuffer blank) instructions
    bill (run.2.map Prod.fst) ≤ instructions.length*instructions.length.size := by
  obtain ⟨_,_,schedule,count⟩ :=
    runBuffer_spec blank (blankBuffer blank) instructions trivial
  change physicalSchedule (fun _ => false) _ at schedule
  exact (physical_schedule_bill _ schedule).trans (Nat.mul_le_mul count (Nat.size_le_size count))

end PvsNP.HennieStearnsBuffer

open PvsNP.HennieStearnsBuffer

theorem solution {A : Type} (blank : A) (instructions : List (A × Turn)) :
    let initial := blankBuffer blank
    let result := runBuffer blank initial instructions
    FitsFrom 0 result.1.layers ∧
      glimpse blank result.1 = runSnapshot (glimpse blank initial) instructions ∧
      physicalSchedule (fun _ => false) result.2 ∧
      result.2.length ≤ instructions.length ∧
      bill (result.2.map Prod.fst) ≤ instructions.length*instructions.length.size := by
  obtain ⟨fit, exactView, legal, eventCount⟩ :=
    runBuffer_spec blank (blankBuffer blank) instructions trivial
  exact ⟨fit, exactView, legal, eventCount, runBuffer_geometric_bound blank instructions⟩
