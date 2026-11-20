-- Prove2me | solution 1 for VWZClique.weighted_nine
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T02:10:15.922219+00:00
-- url     : https://prove2.me/submissions/8a43ae9e-911e-4d72-b6e4-5a387daff1a6

import Definitions.Def_VWZClique_Weighted
import Definitions.Def_VWZClique_FoldedSum
import Mathlib
import Theorems.Thm_VWZClique_no_two_wedges
import Theorems.Thm_VWZClique_rank_or_swap
import Theorems.Thm_VWZClique_fold_to_smaller_pattern
import Theorems.Thm_VWZClique_two_projections

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Circuit

/-- Extend any straight-line program, retaining all previous values. -/
def Build {F I : Type*} [Field F] (f : (I → F) → F) (b : ℕ) : Prop :=
  ∀ (r : ℕ) (p : Program F I r), ∃ (n : ℕ) (q : Program F I n) (out : Fin n) (old : Fin r → Fin n),
    q.cost ≤ p.cost + b ∧ (∀ w, q.eval w out = f w) ∧ ∀ w i, q.eval w (old i) = p.eval w i

variable {F I : Type*} [Field F]

theorem cost_mono {f : (I → F) → F} {a b : ℕ} (h : Build f a) (hab : a ≤ b) : Build f b := by
  intro r p
  obtain ⟨n,q,out,old,hc,ho,hi⟩ := h r p
  exact ⟨n,q,out,old,by omega,ho,hi⟩

theorem const (c : F) : Build (fun _ : I → F => c) 0 := by
  intro r p
  exact ⟨r+1,.step p (.constant c),0,Fin.succ,by simp [Program.cost,Gate.cost],fun _ => rfl,fun _ _ => rfl⟩

theorem read (i : I) : Build (fun w : I → F => w i) 0 := by
  intro r p
  exact ⟨r+1,.step p (.input i),0,Fin.succ,by simp [Program.cost,Gate.cost],fun _ => rfl,fun _ _ => rfl⟩

theorem binary {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b)
    (fn : F → F → F) (gate : ∀ {n : ℕ}, Fin n → Fin n → Gate F I (Fin n))
    (cost : ∀ {n : ℕ} (i j : Fin n), (gate i j).cost ≤ 1)
    (eval : ∀ {n : ℕ} (w : I → F) (v : Fin n → F) i j, (gate i j).eval w v = fn (v i) (v j)) :
    Build (fun w => fn (f w) (g w)) (a+b+1) := by
  intro r p
  obtain ⟨r₁,p₁,o₁,old₁,h₁,e₁,l₁⟩ := hf r p
  obtain ⟨r₂,p₂,o₂,old₂,h₂,e₂,l₂⟩ := hg r₁ p₁
  let g' := gate (old₂ o₁) o₂
  refine ⟨r₂+1,.step p₂ g',0,fun i => (old₂ (old₁ i)).succ,?_,?_,?_⟩
  · have hc := cost (old₂ o₁) o₂
    change p₂.cost + (gate (old₂ o₁) o₂).cost ≤ _
    omega
  · intro w
    change (gate _ _).eval _ _ = _
    rw [eval,l₂,e₁,e₂]
  · intro w i
    exact (l₂ w _).trans (l₁ w _)

theorem add {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b) :
    Build (fun w => f w + g w) (a+b+1) :=
  binary hf hg (·+·) Gate.add (fun _ _ => le_rfl) (fun _ _ _ _ => rfl)

theorem mul {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b) :
    Build (fun w => f w * g w) (a+b+1) :=
  binary hf hg (·*·) Gate.mul (fun _ _ => le_rfl) (fun _ _ _ _ => rfl)

theorem sum {J : Type*} (s : Finset J) (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j ∈ s, Build (f j) b) :
    Build (fun w => ∑ j ∈ s, f j w) (s.card * (b+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (I := I) (0:F))
  | @insert j s hj ih =>
    have h' := add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [hj,Finset.card_insert_of_notMem, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

theorem prod {J : Type*} (s : Finset J) (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j ∈ s, Build (f j) b) :
    Build (fun w => ∏ j ∈ s, f j w) (s.card * (b+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (I := I) (1:F))
  | @insert j s hj ih =>
    have h' := mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [hj,Finset.card_insert_of_notMem, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

theorem computes {f : (I → F) → F} {b : ℕ} (hf : Build f b) :
    computesWithin f b := by
  obtain ⟨r,p,out,_,hc,he,_⟩ := hf 0 .nil
  exact ⟨r,p,out,by exact_mod_cast (by simpa [Program.cost] using hc : p.cost ≤ b),he⟩

end VWZClique.Circuit

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.FoldProof

/-- Compute every member of a finite table, retaining its output register. -/
theorem tabulate {F I J : Type*} [Field F] [Fintype J] (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j, Circuit.Build (f j) b) :
    ∃ (r : ℕ) (p : Program F I r) (out : J → Fin r),
      p.cost ≤ Fintype.card J * b ∧ ∀ w j, p.eval w (out j) = f j w := by
  classical
  have part (s : Finset J) : ∃ (r : ℕ) (p : Program F I r) (out : (j:J) → j ∈ s → Fin r),
      p.cost ≤ s.card*b ∧ ∀ w j hj, p.eval w (out j hj) = f j w := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨0,.nil,fun _ h => False.elim (by simp at h),by simp [Program.cost],fun _ _ h => False.elim (by simp at h)⟩
    | @insert j s hj ih =>
      obtain ⟨n,p,out,hc,he⟩ := ih
      obtain ⟨r,q,o,old,hc',ho,hold⟩ := h j n p
      refine ⟨r,q,fun i hi => if h : i=j then o else old (out i (by simpa [h] using hi)), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hj,Nat.succ_mul]
        omega
      · intro w i hi
        by_cases hij : i=j
        · subst i; simpa using ho w
        · simpa [hij,hold] using he w i (by simpa [hij] using hi)
  obtain ⟨r,p,out,hc,he⟩ := part Finset.univ
  exact ⟨r,p,fun j => out j (Finset.mem_univ _),hc,fun w j => he w j _⟩

abbrev Kind := V ⊕ V × V

def kind (p : V × V) : Kind :=
  if p.1=p.2 then .inl p.1 else if p.1<p.2 then .inr p else .inr (p.2,p.1)

def shape {n : ℕ} : WeightKey n → Kind
  | .inl (i,_) => .inl i
  | .inr (i,j,_,_) => .inr (i,j)

def addressValue {n : ℕ} : WeightKey n → V → Fin n
  | .inl (_,x), _ => x
  | .inr (i,_,x,y), k => if k=i then x else y

def weightAt {n : ℕ} (x : V → Fin n) : Kind → WeightKey n
  | .inl i => .inl (i,x i)
  | .inr (i,j) => .inr (i,j,x i,x j)

theorem value_at_ends {n : ℕ} (x : V → Fin n) (p : V × V) :
    addressValue (weightAt x (kind p)) p.1 = x p.1 ∧
    addressValue (weightAt x (kind p)) p.2 = x p.2 := by
  obtain ⟨i,j⟩ := p
  by_cases h : i=j
  · subst j; simp [kind,weightAt,addressValue]
  · by_cases h' : i < j <;> simp [kind,weightAt,addressValue,h,h',Ne.symm h]

theorem oriented (p : V × V) (i j : V) (h : kind p = .inr (i,j)) :
    i < j ∧ (p = (i,j) ∨ p = (j,i)) := by
  obtain ⟨u,v⟩ := p
  by_cases huv : u=v
  · simp [kind,huv] at h
  · by_cases hlt : u<v
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨hlt,Or.inl rfl⟩
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm huv),Or.inr rfl⟩

def collect {F I T : Type*} [Field F] [Fintype T] {n : ℕ} (ep : T → V × V)
    (f : T → Fin n → Fin n → (I → F) → F) (k : WeightKey n) (w : I → F) : F :=
  ∏ t ∈ Finset.univ.filter (fun t => kind (ep t) = shape k),
    f t (addressValue k (ep t).1) (addressValue k (ep t).2) w

/-- Combine all input factors assigned to the same unary or unordered edge
weight. The upper triangular ordering is the one used by weightedSum. -/
theorem compile_weights {F I T : Type*} [Field F] [Fintype T] {n : ℕ}
    (H : SimpleGraph V) (ep : T → V × V)
    (edge : ∀ t, (ep t).1 ≠ (ep t).2 → H.Adj (ep t).1 (ep t).2)
    (f : T → Fin n → Fin n → (I → F) → F) (hf : ∀ t x y, Circuit.Build (f t x y) 0) :
    ∃ (r : ℕ) (p : Program F I r) (out : WeightKey n → Fin r),
      p.cost ≤ Fintype.card (WeightKey n) * Fintype.card T ∧ ∀ w,
      weightedSum H (fun k => p.eval w (out k)) =
        ∑ x : V → Fin n, ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
  classical
  have build (k : WeightKey n) : Circuit.Build (collect ep f k) (Fintype.card T) := by
    let s := Finset.univ.filter (fun t => kind (ep t) = shape k)
    exact Circuit.cost_mono (Circuit.prod s _ 0 (fun t _ => hf t _ _)) (by simpa using Finset.card_le_univ s)
  obtain ⟨r,p,out,hc,he⟩ := tabulate _ _ build
  refine ⟨r,p,out,hc,?_⟩
  intro w
  have take (x : V → Fin n) (b : Kind) : collect ep f (weightAt x b) w =
      ∏ t ∈ Finset.univ.filter (fun t => kind (ep t) = b), f t (x (ep t).1) (x (ep t).2) w := by
    have hs : shape (weightAt x b) = b := by cases b with | inl _ => rfl | inr v => rcases v with ⟨_,_⟩; rfl
    unfold collect
    rw [hs]
    refine Finset.prod_congr rfl ?_
    intro t ht
    have h := (Finset.mem_filter.mp ht).2
    subst b
    rw [(value_at_ends x (ep t)).1,(value_at_ends x (ep t)).2]
  have inactive (x : V → Fin n) (i j : V) (h : ¬ (i < j ∧ H.Adj i j)) :
      collect ep f (weightAt x (.inr (i,j))) w = 1 := by
    rw [take]
    apply Finset.prod_eq_one
    intro t ht
    obtain ⟨hlt,hp|hp⟩ := oriented _ _ _ (Finset.mem_filter.mp ht).2
    · have hadj := edge t (by simpa [hp] using hlt.ne)
      exact (h ⟨hlt, by simpa [hp] using hadj⟩).elim
    · have hadj := edge t (by simpa [hp] using hlt.ne')
      exact (h ⟨hlt, by simpa [hp] using hadj.symm⟩).elim
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [he]
  have allKeys : (∏ b : Kind, collect ep f (weightAt x b) w) =
      ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
    simp_rw [take]
    exact Finset.prod_fiberwise _ _ _
  rw [← allKeys,Fintype.prod_sum_type,Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : i < j ∧ H.Adj i j
  · simp [h,weightAt]
  · simpa only [if_neg h] using (inactive x i j h).symm

end VWZClique.FoldProof

open VWZClique
namespace VWZClique.FoldProof

abbrev Quad := Bool × Bool × Bool × Bool

def pin {L : ℕ} (m : Option (Mask L)) (read : Quad → Bool) (u : Bits L) : Prop :=
  match m with
  | none => True
  | some mask => ∀ i r, mask i = some r → u i = read r

def restore {L : ℕ} (m : Mask L) (read : Quad → Bool) (u : Bits L) : Bits L :=
  fun i => (m i).elim (u i) read

def post {L : ℕ} (m : Option (Mask L)) (x : PairBits L) : PairBits L :=
  match m with
  | none => x
  | some mask => (restore mask (fun r => r.2.2.1) x.2, restore mask (fun r => r.2.2.2) x.1)

open Classical in
noncomputable def flag {F : Type*} [Field F] {L : ℕ} (m : Option (Mask L)) (read : Quad → Bool)
    (u : Bits L) : F := if pin m read u then 1 else 0

theorem support {L : ℕ} (m : Mask L) (x y : PairBits L) :
    swapOK m x y ↔ pin (some m) Prod.fst x.1 ∧ pin (some m) (fun r => r.2.1) x.2 ∧
      y = post (some m) x := by
  constructor
  · intro h
    have fixed (i : Fin L) (r : Quad) (hi : m i = some r) := h i
    refine ⟨?_,?_,?_⟩
    · intro i r hr
      have hh := h i
      rcases r with ⟨s,u,v,t⟩
      simpa [hr] using congrArg Prod.fst (show (x.1 i,x.2 i,y.1 i,y.2 i) = (s,u,v,t) by simpa [hr] using hh)
    · intro i r hr
      rcases r with ⟨s,u,v,t⟩
      have hh := h i
      simp [hr] at hh
      exact hh.2.1
    · apply Prod.ext <;> funext i <;> have hh := h i <;>
        cases hm : m i with
        | none => simp [hm] at hh; simp [post,restore,hm]; grind
        | some r => rcases r with ⟨s,u,v,t⟩; simp [hm] at hh; simp [post,restore,hm]; grind
  · rintro ⟨h₁,h₂,rfl⟩ i
    cases h : m i with
    | none => simp [post,restore,h]
    | some r =>
      obtain ⟨s,u,v,t⟩ := r
      simp [post,restore,h,h₁ i _ h,h₂ i _ h]

theorem kernel_eq {F : Type*} [Field F] {L : ℕ} (m : Option (Mask L)) (x y : PairBits L) :
    maskKernel (F := F) m x y = if y = post m x then
      flag m Prod.fst x.1 * flag m (fun r => r.2.1) x.2 else 0 := by
  classical
  cases m with
  | none => simp [post,maskKernel,flag,pin,eq_comm]
  | some m =>
    simp only [maskKernel,support,flag]
    split_ifs <;> simp_all

theorem sum_kernels {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L))
    (f : PairBits L → PairBits L → PairBits L → PairBits L → F) :
    (∑ x, ∑ x', ∑ y, ∑ y', maskKernel a x x' * maskKernel b y y' * f x x' y y') =
    ∑ x, ∑ y, ((flag a Prod.fst x.1 * flag a (fun r => r.2.1) x.2) *
      (flag b Prod.fst y.1 * flag b (fun r => r.2.1) y.2)) * f x (post a x) y (post b y) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp [kernel_eq, mul_ite, ite_mul]

end VWZClique.FoldProof

open VWZClique
namespace VWZClique.FoldProof

def site (g i : Fin 3) : V := finProdFinEquiv (g,i)
def next (h : Fin 3) : Fin 3 := ![1,2,0] h
def perm {L : ℕ} (m : Option (Mask L)) (i : Fin 3) : Fin 3 :=
  if m.isSome then ![1,0,2] i else i

def adjust {L : ℕ} (m : Option (Mask L)) (i : Fin 3) (s : Bits L) : Bits L :=
  match m with
  | none => s
  | some m => ![restore m (fun r => r.2.2.1) s, restore m (fun r => r.2.2.2) s,s] i

def route {L : ℕ} (a b : Option (Mask L)) (h : Fin 3) : Slot → V × (Bits L → Bits L)
  | .inl i => if h=1 then (site h (perm b i),adjust b i) else (site h i,id)
  | .inr i => if h=2 then (site (next h) (perm a i),adjust a i) else (site (next h) i,id)

def slotWord {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) (h : Fin 3) (i : Slot) : Bits L :=
  (route a b h i).2 (X (route a b h i).1)

abbrev Packed (L : ℕ) := Bits L × Bits L × Block L × PairBits L × PairBits L

def unpack {L : ℕ} (z : Packed L) : V → Bits L := fun v =>
  let p := (finProdFinEquiv (m := 3) (n := 3)).symm v
  (![block z.2.2.2.1 z.1, block z.2.2.2.2 z.2.1, z.2.2.1] p.1) p.2

@[simp] theorem unpack_site {L : ℕ} (z : Packed L) (g i : Fin 3) :
    unpack z (site g i) = (![block z.2.2.2.1 z.1,block z.2.2.2.2 z.2.1,z.2.2.1] g) i := by
  simp only [unpack,site,Equiv.symm_apply_apply]

def packEquiv (L : ℕ) : (V → Bits L) ≃ Packed L where
  toFun X := (X (site 0 2),X (site 1 2),fun i => X (site 2 i),
    (X (site 0 0),X (site 0 1)),(X (site 1 0),X (site 1 1)))
  invFun := unpack
  left_inv := by
    intro X
    funext v
    obtain ⟨⟨g,i⟩,rfl⟩ := (finProdFinEquiv (m := 3) (n := 3)).surjective v
    fin_cases g <;> fin_cases i <;> rfl
  right_inv := by
    rintro ⟨z₁,z₂,c,x,y⟩
    simp [block, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem routed_slots {L : ℕ} (a b : Option (Mask L)) (z₁ z₂ : Bits L) (c : Block L)
    (x y : PairBits L) (h : Fin 3) (s : Slot) :
    slotWord a b (unpack (z₁,z₂,c,x,y)) h s =
    Sum.elim (![block x z₁,block (post b y) z₂,c] h)
      (![block y z₂,c,block (post a x) z₁] h) s := by
  cases s with
  | inl i => fin_cases h <;> fin_cases i <;> cases b <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]
  | inr i => fin_cases h <;> fin_cases i <;> cases a <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]

noncomputable def unary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (v : Fin 3 × Slot) : F :=
  w (v.1,.inl (v.2,slotWord a b X v.1 v.2))

noncomputable def binary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (e : EdgeSlot) : F :=
  w (e.1,.inr (e.2.1,e.2.2,slotWord a b X e.1 e.2.1,slotWord a b X e.1 e.2.2))

theorem channels_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (z₁ z₂ : Bits L) (c : Block L) (x y : PairBits L) (w : ChannelKey L → F) :
    let X := unpack (z₁,z₂,c,x,y)
    placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block (post b y) z₂) c *
    placedChannel E w 2 c (block (post a x) z₁) =
    (∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e := by
  classical
  let X := unpack (z₁,z₂,c,x,y)
  let row := ![block x z₁,block (post b y) z₂,c]
  let col := ![block y z₂,c,block (post a x) z₁]
  have chan (h : Fin 3) : placedChannel E w h (row h) (col h) =
      (∏ s : Slot, unary a b X w (h,s)) * ∏ e ∈ E, if e.1=h then binary a b X w e else 1 := by
    unfold placedChannel unary binary
    dsimp only
    apply congrArg₂ (·*·)
    · simp only [X,row,col,routed_slots]
    · apply Finset.prod_congr rfl
      intro e he
      by_cases hh : e.1=h
      · subst h
        simp [X,row,col,routed_slots]
      · simp [hh]
  have allRows := Finset.prod_congr (s₁ := Finset.univ) rfl (fun h _ => chan h)
  rw [Finset.prod_mul_distrib] at allRows
  rw [Finset.prod_comm (f := fun h e => if e.1=h then binary a b X w e else 1)] at allRows
  simp only [Finset.prod_ite_eq,Finset.mem_univ,if_true] at allRows
  dsimp only
  rw [Fintype.prod_prod_type]
  convert! allRows using 1
  rw [Fin.prod_univ_three]
  rfl

noncomputable def checks {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) : F :=
  (flag a Prod.fst (X (site 0 0)) * flag a (fun r => r.2.1) (X (site 0 1))) *
  (flag b Prod.fst (X (site 1 0)) * flag b (fun r => r.2.1) (X (site 1 1)))

private theorem five_sums {A B C D E F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [AddCommMonoid F] (f : A × B × C × D × E → F) :
    ∑ z, f z = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f (a,b,c,d,e) := by simp only [Fintype.sum_prod_type]

theorem reindexed {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (w : ChannelKey L → F) :
    placedFold E a b w = ∑ X : V → Bits L, checks a b X *
      ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  classical
  let expr := fun X : V → Bits L => checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e)
  rw [← (packEquiv L).symm.sum_comp expr]
  rw [five_sums (D := PairBits L) (E := PairBits L)]
  unfold placedFold
  apply Finset.sum_congr rfl
  intro z₁ _
  apply Finset.sum_congr rfl
  intro z₂ _
  apply Finset.sum_congr rfl
  intro c _
  let f := fun x x' y y' => placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  have h := sum_kernels a b f
  dsimp only [f] at h
  simp only [mul_assoc] at h ⊢
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hc := channels_product a b E z₁ z₂ c x y w
  dsimp only at hc
  change _ = expr (unpack (z₁,z₂,c,x,y))
  unfold expr
  rw [← hc]
  simp [checks,block,mul_assoc,Fin.isValue]

end VWZClique.FoldProof

open VWZClique VWZClique.FoldProof OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

def endpoint (h : Fin 3) : Slot → V
  | .inl i => site h i
  | .inr i => site (next h) i

def locate (u v : V) : EdgeSlot :=
  let a := (finProdFinEquiv (m := 3) (n := 3)).symm u
  let b := (finProdFinEquiv (m := 3) (n := 3)).symm v
  if a.1 = b.1 then
    if a.2 = 1 ∧ b.2 = 2 then (![2,0,1] a.1,.inr a.2,.inr b.2)
    else (a.1,.inl a.2,.inl b.2)
  else if next a.1 = b.1 then (a.1,.inl a.2,.inr b.2)
  else (b.1,.inr a.2,.inl b.2)

def ends (e : EdgeSlot) : V × V := (endpoint e.1 e.2.1, endpoint e.1 e.2.2)

theorem locate_ends : ∀ u v : V, ends (locate u v) = (u,v) := by decide

def chosen (π : Equiv.Perm V) (p : V × V) : EdgeSlot :=
  locate (min (π.symm p.1) (π.symm p.2)) (max (π.symm p.1) (π.symm p.2))

theorem chosen_ends (π : Equiv.Perm V) (p : V × V) :
    ends (chosen π p) = (π.symm p.1,π.symm p.2) ∨
      ends (chosen π p) = (π.symm p.2,π.symm p.1) := by
  by_cases h : π.symm p.1 ≤ π.symm p.2
  · simp [chosen,locate_ends,min_eq_left h,max_eq_right h]
  · simp [chosen,locate_ends,min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)]

open Classical in
noncomputable def pairs (H : SimpleGraph V) : Finset (V × V) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ H.Adj p.1 p.2

theorem pairs_card (H : SimpleGraph V) : (pairs H).card ≤ Nat.card H.edgeSet := by
  classical
  let mapEdge : ↥(pairs H) → H.edgeSet := fun p =>
    ⟨s(p.val.1,p.val.2),(Finset.mem_filter.mp p.property).2.2⟩
  have hinj : Function.Injective mapEdge := by
    intro p q hpq
    obtain ⟨p,hp⟩ := p
    obtain ⟨q,hq⟩ := q
    apply Subtype.ext
    obtain ⟨hp,_⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨hq,_⟩ := (Finset.mem_filter.mp hq).2
    have huv : s(p.1,p.2) = s(q.1,q.2) := congrArg Subtype.val hpq
    rcases Sym2.eq_iff.mp huv with huv|huv
    · exact Prod.ext huv.1 huv.2
    · exact (not_lt_of_ge hq.le (by simpa only [huv.1,huv.2] using hp)).elim
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective mapEdge hinj

theorem chosen_inj (π : Equiv.Perm V) (H : SimpleGraph V) : Set.InjOn (chosen π) (↑(pairs H)) := by
  classical
  intro p hp q hq he
  have hp' := (Finset.mem_filter.mp hp).2.1
  have hq' := (Finset.mem_filter.mp hq).2.1
  have hinv (a b : V) : π.symm a = π.symm b ↔ a=b := π.symm.injective.eq_iff
  have h := congrArg ends he
  rcases chosen_ends π p with p1|p2 <;> rcases chosen_ends π q with q1|q2 <;>
    simp_all [Prod.ext_iff] <;> exact (lt_asymm hq' hp').elim

noncomputable def slots (π : Equiv.Perm V) (H : SimpleGraph V) : Finset EdgeSlot :=
  (pairs H).image (chosen π)

theorem slots_card (π : Equiv.Perm V) (H : SimpleGraph V) :
    (slots π H).card ≤ Nat.card H.edgeSet := Finset.card_image_le.trans (pairs_card H)

theorem slots_adj (π : Equiv.Perm V) (H : SimpleGraph V) {u v : V} (hlt : u<v)
    (h : H.Adj (π u) (π v)) : locate u v ∈ slots π H := by
  classical
  have ne : π u ≠ π v := π.injective.ne hlt.ne
  rcases lt_or_gt_of_ne ne with hnum|hnum
  · exact Finset.mem_image.mpr ⟨(π u,π v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnum,h⟩,
      by simp [chosen,min_eq_left hlt.le,max_eq_right hlt.le]⟩
  · exact Finset.mem_image.mpr ⟨(π v,π u),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnum,h.symm⟩,
      by simp [chosen,min_eq_right hlt.le,max_eq_left hlt.le]⟩

theorem place_wedges (H : SimpleGraph V) (f g : Fin 3 → V)
    (hf : wedge H f) (hg : wedge H g) (hfg : ∀ i j, f i ≠ g j) :
    ∃ π : Equiv.Perm V, wedgePlaced (slots π H) 0 2 ∧ wedgePlaced (slots π H) 1 0 := by
  let sites : Slot → V := Sum.elim ![0,2,1] ![3,5,4]
  let verts := Sum.elim f g
  have hs : Function.Injective sites := by decide
  have hv : Function.Injective verts := by
    intro v w h
    rcases v with i|i <;> rcases w with j|j
    · exact congrArg Sum.inl (hf.1 h)
    · exact (hfg _ _ h).elim
    · exact (hfg _ _ h.symm).elim
    · exact congrArg Sum.inr (hg.1 h)
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair sites verts hs hv
  have A (i : Fin 3) : π (![0,2,1] i) = f i := hπ (.inl i)
  have B (i : Fin 3) : π (![3,5,4] i) = g i := hπ (.inr i)
  refine ⟨π,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact slots_adj π H (u:=0) (v:=2) (by decide) (by simpa [← A 0,← A 1] using hf.2.1)
  · exact slots_adj π H (u:=1) (v:=2) (by decide) (by simpa [← A 2,← A 1] using hf.2.2.symm)
  · exact slots_adj π H (u:=3) (v:=5) (by decide) (by simpa [← B 0,← B 1] using hg.2.1)
  · exact slots_adj π H (u:=4) (v:=5) (by decide) (by simpa [← B 2,← B 1] using hg.2.2.symm)

end VWZClique.WeightedProof

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

variable {F I J : Type*} [Field F]

def literal (w : I → F) : I ⊕ F → F := Sum.elim w id

def translateGate {r : ℕ} (tag : J → I ⊕ F) : Gate F J (Fin r) → Gate F I (Fin r)
  | .input j => (tag j).elim Gate.input Gate.constant
  | .constant c => .constant c
  | .add x y => .add x y
  | .sub x y => .sub x y
  | .mul x y => .mul x y

def translate (tag : J → I ⊕ F) : {r : ℕ} → Program F J r → Program F I r
  | _,.nil => .nil
  | _,.step p gate => .step (translate tag p) (translateGate tag gate)

omit [Field F] in
theorem translate_cost (tag : J → I ⊕ F) {r : ℕ} (p : Program F J r) :
    (translate tag p).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih =>
    simp only [translate,Program.cost,ih]
    congr 1
    cases g with
    | input j => cases ht : tag j <;> simp [translateGate,ht,Gate.cost]
    | _ => rfl

theorem translate_eval (tag : J → I ⊕ F) {r : ℕ} (p : Program F J r) (w : I → F) :
    (translate tag p).eval w = p.eval (fun j => literal w (tag j)) := by
  induction p with
  | nil => rfl
  | step p g ih =>
    simp only [translate,Program.eval,ih]
    cases g with
    | input j => cases ht : tag j <;> simp [translateGate,ht,Gate.eval,literal]
    | _ => rfl

theorem translated {f : (J → F) → F} {B : ℝ} (h : computesWithin f B) (tag : J → I ⊕ F) :
    computesWithin (fun w => f (fun j => literal w (tag j))) B := by
  obtain ⟨r,p,o,hc,he⟩ := h
  exact ⟨r,translate tag p,o,by rwa [translate_cost],fun w => by rw [translate_eval,he]⟩

def padTag {n N : ℕ} : WeightKey N → WeightKey n ⊕ F
  | .inl (i,x) => if h : x.val < n then .inl (.inl (i,⟨x,h⟩)) else .inr 0
  | .inr (i,j,x,y) => if h : x.val < n ∧ y.val < n then .inl (.inr (i,j,⟨x,h.1⟩,⟨y,h.2⟩)) else .inr 0

theorem weights_padded {n N : ℕ} (hn : n ≤ N) (H : SimpleGraph V) (w : WeightKey n → F) :
    weightedSum H (fun k : WeightKey N => literal w (padTag k)) = weightedSum H w := by
  classical
  let up : (V → Fin n) → V → Fin N := fun a i => (a i).castLE hn
  have inj : Function.Injective up := by
    intro a b h
    funext i
    exact Fin.ext (congrArg (fun x : Fin N => x.val) (congrFun h i))
  symm
  unfold weightedSum
  apply Fintype.sum_of_injective up inj
  · intro a ha
    have hex : ∃ i, ¬ (a i).val < n := by
      by_contra! h
      exact ha ⟨fun i => ⟨a i,h i⟩,rfl⟩
    obtain ⟨i,hi⟩ := hex
    have hz : (∏ j, literal w (padTag (Sum.inl (j,a j)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [padTag,hi,literal])
    simp [hz]
  · intro a
    simp [up,padTag,literal]

theorem padding {n N : ℕ} (hn : n ≤ N) (H : SimpleGraph V) {B : ℝ}
    (h : computesWithin (weightedSum (F := F) (n := N) H) B) :
    computesWithin (weightedSum (F := F) (n := n) H) B := by
  simpa only [weights_padded hn H] using (translated h (padTag (n := n)))

theorem brute {n : ℕ} (H : SimpleGraph V) :
    Circuit.Build (weightedSum (F := F) (n := n) H) ((n^9)*101) := by
  classical
  let un := fun (a : V → Fin n) (i : V) (w : WeightKey n → F) => w (.inl (i,a i))
  let ed := fun (a : V → Fin n) (i j : V) (w : WeightKey n → F) =>
    if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  have bu (a : V → Fin n) : Circuit.Build (fun w => ∏ i, un a i w) 9 :=
    Circuit.prod Finset.univ _ 0 (fun _ _ => Circuit.read _)
  have be (a : V → Fin n) (i j : V) : Circuit.Build (ed a i j) 0 := by
    by_cases h : i<j ∧ H.Adj i j
    · simpa [ed,h] using (Circuit.read (F := F) (Sum.inr (i,j,a i,a j) : WeightKey n))
    · simpa [ed,h] using (Circuit.const (I := WeightKey n) (1:F))
  have bi (a : V → Fin n) (i : V) : Circuit.Build (fun w => ∏ j, ed a i j w) 9 :=
    Circuit.prod Finset.univ _ 0 (fun j _ => be a i j)
  have bp (a : V → Fin n) : Circuit.Build (fun w => ∏ i, ∏ j, ed a i j w) 90 :=
    Circuit.prod Finset.univ _ 9 (fun i _ => bi a i)
  have total := Circuit.sum Finset.univ _ _ (fun a _ => Circuit.mul (bu a) (bp a))
  exact Circuit.cost_mono total (by simp [V])

theorem exists_pow_sandwich {n : ℕ} (hn : 1 ≤ n) : ∃ L : ℕ, n ≤ 2^L ∧ 2^L ≤ 2*n := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt n (by decide : 1 < (2:ℕ))
  let L := Nat.find (⟨k,hk.le⟩ : ∃ k : ℕ, n ≤ 2^k)
  have hL : n ≤ 2^L := Nat.find_spec (⟨k,hk.le⟩ : ∃ k : ℕ, n ≤ 2^k)
  refine ⟨L,hL,?_⟩
  cases h : L with
  | zero => simp; omega
  | succ j =>
    have hj : ¬ n ≤ 2^j := Nat.find_min (⟨k,hk.le⟩ : ∃ k : ℕ, n ≤ 2^k) (by change j<L; omega)
    rw [pow_succ]
    omega

end VWZClique.WeightedProof

open VWZClique VWZClique.FoldProof
namespace VWZClique.WeightedProof

noncomputable def indexWord (L : ℕ) : Bits L ≃ Fin (2^L) :=
  Fintype.equivOfCardEq (by simp [Bits])

def edgeKey {n : ℕ} (i j : V) (x y : Fin n) : WeightKey n :=
  if i<j then .inr (i,j,x,y) else .inr (j,i,y,x)

noncomputable def channelTag {F : Type*} [Field F] {L : ℕ}
    (π : Equiv.Perm V) (E : Finset EdgeSlot) : ChannelKey L → WeightKey (2^L) ⊕ F
  | (h,.inl (.inl i,x)) => .inl (.inl (π (site h i), indexWord L x))
  | (_,.inl (.inr _,_)) => .inr 1
  | (h,.inr (s,t,x,y)) => if (h,s,t) ∈ E then
      .inl (edgeKey (π (endpoint h s)) (π (endpoint h t)) (indexWord L x) (indexWord L y))
    else .inr 1

theorem supported {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (w : WeightKey (2^L) → F) (h : Fin 3) (a b : Block L) :
    let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
    channel inputs h a b = placedChannel E inputs h a b := by
  classical
  dsimp only
  unfold channel placedChannel
  dsimp only
  apply congrArg (fun y : F => _ * y)
  let x := Sum.elim a b
  let v := fun e : EdgeSlot => if e.1=h then literal w
    (channelTag π E (h,.inr (e.2.1,e.2.2,x e.2.1,x e.2.2))) else 1
  have addBack : (∏ e ∈ E, v e) = ∏ e : EdgeSlot, v e := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    by_cases h' : e.1=h
    · obtain ⟨k,s,t⟩ := e
      dsimp only at h'
      subst k
      simp [v,channelTag,he,literal]
    · simp [v,h']
  change _ = ∏ e ∈ E, v e
  rw [addBack,Fintype.prod_prod_type,Finset.prod_comm (f := fun k st => v (k,st))]
  simp only [v,Finset.prod_ite_eq',Finset.mem_univ,if_true]
  rw [Fintype.prod_prod_type]

theorem no_swap_word {L : ℕ} (X : V → Bits L) (h : Fin 3) (s : Slot) :
    slotWord none none X h s = X (endpoint h s) := by
  cases s with
  | inl i => fin_cases h <;> rfl
  | inr i => fin_cases h <;> rfl

theorem encode_graph {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (H : SimpleGraph V)
    (w : WeightKey (2^L) → F) :
    placedFold (slots π H) none none (fun j : ChannelKey L => literal w (channelTag π (slots π H) j)) =
      weightedSum H w := by
  classical
  let E := slots π H
  let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
  let perm := π.arrowCongr (indexWord L)
  rw [reindexed,weightedSum,← perm.sum_comp]
  apply Finset.sum_congr rfl
  intro X _
  let X' := perm X
  have mapped (v : V) : X' (π v) = indexWord L (X v) := by simp [X',perm,Equiv.arrowCongr_apply]
  have mapped' (v : V) : indexWord L (X (π.symm v)) = X' v := rfl
  have uv : (∏ v : Fin 3 × Slot, unary none none X inputs v) =
      ∏ i : V, w (.inl (i,X' i)) := by
    let u := fun i : V => w (Sum.inl (i,X' i))
    rw [← Equiv.prod_comp π u, ← (finProdFinEquiv (m:=3) (n:=3)).prod_comp (fun i => u (π i))]
    rw [Fintype.prod_prod_type,Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro h _
    rw [Fintype.prod_sum_type]
    simp only [unary,inputs,channelTag,literal,Sum.elim_inl,Sum.elim_inr,id_eq,
      Finset.prod_const_one,mul_one,no_swap_word,endpoint,u,mapped,site]
  have ev : (∏ e ∈ E, binary none none X inputs e) =
      ∏ i : V, ∏ j : V, if i < j ∧ H.Adj i j then w (.inr (i,j,X' i,X' j)) else 1 := by
    rw [← Fintype.prod_prod_type (fun p : V × V => if p.1<p.2 ∧ H.Adj p.1 p.2 then
      w (.inr (p.1,p.2,X' p.1,X' p.2)) else 1)]
    rw [← Finset.prod_filter]
    change (∏ e ∈ (pairs H).image (chosen π), binary none none X inputs e) =
      ∏ p ∈ pairs H, w (.inr (p.1,p.2,X' p.1,X' p.2))
    rw [Finset.prod_image (chosen_inj π H)]
    apply Finset.prod_congr rfl
    intro p hp
    let e := chosen π p
    have he : e ∈ E := Finset.mem_image_of_mem _ hp
    have hlt := (Finset.mem_filter.mp hp).2.1
    change literal w (channelTag π E (e.1,.inr (e.2.1,e.2.2,_,_))) = _
    simp only [channelTag,if_pos he,literal,Sum.elim_inl,no_swap_word]
    change w (edgeKey (π (ends e).1) (π (ends e).2) (indexWord L (X (ends e).1)) (indexWord L (X (ends e).2))) = _
    rcases chosen_ends π p with he|he
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,hlt,if_true,mapped']
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,not_lt_of_gt hlt,if_false,mapped']
  have checksOne : checks (F:=F) none none X = 1 := by simp [checks,flag,pin]
  change checks (F:=F) none none X * ((∏ v, unary none none X inputs v) *
      ∏ e ∈ E, binary none none X inputs e) = _
  rw [checksOne,one_mul,uv,ev]

end VWZClique.WeightedProof

open VWZClique
namespace VWZClique.WeightedProof

abbrev KernelArgs (L : ℕ) := PairBits L × PairBits L × PairBits L × PairBits L

noncomputable def evaluate {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (w : ChannelKey L → F) : (KernelArgs L → F) →ₗ[F] F where
  toFun k :=
    ∑ z₁ : Bits L, ∑ z₂ : Bits L, ∑ c : Block L,
      ∑ x : PairBits L, ∑ x' : PairBits L, ∑ y : PairBits L, ∑ y' : PairBits L,
        k (x,x',y,y') * placedChannel E w 0 (block x z₁) (block y z₂) *
          placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  map_add' f g := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum,mul_assoc]

def pairKernel {F : Type*} [Field F] {L : ℕ} (p q : PairBits L → PairBits L → F) :
    KernelArgs L → F := fun z => p z.1 z.2.1 * q z.2.2.1 z.2.2.2

private theorem evalMask {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) :
    evaluate E w (pairKernel (maskKernel a) (maskKernel b)) = placedFold E a b w := by
  rfl

private theorem evalProjection {F : Type*} [Field F] [CharZero F] {L : ℕ} (E : Finset EdgeSlot)
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → F) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    evaluate E w (pairKernel (projected Λ d) (projected Λ d)) = doubleProjection Λ Λ d d w := by
  unfold doubleProjection
  simp_rw [hc]
  rfl

theorem decomposition {F : Type*} [Field F] [CharZero F] {L M : ℕ}
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → ℚ)
    (m : Fin M → Mask L) (c : Fin M → ℤ)
    (hdecomp : ∀ x y : PairBits L,
      (if x = y then (1 : ℚ) else 0) =
        (∑ j ∈ Λ, d j * basisEntry j x * basisEntry j y) +
        ∑ i, (c i : ℚ) * swapEntry (m i) x y)
    (E : Finset EdgeSlot) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    placedFold E none none w =
      doubleProjection Λ Λ (fun j => (d j : F)) (fun j => (d j : F)) w +
      (∑ i, (c i : F) * placedFold E (some (m i)) none w) +
      (∑ j, (c j : F) * placedFold E none (some (m j)) w) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) * placedFold E (some (m i)) (some (m j)) w := by
  classical
  let I := maskKernel (F := F) (L := L) none
  let R := projected Λ (fun j => (d j : F))
  let S := fun i => maskKernel (F := F) (some (m i))
  have hkernel (x y : PairBits L) : I x y = R x y + ∑ i, (c i : F) * S i x y := by
    have eqn := congrArg (fun q : ℚ => (q : F)) (hdecomp x y)
    simpa [I,R,S,maskKernel,projected,swapEntry,apply_ite] using eqn
  have hp : pairKernel I I = pairKernel R R +
      (∑ i, (c i : F) • pairKernel (S i) I) +
      (∑ j, (c j : F) • pairKernel I (S j)) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) • pairKernel (S i) (S j) := by
    funext z
    rcases z with ⟨x,x',y,y'⟩
    simp only [Pi.add_apply,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairKernel]
    simp only [← mul_assoc, ← Finset.sum_mul]
    have swap (j : Fin M) : (c j : F) * I x x' * S j y y' = I x x' * ((c j : F) * S j y y') := by ring
    have both (i j : Fin M) : (c i : F) * (c j : F) * S i x x' * S j y y' =
        ((c i : F) * S i x x') * ((c j : F) * S j y y') := by ring
    simp_rw [swap,both,← Finset.mul_sum,← Finset.sum_mul]
    rw [hkernel x x',hkernel y y']
    ring
  have he := congrArg (evaluate E w) hp
  simpa [I,R,S,map_sum,evalMask,evalProjection E Λ _ w hc] using he

end VWZClique.WeightedProof

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.MM

variable {F I J K O : Type*} [Field F]

def Table (f : (I → F) → O → F) (b : ℕ) : Prop :=
  ∃ (n : ℕ) (p : Program F I n) (out : O → Fin n),
    p.cost ≤ b ∧ ∀ w o, p.eval w (out o) = f w o

inductive Source (F I : Type*) (r : ℕ) where
  | old (i : Fin r)
  | input (i : I)
  | constant (c : F)

def Source.eval {r : ℕ} (w : I → F) (v : Fin r → F) : Source F I r → F
  | .old i => v i
  | .input i => w i
  | .constant c => c

/-- Append a program, wiring each input to a register, external input or constant. -/
theorem runAlong {r m : ℕ} (p : Program F I r) (q : Program F J m)
    (src : J → Source F I r) :
    ∃ (n : ℕ) (s : Program F I n) (old : Fin r → Fin n) (new : Fin m → Fin n),
      s.cost ≤ p.cost + q.cost ∧
      (∀ w i, s.eval w (old i) = p.eval w i) ∧
      ∀ w i, s.eval w (new i) = q.eval (fun j => (src j).eval w (p.eval w)) i := by
  induction q with
  | nil => exact ⟨_,p,id,Fin.elim0,by simp [Program.cost],fun _ _ => rfl,fun _ i => Fin.elim0 i⟩
  | @step m q g ih =>
    obtain ⟨n,s,old,new,hc,ho,hn⟩ := ih
    let v := fun w (j : J) => (src j).eval w (p.eval w)
    have push (g' : Gate F I (Fin n)) (hcost : g'.cost ≤ g.cost)
        (heval : ∀ w, g'.eval w (s.eval w) = g.eval (v w) (q.eval (v w))) :
        ∃ (l : ℕ) (t : Program F I l) (a : Fin r → Fin l) (b : Fin (m+1) → Fin l),
          t.cost ≤ p.cost + (q.step g).cost ∧
          (∀ w i, t.eval w (a i) = p.eval w i) ∧
          ∀ w i, t.eval w (b i) = (q.step g).eval (v w) i := by
      refine ⟨n+1,s.step g',fun i => (old i).succ,Fin.cases 0 (fun i => (new i).succ),?_,
        fun w i => ho w i,?_⟩
      · change s.cost + g'.cost ≤ p.cost + (q.cost + g.cost)
        omega
      · intro w i
        refine Fin.cases (heval w) (fun j => hn w j) i
    cases g with
    | constant c => exact push (.constant c) le_rfl (fun _ => rfl)
    | add i j => exact push (.add (new i) (new j)) le_rfl (fun w => congrArg₂ (·+·) (hn w i) (hn w j))
    | sub i j => exact push (.sub (new i) (new j)) le_rfl (fun w => congrArg₂ (·-·) (hn w i) (hn w j))
    | mul i j => exact push (.mul (new i) (new j)) le_rfl (fun w => congrArg₂ (·*·) (hn w i) (hn w j))
    | input j =>
      cases hj : src j with
      | old i =>
        refine ⟨_,s,old,Fin.cases (old i) new,by simpa [Program.cost,Gate.cost] using hc,ho,?_⟩
        intro w k
        refine Fin.cases ?_ (fun j' => hn w j') k
        change s.eval w (old i) = (src j).eval w (p.eval w)
        simpa [hj,Source.eval] using ho w i
      | input i =>
        apply push (.input i) le_rfl
        intro w
        change w i = (src j).eval w (p.eval w)
        rw [hj]; rfl
      | constant c =>
        apply push (.constant c) le_rfl
        intro w
        change c = (src j).eval w (p.eval w)
        rw [hj]; rfl

theorem splice {r m : ℕ} (p : Program F I r) (q : Program F J m) (ix : J → Fin r) :
    ∃ (n : ℕ) (s : Program F I n) (old : Fin r → Fin n) (new : Fin m → Fin n),
      s.cost ≤ p.cost + q.cost ∧ (∀ w i, s.eval w (old i) = p.eval w i) ∧
      ∀ w i, s.eval w (new i) = q.eval (fun j => p.eval w (ix j)) i :=
  runAlong p q (fun j => .old (ix j))

theorem cost_mono {f : (I → F) → O → F} {a b : ℕ} (hf : Table f a) (hab : a ≤ b) :
    Table f b := by
  obtain ⟨n,p,out,hc,he⟩ := hf
  exact ⟨n,p,out,hc.trans hab,he⟩

theorem congr {f g : (I → F) → O → F} {b : ℕ} (hf : Table f b)
    (h : ∀ w o, f w o = g w o) : Table g b := by
  obtain ⟨n,p,out,hc,he⟩ := hf
  exact ⟨n,p,out,hc,fun w o => (he w o).trans (h w o)⟩

theorem outmap {f : (I → F) → O → F} {a : ℕ} (hf : Table f a) (ix : K → O) :
    Table (fun w k => f w (ix k)) a := by
  obtain ⟨n,p,out,hc,he⟩ := hf
  exact ⟨n,p,fun k => out (ix k),hc,fun w k => he w (ix k)⟩

theorem bind {f : (I → F) → J → F} {g : (J → F) → K → F} {a b : ℕ}
    (hf : Table f a) (hg : Table g b) : Table (fun w => g (f w)) (a+b) := by
  obtain ⟨n,p,out,hc,he⟩ := hf
  obtain ⟨m,q,z,hd,ht⟩ := hg
  obtain ⟨l,s,_,new,hs,_,hq⟩ := splice p q out
  refine ⟨l,s,fun k => new (z k),by omega,fun w k => ?_⟩
  rw [hq,ht]
  exact congrArg (fun v => g v k) (funext (he w))

theorem pair {f : (I → F) → J → F} {g : (I → F) → K → F} {a b : ℕ}
    (hf : Table f a) (hg : Table g b) : Table (fun w => Sum.elim (f w) (g w)) (a+b) := by
  obtain ⟨n,p,out,hc,he⟩ := hf
  obtain ⟨m,q,z,hd,ht⟩ := hg
  obtain ⟨l,s,old,new,hs,hp,hq⟩ := runAlong p q (fun i => .input i)
  refine ⟨l,s,Sum.elim (old ∘ out) (new ∘ z),by omega,?_⟩
  intro w o
  cases o with
  | inl j => exact (hp w _).trans (he w j)
  | inr k => exact (hq w _).trans (ht w k)

theorem inmap {f : (J → F) → O → F} {a : ℕ} (hf : Table f a) (ix : J → I) :
    Table (fun w => f (fun j => w (ix j))) a := by
  obtain ⟨m,q,z,hd,ht⟩ := hf
  obtain ⟨l,s,_,new,hs,_,hq⟩ := runAlong (.nil : Program F I 0) q (fun j => .input (ix j))
  refine ⟨l,s,fun o => new (z o),?_,fun w o => (hq w _).trans (ht _ o)⟩
  simpa [Program.cost] using hs.trans (Nat.add_le_add_left hd 0)

theorem inmapConst {f : (J → F) → O → F} {a : ℕ} (hf : Table f a) (ix : J → I ⊕ F) :
    Table (fun w => f (fun j => (ix j).elim w id)) a := by
  obtain ⟨m,q,z,hd,ht⟩ := hf
  let src : J → Source F I 0 := fun j => (ix j).elim .input .constant
  obtain ⟨l,s,_,new,hs,_,hq⟩ := runAlong (.nil : Program F I 0) q src
  refine ⟨l,s,fun o => new (z o),?_,fun w o => ?_⟩
  · simpa [Program.cost] using hs.trans (Nat.add_le_add_left hd 0)
  · rw [hq,ht]
    apply congrArg (fun v => f v o)
    funext j
    cases h : ix j <;> simp [src,h,Source.eval]

theorem ofBuild {f : (I → F) → F} {b : ℕ} (h : Circuit.Build f b) :
    Table (fun w (_ : Unit) => f w) b := by
  obtain ⟨n,p,out,_,hc,he,_⟩ := h 0 .nil
  exact ⟨n,p,fun _ => out,by simpa [Program.cost] using hc,fun w _ => he w⟩

theorem toBuild {f : (I → F) → O → F} {a : ℕ} (hf : Table f a) (o : O) :
    Circuit.Build (fun w => f w o) a := by
  intro r p
  obtain ⟨m,q,z,hd,ht⟩ := hf
  obtain ⟨l,s,old,new,hs,hp,hq⟩ := runAlong p q (fun i => .input i)
  exact ⟨l,s,new (z o),old,hs.trans (Nat.add_le_add_left hd _),fun w => (hq w _).trans (ht w o),hp⟩

theorem parallelFin (n : ℕ) (f : Fin n → (I → F) → O → F) (b : ℕ)
    (h : ∀ j, Table (f j) b) : Table (fun w (jo : Fin n × O) => f jo.1 w jo.2) (n*b) := by
  induction n with
  | zero => exact ⟨0,.nil,fun x => Fin.elim0 x.1,by simp [Program.cost],fun _ x => Fin.elim0 x.1⟩
  | succ n ih =>
    have ht := ih (fun j => f j.succ) (fun j => h j.succ)
    have ht' := pair (h 0) ht
    let ix (jo : Fin (n+1) × O) : O ⊕ (Fin n × O) :=
      Fin.cases (.inl jo.2) (fun j => .inr (j,jo.2)) jo.1
    apply cost_mono (congr (outmap ht' ix) ?_) (by simp [Nat.succ_mul,Nat.add_comm])
    rintro w ⟨j,o⟩
    refine Fin.cases rfl (fun _ => rfl) j

theorem parallel {X : Type*} [Fintype X] (f : X → (I → F) → O → F) (b : ℕ)
    (h : ∀ x, Table (f x) b) :
    Table (fun w (xo : X × O) => f xo.1 w xo.2) (Fintype.card X*b) := by
  classical
  let e := Fintype.equivFin X
  have ht := parallelFin _ (fun i => f (e.symm i)) b (fun i => h _)
  apply congr (outmap ht (fun (x : X × O) => (e x.1,x.2)))
  intro w x
  simp

theorem tabulate [Fintype O] (f : (I → F) → O → F) (b : ℕ)
    (h : ∀ o, Circuit.Build (fun w => f w o) b) :
    Table f (Fintype.card O*b) := by
  have ht := parallel (fun o (w : I → F) (_ : Unit) => f w o) b (fun o => ofBuild (h o))
  exact outmap ht (fun o => (o,()))

theorem inputs [Fintype O] (ix : O → I) : Table (fun (w : I → F) o => w (ix o)) 0 := by
  simpa using tabulate (fun (w : I → F) o => w (ix o)) 0 (fun o => Circuit.read (ix o))

theorem constants [Fintype O] (f : O → F) : Table (fun (_ : I → F) o => f o) 0 := by
  simpa using tabulate (fun (_ : I → F) o => f o) 0 (fun o => Circuit.const (f o))

end VWZClique.MM

open OAI.MatrixMultiplication.Arithmetic Filter
namespace VWZClique.MM

private def price {F I : Type*} : {r : ℕ} → Program F I r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _+1, .step p g => Fin.cases g.cost (price p)

private theorem sum_price {F I : Type*} {r : ℕ} (p : Program F I r) :
    ∑ i, price p i = p.cost := by
  induction p with
  | nil => simp [Program.cost]
  | step p g ih => rw [Fin.sum_univ_succ]; simpa [price,Program.cost,add_comm] using congrArg (g.cost + ·) ih

private theorem register_kind {F I : Type*} [Field F] {r : ℕ} (p : Program F I r) (i : Fin r) :
    price p i = 1 ∨ (∃ c : F, ∀ w, p.eval w i = c) ∨ ∃ k : I, ∀ w, p.eval w i = w k := by
  induction p with
  | nil => exact Fin.elim0 i
  | step p g ih =>
    refine Fin.cases ?_ (fun i => ih i) i
    cases g with
    | constant c => exact Or.inr (Or.inl ⟨c,fun _ => rfl⟩)
    | input k => exact Or.inr (Or.inr ⟨k,fun _ => rfl⟩)
    | _ => exact Or.inl rfl

theorem square_output_lower_bound {F : Type*} [Field F] {n : ℕ}
    (P : MatrixAlgorithm F n n n) (hc : P.Correct) : n^2 ≤ P.cost := by
  classical
  let out (ij : Fin n × Fin n) := P.output ij.1 ij.2
  have ev (ij : Fin n × Fin n) (A B : Matrix (Fin n) (Fin n) F) :
      P.program.eval (matrixInputs A B) (out ij) = (A*B) ij.1 ij.2 :=
    congrFun (congrFun (hc A B) ij.1) ij.2
  let ones : Matrix (Fin n) (Fin n) F := fun _ _ => 1
  have active (ij : Fin n × Fin n) : price P.program (out ij) = 1 := by
    rcases register_kind P.program (out ij) with h | ⟨c,h⟩ | ⟨k,h⟩
    · exact h
    · have hz := ev ij 0 0
      have ho := ev ij ones 1
      rw [h,Matrix.zero_mul] at hz
      rw [h,Matrix.mul_one] at ho
      exact (zero_ne_one ((show c = 0 from hz).symm.trans (show c=1 from ho))).elim
    · rcases k with ⟨i,j⟩ | ⟨i,j⟩
      · have he := ev ij ones 0
        rw [h,Matrix.mul_zero] at he
        exact (one_ne_zero (show (1:F)=0 from he)).elim
      · have he := ev ij 0 ones
        rw [h,Matrix.zero_mul] at he
        exact (one_ne_zero (show (1:F)=0 from he)).elim
  have inject : Function.Injective out := by
    intro x y he
    by_contra hne
    let A : Matrix (Fin n) (Fin n) F := fun i j => if (i,j)=x then 1 else 0
    have hx := ev x A 1
    have hy := ev y A 1
    rw [he,hy,Matrix.mul_one] at hx
    simp [A,Ne.symm hne] at hx
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (Finset.univ.image out))
      (f := price P.program) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_image (fun _ _ _ _ h => inject h), sum_price] at hsum
  simpa [MatrixAlgorithm.cost,active,pow_two] using hsum

theorem cubic_algorithm (F : Type*) [Field F] (n : ℕ) :
    ∃ P : MatrixAlgorithm F n n n, P.Correct ∧ P.cost ≤ 2*n^3 := by
  let f := fun (v : Fin n × Fin n) (w : MatrixInput n n n → F) => ∑ k : Fin n, w (.inl (v.1,k)) * w (.inr (k,v.2))
  have build (v : Fin n × Fin n) : Circuit.Build (f v) (n*2) := by
    have h := Circuit.sum Finset.univ
      (fun k : Fin n => fun w : MatrixInput n n n → F => w (.inl (v.1,k))*w (.inr (k,v.2))) 1
      (fun k _ => Circuit.mul (Circuit.read _) (Circuit.read _))
    simpa [f] using h
  obtain ⟨r,p,out,hc,he⟩ := FoldProof.tabulate f _ build
  refine ⟨⟨r,p,fun i j => out (i,j)⟩,?_,?_⟩
  · intro A B
    ext i j
    exact he (matrixInputs A B) (i,j)
  · change p.cost ≤ _
    calc p.cost ≤ _ := hc
         _ = _ := by simp [Fintype.card_prod]; ring

theorem cubic_admissible (F : Type*) [Field F] : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2,by norm_num,?_⟩
  intro n hn
  obtain ⟨P,hc,hp⟩ := cubic_algorithm F n
  refine ⟨P,hc,?_⟩
  calc
    (P.cost : ℝ) ≤ 2*(n:ℝ)^3 := by exact_mod_cast hp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num; linarith)

theorem admissible_ge_two {F : Type*} [Field F] {τ : ℝ} (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  by_contra! h
  let ε := (2-τ)/2
  have he : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C,hC,h⟩ := hτ ε he
  have lim := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ev : ∀ᶠ n : ℕ in atTop, C < (n:ℝ)^ε := lim.eventually_gt_atTop C
  obtain ⟨n,hn,hn'⟩ := ((eventually_ge_atTop 1).and ev).exists
  obtain ⟨P,hp,hpc⟩ := h n hn
  have hb := square_output_lower_bound P hp
  have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have heq : (n:ℝ)^2 = (n:ℝ)^ε * (n:ℝ)^(τ+ε) := by
    rw [← Real.rpow_add hpos, show ε+(τ+ε)=2 by dsimp [ε]; ring]
    norm_num
  have hlow : (n:ℝ)^2 ≤ P.cost := by exact_mod_cast hb
  rw [heq] at hlow
  exact (not_lt_of_ge (hlow.trans hpc)) (mul_lt_mul_of_pos_right hn' (Real.rpow_pos_of_pos hpos _))

theorem omega_two_le (F : Type*) [Field F] : 2 ≤ omega F :=
  le_csInf ⟨3,cubic_admissible F⟩ (fun _ ht => admissible_ge_two ht)

theorem omega_le_three (F : Type*) [Field F] : omega F ≤ 3 :=
  csInf_le ⟨2,fun _ h => admissible_ge_two h⟩ (cubic_admissible F)

theorem omega_admissible (F : Type*) [Field F] : AdmissibleExponent F (omega F) := by
  intro ε hε
  obtain ⟨t,ht,hlt⟩ := exists_lt_of_csInf_lt (s := {t : ℝ | AdmissibleExponent F t})
    ⟨3,cubic_admissible F⟩ (show omega F < omega F + ε/2 by linarith)
  obtain ⟨C,hC,hP⟩ := ht (ε/2) (by linarith)
  refine ⟨C,hC,?_⟩
  intro n hn
  obtain ⟨P,hp,hpc⟩ := hP n hn
  exact ⟨P,hp,hpc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hC.le)⟩

end VWZClique.MM

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

variable {F I J : Type*} [Field F]

theorem within_mono {f : (I → F) → F} {A B : ℝ} (h : computesWithin f A) (hle : A ≤ B) :
    computesWithin f B := by
  obtain ⟨r,p,o,hc,he⟩ := h
  exact ⟨r,p,o,hc.trans hle,he⟩

theorem within_nat {f : (I → F) → F} {A : ℝ} (h : computesWithin f A) :
    ∃ b : ℕ, Circuit.Build f b ∧ (b : ℝ) ≤ A := by
  obtain ⟨r,p,o,hc,he⟩ := h
  exact ⟨p.cost, MM.toBuild (O:=Unit) (f:=fun w _ => f w)
    ⟨r,p,fun _ => o,le_rfl,fun w _ => he w⟩ (),hc⟩

theorem within_add {f g : (I → F) → F} {A B : ℝ} (hf : computesWithin f A) (hg : computesWithin g B) :
    computesWithin (fun w => f w + g w) (A+B+1) := by
  obtain ⟨a,ha,hea⟩ := within_nat hf
  obtain ⟨b,hb,heb⟩ := within_nat hg
  apply within_mono (Circuit.computes (Circuit.add ha hb))
  push_cast
  linarith

theorem within_sub {f g : (I → F) → F} {A B : ℝ} (hf : computesWithin f A) (hg : computesWithin g B) :
    computesWithin (fun w => f w - g w) (A+B+1) := by
  obtain ⟨a,ha,hea⟩ := within_nat hf
  obtain ⟨b,hb,heb⟩ := within_nat hg
  apply within_mono (Circuit.computes (Circuit.binary ha hb (·-·) Gate.sub (fun _ _ => le_rfl) (fun _ _ _ _ => rfl)))
  push_cast
  linarith

theorem within_scale {f : (I → F) → F} {A : ℝ} (hf : computesWithin f A) (c : F) :
    computesWithin (fun w => c * f w) (A+1) := by
  obtain ⟨a,ha,hea⟩ := within_nat hf
  apply within_mono (Circuit.computes (Circuit.mul (Circuit.const c) ha))
  push_cast
  linarith

theorem within_sum {T : Type*} [Fintype T] {f : T → (I → F) → F} {B : ℝ}
    (hb : 0 ≤ B) (h : ∀ i, computesWithin (f i) B) :
    computesWithin (fun w => ∑ i, f i w) ((Fintype.card T : ℝ)*(B+1)) := by
  have build (i : T) : Circuit.Build (f i) ⌊B⌋₊ := by
    obtain ⟨a,ha,hb⟩ := within_nat (h i)
    exact Circuit.cost_mono ha (Nat.le_floor hb)
  apply within_mono (Circuit.computes (Circuit.sum Finset.univ _ _ (fun i _ => build i)))
  rw [Finset.card_univ]
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith [Nat.floor_le hb]) (Nat.cast_nonneg _)

theorem within_preprocess {f : (J → F) → F} {g : (I → F) → F} {B : ℝ} {r : ℕ}
    (p : Program F I r) (out : J → Fin r) (A : ℝ) (hc : (p.cost : ℝ) ≤ A)
    (he : ∀ w, f (fun j => p.eval w (out j)) = g w) (hf : computesWithin f B) :
    computesWithin g (A+B) := by
  obtain ⟨m,q,o,hq,eqn⟩ := hf
  obtain ⟨l,s,_,new,hs,_,hs'⟩ := MM.splice p q out
  refine ⟨l,s,new o,?_,fun w => (hs' w o).trans ((eqn _).trans (he w))⟩
  exact (by exact_mod_cast hs : (s.cost : ℝ) ≤ (p.cost : ℝ) + q.cost).trans (add_le_add hc hq)

theorem signed_sum {M : ℕ} (c : Fin M → F) {f p : (I → F) → F}
    {l r : Fin M → (I → F) → F} {b : Fin M → Fin M → (I → F) → F} {A B : ℝ}
    (hb : 0 ≤ B)
    (he : ∀ w, f w = p w + (∑ i, c i * l i w) + (∑ j, c j * r j w) -
      ∑ i, ∑ j, (c i*c j) * b i j w)
    (hp : computesWithin p A) (hl : ∀ i, computesWithin (l i) B)
    (hr : ∀ j, computesWithin (r j) B) (hb' : ∀ i j, computesWithin (b i j) B) :
    computesWithin f (A+(2*(M:ℝ)+M^2)*(B+2)+3) := by
  have h₁ := within_sum (by linarith : 0 ≤ B+1) (fun i => within_scale (hl i) (c i))
  have h₂ := within_sum (by linarith : 0 ≤ B+1) (fun j => within_scale (hr j) (c j))
  have h₃ := within_sum (by linarith : 0 ≤ B+1)
    (fun ij : Fin M × Fin M => within_scale (hb' ij.1 ij.2) (c ij.1*c ij.2))
  have h := within_sub (within_add (within_add hp h₁) h₂) h₃
  simp only [Fintype.sum_prod_type,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at h
  rw [funext he]
  apply within_mono h
  ring_nf
  rfl

end VWZClique.WeightedProof

namespace VWZClique.WeightedProof

theorem recurrence_bound {n ω α β δ η C D M : ℝ} (hn : 1 ≤ n) (hω : 2 ≤ ω)
    (hα : 0 < α) (hα' : α ≤ 1) (hβa : β ≤ α/2) (hβd : β ≤ δ)
    (hδ : 0 < δ) (hη : 0 < η) (hc : 0 ≤ C) (hd : 0 ≤ D)
    (hm : 0 ≤ M) (hm' : M ≤ n^(α/8)) :
    C*n^(3*ω-(ω-1)*δ+η) +
        (2*M+M^2)*(D*n^(3*ω-α+η)+2)+3 ≤
      (C+3*(D+2)+3)*n^(3*ω-β+η) := by
  have hn0 : 0 ≤ n := by linarith
  let x := n^(α/8)
  let y := n^(3*ω-α+η)
  let z := n^(3*ω-β+η)
  have hx : 1 ≤ x := Real.one_le_rpow hn (by positivity)
  have hy : 1 ≤ y := Real.one_le_rpow hn (by linarith)
  have hz : 1 ≤ z := Real.one_le_rpow hn (by linarith)
  have hxy : x^2*y ≤ z := by
    calc
      x^2*y = n^((α/8+α/8)+(3*ω-α+η)) := by
        simp only [Real.rpow_add (by linarith : 0<n),pow_two,x,y,mul_assoc]
      _ ≤ z := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hp : C*n^(3*ω-(ω-1)*δ+η) ≤ C*z := by
    apply mul_le_mul_of_nonneg_left _ hc
    apply Real.rpow_le_rpow_of_exponent_le hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hω) hδ.le]
  have hm2 : 2*M+M^2 ≤ 3*x^2 := by
    have hsq : M^2 ≤ x^2 := by gcongr
    have hx' : x ≤ x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ x)]
    change M ≤ x at hm'
    linarith
  have hDy : D*y+2 ≤ (D+2)*y := by nlinarith
  have hprod : (2*M+M^2)*(D*y+2) ≤ (3*x^2)*((D+2)*y) :=
    mul_le_mul hm2 hDy (by nlinarith [mul_nonneg hd (by linarith : 0 ≤ y)]) (by positivity)
  calc
    _ ≤ C*z+(3*x^2)*((D+2)*y)+3 := by linarith
    _ = C*z+3*(D+2)*(x^2*y)+3 := by ring
    _ ≤ C*z+3*(D+2)*z+3*z := by
      gcongr
      linarith
    _ = _ := by ring

end VWZClique.WeightedProof

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

universe u

def Good (k : ℕ) (α : ℝ) : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F], ∀ η : ℝ, 0<η →
    ∃ C : ℝ, 0<C ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ H : SimpleGraph V, Nat.card H.edgeSet < k →
      computesWithin (weightedSum (F:=F) (n:=2^L) H) (C*((2:ℝ)^L)^(3*omega F-α+η))

theorem induced (k : ℕ) : ∃ α : ℝ, 0<α ∧ α≤1 ∧ Good.{u} k α := by
  induction k with
  | zero =>
    exact ⟨1,by norm_num,le_rfl,fun F _ _ η _ => ⟨1,by norm_num,0,fun _ _ H he => (Nat.not_lt_zero _ he).elim⟩⟩
  | succ k ih =>
    obtain ⟨α,hα,hα',old⟩ := ih
    obtain ⟨δ,hδ,L₀,rank⟩ := rank_or_swap (α/8) (by positivity)
    let δ' := min δ 1
    let β := min (α/2) δ'
    have hd : 0<δ' := lt_min hδ (by norm_num)
    have hd' : δ'≤1 := min_le_right _ _
    have hbd : β≤δ' := min_le_right _ _
    have hba : β≤α/2 := min_le_left _ _
    have hb : 0<β := lt_min (by positivity) hd
    have hb' : β≤1 := le_trans hbd hd'
    refine ⟨β,hb,hb',?_⟩
    intro F _ _ η hη
    obtain ⟨K,hK,L₁,old⟩ := old F η hη
    obtain ⟨S,hS,sparse⟩ := no_two_wedges
    obtain ⟨Q,hQ,proj⟩ := two_projections F δ' hd hd' η hη
    obtain ⟨G,folded⟩ := fold_to_smaller_pattern
    let D := (G:ℝ)+K
    have hD : 0≤D := by dsimp [D]; positivity
    let C := max S (Q+3*(D+2)+3)
    refine ⟨C,lt_of_lt_of_le hS (le_max_left _ _),max L₀ L₁,?_⟩
    intro L hL H hH
    let n : ℝ := (2:ℝ)^L
    have hn : 1≤n := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    have hn0 : 0<n := by linarith
    have hpow : 1≤(2:ℕ)^L := Nat.one_le_pow _ _ (by decide)
    have castn : (((2:ℕ)^L : ℕ):ℝ) = n := by simp [n]
    have hω := MM.omega_two_le F
    have hnC : 0 ≤ n^(3*omega F-β+η) := Real.rpow_nonneg hn0.le _
    by_cases wedges : ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧ ∀ i j, f i ≠ g j
    · obtain ⟨f,g,hf,hg,disj⟩ := wedges
      obtain ⟨π,hpa,hpb⟩ := place_wedges H f g hf hg disj
      let E := slots π H
      let put := fun (w : WeightKey (2^L) → F) (i : ChannelKey L) => literal w (channelTag π E i)
      obtain ⟨M,m,c,Λ,d,hm,hrank,hdecomp⟩ := rank L ((le_max_left _ _).trans hL)
      have hrank' : (Λ.card : ℝ) ≤ n^(2-δ') :=
        hrank.trans (Real.rpow_le_rpow_of_exponent_le hn (by dsimp [δ']; linarith [min_le_left δ (1:ℝ)]))
      let A := Q*n^(3*omega F-(omega F-1)*δ'+η)
      let B := D*n^(3*omega F-α+η)
      have hB : 0≤B := mul_nonneg hD (Real.rpow_nonneg hn0.le _)
      let d' := fun j => (d j : F)
      have hp : computesWithin (fun w => doubleProjection Λ Λ d' d' (put w)) A :=
        translated (proj L Λ Λ d' d' hrank' hrank') (channelTag π E)
      have smaller (a b : Option (Mask L)) (hab : 0 < a.isSome.toNat+b.isSome.toNat) :
          computesWithin (fun w => placedFold E a b (put w)) B := by
        obtain ⟨H',r,p,out,he,hc,heval⟩ := folded F L E a b (fun _ => hpa) (fun _ => hpb)
        have hE : E.card ≤ Nat.card H.edgeSet := slots_card π H
        have hH' : Nat.card H'.edgeSet < k := by omega
        have prev := old L ((le_max_right _ _).trans hL) H' hH'
        have hcost : (p.cost : ℝ) ≤ (G:ℝ)*n^2 := by
          have hh : (p.cost : ℝ) ≤ (G:ℝ)*(((2:ℕ)^L : ℕ):ℝ)^2 := by exact_mod_cast hc
          simpa only [castn] using hh
        have prepare := translated (within_preprocess p out ((G:ℝ)*n^2) hcost heval prev) (channelTag π E)
        apply within_mono prepare
        change (G:ℝ)*n^2 + K*n^(3*omega F-α+η) ≤ ((G:ℝ)+K)*n^(3*omega F-α+η)
        rw [add_mul]
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num; linarith)
      have eqn (w : WeightKey (2^L) → F) := decomposition Λ d m c hdecomp E (put w) (supported π E w)
      have signed := signed_sum (c := fun i => (c i : F)) (f := weightedSum (n:=2^L) H)
        hB (fun w => (encode_graph π H w).symm.trans (eqn w)) hp
        (fun i => smaller (some (m i)) none (by simp))
        (fun j => smaller none (some (m j)) (by simp))
        (fun i j => smaller (some (m i)) (some (m j)) (by simp))
      apply within_mono signed
      apply le_trans (recurrence_bound hn hω hα hα' hba hbd hd hη hQ.le hD (Nat.cast_nonneg M) hm)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hnC
    · have h := sparse F (2^L) hpow H wedges
      apply within_mono h
      rw [castn]
      calc
        S*n^5 ≤ S*n^(3*omega F-β+η) := by
          apply mul_le_mul_of_nonneg_left _ hS.le
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num; linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hnC

theorem all_sizes :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type u) [Field F] [CharZero F],
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ∀ H : SimpleGraph V, computesWithin (weightedSum (F := F) (n := n) H)
          (C * (n : ℝ) ^ (3 * omega F - ε + η)) := by
  classical
  obtain ⟨α,hα,hα',h⟩ := induced.{u} (Nat.card (Sym2 V)+1)
  refine ⟨α,hα,?_⟩
  intro F _ _ η hη
  obtain ⟨K,hK,L₀,h⟩ := h F η hη
  let t := 3*omega F-α+η
  have ht : 0≤t := by dsimp [t]; linarith [MM.omega_two_le F]
  let B : ℕ := ((2^L₀)^9)*101
  let C := max (B:ℝ) (K*(2:ℝ)^t)
  have hK' : 0 < K*(2:ℝ)^t := by positivity
  refine ⟨C,hK'.trans_le (le_max_right _ _),?_⟩
  intro n hn H
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hh : Nat.card H.edgeSet ≤ Nat.card (Sym2 V) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  obtain ⟨L,hnL,hLn⟩ := exists_pow_sandwich hn
  by_cases hL : L₀ ≤ L
  · have hpow := padding hnL H (h L hL H (by omega))
    apply within_mono hpow
    have hscale : ((2:ℝ)^L)^t ≤ ((2:ℝ)*n)^t := by
      apply Real.rpow_le_rpow (by positivity) _ ht
      exact_mod_cast hLn
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at hscale
    calc
      K*((2:ℝ)^L)^t ≤ K*((2:ℝ)^t*(n:ℝ)^t) := mul_le_mul_of_nonneg_left hscale hK.le
      _ = (K*(2:ℝ)^t)*(n:ℝ)^t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have hnB : n ≤ 2^L₀ := hnL.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hsmall : n^9*101 ≤ B := Nat.mul_le_mul_right 101 (Nat.pow_le_pow_left hnB 9)
    apply within_mono (Circuit.computes (brute H))
    calc
      ((n^9*101:ℕ):ℝ) ≤ (B:ℝ) := by exact_mod_cast hsmall
      _ ≤ C := le_max_left _ _
      _ ≤ C*(n:ℝ)^t := le_mul_of_one_le_right (by dsimp [C]; positivity) (Real.one_le_rpow hn' ht)

end VWZClique.WeightedProof

open OAI.MatrixMultiplication.Arithmetic VWZClique

theorem solution :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Type*) [Field F] [CharZero F],
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ∀ H : SimpleGraph V, computesWithin (weightedSum (F := F) (n := n) H)
          (C * (n : ℝ) ^ (3 * omega F - ε + η)) := VWZClique.WeightedProof.all_sizes
