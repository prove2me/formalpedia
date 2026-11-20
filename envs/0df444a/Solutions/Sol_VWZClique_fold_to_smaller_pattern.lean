-- Prove2me | solution 1 for VWZClique.fold_to_smaller_pattern
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T01:50:07.860685+00:00
-- url     : https://prove2.me/submissions/304728dd-386a-4753-9e94-7c9d10c361d8

import Definitions.Def_VWZClique_Weighted
import Definitions.Def_VWZClique_FoldedSum

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

open VWZClique
namespace VWZClique.FoldProof

abbrev FoldToken (E : Finset EdgeSlot) := Fin 4 ⊕ (Fin 3 × Slot) ⊕ ↥E

def pinSite (i : Fin 4) : V := ![site 0 0,site 0 1,site 1 0,site 1 1] i

noncomputable def pinWeight {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L))
    (i : Fin 4) (s : Bits L) : F :=
  ![flag a Prod.fst s,flag a (fun r => r.2.1) s,flag b Prod.fst s,flag b (fun r => r.2.1) s] i

def ends {L : ℕ} (a b : Option (Mask L)) {E : Finset EdgeSlot} : FoldToken E → V × V
  | .inl i => (pinSite i,pinSite i)
  | .inr (.inl (h,s)) => ((route a b h s).1,(route a b h s).1)
  | .inr (.inr e) => ((route a b e.val.1 e.val.2.1).1,(route a b e.val.1 e.val.2.2).1)

noncomputable def weight {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) {E : Finset EdgeSlot} :
    FoldToken E → Bits L → Bits L → (ChannelKey L → F) → F
  | .inl i, s, _, _ => pinWeight a b i s
  | .inr (.inl (h,i)), s, _, w => w (h,.inl (i,(route a b h i).2 s))
  | .inr (.inr e), s,t,w => w (e.val.1,.inr (e.val.2.1,e.val.2.2,
      (route a b e.val.1 e.val.2.1).2 s,(route a b e.val.1 e.val.2.2).2 t))

theorem weight_cost {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) {E : Finset EdgeSlot}
    (t : FoldToken E) (s u : Bits L) : Circuit.Build (weight (F := F) a b t s u) 0 := by
  rcases t with i | ⟨h,i⟩ | e
  · exact Circuit.const _
  · exact Circuit.read _
  · exact Circuit.read _

theorem token_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (X : V → Bits L) (w : ChannelKey L → F) :
    (∏ v : FoldToken E, weight a b v (X (ends a b v).1) (X (ends a b v).2) w) =
    checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  congr 1
  · rw [Fin.prod_univ_four]
    change ((flag a _ _ * flag a _ _) * flag b _ _) * flag b _ _ = _
    simp only [checks,mul_assoc]
    rfl
  · congr 1
    change (∏ e : ↥E, binary a b X w e.val) = _
    exact Finset.prod_attach E (binary a b X w)

noncomputable def wordEquiv (L : ℕ) : Fin (2^L) ≃ Bits L :=
  Fintype.equivOfCardEq (by simp [Bits])

theorem weighted_encoding {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (w : ChannelKey L → F) :
    (∑ x : V → Fin (2^L), ∏ t : FoldToken E,
      weight a b t (wordEquiv L (x (ends a b t).1)) (wordEquiv L (x (ends a b t).2)) w)
    = placedFold E a b w := by
  rw [reindexed]
  let e := Equiv.piCongrRight (fun _ : V => wordEquiv L)
  let raw := fun X : V → Bits L => ∏ t : FoldToken E, weight a b t (X (ends a b t).1) (X (ends a b t).2) w
  change (∑ x, raw (e x)) = _
  rw [e.sum_comp raw]
  exact Finset.sum_congr rfl fun X _ => token_product a b E X w

theorem factor_table_cost (L : ℕ) (E : Finset EdgeSlot) :
    Fintype.card (WeightKey (2^L)) * Fintype.card (FoldToken E) ≤ 11700*(2^L)^2 := by
  let n := 2^L
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have hn' : n ≤ n^2 := by simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n hn
  have base : E.card ≤ 108 := by
    have h := Finset.card_le_univ E
    simpa [EdgeSlot,Slot,Fintype.card_prod,Fintype.card_sum] using h
  have tok : Fintype.card (FoldToken E) ≤ 130 := by
    simp [FoldToken, Slot, Fintype.card_prod, Fintype.card_sum]
    omega
  have keys : Fintype.card (WeightKey n) ≤ 90*n^2 := by
    simp [WeightKey,V,Fintype.card_prod,Fintype.card_sum,pow_two] at *
    nlinarith only [hn']
  calc
    _ ≤ (90*n^2)*130 := Nat.mul_le_mul keys tok
    _ = _ := by dsimp [n]; ring

end VWZClique.FoldProof

open VWZClique
namespace VWZClique.FoldProof

def epPair {L : ℕ} (a b : Option (Mask L)) (e : EdgeSlot) : V × V :=
  ((route a b e.1 e.2.1).1, (route a b e.1 e.2.2).1)

private def edgeImage {L : ℕ} (a b : Option (Mask L)) (e : EdgeSlot) : Sym2 V :=
  s((epPair a b e).1, (epPair a b e).2)

def foldedGraph {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ↑(E.image (edgeImage a b))

theorem folded_adj {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (e : EdgeSlot) (he : e ∈ E) (hne : (epPair a b e).1 ≠ (epPair a b e).2) :
    (foldedGraph a b E).Adj (epPair a b e).1 (epPair a b e).2 :=
  ⟨Finset.mem_image_of_mem (edgeImage a b) he, hne⟩

private theorem image_drop {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (x y : α) (hy : y ∈ T) (hyx : y ≠ x) (h : f x = f y) :
    T.image f = (T.erase x).image f := by
  apply Finset.Subset.antisymm _ (Finset.image_mono f (Finset.erase_subset _ _))
  intro z hz
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
  by_cases heq : u = x
  · subst u
    exact Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hyx,hy⟩, h.symm⟩
  · exact Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨heq,hu⟩)

private def leftEdge (h : Fin 3) : EdgeSlot := (h, .inl 0, .inl 2)
private def rightEdge (h : Fin 3) : EdgeSlot := (h, .inr 1, .inr 2)

theorem folded_count {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (ha : a.isSome = true → wedgePlaced E 0 2)
    (hb : b.isSome = true → wedgePlaced E 1 0) :
    Nat.card (foldedGraph a b E).edgeSet + a.isSome.toNat + b.isSome.toNat ≤ E.card := by
  have graphBound : Nat.card (foldedGraph a b E).edgeSet ≤ (E.image (edgeImage a b)).card := by
    rw [Nat.card_coe_set_eq, foldedGraph, SimpleGraph.edgeSet_fromEdgeSet, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard Set.sdiff_subset
  obtain ⟨T,hImage,hCard,hb'⟩ : ∃ T : Finset EdgeSlot,
      E.image (edgeImage a b) = T.image (edgeImage a b) ∧
      T.card + a.isSome.toNat = E.card ∧
      (b.isSome = true → wedgePlaced T 1 0) := by
    cases a with
    | none => exact ⟨E,rfl,by simp,hb⟩
    | some m =>
      have hA := ha rfl
      refine ⟨E.erase (leftEdge 0), ?_, Finset.card_erase_add_one hA.1, ?_⟩
      · exact image_drop E (edgeImage (some m) b) (leftEdge 0) (rightEdge 2) hA.2 (by decide) rfl
      · intro h
        exact ⟨Finset.mem_erase.mpr ⟨by decide,(hb h).1⟩,
          Finset.mem_erase.mpr ⟨by decide,(hb h).2⟩⟩
  have countT : (T.image (edgeImage a b)).card + b.isSome.toNat ≤ T.card := by
    cases b with
    | none => simpa using (Finset.card_image_le (s := T) (f := edgeImage a none))
    | some m =>
      have hB := hb' rfl
      rw [image_drop T (edgeImage a (some m)) (leftEdge 1) (rightEdge 0) hB.2 (by decide) rfl]
      have hErase : (T.erase (leftEdge 1)).card + 1 = T.card := Finset.card_erase_add_one hB.1
      have hBound := Finset.card_image_le (s := T.erase (leftEdge 1)) (f := edgeImage a (some m))
      change _ + 1 ≤ _
      omega
  rw [hImage] at graphBound
  omega

end VWZClique.FoldProof

open VWZClique VWZClique.FoldProof OAI.MatrixMultiplication.Arithmetic

theorem solution :
    ∃ C : ℕ, ∀ (F : Type*) [Field F] [CharZero F] (L : ℕ)
      (E : Finset EdgeSlot) (a b : Option (Mask L)),
      (a.isSome = true → wedgePlaced E 0 2) →
      (b.isSome = true → wedgePlaced E 1 0) →
      ∃ (H : SimpleGraph V) (r : ℕ) (P : Program F (ChannelKey L) r)
        (out : WeightKey (2^L) → Fin r),
        (Nat.card H.edgeSet + a.isSome.toNat + b.isSome.toNat ≤ E.card) ∧
        P.cost ≤ C * (2^L)^2 ∧ ∀ w,
          weightedSum H (fun i => P.eval w (out i)) = placedFold E a b w := by
  refine ⟨11700,?_⟩
  intro F _ _ L E a b ha hb
  let H := foldedGraph a b E
  let fn := fun (t : FoldToken E) (x y : Fin (2^L)) =>
    weight (F := F) a b t (wordEquiv L x) (wordEquiv L y)
  have edge (t : FoldToken E) (hn : (ends a b t).1 ≠ (ends a b t).2) :
      H.Adj (ends a b t).1 (ends a b t).2 := by
    rcases t with i | ⟨h,i⟩ | e
    · exact (hn rfl).elim
    · exact (hn rfl).elim
    · exact folded_adj a b E e.val e.property hn
  obtain ⟨r,p,out,hc,he⟩ := compile_weights H (ends a b) edge fn
    (fun t x y => weight_cost a b t (wordEquiv L x) (wordEquiv L y))
  exact ⟨H,r,p,out,folded_count a b E ha hb,hc.trans (factor_table_cost L E),
    fun w => (he w).trans (weighted_encoding a b E w)⟩
