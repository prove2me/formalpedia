-- Prove2me | solution 1 for VWZClique.two_projections
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T02:09:21.10907+00:00
-- url     : https://prove2.me/submissions/6d81ee7a-2b18-442c-b337-3f4ae476f99a

import Definitions.Def_VWZClique_Weighted
import Definitions.Def_VWZClique_Contraction
import Theorems.Thm_VWZClique_basis_transform

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

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.MM

variable {F : Type*} [Field F]

abbrev Inputs (X K Y : Type*) := (X × K) ⊕ (K × Y)

def product {X K Y : Type*} [Fintype K] (w : Inputs X K Y → F) (v : X × Y) : F :=
  ∑ k, w (.inl (v.1,k)) * w (.inr (k,v.2))

theorem algorithm {a b c : ℕ} (P : MatrixAlgorithm F a b c) (hP : P.Correct) :
    Table (product (X := Fin a) (K := Fin b) (Y := Fin c) (F := F)) P.cost := by
  refine ⟨P.registers,P.program,fun v => P.output v.1 v.2,by exact Nat.le_refl P.program.cost,fun w v => ?_⟩
  let A : Matrix (Fin a) (Fin b) F := fun i j => w (.inl (i,j))
  let B : Matrix (Fin b) (Fin c) F := fun i j => w (.inr (i,j))
  have he : matrixInputs A B = w := by
    funext ij
    rcases ij with ⟨i,j⟩|⟨i,j⟩ <;> rfl
  have heq := congrFun (congrFun (hP A B) v.1) v.2
  change P.program.eval (matrixInputs A B) _ = _ at heq
  rw [he] at heq
  exact heq.trans (Matrix.mul_apply (M := A) (N := B) (i := v.1) (k := v.2))

theorem square {X K Y : Type*} [Fintype K] {n : ℕ} (P : MatrixAlgorithm F n n n)
    (hP : P.Correct) (eX : X ≃ Fin n) (eK : K ≃ Fin n) (eY : Y ≃ Fin n) :
    Table (product (X := X) (K := K) (Y := Y) (F := F)) P.cost := by
  let ix : MatrixInput n n n → Inputs X K Y := Sum.elim
    (fun v => .inl (eX.symm v.1,eK.symm v.2))
    (fun v => .inr (eK.symm v.1,eY.symm v.2))
  have h := inmap (algorithm P hP) ix
  apply congr (outmap h (fun (xy : X × Y) => (eX xy.1,eY xy.2)))
  intro w v
  simp only [product,ix,Sum.elim_inl,Sum.elim_inr,Equiv.symm_apply_apply]
  exact eK.symm.sum_comp (fun k => w (.inl (v.1,k))*w (.inr (k,v.2)))

end VWZClique.MM

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.MM

variable {F : Type*} [Field F]

noncomputable def pick {α β γ : Type*} (e : α ↪ β) (b : β) (z : γ) (f : α → γ) : γ :=
  (Function.partialInv e b).elim z f

@[simp] theorem pick_hit {α β γ : Type*} (e : α ↪ β) (a : α) (z : γ) (f : α → γ) :
    pick e (e a) z f = f a := by
  simp [pick,Function.partialInv_left e.injective]

theorem sum_pick {α β : Type*} [Fintype α] [Fintype β] (e : α ↪ β) (f : α → F) :
    ∑ b, pick e b 0 f = ∑ a, f a := by
  classical
  let s := Finset.univ.map e
  calc
    (∑ b, pick e b 0 f) = ∑ b ∈ s, pick e b 0 f := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      cases h : Function.partialInv e b with
      | none => simp [pick,h]
      | some a =>
        have he : e a = b := (e.injective.isPartialInv a b).1 h
        exact False.elim (hb (by simp [s,← he]))
    _ = ∑ a, f a := by simp [s]

noncomputable def route {X K Y : Type*} {s t : ℕ}
    (ex : X ↪ Fin s) (ek : K ↪ Fin t × Fin s) (ey : Y ↪ Fin s) (q : Fin t) :
    MatrixInput s s s → Inputs X K Y ⊕ F := Sum.elim
  (fun v => pick ex v.1 (.inr 0) (fun x =>
    pick ek (q,v.2) (.inr 0) (fun k => .inl (.inl (x,k)))))
  (fun v => pick ey v.2 (.inr 0) (fun y =>
    pick ek (q,v.1) (.inr 0) (fun k => .inl (.inr (k,y)))))

/-- Multiply rectangular matrices by breaking the inner dimension into square packets. -/
theorem rect {X K Y : Type*} [Fintype X] [Fintype K] [Fintype Y] {s t : ℕ}
    (P : MatrixAlgorithm F s s s) (hP : P.Correct) (hx : Fintype.card X ≤ s)
    (hy : Fintype.card Y ≤ s) (hk : Fintype.card K ≤ t*s) :
    Table (product (X := X) (K := K) (Y := Y) (F := F))
      (t * (P.cost + Fintype.card X * Fintype.card Y)) := by
  classical
  obtain ⟨ex⟩ : Nonempty (X ↪ Fin s) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hx)
  obtain ⟨ey⟩ : Nonempty (Y ↪ Fin s) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hy)
  obtain ⟨ek⟩ : Nonempty (K ↪ Fin t × Fin s) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hk)
  let f (q : Fin t) (w : Inputs X K Y → F) (v : X × Y) : F :=
    product (fun i => (route ex ek ey q i).elim w id) (ex v.1,ey v.2)
  have part (q : Fin t) : Table (f q) P.cost :=
    outmap (inmapConst (algorithm P hP) (route ex ek ey q)) (fun (v : X × Y) => (ex v.1,ey v.2))
  have parts := parallel f P.cost part
  let addparts (w : Fin t × (X × Y) → F) (v : X × Y) := ∑ q, w (q,v)
  have sumc : Table addparts (Fintype.card (X × Y)*t) := by
    apply tabulate
    intro v
    simpa [addparts] using (Circuit.sum Finset.univ (fun (q : Fin t) (w : Fin t × (X × Y) → F) => w (q,v))
      0 (fun q _ => Circuit.read _))
  have h := bind parts sumc
  apply cost_mono (congr h (g := product) ?_) ?_
  · intro w v
    change (∑ q : Fin t, ∑ j : Fin s, _ * _) = ∑ k : K, _
    rw [← Fintype.sum_prod_type']
    rw [← sum_pick ek (fun k => w (.inl (v.1,k)) * w (.inr (k,v.2)))]
    apply Finset.sum_congr rfl
    rintro ⟨q,j⟩ _
    simp only [route,Sum.elim_inl,Sum.elim_inr,pick_hit]
    cases h' : Function.partialInv ek (q,j) <;> simp [pick,h']
  · simp only [Fintype.card_fin,Fintype.card_prod]
    rw [Nat.mul_add,Nat.mul_comm (Fintype.card X * Fintype.card Y) t]

/-- Contract three rectangular matrices to the trace of their product. -/
theorem trace {U V W : Type*} [Fintype U] [Fintype V] [Fintype W] {s t : ℕ}
    (P : MatrixAlgorithm F s s s) (hP : P.Correct) (hu : Fintype.card U ≤ s)
    (hv : Fintype.card V ≤ s) (hw : Fintype.card W ≤ t*s) :
    Table (fun (w : ((U × V) ⊕ Inputs V W U) → F) (_ : Unit) =>
      ∑ u : U, ∑ v : V, w (.inl (u,v)) *
        ∑ k : W, w (.inr (.inl (v,k))) * w (.inr (.inr (k,u))))
      (t * (P.cost + Fintype.card V * Fintype.card U) + 2 * (Fintype.card V * Fintype.card U)) := by
  classical
  let src := (U × V) ⊕ Inputs V W U
  have hA := inputs (F := F) (fun (v : U × V) => (Sum.inl v : src))
  have hBC := inmap (rect P hP hv hu hw) (fun (v : Inputs V W U) => (Sum.inr v : src))
  have h := pair hA hBC
  let dot (w : (U × V) ⊕ (V × U) → F) := ∑ p : U × V, w (.inl p) * w (.inr (p.2,p.1))
  have hd : Circuit.Build dot (Fintype.card (U × V)*2) := by
    simpa [dot] using Circuit.sum Finset.univ
      (fun (p : U × V) (w : (U × V) ⊕ (V × U) → F) => w (.inl p) * w (.inr (p.2,p.1)))
      1 (fun p _ => Circuit.mul (Circuit.read _) (Circuit.read _))
  apply cost_mono (congr (bind h (ofBuild hd)) ?_) ?_
  · intro w _
    simp [dot,product,Fintype.sum_prod_type]
  · simp only [Nat.zero_add,Fintype.card_prod]
    rw [Nat.mul_comm (Fintype.card U * Fintype.card V) 2, Nat.mul_comm (Fintype.card U) (Fintype.card V)]

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

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Projection

/-- On the support of a basis vector the first string fixes the second. -/
def partner {L : ℕ} (j : BasisLabel L) (s : Bits L) : Bits L :=
  fun i => if j i = 0 then false else if j i = 1 then true else !(s i)

private theorem oneBit_off (j : Fin 4) (s u : Bool)
    (h : u ≠ (if j = 0 then false else if j = 1 then true else !s)) :
    oneBit j s u = 0 := by
  revert h
  fin_cases j <;> cases s <;> cases u <;> decide

theorem basis_off {L : ℕ} (j : BasisLabel L) (s u : Bits L) (h : u ≠ partner j s) :
    basisEntry j (s,u) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (oneBit_off (j i) (s i) (u i) hi)

theorem support_card {L : ℕ} (j : BasisLabel L) :
    (Finset.univ.filter (fun x : PairBits L => basisEntry j x ≠ 0)).card ≤ 2^L := by
  classical
  let S := Finset.univ.filter (fun x : PairBits L => basisEntry j x ≠ 0)
  have on_graph (x : S) : x.val.2 = partner j x.val.1 := by
    by_contra h
    exact (Finset.mem_filter.mp x.property).2 (basis_off j _ _ h)
  have inj : Function.Injective (fun x : S => x.val.1) := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext h ((on_graph x).trans ((congrArg (partner j) h).trans (on_graph y).symm))
  calc S.card = Fintype.card S := (Fintype.card_coe _).symm
       _ ≤ Fintype.card (Bits L) := Fintype.card_le_of_injective _ inj
       _ = 2^L := by simp [Bits]

theorem sum_on_graph {F : Type*} [Field F] [CharZero F] {L : ℕ} (j : BasisLabel L)
    (f : PairBits L → F) :
    (∑ x, (basisEntry j x : F) * f x) =
      ∑ s, (basisEntry j (s,partner j s) : F) * f (s,partner j s) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_eq_single (partner j s)
  · intro u _ hu
    simp [basis_off j s u hu]
  · simp

/-- A projected pivot block can occupy either argument of a channel. -/
noncomputable def single {F : Type*} [Field F] [CharZero F] {L : ℕ}
    (rev : Bool) (h : Fin 3) (j : BasisLabel L) (z : Bits L) (b : Block L)
    (w : ChannelKey L → F) : F :=
  ∑ x, (basisEntry j x : F) *
    (if rev then channel w h b (block x z) else channel w h (block x z) b)

inductive Source where
  | pivot (second : Bool)
  | center
  | other (i : Fin 3)

def nearSource (i : Fin 3) : Source :=
  if i = 0 then .pivot false else if i = 1 then .pivot true else .center

def source (rev : Bool) : Slot → Source
  | .inl i => if rev then .other i else nearSource i
  | .inr i => if rev then nearSource i else .other i

structure Values (L : ℕ) where
  x : PairBits L
  z : Bits L
  b : Block L

def value {L : ℕ} (v : Values L) : Source → Bits L
  | .pivot false => v.x.1
  | .pivot true => v.x.2
  | .center => v.z
  | .other i => v.b i

private theorem value_slot {L : ℕ} (rev : Bool) (i : Slot) (v : Values L) :
    value v (source rev i) = if rev then Sum.elim v.b (block v.x v.z) i
      else Sum.elim (block v.x v.z) v.b i := by
  cases rev <;> rcases i with i | i <;> fin_cases i <;> rfl

inductive Group where
  | pivotCenter
  | pivotOther
  | centerOther
  deriving DecidableEq

/-- An ordered pair of positions can depend on at most two of the three inputs. -/
def group : Source → Source → Group
  | .other _, .pivot _ | .pivot _, .other _ => .pivotOther
  | .other _, _ | _, .other _ => .centerOther
  | _, _ => .pivotCenter

/-- Each group uses only its named inputs. -/
def keep {L : ℕ} (g : Group) (v : Values L) : Values L :=
  match g with
  | .pivotCenter => ⟨v.x,v.z,default⟩
  | .pivotOther => ⟨v.x,default,v.b⟩
  | .centerOther => ⟨default,v.z,v.b⟩

private theorem keep_left {L : ℕ} (v : Values L) (a b : Source) :
    value (keep (group a b) v) a = value v a := by
  cases a with
  | pivot t => cases t <;> cases b <;> rfl
  | center => cases b <;> rfl
  | other i => cases b <;> rfl

private theorem keep_right {L : ℕ} (v : Values L) (a b : Source) :
    value (keep (group a b) v) b = value v b := by
  cases b with
  | pivot t => cases t <;> cases a <;> rfl
  | center => cases a <;> rfl
  | other i => cases a <;> rfl

abbrev Factor := Slot ⊕ Slot × Slot

def factorGroup (rev : Bool) : Factor → Group
  | .inl i => group (source rev i) (source rev i)
  | .inr (i,k) => group (source rev i) (source rev k)

def address {L : ℕ} (rev : Bool) (h : Fin 3) (v : Values L) : Factor → ChannelKey L
  | .inl i => (h,.inl (i,value v (source rev i)))
  | .inr (i,k) => (h,.inr (i,k,value v (source rev i),value v (source rev k)))

private theorem address_keep {L : ℕ} (rev : Bool) (h : Fin 3) (v : Values L) (t : Factor) :
    address rev h (keep (factorGroup rev t) v) t = address rev h v t := by
  rcases t with i | ⟨i,k⟩
  · simp only [factorGroup, address, keep_left]
  · simp only [factorGroup, address, keep_left, keep_right]

/-- Product of the input factors in one of the three groups. -/
noncomputable def piece {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (g : Group) (v : Values L) (w : ChannelKey L → F) : F :=
  ∏ t : Factor, if factorGroup rev t = g then w (address rev h v t) else 1

private theorem factor_product {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (v : Values L) (w : ChannelKey L → F) :
    (∏ t : Factor, w (address rev h v t)) =
      if rev then channel w h v.b (block v.x v.z) else channel w h (block v.x v.z) v.b := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  cases rev <;> simp only [address, value_slot, Bool.false_eq_true, if_false, if_true, channel]

theorem factorization {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (v : Values L) (w : ChannelKey L → F) :
    (if rev then channel w h v.b (block v.x v.z) else channel w h (block v.x v.z) v.b) =
      piece rev h .pivotCenter (keep .pivotCenter v) w *
      piece rev h .pivotOther (keep .pivotOther v) w *
      piece rev h .centerOther (keep .centerOther v) w := by
  rw [← factor_product rev h v w]
  unfold piece
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  have eq := congrArg w (address_keep rev h v t)
  cases hg : factorGroup rev t <;> simpa [hg] using eq.symm

noncomputable def left {F : Type*} [Field F] [CharZero F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (z s : Bits L) (w : ChannelKey L → F) : F :=
  (basisEntry j (s,partner j s) : F) * piece rev h .pivotCenter ⟨(s,partner j s),z,default⟩ w

noncomputable def right {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (s : Bits L) (b : Block L) (w : ChannelKey L → F) : F :=
  piece rev h .pivotOther ⟨(s,partner j s),default,b⟩ w

noncomputable def outside {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (z : Bits L) (b : Block L) (w : ChannelKey L → F) : F :=
  piece rev h .centerOther ⟨default,z,b⟩ w

/-- The projected entries are a matrix product times an entrywise factor (equation 9). -/
theorem single_eq {F : Type*} [Field F] [CharZero F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (z : Bits L) (b : Block L) (w : ChannelKey L → F) :
    single rev h j z b w = (∑ s, left rev h j z s w * right rev h j s b w) * outside rev h z b w := by
  unfold single
  rw [sum_on_graph, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [factorization rev h (⟨(s,partner j s),z,b⟩ : Values L) w]
  simp only [left, right, outside, keep, mul_assoc]

private theorem card_factors : Fintype.card Factor = 42 := by
  simp [Factor, Slot, Fintype.card_sum, Fintype.card_prod]

theorem build_piece {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (g : Group) (v : Values L) : Circuit.Build (piece (F:=F) rev h g v) 42 := by
  have term (t : Factor) : Circuit.Build (fun w : ChannelKey L → F =>
      if factorGroup rev t = g then w (address rev h v t) else 1) 0 := by
    by_cases hp : factorGroup rev t = g
    · simpa [hp] using Circuit.read (F:=F) (address rev h v t)
    · simpa [hp] using Circuit.const (I:=ChannelKey L) (1:F)
  unfold piece
  simpa only [Finset.card_univ, card_factors, Nat.zero_add, Nat.mul_one] using
    Circuit.prod (Finset.univ : Finset Factor) _ 0 (fun t _ => term t)

theorem build_left {F : Type*} [Field F] [CharZero F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (z s : Bits L) : Circuit.Build (left (F:=F) rev h j z s) 43 := by
  exact Circuit.mul (Circuit.const _) (build_piece _ _ _ _)

theorem build_right {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (s : Bits L) (b : Block L) : Circuit.Build (right (F:=F) rev h j s b) 42 :=
  build_piece _ _ _ _

theorem build_outside {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (z : Bits L) (b : Block L) : Circuit.Build (outside (F:=F) rev h z b) 42 :=
  build_piece _ _ _ _

end VWZClique.Projection

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Projection

private theorem card_pairs (L : ℕ) : Fintype.card (PairBits L) = (2^L)^2 := by
  simp [PairBits, Bits, Fintype.card_prod, pow_two]

private theorem block_eta {L : ℕ} (b : Block L) : block (b 0,b 1) (b 2) = b := by
  funext i
  fin_cases i <;> rfl

/-- A square block of columns of the projected channel for one fixed basis vector. -/
private theorem slice {F : Type*} [Field F] [CharZero F] {L c : ℕ}
    (hsq : MM.Table (fun (w : PairBits L ⊕ PairBits L → F) (q : PairBits L) =>
      ∑ s, w (.inl (q.1,s)) * w (.inr (s,q.2))) c)
    (rev : Bool) (h : Fin 3) (j : BasisLabel L) (fixed : PairBits L) :
    MM.Table (fun (w : ChannelKey L → F) (q : PairBits L) =>
      single rev h j q.1 (block fixed q.2) w) (c + 129 * (2^L)^2) := by
  classical
  let m (w : ChannelKey L → F) : PairBits L ⊕ PairBits L → F :=
    Sum.elim (fun q => left rev h j q.1 q.2 w) (fun q => right rev h j q.1 (block fixed q.2) w)
  have hm := MM.tabulate m 43 (fun i => by
    rcases i with q | q
    · exact build_left _ _ _ _ _
    · exact Circuit.cost_mono (build_right _ _ _ _ _) (by decide))
  have product := MM.bind hm hsq
  let k (w : ChannelKey L → F) (q : PairBits L) := outside rev h q.1 (block fixed q.2) w
  have hk := MM.tabulate k 42 (fun _ => build_outside _ _ _ _)
  have both := MM.pair product hk
  have combine := MM.tabulate (fun (w : PairBits L ⊕ PairBits L → F) (q : PairBits L) =>
      w (.inl q) * w (.inr q)) 1
    (fun q => Circuit.mul (Circuit.read (F:=F) (I:=PairBits L ⊕ PairBits L) (.inl q))
      (Circuit.read (F:=F) (I:=PairBits L ⊕ PairBits L) (.inr q)))
  refine MM.cost_mono (MM.congr (MM.bind both combine)
    (fun w q => (single_eq rev h j q.1 (block fixed q.2) w).symm)) ?_
  simp only [Fintype.card_sum, card_pairs]
  omega

/-- All basis vectors and all column blocks are computed by disjoint circuit copies. -/
theorem single_table_of_square {F : Type*} [Field F] [CharZero F] {L c : ℕ}
    (hsq : MM.Table (fun (w : PairBits L ⊕ PairBits L → F) (q : PairBits L) =>
      ∑ s, w (.inl (q.1,s)) * w (.inr (s,q.2))) c)
    (rev : Bool) (h : Fin 3) (Λ : Finset (BasisLabel L)) :
    MM.Table (fun (w : ChannelKey L → F) (v : (↑Λ) × Bits L × Block L) =>
      single rev h v.1.val v.2.1 v.2.2 w)
      (Λ.card * (2^L)^2 * (c + 129 * (2^L)^2)) := by
  classical
  let f (p : (↑Λ) × PairBits L) (w : ChannelKey L → F) (q : PairBits L) :=
    single rev h p.1.val q.1 (block p.2 q.2) w
  have allSlices := MM.parallel f _ (fun p => slice hsq rev h p.1.val p.2)
  let ix (v : (↑Λ) × Bits L × Block L) : ((↑Λ) × PairBits L) × PairBits L :=
    ((v.1,(v.2.2 0,v.2.2 1)),(v.2.1,v.2.2 2))
  refine MM.cost_mono (MM.congr (MM.outmap allSlices ix) (fun w v => by
    simp only [f, ix, block_eta])) ?_
  rw [Fintype.card_prod, Fintype.card_coe, card_pairs]

end VWZClique.Projection

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Projection

/-- Project a channel on one side without constructing the unprojected matrix. -/
theorem single_table {F : Type*} [Field F] [CharZero F] {L : ℕ}
    (P : MatrixAlgorithm F (2^L) (2^L) (2^L)) (hP : P.Correct)
    (rev : Bool) (h : Fin 3) (Λ : Finset (BasisLabel L)) :
    MM.Table (fun (w : ChannelKey L → F) (v : (↑Λ) × Bits L × Block L) =>
      single rev h v.1.val v.2.1 v.2.2 w)
      (Λ.card * (2^L)^2 * (P.cost + 129 * (2^L)^2)) := by
  let e : Bits L ≃ Fin (2^L) := Fintype.equivFinOfCardEq (by simp [Bits])
  exact single_table_of_square (MM.square P hP e e e) rev h Λ

end VWZClique.Projection

open VWZClique

namespace VWZClique.Double

abbrev Node {L : ℕ} (S : Finset (BasisLabel L)) := S × Bits L

variable {F : Type*} [Field F] [CharZero F] {L : ℕ}

noncomputable def leftEntry (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) (u : Node Λ) (v : Node Γ) : F :=
  (d u.1 * e v.1) * ∑ y : PairBits L, (basisEntry v.1 y : F) *
    ∑ x : PairBits L, (basisEntry u.1 x : F) * channel w 0 (block x u.2) (block y v.2)

noncomputable def midEntry (Γ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (v : Node Γ) (c : Block L) : F :=
  ∑ y' : PairBits L, (basisEntry v.1 y' : F) * channel w 1 (block y' v.2) c

noncomputable def rightEntry (Λ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (c : Block L) (u : Node Λ) : F :=
  ∑ x' : PairBits L, (basisEntry u.1 x' : F) * channel w 2 c (block x' u.2)

private theorem projection_subtype (S : Finset (BasisLabel L)) (d : BasisLabel L → F)
    (x x' : PairBits L) :
    projected S d x x' = ∑ j : S, d j * (basisEntry j x : F) * (basisEntry j x' : F) := by
  exact (Finset.sum_attach S (fun j => d j * (basisEntry j x : F) * (basisEntry j x' : F))).symm

private theorem distribute (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (x x' y y' : PairBits L) (a b c : F) :
    projected Λ d x x' * projected Γ e y y' * a * b * c =
    ∑ j : Λ, ∑ k : Γ, ((d j * e k) * ((basisEntry k y : F) * ((basisEntry j x : F) * a))) *
      (((basisEntry k y' : F) * b) * ((basisEntry j x' : F) * c)) := by
  simp only [projection_subtype, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem reorder {Z C X J K R : Type*} [Fintype Z] [Fintype C] [Fintype X]
    [Fintype J] [Fintype K] [AddCommMonoid R]
    (f : Z → Z → C → X → X → X → X → J → K → R) :
    (∑ z, ∑ a, ∑ c, ∑ x, ∑ x', ∑ y, ∑ y', ∑ j, ∑ k, f z a c x x' y y' j k) =
    ∑ j, ∑ z, ∑ k, ∑ a, ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', f z a c x x' y y' j k := by
  let E : (J × Z × K × Z × C × X × X × X × X) ≃
      (Z × Z × C × X × X × X × X × J × K) :=
    { toFun := fun ⟨j,z,k,a,c,y,x,y',x'⟩ => (z,a,c,x,x',y,y',j,k)
      invFun := fun ⟨z,a,c,x,x',y,y',j,k⟩ => (j,z,k,a,c,y,x,y',x')
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : Z × Z × C × X × X × X × X × J × K → R :=
    fun ⟨z,a,c,x,x',y,y',j,k⟩ => f z a c x x' y y' j k
  simpa only [Fintype.sum_prod_type, E, Equiv.coe_fn_mk, g] using (E.sum_comp g).symm

omit [CharZero F] in
private theorem contract_sums {C X : Type*} [Fintype C] [Fintype X]
    (q : F) (s : X → F) (a : X → X → F) (b : C → X → F) (h : C → X → F) :
    q * (∑ y, s y * ∑ x, a y x) * (∑ c, (∑ y', b c y') * ∑ x', h c x') =
    ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', (q * (s y * a y x)) * (b c y' * h c x') := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum _ _ (s y), Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, Finset.mul_sum _ (b c), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x' _
  ring

/-- Expanding both projection kernels gives a three-matrix trace. -/
theorem trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F) (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w =
      ∑ u : Node Λ, ∑ v : Node Γ,
        leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u := by
  classical
  unfold doubleProjection
  simp_rw [distribute]
  rw [reorder]
  let f := fun (u : Node Λ) (v : Node Γ) =>
    leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u
  change _ = ∑ u : Node Λ, ∑ v : Node Γ, f u v
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  exact (contract_sums (d j * e k) (fun y => (basisEntry k y : F))
    (fun y x => (basisEntry j x : F) * channel w 0 (block x z) (block y a))
    (fun c y' => (basisEntry k y' : F) * channel w 1 (block y' a) c)
    (fun c x' => (basisEntry j x' : F) * channel w 2 c (block x' z))).symm

theorem matrix_trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w = Matrix.trace
      (Matrix.of (leftEntry Λ Γ d e w) *
        (Matrix.of (midEntry Γ w) * Matrix.of (rightEntry Λ w))) := by
  exact trace_identity Λ Γ d e w

end VWZClique.Double

open VWZClique Real

namespace VWZClique.Double

noncomputable def side (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ (3-δ)⌉₊
noncomputable def packets (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ δ⌉₊

theorem side_pos {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : 1 ≤ side n δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn' _)

theorem node_fits {n a : ℕ} (hn : 1 ≤ n) (δ : ℝ)
    (ha : (a : ℝ) ≤ (n : ℝ)^(2-δ)) : a*n ≤ side n δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_right ha hn'.le
  have hh : (n : ℝ)^(2-δ) * n = (n : ℝ)^(3-δ) := by
    rw [show (3:ℝ)-δ = (2-δ)+1 by ring, Real.rpow_add_one hn'.ne']
  have hh' := h.trans (hh.le.trans (Nat.le_ceil _))
  exact_mod_cast hh'

theorem block_fits {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : n^3 ≤ packets n δ * side n δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := mul_le_mul (Nat.le_ceil ((n : ℝ)^δ)) (Nat.le_ceil ((n : ℝ)^(3-δ)))
    (Real.rpow_nonneg hn'.le _) (by positivity)
  rw [← Real.rpow_add hn',show δ+(3-δ) = (3:ℝ) by ring] at h
  norm_num at h
  exact_mod_cast h

theorem ceil_bound {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2*x := by
  have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  linarith

theorem length_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ H : ℝ, 0 < H ∧ ∀ L : ℕ, (L:ℝ)+1 ≤ H * (((2:ℝ)^L)^σ) := by
  let a : ℝ := (2 : ℝ)^σ
  have ha : 1 < a := Real.one_lt_rpow (by norm_num) hσ
  have hd : 0 < a-1 := by linarith
  refine ⟨1+1/(a-1),by positivity,?_⟩
  intro L
  have hL := one_add_mul_sub_le_pow (by linarith : -1 ≤ a) L
  have haL : 1 ≤ a^L := one_le_pow₀ ha.le
  have hs : ((2 : ℝ)^L)^σ = a^L := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  rw [hs, add_mul, one_mul,one_div_mul_eq_div]
  have hfrac : (L : ℝ) ≤ a^L/(a-1) := (le_div_iff₀ hd).mpr (by linarith)
  linarith

end VWZClique.Double

open Real

namespace VWZClique.Double

def budget (a g n p T q t : ℕ) : ℕ :=
  (a*n^2*(p+129*n^2) + a*n^2*T + (a*n)*(g*n)) +
  (g*n^2*(p+129*n^2) + a*n^2*(p+129*n^2)) +
  (t*(q + (a*n)*(g*n)) + 2*((a*n)*(g*n)))

private theorem exponent_product (x : ℝ) (hx : 1 ≤ x) {p q b : ℝ} (hab : p+q ≤ b) :
    x^p * x^q ≤ x^b := by
  rw [← Real.rpow_add (by linarith : 0 < x)]
  exact Real.rpow_le_rpow_of_exponent_le hx hab

noncomputable def rate (ω δ σ : ℝ) : ℝ := 3*ω-(ω-1)*δ+4*σ
noncomputable def coefficient (ω σ M H K : ℝ) : ℝ :=
  3*(M+129) + K*H + 5 + 2*(M*2^(ω+σ))

theorem coefficient_pos {ω σ M H K : ℝ} (hM : 0 < M) (hH : 0 < H) (hK : 0 ≤ K) :
    0 < coefficient ω σ M H K := by unfold coefficient; positivity

theorem budget_estimate {ω δ σ M H K : ℝ} (hω : 2 ≤ ω) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1) (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (a g n p T q : ℕ) (hn : 1 ≤ n)
    (ha : (a : ℝ) ≤ (n : ℝ)^(2-δ)) (hg : (g : ℝ) ≤ (n : ℝ)^(2-δ))
    (hp : (p : ℝ) ≤ M*(n : ℝ)^(ω+σ))
    (hT : (T : ℝ) ≤ K*H*((n : ℝ)^(2+σ)))
    (hq : (q : ℝ) ≤ M*(side n δ : ℝ)^(ω+σ)) :
    (budget a g n p T q (packets n δ) : ℝ) ≤
      coefficient ω σ M H K * (n : ℝ)^(rate ω δ σ) := by
  let x : ℝ := n
  let W := x^(rate ω δ σ)
  have hx : 1 ≤ x := by change (1:ℝ) ≤ (n:ℝ); exact_mod_cast hn
  have hx' : 0 < x := by linarith
  have hωσ : 0 ≤ ω+σ := by linarith
  have hs : (side n δ : ℝ) ≤ 2*x^(3-δ) :=
    ceil_bound (Real.one_le_rpow hx (by linarith))
  have ht : (packets n δ : ℝ) ≤ 2*x^δ := ceil_bound (Real.one_le_rpow hx hδ)
  have e₁ : (4-δ)+(ω+σ) ≤ rate ω δ σ := by
    unfold rate
    nlinarith [mul_nonneg (by linarith : 0 ≤ ω-2) (by linarith : 0 ≤ 2-δ)]
  have e₂ : (4-δ)+(2+σ) ≤ rate ω δ σ := by linarith
  have e₃ : δ+(6-2*δ) ≤ rate ω δ σ := by linarith
  have e₄ : 6-2*δ ≤ rate ω δ σ := by linarith
  have e₅ : δ+(3-δ)*(ω+σ) ≤ rate ω δ σ := by
    unfold rate; nlinarith [mul_nonneg hδ hσ]
  have a2 (v : ℕ) (hv : (v : ℝ) ≤ x^(2-δ)) : (v : ℝ)*x^2 ≤ x^(4-δ) := by
    calc
      _ ≤ x^(2-δ)*x^(2:ℝ) := by simpa using mul_le_mul_of_nonneg_right hv (sq_nonneg x)
      _ ≤ _ := exponent_product x hx (by linarith)
  have a1 (v : ℕ) (hv : (v : ℝ) ≤ x^(2-δ)) : (v : ℝ)*x ≤ x^(3-δ) := by
    calc
      _ ≤ x^(2-δ)*x^(1:ℝ) := by simpa using mul_le_mul_of_nonneg_right hv hx'.le
      _ ≤ _ := exponent_product x hx (by linarith)
  have h2 : x^2 ≤ x^(ω+σ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show (2:ℝ) ≤ ω+σ by linarith)
  have hp' : (p : ℝ) + 129*x^2 ≤ (M+129)*x^(ω+σ) := by
    change (p : ℝ) ≤ M*x^(ω+σ) at hp
    linarith
  have prep (v : ℕ) (hv : (v : ℝ) ≤ x^(2-δ)) :
      (v : ℝ)*x^2*((p : ℝ)+129*x^2) ≤ (M+129)*W := by
    calc
      _ ≤ x^(4-δ)*((M+129)*x^(ω+σ)) := mul_le_mul (a2 _ hv) hp' (by positivity) (by positivity)
      _ = (M+129)*(x^(4-δ)*x^(ω+σ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₁) (by positivity)
  have trans : (a : ℝ)*x^2*(T : ℝ) ≤ (K*H)*W := by
    calc
      _ ≤ x^(4-δ)*(K*H*x^(2+σ)) := mul_le_mul (a2 _ ha) hT (by positivity) (by positivity)
      _ = (K*H)*(x^(4-δ)*x^(2+σ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₂) (by positivity)
  let N : ℝ := (a : ℝ)*x*((g : ℝ)*x)
  have pairs : N ≤ x^(6-2*δ) := by
    calc
      _ ≤ x^(3-δ)*x^(3-δ) := mul_le_mul (a1 _ ha) (a1 _ hg) (by positivity) (by positivity)
      _ ≤ _ := exponent_product x hx (by linarith)
  have pairs' : N ≤ W := pairs.trans (Real.rpow_le_rpow_of_exponent_le hx e₄)
  have tpair : (packets n δ : ℝ)*N ≤ 2*W := by
    calc
      _ ≤ (2*x^δ)*x^(6-2*δ) := mul_le_mul ht pairs (by dsimp [N]; positivity) (by positivity)
      _ = 2*(x^δ*x^(6-2*δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₃) (by norm_num)
  have q' : (q : ℝ) ≤ (M*2^(ω+σ))*x^((3-δ)*(ω+σ)) := by
    calc
      _ ≤ M*(side n δ : ℝ)^(ω+σ) := hq
      _ ≤ M*(2*x^(3-δ))^(ω+σ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hs hωσ) hM
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_mul hx'.le]; ring
  have tq : (packets n δ : ℝ)*(q : ℝ) ≤ (2*(M*2^(ω+σ)))*W := by
    calc
      _ ≤ (2*x^δ)*((M*2^(ω+σ))*x^((3-δ)*(ω+σ))) := mul_le_mul ht q' (by positivity) (by positivity)
      _ = (2*(M*2^(ω+σ)))*(x^δ*x^((3-δ)*(ω+σ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₅) (by positivity)
  unfold budget
  push_cast
  change ((a : ℝ)*x^2*((p : ℝ)+129*x^2)+(a:ℝ)*x^2*(T:ℝ)+N) +
    ((g:ℝ)*x^2*((p:ℝ)+129*x^2)+(a:ℝ)*x^2*((p:ℝ)+129*x^2)) +
    ((packets n δ:ℝ)*((q:ℝ)+N)+2*N) ≤ coefficient ω σ M H K*W
  unfold coefficient
  linarith only [prep a ha, prep g hg, trans, pairs', tpair, tq]

end VWZClique.Double

open OAI.MatrixMultiplication.Arithmetic

namespace VWZClique.Double

variable {F : Type*} [Field F] [CharZero F] {L : ℕ}

theorem card_node (Λ : Finset (BasisLabel L)) :
    Fintype.card (Node Λ) = Λ.card * 2^L := by simp [Node,Bits]

theorem card_block (L : ℕ) : Fintype.card (Block L) = (2^L)^3 := by simp [Block,Bits]

/-- The remaining basis change is batched over all first rows and third coordinates. -/
theorem left_table (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F) {b T : ℕ}
    (hfirst : MM.Table (fun (w : ChannelKey L → F) (p : Λ × Bits L × Block L) =>
      ∑ x : PairBits L, (basisEntry p.1 x : F) *
        channel w 0 (block x p.2.1) p.2.2) b)
    (htransform : MM.Table (fun (input : PairBits L → F) (j : BasisLabel L) =>
      ∑ y, (basisEntry j y : F) * input y) T) :
    MM.Table (fun w (uv : Node Λ × Node Γ) => leftEntry Λ Γ d e w uv.1 uv.2)
      (b + (Λ.card * (2^L)^2)*T + (Λ.card * (2^L))*(Γ.card * (2^L))) := by
  classical
  let X := Node Λ × Bits L
  let readAt (p : X) (y : PairBits L) : Λ × Bits L × Block L :=
    (p.1.1,p.1.2,block y p.2)
  let pass (p : X) (u : Λ × Bits L × Block L → F) (j : BasisLabel L) :=
    ∑ y, (basisEntry j y : F) * u (readAt p y)
  have hp := MM.parallel pass T (fun p => MM.inmap htransform (readAt p))
  let take (uv : Node Λ × Node Γ) : X × BasisLabel L := ((uv.1,uv.2.2),uv.2.1)
  have hraw := MM.bind hfirst (MM.outmap hp take)
  let scale (u : Node Λ × Node Γ → F) (uv : Node Λ × Node Γ) :=
    (d uv.1.1 * e uv.2.1) * u uv
  have hs := MM.tabulate scale 1 (fun uv =>
    Circuit.mul (Circuit.const (d uv.1.1 * e uv.2.1)) (Circuit.read uv))
  have hout := MM.bind hraw hs
  have hx : Fintype.card X = Λ.card*(2^L)^2 := by
    dsimp only [X]
    rw [Fintype.card_prod,card_node]
    simp [Bits,pow_two,Nat.mul_assoc]
  rw [hx] at hout
  have hout' := MM.congr hout (g := fun w (uv : Node Λ × Node Γ) => leftEntry Λ Γ d e w uv.1 uv.2)
    (fun w uv => by simp only [scale,pass,take,readAt,leftEntry])
  have hbits : Fintype.card (Bits L) = 2^L := by simp [Bits]
  simpa only [Fintype.card_prod,Fintype.card_coe,hbits,Nat.mul_one] using hout'

end VWZClique.Double

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Double

variable {F : Type*} [Field F] [CharZero F] {L : ℕ}

abbrev singleCost (a n p : ℕ) := a * n^2 * (p + 129*n^2)

noncomputable def singleFn (rev : Bool) (h : Fin 3) (Λ : Finset (BasisLabel L))
    (w : ChannelKey L → F) (v : Λ × Bits L × Block L) : F :=
  ∑ x : PairBits L, (basisEntry v.1 x : F) *
    (if rev then channel w h v.2.2 (block x v.2.1) else channel w h (block x v.2.1) v.2.2)

theorem build (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (T p s t : ℕ) (Q : MatrixAlgorithm F s s s) (hQ : Q.Correct)
    (hu : Λ.card * 2^L ≤ s) (hv : Γ.card * 2^L ≤ s) (hw : (2^L)^3 ≤ t*s)
    (hrow : ∀ (rev : Bool) (h : Fin 3) (S : Finset (BasisLabel L)),
      MM.Table (singleFn (F := F) rev h S) (singleCost S.card (2^L) p))
    (htransform : MM.Table (fun (u : PairBits L → F) (j : BasisLabel L) =>
      ∑ y, (basisEntry j y : F) * u y) T) :
    computesWithin (doubleProjection Λ Γ d e) (budget Λ.card Γ.card (2^L) p T Q.cost t) := by
  classical
  have hA := left_table Λ Γ d e (hrow false 0 Λ) htransform
  let readB (vc : Node Γ × Block L) : Γ × Bits L × Block L := (vc.1.1,vc.1.2,vc.2)
  let readC (cu : Block L × Node Λ) : Λ × Bits L × Block L := (cu.2.1,cu.2.2,cu.1)
  have hB := MM.outmap (hrow false 1 Γ) readB
  have hC := MM.outmap (hrow true 2 Λ) readC
  have hM := MM.trace Q hQ (U := Node Λ) (V := Node Γ) (W := Block L)
    (by simpa only [card_node] using hu) (by simpa only [card_node] using hv)
    (by simpa only [card_block] using hw)
  have hTab := MM.bind (MM.pair hA (MM.pair hB hC)) hM
  have ho := MM.congr hTab (g := fun w (_ : Unit) => doubleProjection Λ Γ d e w)
    (fun w _ => (trace_identity Λ Γ d e w).symm)
  have hcost := Circuit.computes (MM.toBuild ho ())
  convert! hcost using 1
  simp only [budget,singleCost,card_node]
  norm_cast
  ring

/-- The analytic reduction needs only square multiplication and the single-channel circuit. -/
theorem conclude (ω : ℝ) (hω : 2 ≤ ω) (hadm : AdmissibleExponent F ω)
    (hT : ∃ K : ℕ, ∀ L, MM.Table (fun (u : PairBits L → F) (j : BasisLabel L) =>
      ∑ y, (basisEntry j y : F) * u y) (K*(L+1)*4^L))
    (hsingle : ∀ (L : ℕ) (P : MatrixAlgorithm F (2^L) (2^L) (2^L)), P.Correct →
      ∀ (rev : Bool) (h : Fin 3) (S : Finset (BasisLabel L)),
      MM.Table (singleFn (F := F) rev h S) (singleCost S.card (2^L) P.cost))
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F),
      (Λ.card : ℝ) ≤ ((2 : ℝ)^L)^(2-δ) → (Γ.card : ℝ) ≤ ((2 : ℝ)^L)^(2-δ) →
      computesWithin (doubleProjection Λ Γ d e) (C*((2 : ℝ)^L)^(3*ω-(ω-1)*δ+η)) := by
  let σ := η/4
  have hσ : 0 < σ := by dsimp [σ]; linarith
  obtain ⟨M,hM,alg⟩ := hadm σ hσ
  obtain ⟨H,hH,hL⟩ := length_bound σ hσ
  obtain ⟨K,hK⟩ := hT
  refine ⟨coefficient ω σ M H K,coefficient_pos hM hH (by positivity),?_⟩
  intro L Λ Γ d e ha hg
  let n : ℕ := 2^L
  have hn : 1 ≤ n := one_le_pow₀ (by decide : 1 ≤ (2:ℕ))
  have hn' : (n : ℝ) = 2^L := by simp [n]
  have hx' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← hn'] at ha hg
  obtain ⟨P,hP,hpc⟩ := alg n hn
  obtain ⟨Q,hQ,hqc⟩ := alg (side n δ) (side_pos hn δ)
  have ht := hK L
  have hc := build Λ Γ d e (K*(L+1)*4^L) P.cost (side n δ) (packets n δ)
    Q hQ (node_fits hn δ ha) (node_fits hn δ hg) (block_fits hn δ)
    (hsingle L P hP) ht
  have htrans : ((K*(L+1)*4^L : ℕ) : ℝ) ≤ (K : ℝ)*H*(n : ℝ)^(2+σ) := by
    have h4 : (4 : ℝ)^L = (n : ℝ)^2 := by rw [hn',← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    have := hL L
    rw [← hn'] at this
    push_cast
    rw [h4,Real.rpow_add hx',Real.rpow_two]
    calc
      _ ≤ (K : ℝ)*(H*(n : ℝ)^σ)*(n : ℝ)^2 := by gcongr
      _ = _ := by ring
  have hbudget := budget_estimate hω hδ.le hδ' hσ.le hM.le hH.le (by positivity : 0 ≤ (K:ℝ))
    Λ.card Γ.card n P.cost (K*(L+1)*4^L) Q.cost hn ha hg hpc htrans hqc
  have eEq : rate ω δ σ = 3*ω-(ω-1)*δ+η := by unfold rate σ; ring
  rw [hn',eEq] at hbudget
  obtain ⟨r,p,o,hh,he⟩ := hc
  exact ⟨r,p,o,hh.trans hbudget,he⟩

end VWZClique.Double

open VWZClique OAI.MatrixMultiplication.Arithmetic

theorem solution :
    ∀ (F : Type*) [Field F] [CharZero F] (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ)
        (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F),
        (Λ.card : ℝ) ≤ ((2 : ℝ)^L)^(2-δ) →
        (Γ.card : ℝ) ≤ ((2 : ℝ)^L)^(2-δ) →
        computesWithin (doubleProjection Λ Γ d e)
          (C * ((2 : ℝ)^L)^(3 * omega F - (omega F - 1)*δ + η)) := by
  intro F _ _ δ hδ hδ' η hη
  apply Double.conclude (omega F) (MM.omega_two_le F) (MM.omega_admissible F) _ _ δ hδ hδ' η hη
  · obtain ⟨K,hK⟩ := VWZClique.basis_transform
    exact ⟨K,fun L => hK F L⟩
  · exact fun L P hP rev h S => Projection.single_table P hP rev h S
