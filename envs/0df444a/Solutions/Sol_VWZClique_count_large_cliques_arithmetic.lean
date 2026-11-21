-- Prove2me | solution 1 for VWZClique.count_large_cliques_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T02:24:35.216854+00:00
-- url     : https://prove2.me/submissions/7791a28b-f02a-422e-9b8d-c0a97fb94199

import Definitions.Def_VWZClique_Weighted
import Definitions.Def_VWZClique_Count
import Theorems.Thm_VWZClique_weighted_nine

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

/-! Exact reduction from unordered cliques to a single weighted nine-vertex instance.
    A fixed vertex fills unused slots, and order constraints choose one increasing
    enumeration of each clique. The extra slots allow all clique sizes. -/

namespace VWZClique
namespace BlockReduction

open Finset
open scoped BigOperators
noncomputable section
open Classical

/-- An increasing enumeration of a clique. -/
def Ordered {n k : ℕ} (G : SimpleGraph (Fin n)) (f : Fin k → Fin n) : Prop :=
  ∀ i j, i < j → f i < f j ∧ G.Adj (f i) (f j)

/-- A clique has exactly one increasing enumeration. -/
theorem card_ordered {n k : ℕ} (G : SimpleGraph (Fin n)) :
    (univ.filter fun f : Fin k → Fin n => Ordered G f).card = count G k := by
  classical
  unfold count
  apply Finset.card_bij (fun f _ => univ.image f)
  · intro f hf
    have hg : Ordered G f := (mem_filter.mp hf).2
    have hmono : StrictMono f := fun i j h => (hg i j h).1
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, ?_⟩
    · simpa using card_image_of_injective univ hmono.injective
    · intro u hu v hv huv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := mem_image.mp hv
      rcases lt_trichotomy i j with hij | hij | hij
      · exact (hg i j hij).2
      · exact (huv (congrArg f hij)).elim
      · exact (hg j i hij).2.symm
  · intro f hf g hg hfg
    have hm : StrictMono f := fun i j h => ((mem_filter.mp hf).2 i j h).1
    have hn : StrictMono g := fun i j h => ((mem_filter.mp hg).2 i j h).1
    have hcard : (univ.image f).card = k := by
      simpa using card_image_of_injective univ hm.injective
    apply (orderEmbOfFin_unique hcard (fun x => mem_image.mpr ⟨x, mem_univ _, rfl⟩) hm).trans
    symm
    apply orderEmbOfFin_unique hcard _ hn
    intro x
    rw [hfg]
    exact mem_image.mpr ⟨x, mem_univ _, rfl⟩
  · intro s hs
    obtain ⟨hsize, hclique⟩ := mem_filter.mp hs
    have hcard := (mem_powersetCard.mp hsize).2
    let f := s.orderEmbOfFin hcard
    refine ⟨f, mem_filter.mpr ⟨mem_univ _, ?_⟩, s.image_orderEmbOfFin_univ hcard⟩
    intro i j hij
    have hlt := f.strictMono hij
    exact ⟨hlt, hclique _ (s.orderEmbOfFin_mem hcard _) _ (s.orderEmbOfFin_mem hcard _) hlt.ne⟩

/-- Group and coordinate of one padded slot, with row-major numbering. -/
def slot {t : ℕ} (i : V) (p : Fin t) : Fin (9*t) := finProdFinEquiv (i,p)

/-- Value in an encoded block. -/
def digit {n t : ℕ} (a : Fin (n^t)) : Fin t → Fin n := finFunctionFinEquiv.symm a

/-- Read the assignment at a padded slot. -/
def readSlot {n t : ℕ} (a : V → Fin (n^t)) (z : Fin (9*t)) : Fin n :=
  let ij := finProdFinEquiv.symm z
  digit (a ij.1) ij.2

@[simp]
theorem readSlot_slot {n t : ℕ} (a : V → Fin (n^t)) (i : V) (p : Fin t) :
    readSlot a (slot i p) = digit (a i) p := by simp [readSlot, slot]

/-- Assemble the nine block labels from a tuple, filling inactive slots by `pad`. -/
def pack {n k t : ℕ} (pad : Fin n) (f : Fin k → Fin n) : V → Fin (n^t) :=
  fun i => finFunctionFinEquiv fun p =>
    if h : (slot i p).val < k then f ⟨(slot i p).val, h⟩ else pad

@[simp]
theorem readSlot_pack {n k t : ℕ} (pad : Fin n) (f : Fin k → Fin n) (z : Fin (9*t)) :
    readSlot (pack (t := t) pad f) z = if h : z.val < k then f ⟨z.val, h⟩ else pad := by
  obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective z
  change readSlot _ (slot i p) = _
  rw [readSlot_slot]
  simp [digit, pack, slot]

/-- Read the first `k` slots, discarding padding. -/
def unpack {n k t : ℕ} (h : k ≤ 9*t) (a : V → Fin (n^t)) : Fin k → Fin n :=
  fun z => readSlot a (Fin.castLE h z)

@[simp]
theorem unpack_pack {n k t : ℕ} (h : k ≤ 9*t) (pad : Fin n) (f : Fin k → Fin n) :
    unpack h (pack pad f) = f := by
  funext z
  simp [unpack, z.isLt]

/-- A pair of active slots holds adjacent vertices in the order fixed by its positions. -/
def compatible {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (r s : Fin (9*t)) (u v : Fin n) : Prop :=
  r.val < k → s.val < k →
    (r < s → u < v ∧ G.Adj u v) ∧ (s < r → v < u ∧ G.Adj v u)

theorem compatible_comm {n t k : ℕ} {G : SimpleGraph (Fin n)}
    {r s : Fin (9*t)} {u v : Fin n} :
    compatible G k r s u v ↔ compatible G k s r v u := by
  unfold compatible
  constructor <;> intro h h₁ h₂ <;> exact (h h₂ h₁).symm

/-- Unary constraints enforce internal pairs and a unique padding value. -/
def unaryOK {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (pad : Fin n) (i : V) (a : Fin (n^t)) : Prop :=
  (∀ p, k ≤ (slot i p).val → digit a p = pad) ∧
  ∀ p q, compatible G k (slot i p) (slot i q) (digit a p) (digit a q)

/-- An edge constraint checks all pairs crossing the two blocks. -/
def edgeOK {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (i j : V)
    (a b : Fin (n^t)) : Prop :=
  ∀ p q, compatible G k (slot i p) (slot j q) (digit a p) (digit b q)

def valid {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (pad : Fin n)
    (a : V → Fin (n^t)) : Prop :=
  (∀ i, unaryOK G k pad i (a i)) ∧
  ∀ i j, i < j → edgeOK G k i j (a i) (a j)

private theorem valid_iff_slots {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} :
    valid G k pad a ↔
      (∀ r, k ≤ r.val → readSlot a r = pad) ∧
      ∀ r s, compatible G k r s (readSlot a r) (readSlot a s) := by
  constructor
  · rintro ⟨hu, he⟩
    constructor
    · intro r
      obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective r
      change k ≤ (slot i p).val → readSlot a (slot i p) = pad
      simpa only [readSlot_slot] using (hu i).1 p
    · intro r s
      obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective r
      obtain ⟨⟨j,q⟩, rfl⟩ := finProdFinEquiv.surjective s
      change compatible _ _ (slot i p) (slot j q) (readSlot a (slot i p)) (readSlot a (slot j q))
      rw [readSlot_slot, readSlot_slot]
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact he i j hij p q
      · exact (hu i).2 p q
      · exact compatible_comm.mpr (he j i hji q p)
  · rintro ⟨hp, hc⟩
    constructor
    · intro i
      constructor
      · intro p
        simpa only [readSlot_slot] using hp (slot i p)
      · intro p q
        simpa only [readSlot_slot] using hc (slot i p) (slot i q)
    · intro i j _ p q
      simpa only [readSlot_slot] using hc (slot i p) (slot j q)

theorem pack_valid {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {f : Fin k → Fin n} (hf : Ordered G f) : valid (t := t) G k pad (pack pad f) := by
  apply valid_iff_slots.mpr
  constructor
  · intro r hr
    simp [readSlot_pack, Nat.not_lt.mpr hr]
  · intro r s hr hs
    rw [readSlot_pack, readSlot_pack, dif_pos hr, dif_pos hs]
    exact ⟨fun hij => hf _ _ hij, fun hji => hf _ _ hji⟩

theorem ordered_unpack {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} (h : k ≤ 9*t) (ha : valid G k pad a) : Ordered G (unpack h a) := by
  intro i j hij
  exact (((valid_iff_slots.mp ha).2 (Fin.castLE h i) (Fin.castLE h j)) i.isLt j.isLt).1 hij

theorem pack_unpack {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} (h : k ≤ 9*t) (ha : valid G k pad a) :
    pack pad (unpack h a) = a := by
  funext i
  apply finFunctionFinEquiv.symm.injective
  funext p
  change digit (pack pad (unpack h a) i) p = digit (a i) p
  rw [← readSlot_slot, ← readSlot_slot, readSlot_pack]
  split_ifs with hp
  · rfl
  · exact ((valid_iff_slots.mp ha).1 _ (Nat.le_of_not_gt hp)).symm

/-- Initial values use only zero and one in the weighted nine-vertex instance. -/
def weights {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (pad : Fin n) : WeightKey (n^t) → F
  | .inl (i, a) => if unaryOK G k pad i a then 1 else 0
  | .inr (i, j, a, b) => if edgeOK G k i j a b then 1 else 0

theorem weights_binary {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (pad : Fin n) (key : WeightKey (n^t)) :
    weights (F := F) G k pad key = 0 ∨ weights (F := F) G k pad key = 1 := by
  rcases key with ⟨i,a⟩ | ⟨i,j,a,b⟩ <;> simp [weights] <;> exact Classical.em _ |>.symm

/-- The weighted sum on nine vertices is the number of unordered `k`-cliques.
    Any block width with at least `k` slots works. -/
theorem weighted_eq_count {F : Type*} [Field F] {n k t : ℕ} (G : SimpleGraph (Fin n))
    (pad : Fin n) (h : k ≤ 9*t) :
    weightedSum (⊤ : SimpleGraph V) (weights (F := F) (t := t) G k pad) =
    (count G k : F) := by
  classical
  have hn : (univ.filter fun f : Fin k → Fin n => Ordered G f).card =
      (univ.filter fun a : V → Fin (n^t) => valid G k pad a).card := by
    apply Finset.card_bij (fun f _ => pack pad f)
    · intro f hf
      exact mem_filter.mpr ⟨mem_univ _, pack_valid (mem_filter.mp hf).2⟩
    · intro f _ g _ hfg
      simpa using congrArg (unpack h) hfg
    · intro a ha
      obtain hv := (mem_filter.mp ha).2
      exact ⟨unpack h a, mem_filter.mpr ⟨mem_univ _, ordered_unpack h hv⟩, pack_unpack h hv⟩
  rw [← card_ordered G, hn]
  unfold weightedSum
  calc
    _ = ∑ a : V → Fin (n^t), (if valid G k pad a then (1:F) else 0) := by
      apply sum_congr rfl
      intro a _
      by_cases hu : ∀ i, unaryOK G k pad i (a i)
      · have hones : (∏ i : V, weights (F := F) G k pad (.inl (i,a i))) = 1 :=
          prod_eq_one fun i _ => by simp [weights, hu i]
        rw [hones, one_mul]
        by_cases he : ∀ i j, i < j → edgeOK G k i j (a i) (a j)
        · rw [if_pos (show valid G k pad a from ⟨hu,he⟩)]
          apply prod_eq_one
          intro i _
          apply prod_eq_one
          intro j _
          by_cases hij : i < j
          · simp [hij, SimpleGraph.top_adj, hij.ne, weights, he i j hij]
          · simp [hij]
        · rw [if_neg (show ¬ valid G k pad a from fun hh => he hh.2)]
          obtain ⟨i,hi⟩ := not_forall.mp he
          obtain ⟨j,hj⟩ := not_forall.mp hi
          have hij : i < j := by by_contra h'; exact hj (fun h => (h' h).elim)
          have hbad : ¬ edgeOK G k i j (a i) (a j) := fun h => hj (fun _ => h)
          apply prod_eq_zero (mem_univ i)
          apply prod_eq_zero (mem_univ j)
          simp [hij, SimpleGraph.top_adj, hij.ne, weights, hbad]
      · rw [if_neg (show ¬ valid G k pad a from fun hh => hu hh.1)]
        obtain ⟨i,hi⟩ := not_forall.mp hu
        apply mul_eq_zero_of_left
        apply prod_eq_zero (mem_univ i)
        simp [weights, hi]
    _ = _ := Finset.sum_boole _ _

/-- The minimum common width accommodates every clique size. -/
theorem weighted_eq_count_ceil {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (k : ℕ) :
    weightedSum (⊤ : SimpleGraph V)
      (weights (F := F) (t := (k+8)/9) G k ⟨0,hn⟩) = (count G k : F) :=
  weighted_eq_count G _ (by omega)

end
end BlockReduction
end VWZClique

/-! The exponent loss from filling the nine equal-width blocks is bounded
    uniformly in the matrix multiplication exponent for `ω ≤ 3`. -/

namespace VWZClique.BlockReduction
open Classical

/-- With a nine-vertex saving `α`, the rounding from `k/9` to its ceiling
    costs at most a constant in the exponent. The threshold depends only on `α`. -/
theorem grouped_exponent {α ω : ℝ} (hα : 0 < α) (hω : ω ≤ 3) (hscale : 0 ≤ 3*ω-α)
    {k : ℕ} (hk : ⌈144 / α⌉₊ ≤ k) :
    (((k+8)/9 : ℕ) : ℝ) * (3*ω-α) ≤ (ω-α/6)*(k:ℝ)/3 := by
  have hsize : 9 * ((k+8)/9) ≤ k+8 := Nat.mul_div_le _ _
  have hsize' : 9 * (((k+8)/9 : ℕ) : ℝ) ≤ (k:ℝ)+8 := by exact_mod_cast hsize
  have ht : 144 / α ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hcap := (div_le_iff₀ hα).mp ht
  have hround := mul_le_mul_of_nonneg_right hsize' hscale
  nlinarith

/-- Rescaling the domain `N = n^ceil(k/9)` respects the target final time bound. -/
theorem grouped_rpow {α ω : ℝ} (hα : 0 < α) (hω : ω ≤ 3) (hscale : 0 ≤ 3*ω-α)
    {k n : ℕ} (hk : ⌈144 / α⌉₊ ≤ k) (hn : 1 ≤ n) :
    ((n^((k+8)/9) : ℕ) : ℝ)^(3*ω-α) ≤ (n:ℝ)^((ω-α/6)*(k:ℝ)/3) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (grouped_exponent hα hω hscale hk)

/-- Time bounds for the fixed RAM program are closed upwards in their exponent. -/
theorem countsWithin_mono {k : ℕ} {e f : ℝ} (hef : e ≤ f) (h : countsWithin k e) :
    countsWithin k f := by
  obtain ⟨p,b,C,hb,hC,hp⟩ := h
  refine ⟨p,b,C,hb,hC,?_⟩
  intro n G hn
  obtain ⟨t,ht,hrun⟩ := hp n G hn
  refine ⟨t,ht.trans (mul_le_mul_of_nonneg_left ?_ hC.le),hrun⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) hef

end VWZClique.BlockReduction

/-! Cost of constructing the grouped clique instance from the adjacency matrix. -/

namespace VWZClique.BlockReduction
open OAI.MatrixMultiplication.Arithmetic
open scoped BigOperators
open Classical
noncomputable section

def adjacency {F : Type*} [Field F] {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fin n × Fin n → F := fun ij => if G.Adj ij.1 ij.2 then 1 else 0

/-- The circuit for a pair is a single selected adjacency input, zero or one.
    Comparisons of the positions and the two labels are fixed when constructing the circuit. -/
def pairInput {F : Type*} [Field F] {n t : ℕ} (k : ℕ)
    (r s : Fin (9*t)) (u v : Fin n) (w : Fin n × Fin n → F) : F :=
  if r.val < k ∧ s.val < k then
    if r < s then (if u < v then w (u,v) else 0)
    else if s < r then (if v < u then w (v,u) else 0) else 1
  else 1

theorem pairInput_adjacency {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (r s : Fin (9*t)) (u v : Fin n) :
    pairInput k r s u v (adjacency (F := F) G) =
      if compatible G k r s u v then 1 else 0 := by
  by_cases hr : r.val < k
  · by_cases hs : s.val < k
    · rcases lt_trichotomy r s with hrs | rfl | hsr
      · by_cases ht : u < v <;>
          simp [pairInput, compatible, adjacency, hr, hs, hrs, hrs.asymm, ht]
      · simp [pairInput, compatible, hr]
      · by_cases ht : v < u <;>
          simp [pairInput, compatible, adjacency, hr, hs, hsr, hsr.asymm, ht]
    · simp [pairInput, compatible, hs]
  · simp [pairInput, compatible, hr]

theorem build_pairInput {F : Type*} [Field F] {n t : ℕ} (k : ℕ)
    (r s : Fin (9*t)) (u v : Fin n) :
    Circuit.Build (pairInput (F := F) k r s u v) 0 := by
  unfold pairInput
  split <;> first | exact Circuit.const _ | skip
  split
  · split <;> first | exact Circuit.read _ | exact Circuit.const _
  · split
    · split <;> first | exact Circuit.read _ | exact Circuit.const _
    · exact Circuit.const _

/-- Build the two input tables as polynomials in the entries of the adjacency matrix. -/
def preprocess {F : Type*} [Field F] {n t : ℕ} (k : ℕ) (pad : Fin n)
    (w : Fin n × Fin n → F) : WeightKey (n^t) → F
  | .inl (i,a) =>
    if ∀ p, k ≤ (slot i p).val → digit a p = pad then
      ∏ p, ∏ q, pairInput k (slot i p) (slot i q) (digit a p) (digit a q) w
    else 0
  | .inr (i,j,a,b) => ∏ p, ∏ q, pairInput k (slot i p) (slot j q) (digit a p) (digit b q) w

private theorem product_adjacency {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (i j : V) (a b : Fin (n^t)) :
    (∏ p, ∏ q, pairInput k (slot i p) (slot j q) (digit a p) (digit b q) (adjacency (F := F) G)) =
      if edgeOK G k i j a b then 1 else 0 := by
  by_cases he : edgeOK G k i j a b
  · rw [if_pos he]
    apply Finset.prod_eq_one
    intro p _
    apply Finset.prod_eq_one
    intro q _
    rw [pairInput_adjacency, if_pos (he p q)]
  · rw [if_neg he]
    obtain ⟨p,hp⟩ := not_forall.mp he
    obtain ⟨q,hq⟩ := not_forall.mp hp
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    rw [pairInput_adjacency, if_neg hq]

theorem preprocess_adjacency {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (pad : Fin n) :
    preprocess (F := F) (t := t) k pad (adjacency G) = weights G k pad := by
  funext key
  rcases key with ⟨i,a⟩ | ⟨i,j,a,b⟩
  · by_cases hp : ∀ p : Fin t, k ≤ (slot i p).val → digit a p = pad
    · by_cases he : edgeOK G k i i a a
      · have hu : unaryOK G k pad i a := ⟨hp,he⟩
        simp only [preprocess,weights,if_pos hp,if_pos hu]
        exact (product_adjacency G k i i a a).trans (if_pos he)
      · have hu : ¬ unaryOK G k pad i a := fun h => he h.2
        simp only [preprocess,weights,if_pos hp,if_neg hu]
        exact (product_adjacency G k i i a a).trans (if_neg he)
    · have hu : ¬ unaryOK G k pad i a := fun h => hp h.1
      simp only [preprocess,weights,if_neg hp,if_neg hu]
  · exact product_adjacency G k i j a b

private theorem all_pairs {F : Type*} [Field F] {n t : ℕ} (k : ℕ) (i j : V)
    (a b : Fin (n^t)) :
    Circuit.Build (fun w : Fin n × Fin n → F =>
      ∏ p, ∏ q, pairInput k (slot i p) (slot j q) (digit a p) (digit b q) w) (t*(t+1)) := by
  apply Circuit.cost_mono (Circuit.prod Finset.univ _ t (fun p _ => ?_)) (by simp)
  simpa using Circuit.prod Finset.univ _ 0
    (fun q _ => build_pairInput (F := F) k (slot i p) (slot j q) (digit a p) (digit b q))

theorem preprocess_table {F : Type*} [Field F] {n t : ℕ} (k : ℕ) (pad : Fin n) :
    MM.Table (preprocess (F := F) (t := t) k pad)
      (Fintype.card (WeightKey (n^t)) * (t*(t+1))) := by
  apply MM.tabulate
  intro key
  rcases key with ⟨i,a⟩ | ⟨i,j,a,b⟩
  · by_cases hp : ∀ p : Fin t, k ≤ (slot i p).val → digit a p = pad
    · simpa only [preprocess, if_pos hp] using (all_pairs (F := F) k i i a a)
    · simpa only [preprocess, if_neg hp] using
        Circuit.cost_mono (Circuit.const (I := Fin n × Fin n) (0:F)) (Nat.zero_le (t*(t+1)))
  · exact all_pairs k i j a b

/-- A weighted nine-vertex circuit, preceded by the grouped table construction,
    counts every graph from its original adjacency matrix. -/
theorem clique_circuit {F : Type*} [Field F] {n k t : ℕ} (pad : Fin n)
    (hk : k ≤ 9*t) {B : ℝ}
    (hc : computesWithin (weightedSum (F := F) (n := n^t) (⊤ : SimpleGraph V)) B) :
    ∃ (r : ℕ) (p : Program F (Fin n × Fin n) r) (o : Fin r),
      (p.cost : ℝ) ≤ ((9*(n^t) + 81*(n^t)^2) * (t*(t+1)) : ℕ) + B ∧
      ∀ G : SimpleGraph (Fin n), p.eval (adjacency G) o = (count G k : F) := by
  obtain ⟨r,p,out,hp,ep⟩ := preprocess_table (F := F) (t := t) k pad
  obtain ⟨m,q,o,hq,eqn⟩ := hc
  obtain ⟨l,s,_,new,hs,_,es⟩ := MM.splice p q out
  refine ⟨l,s,new o,?_,?_⟩
  · have hcard : Fintype.card (WeightKey (n^t)) = 9*(n^t) + 81*(n^t)^2 := by
      simp [WeightKey, V]
      ring
    rw [hcard] at hp
    calc
      (s.cost : ℝ) ≤ p.cost + (q.cost:ℝ) := by exact_mod_cast hs
      _ ≤ _ := add_le_add (by exact_mod_cast hp) hq
  · intro G
    rw [es,eqn]
    have hprep : (fun j => p.eval (adjacency G) (out j)) = weights G k pad := by
      rw [← preprocess_adjacency (F := F)]
      exact funext (ep (adjacency G))
    rw [hprep, weighted_eq_count G pad hk]

/-- Apply any nine-vertex circuit bound to the original (ungrouped) adjacency
    matrix, including the entire cost of preparing the weight tables. -/
theorem clique_circuit_saving {F : Type*} [Field F] {α ω C : ℝ}
    (ha : 0 < α) (hw : ω ≤ 3) (he : 2 ≤ 3*ω-α) (hC : 0 < C)
    (hweighted : ∀ N : ℕ, 1 ≤ N →
      computesWithin (weightedSum (F := F) (n := N) (⊤ : SimpleGraph V))
        (C*(N:ℝ)^(3*ω-α))) :
    ∀ k ≥ ⌈144/α⌉₊, ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (r : ℕ) (p : Program F (Fin n × Fin n) r) (o : Fin r),
        (p.cost : ℝ) ≤ D*(n:ℝ)^((ω-α/6)*(k:ℝ)/3) ∧
        ∀ G : SimpleGraph (Fin n), p.eval (adjacency G) o = (count G k : F) := by
  intro k hk
  let t := (k+8)/9
  let T : ℝ := (t*(t+1) : ℕ)
  refine ⟨90*T+C, by dsimp [T]; positivity, ?_⟩
  intro n hn
  let N := n^t
  have hN : 1 ≤ N := Nat.one_le_pow _ _ hn
  obtain ⟨r,p,o,hp,ep⟩ := clique_circuit (F := F) (k := k) (t := t) (⟨0,hn⟩ : Fin n)
    (by dsimp [t]; omega) (hweighted N hN)
  refine ⟨r,p,o,?_,ep⟩
  have hN' : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hNs : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  have hT : 0 ≤ T := Nat.cast_nonneg _
  have hNexp : (N:ℝ)^2 ≤ (N:ℝ)^(3*ω-α) := by
    convert Real.rpow_le_rpow_of_exponent_le hN' he using 1
    norm_num
  calc
    (p.cost : ℝ) ≤ (9*(N:ℝ)+81*(N:ℝ)^2)*T + C*(N:ℝ)^(3*ω-α) := by
      simpa only [T,N,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using hp
    _ ≤ (90*T+C)*(N:ℝ)^(3*ω-α) := by
      have hA : 9*(N:ℝ)+81*(N:ℝ)^2 ≤ 90*(N:ℝ)^(3*ω-α) := by linarith
      calc
        _ ≤ 90*(N:ℝ)^(3*ω-α)*T + C*(N:ℝ)^(3*ω-α) := by
          exact add_le_add (mul_le_mul_of_nonneg_right hA hT) le_rfl
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (grouped_rpow ha hw (by linarith) hk hn)
      (by positivity)

end
end VWZClique.BlockReduction

/-! The arithmetic-circuit analogue of the main theorem, with the input gates
    of the resulting program indexed by the original adjacency matrix. -/

namespace VWZClique.BlockReduction

open OAI.MatrixMultiplication.Arithmetic
universe u

theorem count_large_cliques_arithmetic :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ (F : Type u) [Field F] [CharZero F], ∀ k ≥ K,
      ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
        ∃ (r : ℕ) (p : Program F (Fin n × Fin n) r) (o : Fin r),
          (p.cost : ℝ) ≤ D*(n:ℝ)^((omega F-δ)*(k:ℝ)/3) ∧
          ∀ G : SimpleGraph (Fin n), p.eval (adjacency G) o = (count G k : F) := by
  obtain ⟨ε,hε,hweighted⟩ := VWZClique.weighted_nine.{u}
  let α := min (ε/2) 1
  have ha : 0 < α := lt_min (by positivity) (by norm_num)
  have ha' : α ≤ ε/2 := min_le_left _ _
  have ha1 : α ≤ 1 := min_le_right _ _
  refine ⟨α/6,by positivity,⌈144/α⌉₊,?_⟩
  intro F _ _
  obtain ⟨C,hC,hW⟩ := hweighted F (ε/2) (by positivity)
  have hw := MM.omega_two_le F
  apply clique_circuit_saving ha (MM.omega_le_three F) (by linarith) hC
  intro N hN
  obtain ⟨r,p,o,hp,he⟩ := hW N hN (⊤ : SimpleGraph V)
  refine ⟨r,p,o,hp.trans (mul_le_mul_of_nonneg_left ?_ hC.le),he⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

end VWZClique.BlockReduction

open OAI.MatrixMultiplication.Arithmetic VWZClique Classical

theorem solution :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ (F : Type*) [Field F] [CharZero F], ∀ k ≥ K,
      ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
        ∃ (r : ℕ) (p : Program F (Fin n × Fin n) r) (o : Fin r),
          (p.cost : ℝ) ≤ D * (n : ℝ)^((omega F - δ) * (k : ℝ) / 3) ∧
          ∀ G : SimpleGraph (Fin n),
            p.eval (fun ij => if G.Adj ij.1 ij.2 then 1 else 0) o = (count G k : F) :=
  BlockReduction.count_large_cliques_arithmetic
