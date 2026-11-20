-- Prove2me | solution 1 for VWZClique.no_two_wedges
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T01:26:37.002185+00:00
-- url     : https://prove2.me/submissions/4adaec04-4a3b-49d8-ace6-c7af59de6ca0

import Definitions.Def_VWZClique_Weighted

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

open VWZClique
namespace VWZClique.SparseProof

private theorem make_wedge {H : SimpleGraph V} {u i v : V} (hu : H.Adj i u) (hv : H.Adj i v)
    (hne : u ≠ v) : wedge H ![u,i,v] := by
  have hui := hu.ne
  have hiv := hv.ne
  refine ⟨?_,hu.symm,hv⟩
  intro x y he
  fin_cases x <;> fin_cases y <;> simp_all

theorem hitting_set (H : SimpleGraph V)
    (hh : ¬ ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧ ∀ i j, f i ≠ g j) :
    ∃ S : Finset V, S.card ≤ 3 ∧
      ∀ i u v : V, i ∉ S → u ∉ S → v ∉ S → H.Adj i u → H.Adj i v → u = v := by
  classical
  have hit : ∃ S : Finset V, S.card ≤ 3 ∧ ∀ g, wedge H g → ∃ k, g k ∈ S := by
    by_cases h : ∃ f, wedge H f
    · obtain ⟨f,hf⟩ := h
      refine ⟨Finset.univ.image f, Finset.card_image_le.trans (by simp), ?_⟩
      intro g hg
      by_contra! hd
      apply hh
      exact ⟨f,g,hf,hg,fun i j hij => hd j (hij ▸ Finset.mem_image_of_mem f (Finset.mem_univ i))⟩
    · exact ⟨∅,by simp,fun g hg => (h ⟨g,hg⟩).elim⟩
  obtain ⟨S,hs,hhit⟩ := hit
  refine ⟨S,hs,?_⟩
  intro i u v hi hu hv heu hev
  by_contra hne
  obtain ⟨k,hk⟩ := hhit _ (make_wedge heu hev hne)
  fin_cases k <;> simp_all

abbrev Bag := Finset V
abbrev Bucket := Option Bag
abbrev Fiber (key : V → Bucket) (b : Bucket) := {i : V // key i = b}

theorem matching_partition (H : SimpleGraph V)
    (hh : ¬ ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧ ∀ i j, f i ≠ g j) :
    ∃ key : V → Bucket, Fintype.card (Fiber key none) ≤ 3 ∧
      (∀ b : Bag, Fintype.card (Fiber key (some b)) ≤ 2) ∧
      ∀ i j, H.Adj i j → key i = none ∨ key j = none ∨ key i = key j := by
  classical
  obtain ⟨S,hs,hm⟩ := hitting_set H hh
  let bag := fun i : V => Finset.univ.filter fun v : V => v ∉ S ∧ (v = i ∨ H.Adj i v)
  let key := fun i : V => if i ∈ S then (none : Bucket) else some (bag i)
  have mem_self (i : V) (hi : i ∉ S) : i ∈ bag i := by simp [bag,hi]
  have bag_size (i : V) (hi : i ∉ S) : (bag i).card ≤ 2 := by
    by_cases h : ∃ v, v ∉ S ∧ H.Adj i v
    · obtain ⟨v,hv,he⟩ := h
      apply (Finset.card_le_card (t := {i,v}) ?_).trans Finset.card_le_two
      intro x hx
      obtain ⟨hx,hxi|hedge⟩ := (Finset.mem_filter.mp hx).2
      · simp [hxi]
      · simp [hm i x v hi hx hv hedge he]
    · have sub : bag i ⊆ {i} := by
        intro x hx
        obtain ⟨hx,hxi|he⟩ := (Finset.mem_filter.mp hx).2
        · simp [hxi]
        · exact (h ⟨x,hx,he⟩).elim
      exact (Finset.card_le_card sub).trans (by simp)
  have same {i j : V} (hi : i ∉ S) (hj : j ∉ S) (he : H.Adj i j) : bag i ⊆ bag j := by
    intro x hx
    obtain ⟨hx,hxi|he'⟩ := (Finset.mem_filter.mp hx).2
    · subst x; simp [bag,hi,he.symm]
    · have := hm i x j hi hx hj he' he
      subst x; exact mem_self _ hj
  refine ⟨key,?_,?_,?_⟩
  · have : Finset.univ.filter (fun i => key i = none) = S := by ext i; simp [key]
    simpa only [Fiber, Fintype.card_subtype, this] using hs
  · intro b
    have hcard : Fintype.card (Fiber key (some b)) =
        (Finset.univ.filter (fun i => key i = some b)).card := Fintype.card_subtype _
    rw [hcard]
    let T := Finset.univ.filter (fun i => key i = some b)
    change T.card ≤ 2
    by_cases h : T.Nonempty
    · obtain ⟨i,hi⟩ := h
      have read (x : V) (hx : x ∈ T) : x ∉ S ∧ bag x = b := by
        have hh := (Finset.mem_filter.mp hx).2
        by_cases hm : x ∈ S <;> simp_all [key]
      have ⟨hn, he⟩ := read i hi
      apply (Finset.card_le_card (t := b) ?_).trans (he ▸ bag_size i hn)
      intro x hx
      have ⟨hn', he'⟩ := read x hx
      exact he' ▸ mem_self x hn'
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  · intro i j he
    by_cases hi : i ∈ S
    · simp [key,hi]
    by_cases hj : j ∈ S
    · simp [key,hj]
    exact Or.inr (Or.inr (by simp [key,hi,hj,Finset.Subset.antisymm (same hi hj he) (same hj hi he.symm)]))

end VWZClique.SparseProof

open VWZClique
namespace VWZClique.SparseProof

abbrev Token := V ⊕ V × V
abbrev Assignment (key : V → Bucket) (n : ℕ) (b : Bucket) := Fiber key b → Fin n

open Classical in
noncomputable def factor {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V)
    (w : WeightKey n → F) (x : V → Fin n) : Token → F
  | .inl i => w (.inl (i,x i))
  | .inr (i,j) => if i < j ∧ H.Adj i j then w (.inr (i,j,x i,x j)) else 1

def owner (key : V → Bucket) : Token → Bag
  | .inl i => (key i).getD ∅
  | .inr (i,j) => (key i).getD ((key j).getD ∅)

def localAssignment {n : ℕ} (key : V → Bucket) (zero : Fin n) (z : Assignment key n none)
    (k : Bag) (y : Assignment key n (some k)) (i : V) : Fin n :=
  if h : key i = none then z ⟨i,h⟩ else if h' : key i = some k then y ⟨i,h'⟩ else zero

noncomputable def piece {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V) (key : V → Bucket)
    (zero : Fin n) (z : Assignment key n none) (k : Bag) (y : Assignment key n (some k))
    (w : WeightKey n → F) : F :=
  ∏ t ∈ Finset.univ.filter (fun t => owner key t = k), factor H w (localAssignment key zero z k y) t

def assignmentEquiv (key : V → Bucket) (n : ℕ) :
    (V → Fin n) ≃ Assignment key n none × ((k : Bag) → Assignment key n (some k)) :=
  (Equiv.piCongrFiberwise (f := key) (γ₁ := fun _ => Fin n)
    (fun b => Equiv.refl (Assignment key n b))).trans Equiv.piOptionEquivProd

theorem local_matches {n : ℕ} (key : V → Bucket) (zero : Fin n)
    (x : V → Fin n) (k : Bag) (i : V) (hi : key i = none ∨ key i = some k) :
    localAssignment key zero (fun u => x u.val) k (fun u => x u.val) i = x i := by
  rcases hi with h | h <;> simp [localAssignment,h]

theorem restrict_factor {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V) (key : V → Bucket)
    (hedge : ∀ i j, H.Adj i j → key i = none ∨ key j = none ∨ key i = key j)
    (zero : Fin n) (x : V → Fin n) (t : Token) (w : WeightKey n → F) :
    let k := owner key t
    factor H w (localAssignment key zero (fun u => x u.val) k (fun u => x u.val)) t =
    factor H w x t := by
  classical
  cases t with
  | inl i =>
    change w (.inl (_,localAssignment _ _ _ _ _ i)) = w (.inl (_,x i))
    rw [local_matches]
    cases h : key i <;> simp [owner,h]
  | inr v =>
    obtain ⟨i,j⟩ := v
    by_cases he : i < j ∧ H.Adj i j
    · simp only [factor, if_pos he]
      have h := hedge i j he.2
      have hi : key i = none ∨ key i = some (owner key (.inr (i,j))) := by
        cases hi : key i <;> simp [owner,hi]
      have hj : key j = none ∨ key j = some (owner key (.inr (i,j))) := by
        cases hi : key i <;> cases hj : key j <;> simp_all [owner]
      rw [local_matches _ _ _ _ _ hi, local_matches _ _ _ _ _ hj]
    · simp [factor,he]

theorem factorization {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V) (key : V → Bucket)
    (hedge : ∀ i j, H.Adj i j → key i = none ∨ key j = none ∨ key i = key j)
    (zero : Fin n) (w : WeightKey n → F) :
    weightedSum H w = ∑ z : Assignment key n none, ∏ k : Bag,
      ∑ y : Assignment key n (some k), piece H key zero z k y w := by
  classical
  have localProd (x : V → Fin n) :
      (∏ t : Token, factor H w x t) =
      ∏ k : Bag, piece H key zero (fun u => x u.val) k (fun u => x u.val) w := by
    rw [← Finset.prod_fiberwise Finset.univ (owner key)]
    apply Finset.prod_congr rfl
    intro k _
    apply Finset.prod_congr rfl
    intro t ht
    have hk := (Finset.mem_filter.mp ht).2
    subst k
    exact (restrict_factor H key hedge zero x t w).symm
  let e := assignmentEquiv key n
  calc
    weightedSum H w = ∑ x : V → Fin n, ∏ t : Token, factor H w x t := by
      simp [weightedSum, Fintype.prod_sum_type, Fintype.prod_prod_type, factor]
    _ = ∑ x : V → Fin n, ∏ k : Bag, piece H key zero ((e x).1) k ((e x).2 k) w :=
      Finset.sum_congr rfl fun x _ => localProd x
    _ = ∑ p : Assignment key n none × ((k : Bag) → Assignment key n (some k)),
      ∏ k : Bag, piece H key zero p.1 k (p.2 k) w := e.sum_comp (fun p => ∏ k : Bag, piece H key zero p.1 k (p.2 k) w)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.prod_sum]

theorem build_piece {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V) (key : V → Bucket)
    (zero : Fin n) (z : Assignment key n none) (k : Bag) (y : Assignment key n (some k)) :
    Circuit.Build (piece (F := F) H key zero z k y) (Fintype.card Token) := by
  classical
  let s := Finset.univ.filter (fun t => owner key t = k)
  let x := localAssignment key zero z k y
  have h (t : Token) : Circuit.Build (fun w : WeightKey n → F => factor H w x t) 0 := by
    cases t with
    | inl i => exact Circuit.read _
    | inr p =>
      obtain ⟨i,j⟩ := p
      by_cases he : i < j ∧ H.Adj i j
      · simpa [factor,he] using (Circuit.read (F := F) (I := WeightKey n) (.inr (i,j,x i,x j)))
      · simpa [factor,he] using (Circuit.const (I := WeightKey n) (1:F))
  refine Circuit.cost_mono (Circuit.prod s (fun t w => factor H w x t) 0 (fun t _ => h t)) ?_
  simpa using Finset.card_le_univ s

end VWZClique.SparseProof

open VWZClique VWZClique.SparseProof

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F] [CharZero F],
      ∀ (n : ℕ), 1 ≤ n → ∀ H : SimpleGraph V,
      (¬ ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧
        ∀ i j, f i ≠ g j) →
      computesWithin (weightedSum (F := F) (n := n) H) (C * (n : ℝ)^5) := by
  classical
  let K := Fintype.card Bag
  let Q := Fintype.card Token
  let C := K*(Q+2)+1
  refine ⟨(C : ℕ), by dsimp [C]; positivity, ?_⟩
  intro F _ _ n hn H hh
  obtain ⟨key,hr,hs,hedge⟩ := matching_partition H hh
  let zero : Fin n := ⟨0,hn⟩
  have card (b : Bucket) : Fintype.card (Assignment key n b) = n^(Fintype.card (Fiber key b)) := by
    simp [Assignment]
  have inner (z : Assignment key n none) (k : Bag) :
      Circuit.Build (fun w : WeightKey n → F => ∑ y, piece H key zero z k y w) (n^2*(Q+1)) := by
    apply Circuit.cost_mono (Circuit.sum Finset.univ _ Q (fun y _ => build_piece H key zero z k y))
    rw [Finset.card_univ, card]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn (hs k))
  have middle (z : Assignment key n none) :
      Circuit.Build (fun w : WeightKey n → F => ∏ k : Bag, ∑ y, piece H key zero z k y w)
        (K*(n^2*(Q+1)+1)) := Circuit.prod Finset.univ _ _ (fun k _ => inner z k)
  have total := Circuit.sum Finset.univ _ _ (fun z _ => middle z)
  have ident : weightedSum (F := F) (n := n) H =
      (fun w => ∑ z : Assignment key n none, ∏ k : Bag, ∑ y, piece H key zero z k y w) :=
    funext (factorization H key hedge zero)
  have limit : (Finset.univ : Finset (Assignment key n none)).card * (K*(n^2*(Q+1)+1)+1) ≤ C*n^5 := by
    rw [Finset.card_univ, card]
    have h1 : 1 ≤ n^2 := Nat.one_le_pow _ _ hn
    calc
      _ ≤ n^3 * (K*(n^2*(Q+1)+1)+1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn hr)
      _ ≤ n^3 * (K*(n^2*(Q+1)+n^2)+n^2) := by gcongr
      _ = _ := by dsimp [C]; ring
  rw [ident]
  exact_mod_cast Circuit.computes (Circuit.cost_mono total limit)
