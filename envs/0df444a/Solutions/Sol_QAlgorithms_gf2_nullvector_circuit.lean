-- Prove2me | solution 1 for QAlgorithms.gf2_nullvector_circuit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:01:39.502171+00:00
-- url     : https://prove2.me/submissions/63bb1527-8a3c-4873-a725-6590f479b916

import Definitions.Def_QAlgorithms_DeWolf_Ch03_Model
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open QAlgorithms QAlgorithms.DeWolf Classical
open scoped BigOperators
set_option autoImplicit false

@[simp] private lemma bool_false : false = (0 : Bool) := rfl
@[simp] private lemma bool_true : true = (1 : Bool) := rfl
@[simp] private lemma bool_double (b : Bool) : b + b = 0 := BooleanRing.add_self b

private inductive Program : Type → Type → Type 1
  | wire {ι κ : Type} (f : κ → ι) : Program ι κ
  | gate {ι : Type} (op : BoolOp) (a b : ι) : Program ι Unit
  | pair {ι κ τ : Type} : Program ι κ → Program ι τ → Program ι (Sum κ τ)
  | comp {ι κ τ : Type} : Program ι κ → Program κ τ → Program ι τ

private def opValue (op : BoolOp) (a b : Bool) : Bool :=
  match op with | .and => a && b | .or => a || b | .not => !a

private def Program.value {ι κ : Type} : Program ι κ → (ι → Bool) → κ → Bool
  | .wire f, x => x ∘ f
  | .gate op a b, x => fun _ => opValue op (x a) (x b)
  | .pair p q, x => Sum.elim (p.value x) (q.value x)
  | .comp p q, x => q.value (p.value x)

private def Program.cost {ι κ : Type} : Program ι κ → ℕ
  | .wire _ => 0
  | .gate _ _ _ => 1
  | .pair p q => p.cost + q.cost
  | .comp p q => p.cost + q.cost

private def values (xs : List Bool) (gs : List BoolGate) : List Bool :=
  gs.foldl (fun vs g => vs ++ [g.value vs]) xs

private lemma values_length (xs : List Bool) (gs : List BoolGate) :
    (values xs gs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [values]
  | cons g gs ih => simpa [values, List.foldl_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (xs ++ [g.value xs])

private lemma values_prefix (xs : List Bool) (gs : List BoolGate) {i : ℕ} (hi : i < xs.length) :
    (values xs gs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (values (xs ++ [g.value xs]) gs).getD i false = _
    rw [ih (xs ++ [g.value xs]) (by simp only [List.length_append, List.length_singleton]; omega)]
    exact List.getD_append xs _ false i hi

private def Program.compile {ι κ : Type} : Program ι κ → ℕ → (ι → ℕ) → List BoolGate × (κ → ℕ)
  | .wire f, _, env => ([], env ∘ f)
  | .gate op a b, N, env => ([⟨op, env a, env b⟩], fun _ => N)
  | .pair p q, N, env =>
    let gs := (p.compile N env).1
    let out := (p.compile N env).2
    let hs := (q.compile (N + gs.length) env).1
    let out' := (q.compile (N + gs.length) env).2
    (gs ++ hs, Sum.elim out out')
  | .comp p q, N, env =>
    let gs := (p.compile N env).1
    let out := (p.compile N env).2
    let hs := (q.compile (N + gs.length) out).1
    let out' := (q.compile (N + gs.length) out).2
    (gs ++ hs, out')

private def Good (N : ℕ) (gs : List BoolGate) : Prop :=
  ∀ k : Fin gs.length, (gs.get k).a < N + k ∧
    ((gs.get k).op = BoolOp.not ∨ (gs.get k).b < N + k)

private lemma good_append {N : ℕ} {gs hs : List BoolGate}
    (hg : Good N gs) (hh : Good (N + gs.length) hs) : Good N (gs ++ hs) := by
  intro k
  by_cases h : k.val < gs.length
  · simpa [List.get_eq_getElem, List.getElem_append_left h] using hg ⟨k, h⟩
  · have hk : k.val - gs.length < hs.length := by simpa using (show k.val - gs.length < hs.length by have := k.isLt; simp only [List.length_append] at this; omega)
    simpa [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt h),
      show N + gs.length + (k.val - gs.length) = N + k.val by omega] using hh ⟨k.val - gs.length, hk⟩

private lemma compile_spec {ι κ : Type} (p : Program ι κ) (N : ℕ) (env : ι → ℕ)
    (he : ∀ i, env i < N) :
    let z := p.compile N env
    z.1.length = p.cost ∧ Good N z.1 ∧ (∀ i, z.2 i < N + z.1.length) ∧
    ∀ xs : List Bool, xs.length = N → ∀ i,
      (values xs z.1).getD (z.2 i) false = p.value (fun j => xs.getD (env j) false) i := by
  induction p generalizing N with
  | wire f => simp [Program.compile, Program.cost, Good, values, Program.value, he]
  | gate op a b =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · change Good N [⟨op, env a, env b⟩]
      intro k
      have hk : k.val = 0 := by have h := k.isLt; change k.val < 1 at h; omega
      simpa [List.get_eq_getElem, hk] using And.intro (he a) (Or.inr (he b) : op = BoolOp.not ∨ env b < N)
    · intro i; simp [Program.compile]
    · intro xs hx i
      simp [Program.compile, values, Program.value, BoolGate.value, opValue, hx,
        List.getD_eq_getElem?_getD]
      cases op <;> simp
  | @pair ι κ τ p q ihp ihq =>
    obtain ⟨hp, hgp, hop, hvp⟩ := ihp N env he
    obtain ⟨hq, hgq, hoq, hvq⟩ := ihq (N + (p.compile N env).1.length) env (fun i => by have := he i; omega)
    refine ⟨by simp only [Program.compile, Program.cost, List.length_append]; rw [hq, hp], good_append hgp hgq, ?_, ?_⟩
    · intro i; cases i with
      | inl i => simpa [Program.compile, Nat.add_assoc] using (Nat.lt_add_right (q.compile (N + (p.compile N env).1.length) env).1.length (hop i))
      | inr i => simpa [Program.compile, Nat.add_assoc] using hoq i
    · intro xs hx i
      cases i with
      | inl i =>
        change (values xs ((p.compile N env).1 ++ (q.compile (N + (p.compile N env).1.length) env).1)).getD _ false = _
        simp only [values, List.foldl_append]
        change (values (values xs (p.compile N env).1) _).getD _ false = _
        rw [values_prefix _ _ (by rw [values_length, hx]; exact hop i)]
        exact hvp xs hx i
      | inr i =>
        change (values xs ((p.compile N env).1 ++ (q.compile (N + (p.compile N env).1.length) env).1)).getD _ false = _
        simp only [values, List.foldl_append]
        change (values (values xs (p.compile N env).1) _).getD _ false = _
        simp only [Program.compile, Program.value, Sum.elim_inr]
        rw [hvq _ (by rw [values_length, hx])]
        congr 1
        funext j; exact values_prefix xs _ (hx ▸ he j)
  | @comp ι κ τ p q ihp ihq =>
    obtain ⟨hp, hgp, hop, hvp⟩ := ihp N env he
    obtain ⟨hq, hgq, hoq, hvq⟩ := ihq (N + (p.compile N env).1.length) (p.compile N env).2 hop
    refine ⟨by simp only [Program.compile, Program.cost, List.length_append]; rw [hq, hp], good_append hgp hgq,
      by simpa [Program.compile, Nat.add_assoc] using hoq, ?_⟩
    intro xs hx i
    change (values xs ((p.compile N env).1 ++ (q.compile (N + (p.compile N env).1.length) (p.compile N env).2).1)).getD _ false = _
    simp only [values, List.foldl_append]
    change (values (values xs (p.compile N env).1) _).getD _ false = _
    simp only [Program.compile, Program.value]
    rw [hvq _ (by rw [values_length, hx])]
    congr 1
    funext j; exact hvp xs hx j

private def HasProgram {ι κ : Type} (f : (ι → Bool) → κ → Bool) (s : ℕ) : Prop :=
  ∃ p : Program ι κ, p.value = f ∧ p.cost ≤ s

private lemma hp_wire {ι κ : Type} (f : κ → ι) : HasProgram (fun x => x ∘ f) 0 :=
  ⟨.wire f, rfl, le_rfl⟩

private lemma hp_comp {ι κ τ : Type} {f : (ι → Bool) → κ → Bool} {g : (κ → Bool) → τ → Bool}
    {a b : ℕ} (hf : HasProgram f a) (hg : HasProgram g b) : HasProgram (fun x => g (f x)) (a+b) := by
  obtain ⟨p, rfl, hp⟩ := hf; obtain ⟨q, rfl, hq⟩ := hg
  exact ⟨.comp p q, rfl, Nat.add_le_add hp hq⟩

private lemma hp_pair {ι κ τ : Type} {f : (ι → Bool) → κ → Bool} {g : (ι → Bool) → τ → Bool}
    {a b : ℕ} (hf : HasProgram f a) (hg : HasProgram g b) :
    HasProgram (fun x => Sum.elim (f x) (g x)) (a+b) := by
  obtain ⟨p, rfl, hp⟩ := hf; obtain ⟨q, rfl, hq⟩ := hg
  exact ⟨.pair p q, rfl, Nat.add_le_add hp hq⟩

private lemma hp_mono {ι κ : Type} {f : (ι → Bool) → κ → Bool} {a b : ℕ}
    (hf : HasProgram f a) (h : a ≤ b) : HasProgram f b := by
  obtain ⟨p, hp, hc⟩ := hf; exact ⟨p, hp, hc.trans h⟩

private lemma hp_map {ι κ τ : Type} {f : (ι → Bool) → κ → Bool} {a : ℕ}
    (hf : HasProgram f a) (g : τ → κ) : HasProgram (fun x => f x ∘ g) a := by
  simpa using hp_comp hf (hp_wire g)

private lemma hp_op {ι : Type} (op : BoolOp) (a b : ι) :
    HasProgram (fun x (_ : Unit) => opValue op (x a) (x b)) 1 :=
  ⟨.gate op a b, rfl, le_rfl⟩

private lemma hp_scalar_op {ι : Type} {f g : (ι → Bool) → Unit → Bool} {a b : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) (op : BoolOp) :
    HasProgram (fun x (_ : Unit) => opValue op (f x ()) (g x ())) (a+b+1) := by
  exact hp_comp (hp_pair hf hg) (hp_op op (Sum.inl ()) (Sum.inr ()))

private lemma hp_neg {ι : Type} {f : (ι → Bool) → Unit → Bool} {a : ℕ}
    (hf : HasProgram f a) : HasProgram (fun x (_ : Unit) => !(f x ())) (a+1) := by
  exact hp_comp hf (hp_op .not () ())

private lemma hp_mul {ι : Type} {f g : (ι → Bool) → Unit → Bool} {a b : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) :
    HasProgram (fun x (_ : Unit) => f x () * g x ()) (a+b+1) :=
  hp_scalar_op hf hg .and

private lemma hp_xor_wires {ι : Type} (a b : ι) :
    HasProgram (fun x (_ : Unit) => x a + x b) 4 := by
  have ho := hp_op (ι := ι) .or a b
  have ha := hp_op (ι := ι) .and a b
  have h := hp_mul ho (hp_neg ha)
  convert h using 1
  funext x u; cases x a <;> cases x b <;> rfl

private lemma hp_add {ι : Type} {f g : (ι → Bool) → Unit → Bool} {a b : ℕ}
    (hf : HasProgram f a) (hg : HasProgram g b) :
    HasProgram (fun x (_ : Unit) => f x () + g x ()) (a+b+4) :=
  hp_comp (hp_pair hf hg) (hp_xor_wires (Sum.inl ()) (Sum.inr ()))

private lemma hp_const {ι : Type} (i : ι) (b : Bool) :
    HasProgram (fun _ : ι → Bool => fun _ : Unit => b) 3 := by
  have hx := hp_wire (fun _ : Unit => i)
  have hn := hp_neg hx
  cases b with
  | false =>
    have h := hp_mono (hp_mul hx hn) (by decide : 0+(0+1)+1 ≤ 3)
    convert h using 1
    funext x u; dsimp [opValue]; cases x i <;> rfl
  | true =>
    have h := hp_mono (hp_scalar_op hx hn .or) (by decide : 0+(0+1)+1 ≤ 3)
    convert h using 1
    funext x u; dsimp [opValue]; cases x i <;> rfl

private lemma hp_all {ι : Type} {n s : ℕ} (f : (ι → Bool) → Fin n → Bool)
    (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) : HasProgram f (n*s) := by
  induction n with
  | zero => exact ⟨.wire Fin.elim0, by funext x j; exact j.elim0, Nat.zero_le _⟩
  | succ n ih =>
    have ht := ih (fun x j => f x j.succ) (fun j => h j.succ)
    have hp := hp_pair (h 0) ht
    have hm := hp_map hp (Fin.cases (Sum.inl ()) Sum.inr)
    convert hp_mono hm (by nlinarith : s+n*s ≤ (n+1)*s) using 1
    funext x j; refine Fin.cases ?_ (fun j => ?_) j <;> rfl

private lemma hp_all_finite {ι κ : Type} [Fintype κ] {s : ℕ}
    (f : (ι → Bool) → κ → Bool) (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) :
    HasProgram f (Fintype.card κ*s) := by
  have ht := hp_all (fun x j => f x ((Fintype.equivFin κ).symm j)) (fun j => h _)
  convert hp_map ht (Fintype.equivFin κ) using 1
  funext x j; simp

private lemma hp_sum {ι : Type} (i : ι) {n s : ℕ}
    (f : (ι → Bool) → Fin n → Bool)
    (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) :
    HasProgram (fun x (_ : Unit) => ∑ j, f x j) (n*(s+4)+3) := by
  induction n with
  | zero => simpa using hp_const i false
  | succ n ih =>
    have ht := ih (fun x j => f x j.succ) (fun j => h j.succ)
    have hp := hp_add (h 0) ht
    convert hp_mono hp (by nlinarith : s+(n*(s+4)+3)+4 ≤ (n+1)*(s+4)+3) using 1
    funext x u; simp [Fin.sum_univ_succ]

private lemma hp_prod {ι : Type} (i : ι) {n s : ℕ}
    (f : (ι → Bool) → Fin n → Bool)
    (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) :
    HasProgram (fun x (_ : Unit) => ∏ j, f x j) (n*(s+1)+3) := by
  induction n with
  | zero => simpa using hp_const i true
  | succ n ih =>
    have ht := ih (fun x j => f x j.succ) (fun j => h j.succ)
    have hp := hp_mul (h 0) ht
    convert hp_mono hp (by nlinarith : s+(n*(s+1)+3)+1 ≤ (n+1)*(s+1)+3) using 1
    funext x u; simp [Fin.prod_univ_succ]

private def dot {n : ℕ} (a b : Fin n → Bool) : Bool := ∑ i, a i * b i
private def chooseBit {n : ℕ} (d : Fin n → Bool) (j : Fin n) : Bool :=
  d j * ∏ i : Fin n, if i < j then (1 + d i) else 1
private def nextBasis {n : ℕ} (V : Fin n → Fin n → Bool) (a : Fin n → Bool) : Fin n → Fin n → Bool :=
  let d := fun j => dot a (V j)
  let w := fun i => ∑ j, chooseBit d j * V j i
  fun j i => V j i + d j * w i

private lemma dot_add {n : ℕ} (a b c : Fin n → Bool) : dot a (b+c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]
private lemma dot_mul {n : ℕ} (a b : Fin n → Bool) (c : Bool) :
    dot a (fun i => c * b i) = c * dot a b := by
  simp [dot, Finset.mul_sum, mul_left_comm]

private lemma chooseBit_eq {n : ℕ} (d : Fin n → Bool) (p : Fin n)
    (hp : d p = 1) (hprev : ∀ i < p, d i = 0) :
    ∀ j, chooseBit d j = if j = p then 1 else 0 := by
  intro j
  by_cases hj : j = p
  · subst j; simp only [chooseBit, hp, one_mul]
    apply Finset.prod_eq_one
    intro i _; split_ifs with hi
    · rw [hprev i hi]; rfl
    · rfl
  · rw [if_neg hj]
    rcases lt_or_gt_of_ne hj with hjp | hpj
    · simp [chooseBit, hprev j hjp]
    · unfold chooseBit
      have hz : (∏ i : Fin n, if i < j then (1 + d i) else 1) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hpj, hp])
      simp [hz]

private def Valid {n : ℕ} (V : Fin n → Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  (∀ j ∉ S, ∀ i, V j i = 0) ∧ ∀ i ∈ S, ∀ j, V j i = if j = i then 1 else 0

private lemma next_preserves {n : ℕ} (V : Fin n → Fin n → Bool) (a b : Fin n → Bool)
    (h : ∀ j, dot b (V j) = 0) : ∀ j, dot b (nextBasis V a j) = 0 := by
  intro j
  change dot b (V j + fun i => dot a (V j) * (∑ l, chooseBit (fun j => dot a (V j)) l * V l i)) = 0
  rw [dot_add, h j, zero_add, dot_mul]
  have hz : dot b (fun i => ∑ l, chooseBit (fun j => dot a (V j)) l * V l i) = 0 := by
    change (∑ i, b i * (∑ l, chooseBit (fun j => dot a (V j)) l * V l i)) = 0
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hh : ∀ l, (∑ i, b i * (chooseBit (fun j => dot a (V j)) l * V l i)) =
        chooseBit (fun j => dot a (V j)) l * dot b (V l) := by
      intro l; simp only [dot, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    simp_rw [hh, h]; simp
  rw [hz, mul_zero]

private lemma next_valid {n : ℕ} (V : Fin n → Fin n → Bool) (a : Fin n → Bool)
    (S : Finset (Fin n)) (hv : Valid V S) :
    ∃ T : Finset (Fin n), S.card ≤ T.card + 1 ∧ Valid (nextBasis V a) T ∧
      ∀ j, dot a (nextBasis V a j) = 0 := by
  let d := fun j => dot a (V j)
  by_cases hd : ∃ j, d j = 1
  · let U := Finset.univ.filter fun j => d j = 1
    have hu : U.Nonempty := by obtain ⟨j, hj⟩ := hd; exact ⟨j, by simp [U, hj]⟩
    let p := U.min' hu
    have hp : d p = 1 := (Finset.mem_filter.mp (Finset.min'_mem U hu)).2
    have hprev : ∀ i < p, d i = 0 := by
      intro i hi
      cases hdi : d i with
      | false => rfl
      | true =>
        have hiu : i ∈ U := by simp [U, hdi]
        exact False.elim (not_le_of_gt hi (Finset.min'_le U i hiu))
    have hw : (fun i => ∑ j, chooseBit d j * V j i) = V p := by
      funext i; simp [chooseBit_eq d p hp hprev]
    have hnext : nextBasis V a = fun j i => V j i + d j * V p i := by
      unfold nextBasis; change (fun j i => V j i + d j * (∑ l, chooseBit d l * V l i)) = _
      funext j i; rw [congrFun hw i]
    have hps : p ∈ S := by
      by_contra hps
      have hzero : V p = 0 := by funext i; exact hv.1 p hps i
      have : d p = 0 := by simp [d, hzero, dot]
      rw [hp] at this; contradiction
    refine ⟨S.erase p, by rw [Finset.card_erase_of_mem hps]; have := Finset.card_pos.mpr (show S.Nonempty from ⟨p,hps⟩); omega, ?_, ?_⟩
    · constructor
      · intro j hj i
        rw [hnext]
        by_cases hjp : j = p
        · subst j; simp [hp]
        · have hjs : j ∉ S := by simpa [hjp] using hj
          have hjzero : V j = 0 := by funext l; exact hv.1 j hjs l
          simp [hv.1 j hjs i, d, hjzero, dot]
      · intro i hi j
        obtain ⟨hip, his⟩ := Finset.mem_erase.mp hi
        simp only [hnext]
        rw [hv.2 i his j, hv.2 i his p, if_neg (Ne.symm hip), mul_zero, add_zero]
    · intro j
      rw [hnext]
      change dot a (V j + fun i => d j * V p i) = 0
      rw [dot_add, dot_mul]
      change d j + d j * d p = 0
      simp [hp]
  · have hz : ∀ j, d j = 0 := by intro j; cases hj : d j <;> simp_all
    have hn : nextBasis V a = V := by
      funext j i; change V j i + d j * _ = V j i; rw [hz j, zero_mul, add_zero]
    refine ⟨S, by omega, by simpa only [hn] using hv, ?_⟩
    intro j; rw [hn]; exact hz j

private def runBasis {n : ℕ} (rows : List (Fin n → Bool)) : Fin n → Fin n → Bool :=
  rows.foldl nextBasis (fun j i => if j = i then 1 else 0)

private lemma run_valid {n : ℕ} (rows : List (Fin n → Bool)) :
    ∃ S : Finset (Fin n), n ≤ S.card + rows.length ∧ Valid (runBasis rows) S ∧
      ∀ a ∈ rows, ∀ j, dot a (runBasis rows j) = 0 := by
  have aux (V : Fin n → Fin n → Bool) (S : Finset (Fin n)) (hv : Valid V S) :
      ∃ T, S.card ≤ T.card + rows.length ∧ Valid (rows.foldl nextBasis V) T ∧
        (∀ a ∈ rows, ∀ j, dot a (rows.foldl nextBasis V j) = 0) ∧
        (∀ b, (∀ j, dot b (V j) = 0) → ∀ j, dot b (rows.foldl nextBasis V j) = 0) := by
    induction rows generalizing V S with
    | nil => exact ⟨S, by simp, hv, by simp, fun b h => h⟩
    | cons a rows ih =>
      obtain ⟨T, hcard, ht, ha⟩ := next_valid V a S hv
      obtain ⟨U, hcard', hu, hrows, hpres⟩ := ih _ T ht
      refine ⟨U, by simp only [List.length_cons]; omega, hu, ?_, ?_⟩
      · intro b hb; rcases List.mem_cons.mp hb with rfl | hb
        · exact hpres _ ha
        · exact hrows b hb
      · intro b hb; exact hpres b (next_preserves V a b hb)
  obtain ⟨T, ht, hv, hr, _⟩ := aux (fun j i => if j = i then 1 else 0) Finset.univ
    ⟨by simp, by simp⟩
  exact ⟨T, by simpa using ht, hv, hr⟩

private lemma run_nullvector {n : ℕ} (_hn : 0 < n) (rows : List (Fin n → Bool))
    (hm : rows.length < n) :
    let y := fun i => ∑ j, runBasis rows j i
    y ≠ 0 ∧ ∀ a ∈ rows, dot a y = 0 := by
  obtain ⟨S, hc, hv, hr⟩ := run_valid rows
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hs
  constructor
  · intro hz
    have hh := congrFun hz i
    have hall : ∀ j, runBasis rows j i = if j = i then 1 else 0 := hv.2 i hi
    simp [hall] at hh
  · intro a ha
    simp only [dot, Finset.mul_sum]
    rw [Finset.sum_comm]
    change (∑ j, dot a (runBasis rows j)) = 0
    simp [hr a ha]

private lemma hp_next {ι : Type} (i₀ : ι) (n : ℕ) (hn : 0 < n)
    (v : Fin n × Fin n → ι) (a : Fin n → ι) :
    HasProgram (fun x (p : Fin n × Fin n) => nextBasis (fun j i => x (v (j,i))) (x ∘ a) p.1 p.2)
      (29*n^2) := by
  let D := fun (x : ι → Bool) (j : Fin n) => dot (x ∘ a) (fun l => x (v (j,l)))
  have hD : HasProgram D (n*(5*n+3)) := by
    apply hp_all
    intro j
    simpa only [D, dot, Function.comp_apply, Nat.mul_comm] using
      hp_sum i₀ (fun x l => x (a l) * x (v (j,l)))
        (fun l => hp_mul (hp_wire (fun _ : Unit => a l)) (hp_wire (fun _ : Unit => v (j,l))))
  let J := Sum ι (Fin n)
  let P := fun (x : J → Bool) j => chooseBit (fun l => x (.inr l)) j
  have hP : HasProgram P (n*(4*n+4)) := by
    apply hp_all
    intro j
    have hf : ∀ l : Fin n, HasProgram
        (fun (x : J → Bool) (_ : Unit) => if l < j then (1 + x (.inr l)) else 1) 3 := by
      intro l
      by_cases hlj : l < j
      · have hh := hp_mono (hp_neg (hp_wire (fun _ : Unit => (Sum.inr l : J)))) (by decide : 0+1 ≤ 3)
        convert hh using 1
        funext x u; simp only [if_pos hlj, Function.comp_apply]; cases x (.inr l) <;> rfl
      · simpa [hlj] using hp_const (Sum.inl i₀ : J) true
    have hh := hp_mul (hp_wire (fun _ : Unit => (Sum.inr j : J)))
      (hp_prod (Sum.inl i₀ : J) _ hf)
    simpa only [P, chooseBit, Function.comp_apply, Nat.zero_add, Nat.add_assoc, Nat.mul_comm] using hh
  let K := Sum J (Fin n)
  let W := fun (x : K → Bool) (l : Fin n) => ∑ j : Fin n, x (.inr j) * x (.inl (.inl (v (j,l))))
  have hW : HasProgram W (n*(5*n+3)) := by
    apply hp_all
    intro l
    simpa only [W, Function.comp_apply, Nat.mul_comm] using hp_sum (Sum.inl (.inl i₀) : K) _
      (fun j => hp_mul (hp_wire (fun _ : Unit => (Sum.inr j : K)))
        (hp_wire (fun _ : Unit => (Sum.inl (.inl (v (j,l))) : K))))
  let L := Sum K (Fin n)
  let U := fun (x : L → Bool) (p : Fin n × Fin n) =>
    x (.inl (.inl (.inl (v p)))) + x (.inl (.inl (.inr p.1))) * x (.inr p.2)
  have hU : HasProgram U (n^2*5) := by
    convert hp_all_finite U (fun p => hp_add
      (hp_wire (fun _ : Unit => (Sum.inl (.inl (.inl (v p))) : L)))
      (hp_mul (hp_wire (fun _ : Unit => (Sum.inl (.inl (.inr p.1)) : L)))
        (hp_wire (fun _ : Unit => (Sum.inr p.2 : L))))) using 1;
      simp [Fintype.card_prod, pow_two]
  have h := hp_comp (hp_comp (hp_comp (hp_pair (hp_wire id) hD)
      (hp_pair (hp_wire id) hP)) (hp_pair (hp_wire id) hW)) hU
  have hc : n*(5*n+3) + n*(4*n+4) + n*(5*n+3) + n^2*5 ≤ 29*n^2 := by
    have : n ≤ n^2 := by nlinarith
    nlinarith
  convert hp_mono h (by simpa using hc) using 1
  funext x p; rfl

private abbrev State (m n : ℕ) := Sum (Fin m × Fin n) (Fin n × Fin n)

private def startState {m n : ℕ} (x : (Fin m × Fin n) → Bool) : State m n → Bool :=
  Sum.elim x (fun p => if p.1 = p.2 then 1 else 0)

private def stepState {m n : ℕ} (k : Fin m) (x : State m n → Bool) : State m n → Bool :=
  Sum.elim (fun p => x (.inl p))
    (fun p => nextBasis (fun j i => x (.inr (j,i))) (fun i => x (.inl (k,i))) p.1 p.2)

private lemma hp_start {m n : ℕ} (i₀ : Fin m × Fin n) :
    HasProgram (@startState m n) (3*n^2) := by
  change HasProgram (fun x => Sum.elim x (fun p : Fin n × Fin n => if p.1 = p.2 then 1 else 0)) _
  have h := hp_pair (hp_wire id) (hp_all_finite
    (fun (_ : (Fin m × Fin n) → Bool) (p : Fin n × Fin n) => if p.1 = p.2 then (1 : Bool) else 0)
    (fun p => hp_const i₀ (if p.1 = p.2 then true else false)))
  simpa only [startState, Function.comp_def, id_eq, Fintype.card_prod, Fintype.card_fin, Nat.zero_add, pow_two, Nat.mul_comm] using h

private lemma hp_step {m n : ℕ} (hn : 0 < n) (k : Fin m) :
    HasProgram (@stepState m n k) (29*n^2) := by
  change HasProgram (fun x : State m n → Bool => Sum.elim (fun p : Fin m × Fin n => x (.inl p))
    (fun p : Fin n × Fin n => nextBasis (fun j i => x (.inr (j,i))) (fun i => x (.inl (k,i))) p.1 p.2)) _
  have h := hp_pair (hp_wire (fun p : Fin m × Fin n => (Sum.inl p : State m n)))
    (hp_next (Sum.inl (k, ⟨0,hn⟩) : State m n) n hn Sum.inr (fun i => Sum.inl (k,i)))
  simpa only [stepState, Function.comp_def, Nat.zero_add] using h

private def allSteps {m n : ℕ} (ks : List (Fin m)) (x : State m n → Bool) : State m n → Bool :=
  ks.foldl (fun x k => stepState k x) x

private lemma hp_steps {m n : ℕ} (hn : 0 < n) (ks : List (Fin m)) :
    HasProgram (@allSteps m n ks) (ks.length*(29*n^2)) := by
  induction ks with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    change HasProgram (fun x : State m n → Bool => x) 0
    exact hp_wire id
  | cons k ks ih =>
    have h := hp_comp (hp_step hn k) ih
    change HasProgram (fun x => allSteps ks (stepState k x)) ((ks.length+1)*(29*n^2))
    simpa only [Nat.add_mul, one_mul, Nat.add_comm] using h

private lemma allSteps_eq {m n : ℕ} (ks : List (Fin m))
    (x : State m n → Bool) :
    allSteps ks x = Sum.elim (fun p => x (.inl p))
      (fun p => (ks.map (fun k i => x (.inl (k,i)))).foldl nextBasis
        (fun j i => x (.inr (j,i))) p.1 p.2) := by
  induction ks generalizing x with
  | nil => funext p; cases p <;> rfl
  | cons k ks ih =>
    rw [allSteps, List.foldl_cons]
    change allSteps ks (stepState k x) = _
    rw [ih]
    rfl

private def output {m n : ℕ} (x : State m n → Bool) : Fin n → Bool :=
  fun i => ∑ j, x (.inr (j,i))

private lemma hp_output {m n : ℕ} (i₀ : State m n) :
    HasProgram (@output m n) (n*(4*n+3)) := by
  apply hp_all
  intro i
  simpa only [output, Function.comp_apply, Nat.mul_comm] using
    hp_sum i₀ _ (fun j => hp_wire (fun _ : Unit => (Sum.inr (j,i) : State m n)))

private lemma program_circuit {N M s : ℕ} {f : (Fin N → Bool) → Fin M → Bool}
    (hf : HasProgram f s) :
    ∃ G : BoolCircuit N M, G.WellFormed ∧ G.size ≤ s ∧ G.eval = f := by
  obtain ⟨p, hp, hc⟩ := hf
  let z := p.compile N Fin.val
  obtain ⟨hz, hg, ho, hv⟩ := compile_spec p N Fin.val (fun i => i.isLt)
  refine ⟨⟨z.1, z.2⟩, ⟨hg, ho⟩, ?_, ?_⟩
  · change z.1.length ≤ s; exact hz.trans_le hc
  · funext x j
    change (values (List.ofFn x) z.1).getD (z.2 j) false = f x j
    rw [hv _ (by simp)]
    have hx : (fun i : Fin N => (List.ofFn x).getD i.val false) = x := by
      funext i; simp [i.isLt]
    rw [hx, hp]

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ G : BoolCircuit ((n - 1) * n) n,
      G.WellFormed ∧ (G.size : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
      ∀ js : Fin (n - 1) → Qubits n,
        LinearIndependent (ZMod 2) (fun k => simonBitsToZMod2 (js k)) →
        let y := G.eval (fun p => js (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
        y ≠ 0 ∧ ∀ k, dotBits (js k) y = false := by
  refine ⟨64, by norm_num, 2, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  let i₀ : Fin (n-1) × Fin n := (⟨0,by omega⟩, ⟨0,hnpos⟩)
  let ks := List.ofFn (id : Fin (n-1) → Fin (n-1))
  let solve := fun x : (Fin (n-1) × Fin n) → Bool => output (allSteps ks (startState x))
  have hs : HasProgram solve (3*n^2 + (n-1)*(29*n^2) + n*(4*n+3)) := by
    simpa [solve, ks] using hp_comp (hp_comp (hp_start i₀) (hp_steps hnpos ks)) (hp_output (Sum.inl i₀))
  have hs' := hp_comp (hp_wire (fun p : Fin (n-1) × Fin n => finProdFinEquiv p)) hs
  obtain ⟨G, hwf, hsize, heval⟩ := program_circuit hs'
  refine ⟨G, hwf, ?_, ?_⟩
  · have hb : 3*n^2 + (n-1)*(29*n^2) + n*(4*n+3) ≤ 64*n^3 := by
      have hnn : n ≤ n^2 := by nlinarith
      have hnm : n-1 ≤ n := Nat.sub_le _ _
      have hh := Nat.mul_le_mul_right (29*n^2) hnm
      nlinarith
    have h := (hsize.trans (by simpa only [Nat.zero_add] using hb))
    exact_mod_cast h
  · intro js _
    let rows := List.ofFn js
    have hr := run_nullvector hnpos rows (by simp [rows]; omega)
    have hy : G.eval (fun p => js (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) =
        fun i => ∑ j, runBasis rows j i := by
      rw [heval]
      have hx : (fun p : Fin (n-1) × Fin n =>
          js (finProdFinEquiv.symm (finProdFinEquiv p)).1 (finProdFinEquiv.symm (finProdFinEquiv p)).2) =
          fun p => js p.1 p.2 := by funext p; simp
      change solve (fun p : Fin (n-1) × Fin n =>
        js (finProdFinEquiv.symm (finProdFinEquiv p)).1 (finProdFinEquiv.symm (finProdFinEquiv p)).2) = _
      rw [hx]
      unfold solve
      rw [allSteps_eq]
      change (fun i => ∑ j, (ks.map (fun k => js k)).foldl nextBasis
        (fun j i => if j = i then 1 else 0) j i) = _
      have hk : ks.map (fun k => js k) = rows := by simp [ks, rows, List.map_ofFn]
      rw [hk]; rfl
    rw [hy]
    refine ⟨hr.1, ?_⟩
    intro k
    have h := hr.2 (js k) (by simp [rows])
    exact h
