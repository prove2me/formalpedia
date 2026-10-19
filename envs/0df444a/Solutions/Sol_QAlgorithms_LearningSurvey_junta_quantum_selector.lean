-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.junta_quantum_selector
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:52:12.970947+00:00
-- url     : https://prove2.me/submissions/0c04c266-b685-4f4d-8c23-1d3bbf65ce45

import Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model
import Theorems.Thm_QAlgorithms_LearningSurvey_junta_fourier_influence_sampler
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open QAlgorithms QAlgorithms.LearningSurvey Classical
open scoped BigOperators
set_option autoImplicit false

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

private lemma hp_any {ι : Type} (i : ι) {n s : ℕ}
    (f : (ι → Bool) → Fin n → Bool)
    (h : ∀ j, HasProgram (fun x (_ : Unit) => f x j) s) :
    HasProgram (fun x (_ : Unit) => decide (∃ j, f x j = true)) (n*(s+1)+3) := by
  induction n with
  | zero => simpa using hp_const i false
  | succ n ih =>
    have ht := ih (fun x j => f x j.succ) (fun j => h j.succ)
    have hp := hp_scalar_op (h 0) ht .or
    convert hp_mono hp (by nlinarith : s+(n*(s+1)+3)+1 ≤ (n+1)*(s+1)+3) using 1
    funext x u
    simp only [opValue]
    apply Bool.eq_iff_iff.mpr
    simp [Fin.exists_fin_succ]

private def counts {n r : ℕ} (is : List (Fin n)) (x : Qubits n) : Fin r → Bool :=
  fun j => decide (j.val ≤ is.countP (fun i => x i))

private def updateCount {r : ℕ} (x : Sum (Fin r) Unit → Bool) : Fin r → Bool :=
  fun j => if h : j.val = 0 then x (.inl j)
    else x (.inl j) || (x (.inr ()) && x (.inl ⟨j.val-1, by omega⟩))

private lemma hp_update (r : ℕ) : HasProgram (@updateCount r) (r*2) := by
  apply hp_all
  intro j
  by_cases hj : j.val = 0
  · have he : (fun x (_ : Unit) => updateCount x j) =
        (fun x (_ : Unit) => x (Sum.inl j)) := by funext x u; simp [updateCount, hj]
    rw [he]
    exact hp_mono (hp_wire (fun _ : Unit => Sum.inl j)) (by omega)
  · have h := hp_scalar_op
      (hp_wire (fun _ : Unit => Sum.inl j))
      (hp_op .and (Sum.inr ()) (Sum.inl (⟨j.val-1, by omega⟩ : Fin r))) .or
    simpa [updateCount, hj, opValue] using h

private lemma counts_step {n r : ℕ} (i : Fin n) (is : List (Fin n)) (x : Qubits n) :
    counts (r:=r) (i::is) x =
      updateCount (Sum.elim (counts is x) (fun _ : Unit => x i)) := by
  funext j
  by_cases hj : j.val = 0
  · simp [counts, updateCount, hj]
  · simp only [counts, updateCount, hj, ↓reduceDIte, Sum.elim_inl, Sum.elim_inr]
    apply Bool.eq_iff_iff.mpr
    cases hi : x i <;> simp [hi]
    all_goals omega

private lemma hp_counts {n r : ℕ} (i₀ : Fin n) (is : List (Fin n)) :
    HasProgram (@counts n r is) (3*r + is.length*(2*r)) := by
  induction is with
  | nil =>
    change HasProgram (fun _ : Qubits n => fun j : Fin r => decide (j.val ≤ 0)) _
    simpa only [List.length_nil, Nat.zero_mul, Nat.add_zero, Nat.mul_comm] using hp_all (fun _ : Qubits n => fun j : Fin r => decide (j.val ≤ 0))
      (fun j => hp_const i₀ (decide (j.val ≤ 0)))
  | cons i is ih =>
    have h := hp_comp (hp_pair ih (hp_wire (fun _ : Unit => i))) (hp_update r)
    convert h using 1
    · funext x; exact counts_step i is x
    · simp only [List.length_cons]; ring

private lemma count_all {n : ℕ} (x : Qubits n) :
    (List.finRange n).countP (fun i => x i) = hammingWeight x := by
  rw [List.countP_eq_length_filter]
  have h : ((List.finRange n).filter (fun i => x i)).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup h]
  congr 1
  ext i
  simp

private def capped {n : ℕ} (k : ℕ) (x : Qubits n) : Qubits n :=
  if hammingWeight x ≤ k then x else fun _ => false

private lemma hp_cap {n k : ℕ} (i₀ : Fin n) :
    HasProgram (@capped n k) (3*(k+2) + n*(2*(k+2)) + 2*n) := by
  let j : Fin (k+2) := ⟨k+1, by omega⟩
  have hcnt := hp_counts (r:=k+2) i₀ (List.finRange n)
  have ho : HasProgram (fun x : Sum (Fin n) (Fin (k+2)) → Bool =>
      fun i : Fin n => x (.inl i) && !x (.inr j)) (n*2) := by
    apply hp_all
    intro i
    exact hp_mul (hp_wire (fun _ : Unit => Sum.inl i))
      (hp_neg (hp_wire (fun _ : Unit => Sum.inr j)))
  have h := hp_comp (hp_pair (hp_wire id) hcnt) ho
  convert h using 1
  · funext x i
    dsimp [capped, counts, j]
    rw [count_all]
    by_cases hc : hammingWeight x ≤ k
    · simp [hc, show ¬k+1 ≤ hammingWeight x by omega]
    · simp [hc, show k+1 ≤ hammingWeight x by omega]
  · simp; ring

private def rawMask {n T N : ℕ} (z : Qubits N) : Qubits n :=
  fun i => decide (∃ j : Fin T, exInput n z j i = true)

private lemma mask_circuit (n k T : ℕ) (hn : 0 < n) (hT : 0 < T) :
    ∃ G : BoolCircuit (T*(n+1)+0) n,
      G.WellFormed ∧ G.size ≤ n*(T+3) + 3*(k+2) + n*(2*(k+2)) + 2*n ∧
      G.eval = fun z => capped k (rawMask (n:=n) (T:=T) z) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let z₀ : Fin (T*(n+1)+0) := ⟨0, by positivity⟩
  have hr : HasProgram (@rawMask n T (T*(n+1)+0)) (n*(T+3)) := by
    apply hp_all
    intro i
    have hs (j : Fin T) : j.val*(n+1)+i.val < T*(n+1)+0 := by
      have hj : j.val+1 ≤ T := j.isLt
      have hi := i.isLt
      nlinarith
    have h := hp_any z₀ (fun z (j : Fin T) => exInput n z j i)
      (fun j => by
        simpa only [exInput, regBit, dif_pos (hs j), Function.comp_def] using
          hp_wire (fun _ : Unit => (⟨j.val*(n+1)+i.val, hs j⟩ : Fin (T*(n+1)+0))))
    simpa [rawMask] using h
  have h := program_circuit (hp_comp hr (hp_cap (k:=k) i₀))
  simpa only [Nat.add_assoc] using h

private lemma capped_weight {n : ℕ} (k : ℕ) (x : Qubits n) :
    hammingWeight (capped k x) ≤ k := by
  by_cases h : hammingWeight x ≤ k
  · rw [capped, if_pos h]; exact h
  · rw [capped, if_neg h]; simp [hammingWeight]

private lemma capped_eq {n : ℕ} {k : ℕ} {x : Qubits n} (h : hammingWeight x ≤ k) :
    capped k x = x := by simp [capped, h]

private lemma missed_influence (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (T : ℕ) (hT : 0 < T) : a * (1-a/2)^T ≤ 2/(T:ℝ) := by
  have ht : (0:ℝ) < T := by exact_mod_cast hT
  have hq : 0 ≤ 1-a/2 := by linarith
  have hqe : 1-a/2 ≤ Real.exp (-a/2) := by
    have := Real.add_one_le_exp (-a/2)
    linarith
  have hp := pow_le_pow_left₀ hq hqe T
  rw [← Real.exp_nat_mul] at hp
  have hx : (T:ℝ)*a/2 ≤ Real.exp ((T:ℝ)*a/2) := by
    have := Real.add_one_le_exp ((T:ℝ)*a/2)
    linarith
  have hxe := mul_le_mul_of_nonneg_right hx (Real.exp_pos (-((T:ℝ)*a/2))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hxe
  have hm := mul_le_mul_of_nonneg_left hp ha
  have he : (T:ℝ)*(-a/2) = -((T:ℝ)*a/2) := by ring
  rw [he] at hm
  apply (le_div_iff₀ ht).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm ht.le]

private noncomputable def disagreement {n : ℕ} (f : Qubits n → Bool) (V : Qubits n) : ℝ :=
  ((2:ℝ)^n)⁻¹ * ∑ x : Qubits n,
    (((2:ℝ)^n)⁻¹ * ∑ y : Qubits n,
      if (∀ i, V i = true → y i = x i) ∧ f y ≠ f x then (1:ℝ) else 0) *
    (2:ℝ)^hammingWeight V

private lemma expected_missing {n T : ℕ} {Z : Type} [Fintype Z]
    (p : Z → ℝ) (V : Z → Qubits n) (I : Fin n → ℝ)
    (S : Finset (Fin n)) (D : Qubits n → ℝ) (hT : 0 < T)
    (hp : ∀ z, 0 ≤ p z)
    (hI : ∀ i ∈ S, 0 ≤ I i ∧ I i ≤ 1 ∧
      (∑ z, if V z i = false then p z else 0) ≤ (1-I i/2)^T)
    (hD : ∀ W, D W ≤ ∑ i ∈ S, if W i = true then 0 else I i) :
    (∑ z, p z * D (V z)) ≤ (S.card:ℝ) * (2/(T:ℝ)) := by
  calc
    _ ≤ ∑ z, p z * ∑ i ∈ S, if V z i = true then 0 else I i :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hD _) (hp z)
    _ = ∑ i ∈ S, I i * ∑ z, if V z i = false then p z else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro z hz
      cases V z i <;> simp [mul_comm]
    _ ≤ ∑ i ∈ S, I i * (1-I i/2)^T :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hI i hi).2.2 (hI i hi).1
    _ ≤ ∑ _i ∈ S, 2/(T:ℝ) :=
      Finset.sum_le_sum fun i hi => missed_influence _ (hI i hi).1 (hI i hi).2.1 T hT
    _ = _ := by simp

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ L : QAlgorithms.LearningSurvey.JuntaHybridLearner n,
        L.TC = 0 ∧
        (L.TQ : ℝ) ≤ C * ((k : ℝ) * Real.log k / η) ∧
        ((L.circ.size + (L.TQ * (n + 1) + L.anc) + L.post.size : ℕ) : ℝ) ≤
          C * ((n : ℝ) * k * Real.log k / η) ∧
        (∀ z, QAlgorithms.hammingWeight (L.post.eval z) ≤ k) ∧
        ∀ f : QAlgorithms.Qubits n → Bool, QAlgorithms.LearningSurvey.IsJunta f k →
          (∑ z, QAlgorithms.prob
            (QAlgorithms.act L.circ.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n L.TQ L.anc f)) z) = 1 ∧
          (∑ z, QAlgorithms.prob
            (QAlgorithms.act L.circ.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n L.TQ L.anc f)) z *
            (((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
              (((2 : ℝ)^n)⁻¹ * ∑ y : QAlgorithms.Qubits n,
                if (∀ i, L.post.eval z i = true → y i = x i) ∧ f y ≠ f x then (1 : ℝ) else 0) *
              (2 : ℝ)^QAlgorithms.hammingWeight (L.post.eval z))) ≤ η := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨100 / Real.log 2, by positivity, ?_⟩
  intro n k hk hkn η hη hη1
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hn : 0 < n := by omega
  have hlog : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hkR
  let T := Nat.ceil (2*(k:ℝ)/η)
  have hTlo : 2*(k:ℝ)/η ≤ T := Nat.le_ceil _
  have hThi : (T:ℝ) ≤ 2*(k:ℝ)/η+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hTk : (k:ℝ) ≤ T := by
    have hh : (k:ℝ) ≤ 2*(k:ℝ)/η := (le_div_iff₀ hη).mpr (by nlinarith)
    exact hh.trans hTlo
  have hTkN : k ≤ T := by exact_mod_cast hTk
  have hT : 0 < T := by omega
  have ht : (0:ℝ) < T := by exact_mod_cast hT
  have hTscale : (T:ℝ) ≤ 3*((k:ℝ)/η) := by
    have hh : (1:ℝ) ≤ (k:ℝ)/η := (le_div_iff₀ hη).mpr (by linarith)
    have hhT : (T:ℝ) ≤ 2*((k:ℝ)/η)+1 := by simpa only [div_eq_mul_inv, mul_assoc] using hThi
    linarith
  have hTlog : (T:ℝ) ≤ (3/Real.log 2)*((k:ℝ)*Real.log k/η) := by
    calc
      (T:ℝ) ≤ 3*((k:ℝ)/η) := hTscale
      _ = (3*((k:ℝ)/η)*Real.log 2)/Real.log 2 := by field_simp
      _ ≤ (3*((k:ℝ)/η)*Real.log k)/Real.log 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity)) hl2.le
      _ = _ := by ring
  obtain ⟨c, hc, hsample⟩ := junta_fourier_influence_sampler n T hT
  obtain ⟨G, hG, hsize, heval⟩ := mask_circuit n k T hn hT
  let L : JuntaHybridLearner n := ⟨T, 0, c, G, hG, 0⟩
  have hcostN : c.size+(T*(n+1)+0)+G.size ≤ 20*n*T := by
    have hn2 : 2 ≤ n := hk.trans hkn
    have hT2 : 2 ≤ T := hk.trans hTkN
    have hc' : c.size + T*(n+1) ≤ 3*n*T := by nlinarith
    have ha : 3*(k+2) ≤ 3*n*T := by nlinarith
    have hb : n*(2*(k+2)) ≤ 4*n*T := by nlinarith
    have hd : 2*n ≤ n*T := by nlinarith
    have he : n*(T+3) ≤ 3*n*T := by nlinarith
    nlinarith only [hc', ha, hb, hd, he, hsize]
  have hbase : 0 ≤ (k:ℝ)*Real.log k/η := by positivity
  have hqbound : (T:ℝ) ≤ (100/Real.log 2)*((k:ℝ)*Real.log k/η) := by
    apply hTlog.trans
    apply mul_le_mul_of_nonneg_right _ hbase
    exact div_le_div_of_nonneg_right (by norm_num) hl2.le
  have htime : ((c.size+(T*(n+1)+0)+G.size:ℕ):ℝ) ≤
      (100/Real.log 2)*((n:ℝ)*k*Real.log k/η) := by
    have hcostR : ((c.size+(T*(n+1)+0)+G.size:ℕ):ℝ) ≤ 20*(n:ℝ)*T := by exact_mod_cast hcostN
    apply hcostR.trans
    have hmul := mul_le_mul_of_nonneg_left hTlog (show 0 ≤ 20*(n:ℝ) by positivity)
    have hconst : 20*(3/Real.log 2) ≤ 100/Real.log 2 := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by norm_num) hl2.le
    have hmul' := mul_le_mul_of_nonneg_right hconst
      (show 0 ≤ (n:ℝ)*((k:ℝ)*Real.log k/η) by positivity)
    calc
      20*(n:ℝ)*T ≤ 20*(n:ℝ)*((3/Real.log 2)*((k:ℝ)*Real.log k/η)) := hmul
      _ = (20*(3/Real.log 2))*((n:ℝ)*((k:ℝ)*Real.log k/η)) := by ring
      _ ≤ (100/Real.log 2)*((n:ℝ)*((k:ℝ)*Real.log k/η)) := hmul'
      _ = _ := by ring
  refine ⟨L, rfl, hqbound, htime, ?_, ?_⟩
  · intro z
    change hammingWeight (G.eval z) ≤ k
    rw [heval]
    exact capped_weight k _
  · intro f hf
    obtain ⟨S, hSk, hSf⟩ := hf
    obtain ⟨hnorm, hsupp, hI, hD⟩ := hsample f S hSf
    refine ⟨hnorm, ?_⟩
    let p := fun z => prob (act c.unitary (juntaExamplesState n T 0 f)) z
    let I := fun i : Fin n => ((2:ℝ)^n)⁻¹ * ∑ x : Qubits n,
      if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0
    have hraw : (∑ z, p z * disagreement f (rawMask (n:=n) (T:=T) z)) ≤ (S.card:ℝ)*(2/(T:ℝ)) :=
      expected_missing p (@rawMask n T (T*(n+1)+0)) I S (disagreement f) hT
        (fun z => by dsimp [p, prob]; positivity) hI hD
    have hcap (z : Qubits (T*(n+1)+0)) (hz : p z ≠ 0) :
        capped k (rawMask (n:=n) (T:=T) z) = rawMask (n:=n) (T:=T) z := by
      apply capped_eq
      apply le_trans (show hammingWeight (rawMask (n:=n) (T:=T) z) ≤ S.card from ?_) hSk
      apply Finset.card_le_card
      intro i hi
      exact hsupp z hz i (Finset.mem_filter.mp hi).2
    have he : (∑ z, p z * disagreement f (G.eval z)) =
        ∑ z, p z * disagreement f (rawMask (n:=n) (T:=T) z) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hpz : p z = 0
      · simp [hpz]
      · simp only [heval, hcap z hpz]
    change (∑ z, p z * disagreement f (G.eval z)) ≤ η
    rw [he]
    apply hraw.trans
    have hcR : (S.card:ℝ) ≤ k := by exact_mod_cast hSk
    have hcard := mul_le_mul_of_nonneg_right hcR (show 0 ≤ 2/(T:ℝ) by positivity)
    apply hcard.trans
    have hlo := (div_le_iff₀ hη).mp hTlo
    calc
      (k:ℝ)*(2/(T:ℝ)) = (2*(k:ℝ))/(T:ℝ) := by ring
      _ ≤ η := (div_le_iff₀ ht).mpr (by nlinarith only [hlo])

