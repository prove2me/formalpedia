-- Prove2me | solution 1 for QAlgorithms.DeWolf.chp_loop_machine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:44:35.742196+00:00
-- url     : https://prove2.me/submissions/3e38afa1-a5a5-4fbc-869d-014dfd71f550

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer
set_option linter.all false
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OCRS19TM

open Turing

/-- An embedding of a sub-machine `T` into a big TM2 with stacks `K`, alphabets `Γ`,
labels `Λ`, states `σ`. `T`'s halt becomes a jump to `ret`. -/
structure Slot (T : FinTM2) (K : Type) (Γ : K → Type) (Λ σ : Type) where
  kf : T.K → K
  kf_inj : Function.Injective kf
  gin : ∀ k, T.Γ k → Γ (kf k)
  gout : ∀ k, Γ (kf k) → T.Γ k
  gout_gin : ∀ k a, gout k (gin k a) = a
  sget : σ → T.σ
  sset : σ → T.σ → σ
  get_set : ∀ v s, sget (sset v s) = s
  set_set : ∀ v s s', sset (sset v s) s' = sset v s'
  lf : T.Λ → Λ
  ret : Λ

namespace Slot

variable {T : FinTM2} {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (E : Slot T K Γ Λ σ)

/-- translation of a sub-machine statement -/
def tr : TM2.Stmt T.Γ T.Λ T.σ → TM2.Stmt Γ Λ σ
  | TM2.Stmt.push k f q => TM2.Stmt.push (E.kf k) (fun v => E.gin k (f (E.sget v))) (tr q)
  | TM2.Stmt.peek k f q =>
      TM2.Stmt.peek (E.kf k) (fun v o => E.sset v (f (E.sget v) (o.map (E.gout k)))) (tr q)
  | TM2.Stmt.pop k f q =>
      TM2.Stmt.pop (E.kf k) (fun v o => E.sset v (f (E.sget v) (o.map (E.gout k)))) (tr q)
  | TM2.Stmt.load a q => TM2.Stmt.load (fun v => E.sset v (a (E.sget v))) (tr q)
  | TM2.Stmt.branch p q₁ q₂ => TM2.Stmt.branch (fun v => p (E.sget v)) (tr q₁) (tr q₂)
  | TM2.Stmt.goto l => TM2.Stmt.goto (fun v => E.lf (l (E.sget v)))
  | TM2.Stmt.halt => TM2.Stmt.goto (fun _ => E.ret)

/-- big stacks `S` represent sub stacks `ST`, and agree with the frame `S0` elsewhere -/
def Rel (ST : ∀ k, List (T.Γ k)) (S S0 : ∀ k, List (Γ k)) : Prop :=
  (∀ k, S (E.kf k) = (ST k).map (E.gin k)) ∧ (∀ k', (∀ k, E.kf k ≠ k') → S k' = S0 k')

/-- label translation -/
def lab (l : Option T.Λ) : Λ := l.elim E.ret E.lf

lemma rel_update (ST : ∀ k, List (T.Γ k)) (S S0 : ∀ k, List (Γ k)) (h : E.Rel ST S S0)
    (k : T.K) (L : List (T.Γ k)) :
    E.Rel (Function.update ST k L) (Function.update S (E.kf k) (L.map (E.gin k))) S0 := by
  constructor
  · intro k''
    by_cases hk : k'' = k
    · subst hk; simp
    · rw [Function.update_of_ne (fun h' => hk (E.kf_inj h')), Function.update_of_ne hk, h.1]
  · intro k' hk'
    rw [Function.update_of_ne (Ne.symm (hk' k)), h.2 k' hk']

lemma head_map_gout (ST : ∀ k, List (T.Γ k)) (S S0 : ∀ k, List (Γ k)) (h : E.Rel ST S S0)
    (k : T.K) : (S (E.kf k)).head?.map (E.gout k) = (ST k).head? := by
  rw [h.1 k]
  cases ST k <;> simp [E.gout_gin]

lemma stepAux_sim (q : TM2.Stmt T.Γ T.Λ T.σ) (v0 : σ) (S0 : ∀ k, List (Γ k)) :
    ∀ (vT : T.σ) (ST : ∀ k, List (T.Γ k)) (S : ∀ k, List (Γ k)), E.Rel ST S S0 →
      ∃ S', E.Rel (TM2.stepAux q vT ST).stk S' S0 ∧
        TM2.stepAux (E.tr q) (E.sset v0 vT) S =
          ⟨some (E.lab (TM2.stepAux q vT ST).l), E.sset v0 (TM2.stepAux q vT ST).var, S'⟩ := by
  induction q with
  | push k f q ih =>
    intro vT ST S h
    simp only [tr, TM2.stepAux, E.get_set]
    have h' := E.rel_update ST S S0 h k (f vT :: ST k)
    rw [List.map_cons, ← h.1 k] at h'
    exact ih vT _ _ h'
  | peek k f q ih =>
    intro vT ST S h
    simp only [tr, TM2.stepAux, E.get_set, E.set_set]
    rw [E.head_map_gout ST S S0 h k]
    exact ih _ ST S h
  | pop k f q ih =>
    intro vT ST S h
    simp only [tr, TM2.stepAux, E.get_set, E.set_set]
    rw [E.head_map_gout ST S S0 h k]
    have h' := E.rel_update ST S S0 h k (ST k).tail
    rw [List.map_tail, ← h.1 k] at h'
    exact ih _ _ _ h'
  | load a q ih =>
    intro vT ST S h
    simp only [tr, TM2.stepAux, E.get_set, E.set_set]
    exact ih _ ST S h
  | branch p q₁ q₂ ih₁ ih₂ =>
    intro vT ST S h
    simp only [tr, TM2.stepAux, E.get_set]
    cases p vT
    · exact ih₂ vT ST S h
    · exact ih₁ vT ST S h
  | goto l =>
    intro vT ST S h
    exact ⟨S, h, by simp [tr, TM2.stepAux, lab, E.get_set]⟩
  | halt =>
    intro vT ST S h
    exact ⟨S, h, by simp [tr, TM2.stepAux, lab]⟩

/-- the big program runs the translated sub-program at the slot labels -/
def Hosts (M : Λ → TM2.Stmt Γ Λ σ) : Prop := ∀ l, M (E.lf l) = E.tr (T.m l)

lemma run_sim (M : Λ → TM2.Stmt Γ Λ σ) (hM : E.Hosts M) (v0 : σ) (S0 : ∀ k, List (Γ k)) :
    ∀ (n : ℕ) (c c' : T.Cfg), (flip bind T.step)^[n] (some c) = some c' →
      ∀ S, E.Rel c.stk S S0 →
      ∃ S', E.Rel c'.stk S' S0 ∧
        (flip bind (TM2.step M))^[n] (some ⟨some (E.lab c.l), E.sset v0 c.var, S⟩) =
          some ⟨some (E.lab c'.l), E.sset v0 c'.var, S'⟩ := by
  intro n
  induction n with
  | zero =>
    intro c c' hc S h
    simp only [Function.iterate_zero, id, Option.some.injEq] at hc
    subst hc
    exact ⟨S, h, rfl⟩
  | succ n ih =>
    intro c c' hc S h
    rw [Function.iterate_succ_apply] at hc ⊢
    obtain ⟨l, vT, ST⟩ := c
    cases l with
    | none =>
      exfalso
      have : (flip bind T.step) (some (⟨none, vT, ST⟩ : T.Cfg)) = none := rfl
      rw [this] at hc
      have hn : ∀ m, (flip bind T.step)^[m] (none : Option T.Cfg) = none := by
        intro m
        induction m with
        | zero => rfl
        | succ m ihm => rw [Function.iterate_succ_apply]; exact ihm
      rw [hn] at hc
      cases hc
    | some l =>
      obtain ⟨S', hS', heq⟩ := E.stepAux_sim (T.m l) v0 S0 vT ST S h
      have h1 : (flip bind T.step) (some (⟨some l, vT, ST⟩ : T.Cfg)) =
          some (TM2.stepAux (T.m l) vT ST) := rfl
      rw [h1] at hc
      obtain ⟨S'', hS'', heq'⟩ := ih _ c' hc S' hS'
      refine ⟨S'', hS'', ?_⟩
      have h2 : (flip bind (TM2.step M))
          (some ⟨some (E.lab (some l)), E.sset v0 vT, S⟩) =
          some ⟨some (E.lab (TM2.stepAux (T.m l) vT ST).l),
            E.sset v0 (TM2.stepAux (T.m l) vT ST).var, S'⟩ := by
        show some (TM2.stepAux (M (E.lf l)) (E.sset v0 vT) S) = _
        rw [hM l, heq]
      rw [h2]
      exact heq'

end Slot

/-- `M` goes from `c` to `c'` in at most `t` steps -/
def Reach {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)
    (c c' : TM2.Cfg Γ Λ σ) (t : ℕ) : Prop :=
  ∃ n ≤ t, (flip bind (TM2.step M))^[n] (some c) = some c'

namespace Reach

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} {M : Λ → TM2.Stmt Γ Λ σ}

lemma refl (c : TM2.Cfg Γ Λ σ) : Reach M c c 0 := ⟨0, le_rfl, rfl⟩

lemma mono {c c' : TM2.Cfg Γ Λ σ} {t t' : ℕ} (h : Reach M c c' t) (ht : t ≤ t') :
    Reach M c c' t' := by
  obtain ⟨n, hn, e⟩ := h; exact ⟨n, hn.trans ht, e⟩

lemma trans {c c' c'' : TM2.Cfg Γ Λ σ} {t t' : ℕ} (h : Reach M c c' t) (h' : Reach M c' c'' t') :
    Reach M c c'' (t + t') := by
  obtain ⟨n, hn, e⟩ := h
  obtain ⟨n', hn', e'⟩ := h'
  refine ⟨n' + n, by omega, ?_⟩
  rw [Function.iterate_add_apply, e, e']

lemma single {c c' : TM2.Cfg Γ Λ σ} (h : TM2.step M c = some c') : Reach M c c' 1 :=
  ⟨1, le_rfl, by simpa [flip] using h⟩

end Reach

lemma initList_stk_k0 (T : FinTM2) (inp : List (T.Γ T.k₀)) :
    (initList T inp).stk T.k₀ = inp := by
  simp [initList]

lemma initList_stk_ne (T : FinTM2) (inp : List (T.Γ T.k₀)) (k : T.K) (hk : k ≠ T.k₀) :
    (initList T inp).stk k = [] := by
  simp [initList, hk]

lemma haltList_stk_k1 (T : FinTM2) (out : List (T.Γ T.k₁)) :
    (haltList T out).stk T.k₁ = out := by
  simp [haltList]

lemma haltList_stk_ne (T : FinTM2) (out : List (T.Γ T.k₁)) (k : T.K) (hk : k ≠ T.k₁) :
    (haltList T out).stk k = [] := by
  simp [haltList, hk]

namespace Slot

variable {T : FinTM2} {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (E : Slot T K Γ Λ σ)

/-- a complete run of the sub-machine inside the big one -/
lemma sub_run (M : Λ → TM2.Stmt Γ Λ σ) (hM : E.Hosts M) (v0 : σ) (S0 S : ∀ k, List (Γ k))
    {inp : List (T.Γ T.k₀)} {out : List (T.Γ T.k₁)} {t : ℕ}
    (hrun : TM2OutputsInTime T inp (some out) t) (h : E.Rel (initList T inp).stk S S0) :
    ∃ S', E.Rel (haltList T out).stk S' S0 ∧
      Reach M ⟨some (E.lf T.main), E.sset v0 T.initialState, S⟩
        ⟨some E.ret, E.sset v0 T.initialState, S'⟩ t := by
  obtain ⟨⟨n, hn⟩, hle⟩ := hrun
  obtain ⟨S', hS', e⟩ := E.run_sim M hM v0 S0 n _ _ hn S h
  exact ⟨S', hS', n, hle, e⟩

end Slot

end OCRS19TM


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OCRS19TM

open Turing

section
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- maximal number of pushes along one execution of a statement -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | TM2.Stmt.push _ _ q => pushes q + 1
  | TM2.Stmt.peek _ _ q => pushes q
  | TM2.Stmt.pop _ _ q => pushes q
  | TM2.Stmt.load _ q => pushes q
  | TM2.Stmt.branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | TM2.Stmt.goto _ => 0
  | TM2.Stmt.halt => 0

lemma stepAux_len (q : TM2.Stmt Γ Λ σ) (k : K) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)),
      ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q with
  | push k' f q ih =>
    intro v S
    refine (ih _ _).trans ?_
    simp only [pushes]
    by_cases hk : k = k'
    · subst hk; simp; omega
    · rw [Function.update_of_ne hk]; omega
  | peek k' f q ih => intro v S; exact ih _ _
  | pop k' f q ih =>
    intro v S
    refine (ih _ _).trans ?_
    simp only [pushes]
    by_cases hk : k = k'
    · subst hk; simp
    · rw [Function.update_of_ne hk]
  | load a q ih => intro v S; exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [TM2.stepAux, pushes]
    cases p v
    · exact (ih₂ v S).trans (by simp)
    · exact (ih₁ v S).trans (by simp)
  | goto l => intro v S; simp [TM2.stepAux]
  | halt => intro v S; simp [TM2.stepAux]

end

/-- push constant of a machine -/
def pushC (T : FinTM2) : ℕ :=
  @Finset.sup _ _ _ _ (@Finset.univ T.Λ T.ΛFin) (fun l => pushes (T.m l))

lemma pushes_le (T : FinTM2) (l : T.Λ) : pushes (T.m l) ≤ pushC T :=
  @Finset.le_sup _ _ _ _ (@Finset.univ T.Λ T.ΛFin) (fun l => pushes (T.m l)) l
    (@Finset.mem_univ _ T.ΛFin l)

lemma iter_len (T : FinTM2) (k : T.K) :
    ∀ (n : ℕ) (c c' : T.Cfg), (flip bind T.step)^[n] (some c) = some c' →
      (c'.stk k).length ≤ (c.stk k).length + pushC T * n := by
  intro n
  induction n with
  | zero =>
    intro c c' h
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h; simp
  | succ n ih =>
    intro c c' h
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none =>
      exfalso
      have : (flip bind T.step) (some (⟨none, v, S⟩ : T.Cfg)) = none := rfl
      rw [this] at h
      have hn : ∀ m, (flip bind T.step)^[m] (none : Option T.Cfg) = none := by
        intro m
        induction m with
        | zero => rfl
        | succ m ihm => rw [Function.iterate_succ_apply]; exact ihm
      rw [hn] at h
      cases h
    | some l =>
      have h1 : (flip bind T.step) (some (⟨some l, v, S⟩ : T.Cfg)) =
          some (TM2.stepAux (T.m l) v S) := rfl
      rw [h1] at h
      have a := ih _ _ h
      have b := stepAux_len (T.m l) k v S
      have c := pushes_le T l
      simp only at a b ⊢
      rw [Nat.mul_succ]
      calc (c'.stk k).length ≤ ((TM2.stepAux (T.m l) v S).stk k).length + pushC T * n := a
        _ ≤ (S k).length + pushes (T.m l) + pushC T * n := by omega
        _ ≤ (S k).length + (pushC T * n + pushC T) := by omega

lemma out_len (T : FinTM2) {inp : List (T.Γ T.k₀)} {out : List (T.Γ T.k₁)} {t : ℕ}
    (h : TM2OutputsInTime T inp (some out) t) : out.length ≤ inp.length + pushC T * t := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  have a := iter_len T T.k₁ n _ _ hn
  have e1 : (haltList T out).stk T.k₁ = out := by simp [haltList]
  rw [e1] at a
  have e2 : ((initList T inp).stk T.k₁).length ≤ inp.length := by
    by_cases hk : T.k₁ = T.k₀
    · have e3 : ∀ k, k = T.k₀ → ((initList T inp).stk k).length = inp.length := by
        intro k hk'; subst hk'; simp [initList]
      exact (e3 _ hk).le
    · simp [initList, hk]
  have := Nat.mul_le_mul_left (pushC T) (show n ≤ t from hle)
  omega

end OCRS19TM


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OCRS19TM

open Turing

section Transfer

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)

/-- Transfer loop: pop from `a`, stop when `done`, else push `f x` onto `b` and repeat.
One step per symbol (plus one for the stop symbol / empty stack). -/
lemma transfer (L : Λ) (a b : K) (hab : a ≠ b) (upd : σ → Option (Γ a) → σ) (done : σ → Bool)
    (exitL : σ → Λ) (out : σ → Γ b) (f : Γ a → Γ b) (cont : Γ a → Prop)
    (hM : M L = TM2.Stmt.pop a upd
      (TM2.Stmt.branch done (TM2.Stmt.goto exitL) (TM2.Stmt.push b out (TM2.Stmt.goto fun _ => L))))
    (hupd : ∀ v o o', upd (upd v o) o' = upd v o')
    (hcont : ∀ v x, cont x → done (upd v (some x)) = false ∧ out (upd v (some x)) = f x)
    (rest : List (Γ a)) :
    ∀ (xs : List (Γ a)) (S : ∀ k, List (Γ k)) (v : σ), (∀ x ∈ xs, cont x) → S a = xs ++ rest →
      done (upd v rest.head?) = true →
      Reach M ⟨some L, v, S⟩
        ⟨some (exitL (upd v rest.head?)), upd v rest.head?,
          Function.update (Function.update S a rest.tail) b ((xs.map f).reverse ++ S b)⟩
        (xs.length + 1) := by
  intro xs
  induction xs with
  | nil =>
    intro S v _ hS hd
    refine ⟨1, le_rfl, ?_⟩
    show TM2.step M ⟨some L, v, S⟩ = _
    simp only [TM2.step, hM, TM2.stepAux, hS,
      List.nil_append, hd, cond_true, List.map_nil, List.reverse_nil]
    congr 2
    exact (Function.update_eq_self_iff.mpr (Function.update_of_ne (Ne.symm hab) _ _).symm).symm
  | cons x xs ih =>
    intro S v hc hS hd
    have hx := hcont v x (hc x (by simp))
    set S2 := Function.update (Function.update S a (xs ++ rest)) b (f x :: S b) with hS2
    have h2a : S2 a = xs ++ rest := by
      rw [hS2, Function.update_of_ne hab, Function.update_self]
    have h2b : S2 b = f x :: S b := by rw [hS2, Function.update_self]
    have hd' : done (upd (upd v (some x)) rest.head?) = true := by rw [hupd]; exact hd
    obtain ⟨n, hn, e⟩ := ih S2 (upd v (some x)) (fun y hy => hc y (by simp [hy])) h2a hd'
    refine ⟨n + 1, by simp; omega, ?_⟩
    rw [Function.iterate_succ_apply]
    have step1 : (flip bind (TM2.step M)) (some ⟨some L, v, S⟩) =
        some ⟨some L, upd v (some x), S2⟩ := by
      show TM2.step M ⟨some L, v, S⟩ = _
      simp only [TM2.step, hM, TM2.stepAux, hS, List.cons_append,
        List.head?_cons, List.tail_cons, hx.1, hx.2, cond_false]
      congr 2
      rw [hS2, Function.update_of_ne (Ne.symm hab)]
    rw [step1, e, hupd, h2b]
    congr 2
    rw [hS2, Function.update_comm hab, Function.update_idem, Function.update_comm (Ne.symm hab),
      Function.update_idem]
    simp

end Transfer

end OCRS19TM


set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace OCRS19TM

/-! Pure LSB-first binary arithmetic mirroring the machine routines. -/

/-- LSB-first value of a bit list (non-canonical lists allowed). -/
def val : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * val l

@[simp] lemma val_nil : val [] = 0 := rfl
@[simp] lemma val_cons (b : Bool) (l : List Bool) : val (b :: l) = b.toNat + 2 * val l := rfl

lemma val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [pow_succ] <;> omega

/-- strip high zeros: the LSB-first list read MSB-first, leading `false`s dropped. -/
def strip (l : List Bool) : List Bool := (l.reverse.dropWhile (fun b => !b)).reverse

lemma strip_nil : strip [] = [] := rfl

lemma strip_cons (b : Bool) (l : List Bool) :
    strip (b :: l) = if strip l = [] then (if b then [true] else []) else b :: strip l := by
  unfold strip
  rw [List.reverse_cons, List.dropWhile_append]
  by_cases h : (l.reverse.dropWhile (fun b => !b)) = []
  · simp only [h, List.isEmpty_nil, if_true, List.reverse_nil]
    cases b <;> simp
  · have h' : (l.reverse.dropWhile (fun b => !b)).isEmpty = false := by
      cases hh : l.reverse.dropWhile (fun b => !b) with
      | nil => exact absurd hh h
      | cons _ _ => rfl
    rw [h', if_neg (by simp)]
    rw [if_neg (by simpa using h)]
    simp

lemma val_strip (l : List Bool) : val (strip l) = val l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [strip_cons]
    split_ifs with h hb
    · rw [h] at ih; simp [hb, ← ih]
    · rw [h] at ih; simp at hb; simp [hb, ← ih]
    · simp [ih]

lemma encodeNat_bit (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    Computability.encodeNat (b.toNat + 2 * n) = b :: Computability.encodeNat n := by
  obtain ⟨p, hp⟩ : ∃ p : PosNum, (n : Num) = Num.pos p := by
    cases h : (n : Num) with
    | zero => exfalso; apply hn; have := congrArg (fun m : Num => (m : ℕ)) h; simpa using this
    | pos p => exact ⟨p, rfl⟩
  have hb : ((b.toNat + 2 * n : ℕ) : Num) = Num.pos (cond b (PosNum.bit1 p) (PosNum.bit0 p)) := by
    apply Num.to_nat_inj.mp
    have hn' : ((Num.pos p : Num) : ℕ) = n := by rw [← hp]; simp
    cases b
    · simp only [cond_false]
      rw [Num.cast_pos, PosNum.cast_bit0, ← Num.cast_pos, hn', Num.to_of_nat]
      simp; ring
    · simp only [cond_true]
      rw [Num.cast_pos, PosNum.cast_bit1, ← Num.cast_pos, hn', Num.to_of_nat]
      simp; ring
  unfold Computability.encodeNat
  rw [hb, hp]
  cases b <;> rfl

lemma encodeNat_val (l : List Bool) : Computability.encodeNat (val l) = strip l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [strip_cons, val_cons]
    split_ifs with h hb
    · have h0 : val l = 0 := by rw [← val_strip, h]; rfl
      rw [h0, hb]; rfl
    · have h0 : val l = 0 := by rw [← val_strip, h]; rfl
      simp at hb; rw [h0, hb]; rfl
    · have h0 : val l ≠ 0 := by
        intro h0
        rw [h0] at ih
        exact h ih.symm
      rw [encodeNat_bit b _ h0, ih]

lemma val_encodeNat (n : ℕ) : val (Computability.encodeNat n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · obtain ⟨b, m, rfl⟩ : ∃ b : Bool, ∃ m, n = b.toNat + 2 * m :=
        ⟨n % 2 == 1, n / 2, by
          rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2] <;> omega⟩
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; cases b
        · simp at h
        · rfl
      · rw [encodeNat_bit b m hm.ne', val_cons, ih m (by cases b <;> simp <;> omega)]

/-- binary addition with carry, LSB first; the final carry is always emitted. -/
def addL : Bool → List Bool → List Bool → List Bool
  | c, [], [] => [c]
  | c, x :: a, [] => (xor x c) :: addL (x && c) a []
  | c, [], y :: b => (xor y c) :: addL (y && c) [] b
  | c, x :: a, y :: b => (xor (xor x y) c) :: addL ((x && y) || (c && xor x y)) a b

lemma val_addL (c : Bool) (a b : List Bool) : val (addL c a b) = c.toNat + val a + val b := by
  induction c, a, b using addL.induct with
  | case1 c => simp [addL]
  | case2 c x a ih => rw [addL, val_cons, ih]; cases x <;> cases c <;> simp <;> omega
  | case3 c y b ih => rw [addL, val_cons, ih]; cases y <;> cases c <;> simp <;> omega
  | case4 c x a y b ih =>
    rw [addL, val_cons, ih]; cases x <;> cases y <;> cases c <;> simp <;> omega

lemma length_addL (c : Bool) (a b : List Bool) :
    (addL c a b).length = max a.length b.length + 1 := by
  induction c, a, b using addL.induct with
  | case1 c => simp [addL]
  | case2 c x a ih => simp [addL, ih]
  | case3 c y b ih => simp [addL, ih]
  | case4 c x a y b ih => simp [addL, ih]

/-- binary subtraction `a - b - c` with borrow, LSB first; digits only. -/
def subL : Bool → List Bool → List Bool → List Bool
  | _, [], [] => []
  | c, x :: a, [] => (xor x c) :: subL (!x && c) a []
  | c, [], y :: b => (xor y c) :: subL (y || c) [] b
  | c, x :: a, y :: b => (xor (xor x y) c) :: subL ((!x && y) || (c && !(xor x y))) a b

/-- final borrow of `subL` -/
def subB : Bool → List Bool → List Bool → Bool
  | c, [], [] => c
  | c, x :: a, [] => subB (!x && c) a []
  | c, [], y :: b => subB (y || c) [] b
  | c, x :: a, y :: b => subB ((!x && y) || (c && !(xor x y))) a b

lemma subL_spec (c : Bool) (a b : List Bool) :
    val a + 2 ^ (subL c a b).length * (subB c a b).toNat = val (subL c a b) + val b + c.toNat := by
  induction c, a, b using subL.induct with
  | case1 c => simp [subL, subB]
  | case2 c x a ih =>
    simp only [subL, subB, val_cons, List.length_cons, pow_succ] at ih ⊢
    cases x <;> cases c <;> simp at ih ⊢ <;> linarith
  | case3 c y b ih =>
    simp only [subL, subB, val_cons, List.length_cons, pow_succ] at ih ⊢
    cases y <;> cases c <;> simp at ih ⊢ <;> linarith
  | case4 c x a y b ih =>
    simp only [subL, subB, val_cons, List.length_cons, pow_succ] at ih ⊢
    cases x <;> cases y <;> cases c <;> simp at ih ⊢ <;> linarith

lemma length_subL (c : Bool) (a b : List Bool) :
    (subL c a b).length = max a.length b.length := by
  induction c, a, b using subL.induct with
  | case1 c => simp [subL]
  | case2 c x a ih => simp [subL, ih]
  | case3 c y b ih => simp [subL, ih]
  | case4 c x a y b ih => simp [subL, ih]

/-- no final borrow iff `b ≤ a`; then the digits are `a - b`. -/
lemma subB_false_iff (a b : List Bool) : subB false a b = false ↔ val b ≤ val a := by
  have h := subL_spec false a b
  have hl := val_lt (subL false a b)
  cases hB : subB false a b <;> simp [hB] at h ⊢ <;> omega

lemma val_subL (a b : List Bool) (h : val b ≤ val a) : val (subL false a b) = val a - val b := by
  have hs := subL_spec false a b
  rw [(subB_false_iff a b).mpr h] at hs
  simp at hs
  omega

end OCRS19TM


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace OCRS19TM

open Turing

namespace Reach
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} {M : Λ → TM2.Stmt Γ Λ σ}

lemma of_eq {c c₁ c₂ : TM2.Cfg Γ Λ σ} {t : ℕ} (h : Reach M c c₁ t) (e : c₁ = c₂) :
    Reach M c c₂ t := e ▸ h

lemma step_trans {c c' c'' : TM2.Cfg Γ Λ σ} {t : ℕ} (h : TM2.step M c = some c')
    (h' : Reach M c' c'' t) : Reach M c c'' (t + 1) := by
  have := (single h).trans h'
  rwa [Nat.add_comm] at this

end Reach

/-! Bool work stacks `Sum.inl k`, other stacks `Sum.inr r`; registers `(x, y, c)`. -/

/-- stack alphabets: Bool on the work stacks -/
abbrev BΓ (Kb : Type) {R : Type} (G : R → Type) (k : Kb ⊕ R) : Type :=
  Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) G

example {Kb R : Type} (G : R → Type) (a : Kb) : BΓ Kb G (Sum.inl a) = Bool := by with_reducible rfl

/-- registers: two popped bits and a carry/flag -/
abbrev Reg : Type := Option Bool × Option Bool × Bool

/-- read a Bool work stack -/
def bs {Kb R : Type} {G : R → Type} (S : ∀ k : Kb ⊕ R, List (BΓ Kb G k)) (k : Kb) : List Bool :=
  S (Sum.inl k)

section Bool

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- one step of binary addition: pop `a`, `b`, push the sum bit on `o`. -/
def addStmt (a b o : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.pop (Sum.inl b) (fun v y => ((v.1.1, y, v.1.2.2), v.2))
      (TM2.Stmt.branch (fun v => v.1.1.isNone && v.1.2.1.isNone)
        (TM2.Stmt.push (Sum.inl o) (fun v => v.1.2.2)
          (TM2.Stmt.load (fun v => ((none, none, false), v.2)) (TM2.Stmt.goto fun _ => E)))
        (TM2.Stmt.push (Sum.inl o)
          (fun v => xor (xor (v.1.1.getD false) (v.1.2.1.getD false)) v.1.2.2)
          (TM2.Stmt.load (fun v => ((none, none,
              ((v.1.1.getD false) && (v.1.2.1.getD false)) ||
                (v.1.2.2 && xor (v.1.1.getD false) (v.1.2.1.getD false))), v.2))
            (TM2.Stmt.goto fun _ => L)))))

lemma add_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b o : Kb) (hab : a ≠ b) (hao : a ≠ o)
    (hbo : b ≠ o) (L E : Λ) (hM : M L = addStmt a b o L E) (r : ρ) :
    ∀ (c : Bool) (A B : List Bool) (S : ∀ k, List (BΓ Kb G k)),
      S (Sum.inl a) = A → S (Sum.inl b) = B →
      ∃ S', Reach M ⟨some L, ((none, none, c), r), S⟩ ⟨some E, ((none, none, false), r), S'⟩
          (max A.length B.length + 1) ∧
        S' (Sum.inl a) = [] ∧ S' (Sum.inl b) = [] ∧
        bs S' o = (addL c A B).reverse ++ bs S o ∧
        ∀ k, k ≠ Sum.inl a → k ≠ Sum.inl b → k ≠ Sum.inl o → S' k = S k := by
  have hab' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl b := fun h => hab (Sum.inl_injective h)
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  have hbo' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl o := fun h => hbo (Sum.inl_injective h)
  intro c A B
  induction c, A, B using addL.induct with
  | case1 c =>
    intro S hA hB
    refine ⟨Function.update (Function.update (Function.update S (Sum.inl a) [])
      (Sum.inl b) []) (Sum.inl o) (c :: S (Sum.inl o)), ?_, ?_, ?_, ?_, ?_⟩
    · apply (Reach.single _).mono (by simp)
      simp only [TM2.step, hM, addStmt, TM2.stepAux, hA, hB, List.head?_nil, List.tail_nil,
        Function.update_of_ne hab'.symm, Option.isNone_none, Bool.and_self, cond_true,
        Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm]
      all_goals try rfl
    · rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self]
    · rw [Function.update_of_ne hbo', Function.update_self]
    · simp [addL, bs]
    · intro k h1 h2 h3
      rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  | case2 c x A ih =>
    intro S hA hB
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
      (Sum.inl a) A) (Sum.inl b) []) (Sum.inl o) (xor x c :: S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ?_, h1, h2, ?_, ?_⟩
    · refine (Reach.step_trans ?_ hR).mono (by simp)
      simp only [TM2.step, hM, addStmt, TM2.stepAux, hA, hB, List.head?_nil, List.tail_nil,
        List.head?_cons, List.tail_cons, Function.update_of_ne hab'.symm,
        Option.isNone_none, Option.isNone_some, Bool.false_and, cond_false,
        Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm,
        Option.getD_some, Option.getD_none, Bool.xor_false, Bool.and_false, Bool.or_false]
      all_goals (cases x <;> cases c <;> rfl)
    · unfold bs at h3 ⊢; rw [h3, Function.update_self]; simp [addL]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2,
        Function.update_of_ne k1]
  | case3 c y B ih =>
    intro S hA hB
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
      (Sum.inl a) []) (Sum.inl b) B) (Sum.inl o) (xor y c :: S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ?_, h1, h2, ?_, ?_⟩
    · refine (Reach.step_trans ?_ hR).mono (by simp)
      simp only [TM2.step, hM, addStmt, TM2.stepAux, hA, hB, List.head?_nil, List.tail_nil,
        List.head?_cons, List.tail_cons, Function.update_of_ne hab'.symm,
        Option.isNone_none, Option.isNone_some, Bool.and_false, cond_false,
        Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm,
        Option.getD_some, Option.getD_none, Bool.false_xor, Bool.false_and, Bool.or_false]
      all_goals (cases y <;> cases c <;> rfl)
    · unfold bs at h3 ⊢; rw [h3, Function.update_self]; simp [addL]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2,
        Function.update_of_ne k1]
  | case4 c x A y B ih =>
    intro S hA hB
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
      (Sum.inl a) A) (Sum.inl b) B) (Sum.inl o) (xor (xor x y) c :: S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ?_, h1, h2, ?_, ?_⟩
    · refine (Reach.step_trans ?_ hR).mono (by simp)
      simp only [TM2.step, hM, addStmt, TM2.stepAux, hA, hB,
        List.head?_cons, List.tail_cons, Function.update_of_ne hab'.symm,
        Option.isNone_some, Bool.false_and, cond_false,
        Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm,
        Option.getD_some]
      all_goals try rfl
    · unfold bs at h3 ⊢; rw [h3, Function.update_self]; simp [addL]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2,
        Function.update_of_ne k1]

/-- one step of binary subtraction `a - b`: pop `a`, `b`, push the difference bit on `o`;
the final borrow stays in the flag register. -/
def subStmt (a b o : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.pop (Sum.inl b) (fun v y => ((v.1.1, y, v.1.2.2), v.2))
      (TM2.Stmt.branch (fun v => v.1.1.isNone && v.1.2.1.isNone)
        (TM2.Stmt.goto fun _ => E)
        (TM2.Stmt.push (Sum.inl o)
          (fun v => xor (xor (v.1.1.getD false) (v.1.2.1.getD false)) v.1.2.2)
          (TM2.Stmt.load (fun v => ((none, none,
              (!(v.1.1.getD false) && (v.1.2.1.getD false)) ||
                (v.1.2.2 && !(xor (v.1.1.getD false) (v.1.2.1.getD false)))), v.2))
            (TM2.Stmt.goto fun _ => L)))))

lemma sub_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b o : Kb) (hab : a ≠ b) (hao : a ≠ o)
    (hbo : b ≠ o) (L E : Λ) (hM : M L = subStmt a b o L E) (r : ρ) :
    ∀ (c : Bool) (A B : List Bool) (S : ∀ k, List (BΓ Kb G k)),
      S (Sum.inl a) = A → S (Sum.inl b) = B →
      ∃ S', Reach M ⟨some L, ((none, none, c), r), S⟩
          ⟨some E, ((none, none, subB c A B), r), S'⟩ (max A.length B.length + 1) ∧
        S' (Sum.inl a) = [] ∧ S' (Sum.inl b) = [] ∧
        bs S' o = (subL c A B).reverse ++ bs S o ∧
        ∀ k, k ≠ Sum.inl a → k ≠ Sum.inl b → k ≠ Sum.inl o → S' k = S k := by
  have hab' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl b := fun h => hab (Sum.inl_injective h)
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  have hbo' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl o := fun h => hbo (Sum.inl_injective h)
  intro c A B
  induction c, A, B using subL.induct with
  | case1 c =>
    intro S hA hB
    refine ⟨S, ?_, hA, hB, by simp [subL, bs], fun k _ _ _ => rfl⟩
    apply (Reach.single _).mono (by simp)
    have e1 : Function.update S (Sum.inl a) [] = S := by
      rw [Function.update_eq_self_iff]; exact hA.symm
    have e2 : Function.update S (Sum.inl b) [] = S := by
      rw [Function.update_eq_self_iff]; exact hB.symm
    simp only [TM2.step, hM, subStmt, TM2.stepAux, hA, hB, List.head?_nil, List.tail_nil, e1,
      e2, Option.isNone_none, Bool.and_self, cond_true, subB]
    all_goals try rfl
  | case2 c x A ih =>
    intro S hA hB
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
      (Sum.inl a) A) (Sum.inl b) []) (Sum.inl o) (xor x c :: S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ?_, h1, h2, ?_, ?_⟩
    · have e : subB c (x :: A) [] = subB (!x && c) A [] := by rw [subB]
      rw [e]
      refine (Reach.step_trans ?_ hR).mono (by simp)
      simp only [TM2.step, hM, subStmt, TM2.stepAux, hA, hB, List.head?_nil, List.tail_nil,
        List.head?_cons, List.tail_cons, Function.update_of_ne hab'.symm,
        Option.isNone_none, Option.isNone_some, Bool.false_and, cond_false,
        Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm,
        Option.getD_some, Option.getD_none, Bool.xor_false, Bool.and_false, Bool.false_or]
      all_goals try rfl
      cases x <;> cases c <;> rfl
    · unfold bs at h3 ⊢; rw [h3, Function.update_self]; simp [subL]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2,
        Function.update_of_ne k1]
  | case3 c y B ih =>
    intro S hA hB
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
      (Sum.inl a) []) (Sum.inl b) B) (Sum.inl o) (xor y c :: S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ?_, h1, h2, ?_, ?_⟩
    · have e : subB c [] (y :: B) = subB (y || c) [] B := by rw [subB]
      rw [e]
      refine (Reach.step_trans ?_ hR).mono (by simp)
      simp only [TM2.step, hM, subStmt, TM2.stepAux, hA, hB, List.head?_nil, List.tail_nil,
        List.head?_cons, List.tail_cons, Function.update_of_ne hab'.symm,
        Option.isNone_none, Option.isNone_some, Bool.and_false, cond_false,
        Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm,
        Option.getD_some, Option.getD_none, Bool.false_xor]
      all_goals try rfl
      cases y <;> cases c <;> rfl
    · unfold bs at h3 ⊢; rw [h3, Function.update_self]; simp [subL]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2,
        Function.update_of_ne k1]
  | case4 c x A y B ih =>
    intro S hA hB
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
      (Sum.inl a) A) (Sum.inl b) B) (Sum.inl o) (xor (xor x y) c :: S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ?_, h1, h2, ?_, ?_⟩
    · have e : subB c (x :: A) (y :: B) = subB ((!x && y) || (c && !(xor x y))) A B := by
        rw [subB]
      rw [e]
      refine (Reach.step_trans ?_ hR).mono (by simp)
      simp only [TM2.step, hM, subStmt, TM2.stepAux, hA, hB,
        List.head?_cons, List.tail_cons, Function.update_of_ne hab'.symm,
        Option.isNone_some, Bool.false_and, cond_false,
        Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm,
        Option.getD_some]
      all_goals try rfl
    · unfold bs at h3 ⊢; rw [h3, Function.update_self]; simp [subL]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2,
        Function.update_of_ne k1]

/-- empty a Bool stack -/
def clearStmt (a : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L)))

lemma clear_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a : Kb) (L E : Λ)
    (hM : M L = clearStmt a L E) (r : ρ) (c : Bool) :
    ∀ (A : List Bool) (S : ∀ k, List (BΓ Kb G k)), S (Sum.inl a) = A →
      Reach M ⟨some L, ((none, none, c), r), S⟩
        ⟨some E, ((none, none, c), r), Function.update S (Sum.inl a) []⟩ (A.length + 1) := by
  intro A
  induction A with
  | nil =>
    intro S hA
    apply (Reach.single _).mono (by simp)
    simp only [TM2.step, hM, clearStmt, TM2.stepAux, hA, List.head?_nil, List.tail_nil,
      Option.isNone_none, cond_true]
    all_goals try rfl
  | cons x A ih =>
    intro S hA
    have := ih (Function.update S (Sum.inl a) A) (by rw [Function.update_self])
    rw [Function.update_idem] at this
    refine (Reach.step_trans ?_ this).mono (by simp)
    simp only [TM2.step, hM, clearStmt, TM2.stepAux, hA, List.head?_cons, List.tail_cons,
      Option.isNone_some, cond_false]
    all_goals try rfl

/-- pushed bits of the canonicalizing transfer -/
def stripPush (c : Bool) (l : List Bool) : List Bool := if c then l else l.dropWhile (fun b => !b)

/-- transfer `a` to `o`, skipping leading `false`s until the flag is set -/
def stripStmt (a o : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.load (fun v => ((none, none, false), v.2)) (TM2.Stmt.goto fun _ => E))
      (TM2.Stmt.branch (fun v => v.1.2.2 || v.1.1.getD false)
        (TM2.Stmt.push (Sum.inl o) (fun v => v.1.1.getD false)
          (TM2.Stmt.load (fun v => ((none, none, true), v.2)) (TM2.Stmt.goto fun _ => L)))
        (TM2.Stmt.load (fun v => ((none, none, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L))))

lemma strip_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a o : Kb) (hao : a ≠ o) (L E : Λ)
    (hM : M L = stripStmt a o L E) (r : ρ) :
    ∀ (A : List Bool) (c : Bool) (S : ∀ k, List (BΓ Kb G k)), S (Sum.inl a) = A →
      Reach M ⟨some L, ((none, none, c), r), S⟩
        ⟨some E, ((none, none, false), r), Function.update (Function.update S (Sum.inl a) [])
          (Sum.inl o) ((stripPush c A).reverse ++ bs S o)⟩ (A.length + 1) := by
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  intro A
  induction A with
  | nil =>
    intro c S hA
    apply (Reach.single _).mono (by simp)
    have e1 : Function.update S (Sum.inl a) [] = S := by
      rw [Function.update_eq_self_iff]; exact hA.symm
    have e2 : (stripPush c []).reverse ++ bs S o = S (Sum.inl o) := by
      cases c <;> simp [stripPush, bs]
    simp only [TM2.step, hM, stripStmt, TM2.stepAux, hA, List.head?_nil, List.tail_nil,
      Option.isNone_none, cond_true, e1, e2, Function.update_eq_self]
    all_goals try rfl
  | cons x A ih =>
    intro c S hA
    by_cases hx : (c || x) = true
    · have := ih true (Function.update (Function.update S (Sum.inl a) A) (Sum.inl o)
        (x :: S (Sum.inl o)))
        (by rw [Function.update_of_ne hao', Function.update_self])
      have e : stripPush c (x :: A) = x :: stripPush true A := by
        cases c <;> cases x <;> simp_all [stripPush]
      rw [e]
      refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by simp)
      · simp only [TM2.step, hM, stripStmt, TM2.stepAux, hA, List.head?_cons, List.tail_cons,
          Option.isNone_some, cond_false, Option.getD_some, hx, cond_true,
          Function.update_of_ne hao'.symm]
        all_goals try rfl
      · congr 1
        funext k
        by_cases h1 : k = Sum.inl o
        · subst h1; simp [bs]
        · by_cases h2 : k = Sum.inl a
          · subst h2; simp only [Function.update_of_ne h1, Function.update_self]
          · simp only [Function.update_of_ne h1, Function.update_of_ne h2]
    · have hc : c = false := by cases c <;> simp_all
      have hx' : x = false := by cases x <;> simp_all
      subst hc hx'
      have := ih false (Function.update S (Sum.inl a) A) (by rw [Function.update_self])
      have e : stripPush false (false :: A) = stripPush false A := by simp [stripPush]
      rw [e]
      refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by simp)
      · simp only [TM2.step, hM, stripStmt, TM2.stepAux, hA, List.head?_cons, List.tail_cons,
          Option.isNone_some, cond_false, Option.getD_some, Bool.or_self]
        all_goals try rfl
      · congr 1
        funext k
        by_cases h1 : k = Sum.inl o
        · subst h1; simp [bs, Function.update_of_ne hao'.symm]
        · by_cases h2 : k = Sum.inl a
          · subst h2; simp only [Function.update_of_ne h1, Function.update_self]
          · simp only [Function.update_of_ne h1, Function.update_of_ne h2]

end Bool

section Generic

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)

/-- copy loop: pop `a` until empty, pushing `f₁ x` on `b` and `f₂ x` on `c`. -/
lemma copy2 (L : Λ) (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (upd : σ → Option (Γ a) → σ) (done : σ → Bool)
    (exitL : σ → Λ) (out₁ : σ → Γ b) (out₂ : σ → Γ c) (f₁ : Γ a → Γ b) (f₂ : Γ a → Γ c)
    (hM : M L = TM2.Stmt.pop a upd
      (TM2.Stmt.branch done (TM2.Stmt.goto exitL)
        (TM2.Stmt.push b out₁ (TM2.Stmt.push c out₂ (TM2.Stmt.goto fun _ => L)))))
    (hupd : ∀ v o o', upd (upd v o) o' = upd v o')
    (hnone : ∀ v, done (upd v none) = true)
    (hsome : ∀ v x, done (upd v (some x)) = false ∧ out₁ (upd v (some x)) = f₁ x ∧
      out₂ (upd v (some x)) = f₂ x) :
    ∀ (xs : List (Γ a)) (S : ∀ k, List (Γ k)) (v : σ), S a = xs →
      ∃ S', Reach M ⟨some L, v, S⟩ ⟨some (exitL (upd v none)), upd v none, S'⟩ (xs.length + 1) ∧
        S' a = [] ∧ S' b = (xs.map f₁).reverse ++ S b ∧ S' c = (xs.map f₂).reverse ++ S c ∧
        ∀ k, k ≠ a → k ≠ b → k ≠ c → S' k = S k := by
  intro xs
  induction xs with
  | nil =>
    intro S v hS
    refine ⟨S, ?_, hS, by simp, by simp, fun _ _ _ _ => rfl⟩
    apply (Reach.single _).mono (by simp)
    have e1 : Function.update S a [] = S := by
      rw [Function.update_eq_self_iff]; exact hS.symm
    simp only [TM2.step, hM, TM2.stepAux, hS, List.head?_nil, List.tail_nil, hnone, cond_true, e1]
    all_goals try rfl
  | cons x xs ih =>
    intro S v hS
    obtain ⟨h1, h2, h3⟩ := hsome v x
    obtain ⟨S', hR, k1, k2, k3, k4⟩ := ih (Function.update (Function.update
      (Function.update S a xs) b (f₁ x :: S b)) c (f₂ x :: S c)) (upd v (some x))
      (by rw [Function.update_of_ne hac, Function.update_of_ne hab, Function.update_self])
    rw [hupd] at hR
    refine ⟨S', (Reach.step_trans ?_ hR).mono (by simp), k1, ?_, ?_, ?_⟩
    · simp only [TM2.step, hM, TM2.stepAux, hS, List.head?_cons, List.tail_cons, h1, h2, h3,
        cond_false, Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
        Function.update_of_ne hbc.symm]
    · rw [k2, Function.update_of_ne hbc, Function.update_self]; simp
    · rw [k3, Function.update_self]; simp
    · intro k j1 j2 j3
      rw [k4 k j1 j2 j3, Function.update_of_ne j3, Function.update_of_ne j2,
        Function.update_of_ne j1]

end Generic

end OCRS19TM


/-! L6: stacks as `mk B Q` (Bool work stacks `B : Kb → List Bool`, other stacks `Q`), the Bool
routines restated on `mk`, plus `mv` (Bool transfer) and `dup` (Bool copy to two stacks). -/

namespace OCRS19TM

open Turing

section MK

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- assemble a stack function from Bool work stacks and the other stacks -/
def mk (B : Kb → List Bool) (Q : ∀ r, List (G r)) : ∀ k : Kb ⊕ R, List (BΓ Kb G k) :=
  fun k => Sum.casesOn (motive := fun k => List (BΓ Kb G k)) k B Q

@[simp] lemma mk_inl (B : Kb → List Bool) (Q : ∀ r, List (G r)) (a : Kb) :
    mk B Q (Sum.inl a) = B a := rfl

@[simp] lemma mk_inr (B : Kb → List Bool) (Q : ∀ r, List (G r)) (r : R) :
    mk B Q (Sum.inr r) = Q r := rfl

lemma bs_mk (B : Kb → List Bool) (Q : ∀ r, List (G r)) (a : Kb) : bs (mk B Q) a = B a := rfl

@[simp] lemma update_mk (B : Kb → List Bool) (Q : ∀ r, List (G r)) (a : Kb) (l : List Bool) :
    Function.update (mk B Q) (Sum.inl a) l = mk (Function.update B a l) Q := by
  funext k
  cases k with
  | inl b =>
    by_cases h : b = a
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Sum.inl_injective e))]
      simp [Function.update_of_ne h]
  | inr r => rw [Function.update_of_ne (fun e => Sum.inl_ne_inr e.symm)]; simp

lemma mk_ext {B' : Kb → List Bool} {Q : ∀ r, List (G r)} (S : ∀ k : Kb ⊕ R, List (BΓ Kb G k))
    (h1 : ∀ a, S (Sum.inl a) = B' a) (h2 : ∀ r, S (Sum.inr r) = Q r) : S = mk B' Q := by
  funext k
  cases k with
  | inl a => exact h1 a
  | inr r => exact h2 r

variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

/-- Bool transfer `a → b` (reverses) -/
def mvStmt (a b : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.push (Sum.inl b) (fun v => v.1.1.getD false)
        (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L))))

lemma mv_run (a b : Kb) (hab : a ≠ b) (L E : Λ) (hM : M L = mvStmt a b L E) (r : ρ) (c : Bool)
    (Q : ∀ r, List (G r)) :
    ∀ (A : List Bool) (B : Kb → List Bool), B a = A →
      Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update (Function.update B a []) b (A.reverse ++ B b)) Q⟩ (A.length + 1) := by
  intro A
  induction A with
  | nil =>
    intro B hA
    apply (Reach.single _).mono (by simp)
    have e : Function.update (Function.update B a []) b ([].reverse ++ B b) = B := by
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
    simp only [TM2.step, hM, mvStmt, TM2.stepAux, mk_inl, hA, List.head?_nil, List.tail_nil,
      Option.isNone_none, cond_true, e, update_mk]
    all_goals (rw [(Function.update_eq_self_iff).mpr hA.symm])
  | cons x A ih =>
    intro B hA
    have := ih (Function.update (Function.update B a A) b (x :: B b))
      (by simp [Function.update_apply, hab])
    refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by simp)
    · simp only [TM2.step, hM, mvStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
        Option.isNone_some, cond_false, Option.getD_some, update_mk,
        Function.update_of_ne hab.symm]
      all_goals try rfl
    · congr 2
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all

/-- Bool copy `a → b, c` (both reversed) -/
def dupStmt (a b c : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.push (Sum.inl b) (fun v => v.1.1.getD false)
        (TM2.Stmt.push (Sum.inl c) (fun v => v.1.1.getD false)
          (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L)))))

lemma dup_run (a b c : Kb) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (L E : Λ)
    (hM : M L = dupStmt a b c L E) (r : ρ) (cr : Bool) (Q : ∀ r, List (G r)) :
    ∀ (A : List Bool) (B : Kb → List Bool), B a = A →
      Reach M ⟨some L, ((none, none, cr), r), mk B Q⟩
        ⟨some E, ((none, none, cr), r),
          mk (Function.update (Function.update (Function.update B a []) b (A.reverse ++ B b)) c
            (A.reverse ++ B c)) Q⟩ (A.length + 1) := by
  intro A
  induction A with
  | nil =>
    intro B hA
    apply (Reach.single _).mono (by simp)
    have e : Function.update (Function.update (Function.update B a []) b ([].reverse ++ B b)) c
        ([].reverse ++ B c) = B := by
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
    simp only [TM2.step, hM, dupStmt, TM2.stepAux, mk_inl, hA, List.head?_nil, List.tail_nil,
      Option.isNone_none, cond_true, e, update_mk]
    all_goals (rw [(Function.update_eq_self_iff).mpr hA.symm])
  | cons x A ih =>
    intro B hA
    have := ih (Function.update (Function.update (Function.update B a A) b (x :: B b)) c
      (x :: B c)) (by simp [Function.update_apply, hab, hac])
    refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by simp)
    · simp only [TM2.step, hM, dupStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
        Option.isNone_some, cond_false, Option.getD_some, update_mk,
        Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
        Function.update_of_ne hbc.symm]
      all_goals try rfl
    · congr 2
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all

lemma add_mk (a b o : Kb) (hab : a ≠ b) (hao : a ≠ o) (hbo : b ≠ o) (L E : Λ)
    (hM : M L = addStmt a b o L E) (r : ρ) (c : Bool) (B : Kb → List Bool) (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, false), r), mk (Function.update (Function.update (Function.update B
        a []) b []) o ((addL c (B a) (B b)).reverse ++ B o)) Q⟩
      (max (B a).length (B b).length + 1) := by
  obtain ⟨S', hR, h1, h2, h3, h4⟩ := add_run M a b o hab hao hbo L E hM r c (B a) (B b) (mk B Q) rfl rfl
  have hS : S' = mk (Function.update (Function.update (Function.update B a []) b []) o
      ((addL c (B a) (B b)).reverse ++ B o)) Q := by
    apply mk_ext
    · intro k
      by_cases ka : k = a
      · subst ka; rw [h1]; simp [Function.update_apply, hab, hao]
      by_cases kb : k = b
      · subst kb; rw [h2]; simp [Function.update_apply, hbo, ka]
      by_cases ko : k = o
      · subst ko
        have h3' := h3
        simp only [bs_mk] at h3'
        unfold bs at h3'
        rw [h3']; simp [Function.update_apply, ka, kb]
      rw [h4 _ (fun e => ka (Sum.inl_injective e)) (fun e => kb (Sum.inl_injective e))
        (fun e => ko (Sum.inl_injective e))]
      simp [Function.update_apply, ka, kb, ko]
    · intro q
      rw [h4 _ (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)
        (fun e => Sum.inl_ne_inr e.symm)]
      rfl
  rw [hS] at hR
  exact hR

lemma sub_mk (a b o : Kb) (hab : a ≠ b) (hao : a ≠ o) (hbo : b ≠ o) (L E : Λ)
    (hM : M L = subStmt a b o L E) (r : ρ) (c : Bool) (B : Kb → List Bool) (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, subB c (B a) (B b)), r), mk (Function.update (Function.update
        (Function.update B a []) b []) o ((subL c (B a) (B b)).reverse ++ B o)) Q⟩
      (max (B a).length (B b).length + 1) := by
  obtain ⟨S', hR, h1, h2, h3, h4⟩ := sub_run M a b o hab hao hbo L E hM r c (B a) (B b) (mk B Q) rfl rfl
  have hS : S' = mk (Function.update (Function.update (Function.update B a []) b []) o
      ((subL c (B a) (B b)).reverse ++ B o)) Q := by
    apply mk_ext
    · intro k
      by_cases ka : k = a
      · subst ka; rw [h1]; simp [Function.update_apply, hab, hao]
      by_cases kb : k = b
      · subst kb; rw [h2]; simp [Function.update_apply, hbo, ka]
      by_cases ko : k = o
      · subst ko
        have h3' := h3
        simp only [bs_mk] at h3'
        unfold bs at h3'
        rw [h3']; simp [Function.update_apply, ka, kb]
      rw [h4 _ (fun e => ka (Sum.inl_injective e)) (fun e => kb (Sum.inl_injective e))
        (fun e => ko (Sum.inl_injective e))]
      simp [Function.update_apply, ka, kb, ko]
    · intro q
      rw [h4 _ (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)
        (fun e => Sum.inl_ne_inr e.symm)]
      rfl
  rw [hS] at hR
  exact hR

lemma clear_mk (a : Kb) (L E : Λ) (hM : M L = clearStmt a L E) (r : ρ) (c : Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk (Function.update B a []) Q⟩ ((B a).length + 1) := by
  have := clear_run M a L E hM r c (B a) (mk B Q) rfl
  rwa [update_mk] at this

lemma strip_mk (a o : Kb) (hao : a ≠ o) (L E : Λ) (hM : M L = stripStmt a o L E) (r : ρ)
    (c : Bool) (B : Kb → List Bool) (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, false), r),
        mk (Function.update (Function.update B a []) o ((stripPush c (B a)).reverse ++ B o)) Q⟩
      ((B a).length + 1) := by
  have := strip_run M a o hao L E hM r (B a) c (mk B Q) rfl
  rwa [update_mk, update_mk, bs_mk] at this

end MK

/-! ## e261f9b1 K1: generic synchronized two-stack transducer (pops `a`, `b` in lockstep,
finite-state update `δ` in the user part `ρ`, optional output symbol pushed on `o`). -/

section Zip

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- Pure semantics: final user state and the emitted symbols (in emission order). -/
def zipOut (δ : ρ → Option Bool → Option Bool → ρ) (out : ρ → Option Bool → Option Bool → Option Bool) :
    ρ → List Bool → List Bool → ρ × List Bool
  | r, [], [] => (r, [])
  | r, x :: A, [] =>
    let p := zipOut δ out (δ r (some x) none) A []
    (p.1, (out r (some x) none).toList ++ p.2)
  | r, [], y :: B =>
    let p := zipOut δ out (δ r none (some y)) [] B
    (p.1, (out r none (some y)).toList ++ p.2)
  | r, x :: A, y :: B =>
    let p := zipOut δ out (δ r (some x) (some y)) A B
    (p.1, (out r (some x) (some y)).toList ++ p.2)

def zipStmt (a b o : Kb) (L E : Λ) (δ : ρ → Option Bool → Option Bool → ρ)
    (out : ρ → Option Bool → Option Bool → Option Bool) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.pop (Sum.inl b) (fun v y => ((v.1.1, y, v.1.2.2), v.2))
      (TM2.Stmt.branch (fun v => v.1.1.isNone && v.1.2.1.isNone)
        (TM2.Stmt.goto fun _ => E)
        (TM2.Stmt.branch (fun v => (out v.2 v.1.1 v.1.2.1).isSome)
          (TM2.Stmt.push (Sum.inl o) (fun v => (out v.2 v.1.1 v.1.2.1).getD false)
            (TM2.Stmt.load (fun v => ((none, none, v.1.2.2), δ v.2 v.1.1 v.1.2.1))
              (TM2.Stmt.goto fun _ => L)))
          (TM2.Stmt.load (fun v => ((none, none, v.1.2.2), δ v.2 v.1.1 v.1.2.1))
            (TM2.Stmt.goto fun _ => L)))))

/-- One loop step, abstractly: from `(x?, y?)` not both `none`. -/
lemma zip_step (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b o : Kb) (hab : a ≠ b) (hao : a ≠ o)
    (hbo : b ≠ o) (L E : Λ) (δ : ρ → Option Bool → Option Bool → ρ)
    (out : ρ → Option Bool → Option Bool → Option Bool) (hM : M L = zipStmt a b o L E δ out)
    (c : Bool) (r : ρ) (A B : List Bool) (S : ∀ k, List (BΓ Kb G k))
    (hA : S (Sum.inl a) = A) (hB : S (Sum.inl b) = B) (hne : ¬ (A = [] ∧ B = [])) :
    TM2.step M ⟨some L, ((none, none, c), r), S⟩ =
      some ⟨some L, ((none, none, c), δ r A.head? B.head?),
        Function.update (Function.update (Function.update S (Sum.inl a) A.tail) (Sum.inl b) B.tail)
          (Sum.inl o) ((out r A.head? B.head?).toList.reverse ++ S (Sum.inl o))⟩ := by
  have hab' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl b := fun h => hab (Sum.inl_injective h)
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  have hbo' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl o := fun h => hbo (Sum.inl_injective h)
  have hn : (A.head?.isNone && B.head?.isNone) = false := by
    cases A <;> cases B <;> simp_all
  cases ho : out r A.head? B.head? with
  | none =>
    simp only [TM2.step, hM, zipStmt, TM2.stepAux, hA, hB, Function.update_of_ne hab'.symm, hn,
      ho, Option.isSome_none, cond_false, Option.toList_none, List.reverse_nil, List.nil_append,
      Function.update_of_ne hao'.symm, Function.update_of_ne hbo'.symm, Function.update_eq_self,
      Bool.false_eq_true]
    simp only [Option.some.injEq, TM2.Cfg.mk.injEq, true_and, and_true]
    rw [eq_comm, Function.update_eq_self_iff, Function.update_of_ne hbo'.symm,
      Function.update_of_ne hao'.symm]
  | some z =>
    simp only [TM2.step, hM, zipStmt, TM2.stepAux, hA, hB, Function.update_of_ne hab'.symm, hn,
      ho, Option.isSome_some, cond_true, cond_false, Option.toList_some, List.reverse_singleton,
      List.singleton_append, Option.getD_some, Function.update_of_ne hao'.symm,
      Function.update_of_ne hbo'.symm]

lemma zip_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b o : Kb) (hab : a ≠ b) (hao : a ≠ o)
    (hbo : b ≠ o) (L E : Λ) (δ : ρ → Option Bool → Option Bool → ρ)
    (out : ρ → Option Bool → Option Bool → Option Bool) (hM : M L = zipStmt a b o L E δ out)
    (c : Bool) : ∀ (r : ρ) (A B : List Bool) (S : ∀ k, List (BΓ Kb G k)),
      S (Sum.inl a) = A → S (Sum.inl b) = B →
      ∃ S', Reach M ⟨some L, ((none, none, c), r), S⟩
          ⟨some E, ((none, none, c), (zipOut δ out r A B).1), S'⟩ (A.length + B.length + 1) ∧
        S' (Sum.inl a) = [] ∧ S' (Sum.inl b) = [] ∧
        bs S' o = (zipOut δ out r A B).2.reverse ++ bs S o ∧
        ∀ k, k ≠ Sum.inl a → k ≠ Sum.inl b → k ≠ Sum.inl o → S' k = S k := by
  have hab' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl b := fun h => hab (Sum.inl_injective h)
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  have hbo' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl o := fun h => hbo (Sum.inl_injective h)
  intro r A B
  induction r, A, B using zipOut.induct δ out with
  | case1 r =>
    intro S hA hB
    have e1 : Function.update S (Sum.inl a) [] = S := Function.update_eq_self_iff.mpr hA.symm
    have e2 : Function.update S (Sum.inl b) [] = S := Function.update_eq_self_iff.mpr hB.symm
    refine ⟨S, ?_, hA, hB, by simp [zipOut], fun _ _ _ _ => rfl⟩
    apply (Reach.single _).mono (by simp)
    simp only [TM2.step, hM, zipStmt, TM2.stepAux, hA, List.tail_nil, e1, hB, e2, List.head?_nil,
      Option.isNone_none, Bool.and_self, cond_true, zipOut]
  | case2 r x A ih =>
    intro S hA hB
    have hs := zip_step M a b o hab hao hbo L E δ out hM c r (x :: A) [] S hA hB (by simp)
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
        (Sum.inl a) A) (Sum.inl b) []) (Sum.inl o) ((out r (some x) none).toList.reverse ++ S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ((Reach.step_trans hs hR).mono
      (by simp only [List.length_cons, List.length_nil]; omega)).of_eq (by simp [zipOut]),
      h1, h2, ?_, ?_⟩
    · unfold bs at h3 ⊢
      rw [h3, Function.update_self]
      simp [zipOut]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2, Function.update_of_ne k1]
  | case3 r y B ih =>
    intro S hA hB
    have hs := zip_step M a b o hab hao hbo L E δ out hM c r [] (y :: B) S hA hB (by simp)
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
        (Sum.inl a) []) (Sum.inl b) B) (Sum.inl o) ((out r none (some y)).toList.reverse ++ S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ((Reach.step_trans hs hR).mono
      (by simp only [List.length_cons, List.length_nil]; omega)).of_eq (by simp [zipOut]),
      h1, h2, ?_, ?_⟩
    · unfold bs at h3 ⊢
      rw [h3, Function.update_self]
      simp [zipOut]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2, Function.update_of_ne k1]
  | case4 r x A y B ih =>
    intro S hA hB
    have hs := zip_step M a b o hab hao hbo L E δ out hM c r (x :: A) (y :: B) S hA hB (by simp)
    obtain ⟨S', hR, h1, h2, h3, h4⟩ := ih (Function.update (Function.update (Function.update S
        (Sum.inl a) A) (Sum.inl b) B) (Sum.inl o)
          ((out r (some x) (some y)).toList.reverse ++ S (Sum.inl o)))
      (by rw [Function.update_of_ne hao', Function.update_of_ne hab', Function.update_self])
      (by rw [Function.update_of_ne hbo', Function.update_self])
    refine ⟨S', ((Reach.step_trans hs hR).mono
      (by simp only [List.length_cons]; omega)).of_eq (by simp [zipOut]),
      h1, h2, ?_, ?_⟩
    · unfold bs at h3 ⊢
      rw [h3, Function.update_self]
      simp [zipOut]
    · intro k k1 k2 k3
      rw [h4 k k1 k2 k3, Function.update_of_ne k3, Function.update_of_ne k2, Function.update_of_ne k1]

end Zip

end OCRS19TM

/-! ## e261f9b1 K1: anticommutation parity scan (`antiB`) as a zip instance (pure level). -/

namespace OCRS19TM

section AntiScan

open QAlgorithms.Stabilizer

/-- x-bit and z-bit of a one-qubit Pauli (`encPauli a = [xbit a, zbit a]`). -/
def xbit : Pauli → Bool
  | .X => true
  | .Y => true
  | _ => false

def zbit : Pauli → Bool
  | .Y => true
  | .Z => true
  | _ => false

lemma encPauli_bits (a : Pauli) : encPauli a = [xbit a, zbit a] := by
  cases a <;> rfl

/-- symplectic form: the two Paulis anticommute -/
def sympB (a b : Pauli) : Bool := xor (xbit a && zbit b) (zbit a && xbit b)

/-- scan state: parity so far, and the pending first bits of the current wire. -/
def antiδ : Bool × Option (Bool × Bool) → Option Bool → Option Bool → Bool × Option (Bool × Bool)
  | (p, none), some x, some y => (p, some (x, y))
  | (p, some (x1, y1)), some x2, some y2 => (xor p (xor (x1 && y2) (x2 && y1)), none)
  | s, _, _ => s

def noOut : Bool × Option (Bool × Bool) → Option Bool → Option Bool → Option Bool :=
  fun _ _ _ => none

lemma zipOut_anti (l : List (Pauli × Pauli)) (p : Bool) :
    zipOut antiδ noOut (p, none) (l.flatMap fun pq => encPauli pq.1)
        (l.flatMap fun pq => encPauli pq.2) =
      ((l.foldl (fun acc pq => xor acc (sympB pq.1 pq.2)) p, none), []) := by
  induction l generalizing p with
  | nil => simp [zipOut]
  | cons pq l ih =>
    obtain ⟨a, b⟩ := pq
    rw [List.flatMap_cons, List.flatMap_cons, encPauli_bits a, encPauli_bits b]
    simp only [List.cons_append, List.nil_append, zipOut, antiδ, noOut, Option.toList_none, List.nil_append, ih, List.foldl_cons,
      sympB]

lemma foldl_xor_ofFn {α : Type} (f : α → Bool) {n : ℕ} (h : Fin n → α) (p : Bool) :
    (List.ofFn h).foldl (fun acc x => xor acc (f x)) p =
      xor p (decide (Odd (Finset.univ.filter fun q => f (h q) = true).card)) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, ih (fun i => h i.succ)]
    simp only [Finset.card_filter, Fin.sum_univ_succ]
    generalize (∑ i : Fin n, if f (h i.succ) = true then 1 else 0) = s
    cases hh : f (h 0) <;> cases p <;> by_cases hs : Odd s <;>
      simp [hs, Nat.odd_add, ← Nat.not_odd_iff_even]

lemma ofFn_flatten_flatMap {n : ℕ} (f : Fin n → Pauli × Pauli) (g : Pauli × Pauli → Pauli) :
    (List.ofFn fun q => encPauli (g (f q))).flatten =
      (List.ofFn f).flatMap fun pq => encPauli (g pq) := by
  rw [List.flatMap, List.map_ofFn]
  rfl

/-- The anticommutation parity of two Pauli strings is computed by one zip pass over their
operator encodings. -/
theorem zipOut_antiB {n : ℕ} (P Q : PauliString n) (p : Bool) :
    zipOut antiδ noOut (p, none) (List.ofFn fun q => encPauli (P.ops q)).flatten
        (List.ofFn fun q => encPauli (Q.ops q)).flatten =
      ((xor p (decide (Odd (Finset.univ.filter fun q => sympB (P.ops q) (Q.ops q) = true).card)),
        none), []) := by
  have h1 := ofFn_flatten_flatMap (fun q => (P.ops q, Q.ops q)) Prod.fst
  have h2 := ofFn_flatten_flatMap (fun q => (P.ops q, Q.ops q)) Prod.snd
  simp only at h1 h2
  rw [h1, h2, zipOut_anti]
  exact congrArg (fun z => ((z, none), [])) (foldl_xor_ofFn (fun pq : Pauli × Pauli => sympB pq.1 pq.2) _ p)

lemma pauliOfBits_bits (a : Pauli) : pauliOfBits (xbit a) (zbit a) = a := by
  cases a <;> rfl

lemma encPauli_mul (a b : Pauli) :
    encPauli (Pauli.mul a b).2 = [xor (xbit a) (xbit b), xor (zbit a) (zbit b)] := by
  cases a <;> cases b <;> rfl

/-- row-multiply scan state: phase accumulator and the pending x-bits of the current wire. -/
def mulδ : ZMod 4 × Option (Bool × Bool) → Option Bool → Option Bool → ZMod 4 × Option (Bool × Bool)
  | (c, none), some x, some y => (c, some (x, y))
  | (c, some (x1, y1)), some x2, some y2 =>
    (c + (Pauli.mul (pauliOfBits x1 x2) (pauliOfBits y1 y2)).1, none)
  | s, _, _ => s

/-- the product's bits are the xor of the factors' bits -/
def mulOut : ZMod 4 × Option (Bool × Bool) → Option Bool → Option Bool → Option Bool
  | _, some x, some y => some (xor x y)
  | _, _, _ => none

lemma zipOut_mul (l : List (Pauli × Pauli)) (c : ZMod 4) :
    zipOut mulδ mulOut (c, none) (l.flatMap fun pq => encPauli pq.1)
        (l.flatMap fun pq => encPauli pq.2) =
      ((l.foldl (fun acc pq => acc + (Pauli.mul pq.1 pq.2).1) c, none),
        l.flatMap fun pq => encPauli (Pauli.mul pq.1 pq.2).2) := by
  induction l generalizing c with
  | nil => simp [zipOut]
  | cons pq l ih =>
    obtain ⟨a, b⟩ := pq
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, encPauli_bits a, encPauli_bits b,
      encPauli_mul]
    simp only [List.cons_append, List.nil_append, zipOut, mulδ, mulOut, Option.toList_some,
      pauliOfBits_bits, ih, List.foldl_cons, List.singleton_append]

lemma foldl_add_ofFn {α : Type} (f : α → ZMod 4) {n : ℕ} (h : Fin n → α) (c : ZMod 4) :
    (List.ofFn h).foldl (fun acc x => acc + f x) c = c + ∑ q, f (h q) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, ih (fun i => h i.succ), Fin.sum_univ_succ, add_assoc]

/-- One zip pass over the operator encodings computes `PauliString.mul`: the phase sum and the
encoding of the product's operators. -/
theorem zipOut_mulRow {n : ℕ} (P Q : PauliString n) (c : ZMod 4) :
    zipOut mulδ mulOut (c, none) (List.ofFn fun q => encPauli (P.ops q)).flatten
        (List.ofFn fun q => encPauli (Q.ops q)).flatten =
      ((c + ∑ q : Fin n, (Pauli.mul (P.ops q) (Q.ops q)).1, none),
        (List.ofFn fun q => encPauli ((P.mul Q).ops q)).flatten) := by
  have h1 := ofFn_flatten_flatMap (fun q => (P.ops q, Q.ops q)) Prod.fst
  have h2 := ofFn_flatten_flatMap (fun q => (P.ops q, Q.ops q)) Prod.snd
  have h3 := ofFn_flatten_flatMap (fun q => (P.ops q, Q.ops q))
    (fun pq : Pauli × Pauli => (Pauli.mul pq.1 pq.2).2)
  simp only at h1 h2 h3
  rw [h1, h2, zipOut_mul, foldl_add_ofFn (fun pq : Pauli × Pauli => (Pauli.mul pq.1 pq.2).1)]
  simp only [PauliString.mul]
  rw [h3]

end AntiScan

end OCRS19TM

-- ===== merged K2 =====
set_option autoImplicit false

/-! e261f9b1 K2 (session 9): single-wire Clifford gate on one tableau row as a zip pass (pure level).
On merge into K1: drop the duplicated `zipOut`, `xbit`, `zbit`, `encPauli_bits`, `pauliOfBits_bits`. -/

namespace OCRS19TM

open QAlgorithms.Stabilizer

/-- copy of e261f9b1_gate.lean's CNOT table (drop on merge). -/
def px : Pauli → Bool | .I => false | .X => true | .Y => true | .Z => false
def pz : Pauli → Bool | .I => false | .X => false | .Y => true | .Z => true
def cnotTab (Pc Pt : Pauli) : ZMod 4 × Pauli × Pauli :=
  (if px Pc && pz Pt && (px Pt == pz Pc) then 2 else 0,
    pauliOfBits (px Pc) (xor (pz Pc) (pz Pt)), pauliOfBits (xor (px Pt) (px Pc)) (pz Pt))
def cnotPS {n : ℕ} (c t : Fin n) (P : PauliString n) : PauliString n :=
  ⟨P.phase + (cnotTab (P.ops c) (P.ops t)).1,
    Function.update (Function.update P.ops c (cnotTab (P.ops c) (P.ops t)).2.1) t
      (cnotTab (P.ops c) (P.ops t)).2.2⟩


section Gate1

/-- gate-scan state: phase delta, pending (x-bit, mask bit) of the current wire, owed z-bit. -/
abbrev G1S : Type := ZMod 4 × Option (Bool × Bool) × Option Bool

/-- the new (phase, Pauli) of one wire: the table `f` on the masked wire, identity elsewhere. -/
def g1new (f : Pauli → ZMod 4 × Pauli) (x z m : Bool) : ZMod 4 × Pauli :=
  if m then f (pauliOfBits x z) else (0, pauliOfBits x z)

def g1δ (f : Pauli → ZMod 4 × Pauli) : G1S → Option Bool → Option Bool → G1S
  | (d, none, _), some x, some m => (d, some (x, m), none)
  | (d, some (x, m), _), some z, some _ =>
    (d + (g1new f x z m).1, none, some (zbit (g1new f x z m).2))
  | (d, p, _), none, some _ => (d, p, none)
  | s, _, _ => s

def g1out (f : Pauli → ZMod 4 × Pauli) : G1S → Option Bool → Option Bool → Option Bool
  | (_, none, o), some _, some _ => o
  | (_, some (x, m), _), some z, some _ => some (xbit (g1new f x z m).2)
  | (_, _, o), none, some _ => o
  | _, _, _ => none

/-- One pass over a row's operator bits against the doubled wire mask (plus one trailing flush
bit) applies `f` to the masked wires, accumulating the phase deltas. -/
lemma zipOut_g1 (f : Pauli → ZMod 4 × Pauli) (y : Bool) (l : List (Pauli × Bool)) (d : ZMod 4)
    (o : Option Bool) :
    zipOut (g1δ f) (g1out f) (d, none, o) (l.flatMap fun p => encPauli p.1)
        (l.flatMap (fun p => [p.2, p.2]) ++ [y]) =
      ((l.foldl (fun acc p => acc + (if p.2 then (f p.1).1 else 0)) d, none, none),
        o.toList ++ l.flatMap fun p => encPauli (if p.2 then (f p.1).2 else p.1)) := by
  induction l generalizing d o with
  | nil => cases o <;> simp [zipOut, g1δ, g1out]
  | cons p l ih =>
    obtain ⟨a, m⟩ := p
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, encPauli_bits a]
    cases m with
    | false =>
      simp only [List.cons_append, List.nil_append, zipOut, g1δ, g1out, g1new, pauliOfBits_bits,
        Bool.false_eq_true, if_false, ih, List.foldl_cons, add_zero, Option.toList_some,
        encPauli_bits a, List.singleton_append]
    | true =>
      simp only [List.cons_append, List.nil_append, zipOut, g1δ, g1out, g1new, pauliOfBits_bits,
        if_true, ih, List.foldl_cons, Option.toList_some, encPauli_bits (f a).2,
        List.singleton_append]

lemma ofFn_flatten_flatMap' {α β : Type} {n : ℕ} (f : Fin n → α) (g : α → List β) :
    (List.ofFn fun q => g (f q)).flatten = (List.ofFn f).flatMap g := by
  rw [List.flatMap, List.map_ofFn]
  rfl

lemma foldl_add_ofFn' {α : Type} (f : α → ZMod 4) {n : ℕ} (h : Fin n → α) (c : ZMod 4) :
    (List.ofFn h).foldl (fun acc x => acc + f x) c = c + ∑ q, f (h q) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, ih (fun i => h i.succ), Fin.sum_univ_succ, add_assoc]

/-- the doubled one-hot mask of wire `w`, plus one trailing flush bit. -/
def mask1 (n : ℕ) (w : Fin n) (y : Bool) : List Bool :=
  (List.ofFn fun q : Fin n => [decide (q = w), decide (q = w)]).flatten ++ [y]

/-- PauliString level: one zip pass computes `rowG1 f w` on the operators and its phase delta. -/
theorem zipOut_gate1 {n : ℕ} (f : Pauli → ZMod 4 × Pauli) (w : Fin n) (P : PauliString n)
    (y : Bool) (d : ZMod 4) :
    zipOut (g1δ f) (g1out f) (d, none, none) (List.ofFn fun q => encPauli (P.ops q)).flatten
        (mask1 n w y) =
      ((d + (f (P.ops w)).1, none, none),
        (List.ofFn fun q => encPauli (Function.update P.ops w (f (P.ops w)).2 q)).flatten) := by
  have h1 := ofFn_flatten_flatMap' (fun q => (P.ops q, decide (q = w)))
    (fun p : Pauli × Bool => encPauli p.1)
  have h2 := ofFn_flatten_flatMap' (fun q => (P.ops q, decide (q = w)))
    (fun p : Pauli × Bool => [p.2, p.2])
  have h3 := ofFn_flatten_flatMap' (fun q => (P.ops q, decide (q = w)))
    (fun p : Pauli × Bool => encPauli (if p.2 then (f p.1).2 else p.1))
  simp only at h1 h2 h3
  rw [mask1, h1, h2, zipOut_g1,
    foldl_add_ofFn' (fun p : Pauli × Bool => if p.2 then (f p.1).1 else 0)]
  simp only [Option.toList_none, List.nil_append, decide_eq_true_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← h3]
  congr 3
  funext q
  by_cases hq : q = w
  · subst hq; simp
  · simp [hq, Function.update_of_ne hq]

/-- reverse-copy pass (restores the order of a zip output stack). -/
lemma zipOut_copy {ρ : Type} (r : ρ) (l : List Bool) :
    zipOut (fun r _ _ => r) (fun _ a _ => a) r l [] = (r, l) := by
  induction l with
  | nil => simp [zipOut]
  | cons x l ih => simp [zipOut, ih]

end Gate1

section Wire

variable {σ : Type}

/-- generic per-wire transducer: state, two mask bits per wire, one Pauli in, one Pauli out. -/
def wrun (W : σ → Bool → Bool → Pauli → σ × Pauli) : σ → List (Pauli × Bool × Bool) → σ × List Pauli
  | s, [] => (s, [])
  | s, (a, m1, m2) :: l =>
    ((wrun W (W s m1 m2 a).1 l).1, (W s m1 m2 a).2 :: (wrun W (W s m1 m2 a).1 l).2)

def wδ (W : σ → Bool → Bool → Pauli → σ × Pauli) :
    σ × Option (Bool × Bool) × Option Bool → Option Bool → Option Bool →
      σ × Option (Bool × Bool) × Option Bool
  | (s, none, _), some x, some m => (s, some (x, m), none)
  | (s, some (x, m1), _), some z, some m2 =>
    ((W s m1 m2 (pauliOfBits x z)).1, none, some (zbit (W s m1 m2 (pauliOfBits x z)).2))
  | (s, p, _), none, some _ => (s, p, none)
  | st, _, _ => st

def wout (W : σ → Bool → Bool → Pauli → σ × Pauli) :
    σ × Option (Bool × Bool) × Option Bool → Option Bool → Option Bool → Option Bool
  | (_, none, o), some _, some _ => o
  | (s, some (x, m1), _), some z, some m2 => some (xbit (W s m1 m2 (pauliOfBits x z)).2)
  | (_, _, o), none, some _ => o
  | _, _, _ => none

lemma zipOut_w (W : σ → Bool → Bool → Pauli → σ × Pauli) (y : Bool) (l : List (Pauli × Bool × Bool))
    (s : σ) (o : Option Bool) :
    zipOut (wδ W) (wout W) (s, none, o) (l.flatMap fun p => encPauli p.1)
        (l.flatMap (fun p => [p.2.1, p.2.2]) ++ [y]) =
      (((wrun W s l).1, none, none), o.toList ++ (wrun W s l).2.flatMap encPauli) := by
  induction l generalizing s o with
  | nil => cases o <;> simp [zipOut, wδ, wout, wrun]
  | cons p l ih =>
    obtain ⟨a, m1, m2⟩ := p
    rw [List.flatMap_cons, List.flatMap_cons, encPauli_bits a]
    simp only [List.cons_append, List.nil_append, zipOut, wδ, wout, pauliOfBits_bits, ih, wrun,
      Option.toList_some, List.flatMap_cons, encPauli_bits (W s m1 m2 a).2]

/-- stateless instance -/
lemma wrun_map (F : Bool → Bool → Pauli → Pauli) (s : σ) (l : List (Pauli × Bool × Bool)) :
    wrun (fun s m1 m2 a => (s, F m1 m2 a)) s l = (s, l.map fun p => F p.2.1 p.2.2 p.1) := by
  induction l with
  | nil => rfl
  | cons p l ih => obtain ⟨a, m1, m2⟩ := p; simp [wrun, ih]

/-- capture instance: remember the Paulis on the two masked wires, copy the row. -/
def capW : Pauli × Pauli → Bool → Bool → Pauli → (Pauli × Pauli) × Pauli :=
  fun s m1 m2 a => ((if m1 then a else s.1, if m2 then a else s.2), a)

lemma wrun_cap (s : Pauli × Pauli) (l : List (Pauli × Bool × Bool)) :
    wrun capW s l = ((l.foldl (fun acc p => if p.2.1 then p.1 else acc) s.1,
      l.foldl (fun acc p => if p.2.2 then p.1 else acc) s.2), l.map Prod.fst) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih => obtain ⟨a, m1, m2⟩ := p; simp [wrun, ih, capW]

lemma foldl_pick_none {α β : Type} (P : α → Prop) [DecidablePred P] (g : α → β) (l : List α) (b : β)
    (h : ∀ x ∈ l, ¬ P x) : l.foldl (fun acc x => if P x then g x else acc) b = b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, if_neg (h x List.mem_cons_self)]
    exact ih b fun y hy => h y (List.mem_cons_of_mem _ hy)

lemma foldl_pick_fin {β : Type} {n : ℕ} (g : Fin n → β) (c : Fin n) (b : β) :
    (List.finRange n).foldl (fun acc q => if q = c then g q else acc) b = g c := by
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem (List.mem_finRange c)
  have hnd := List.nodup_finRange n
  rw [hl] at hnd ⊢
  have hc2 : c ∉ l2 := by
    rw [List.nodup_append] at hnd
    exact (List.nodup_cons.1 hnd.2.1).1
  rw [List.foldl_append, List.foldl_cons, if_pos rfl]
  exact foldl_pick_none (· = c) g l2 _ fun x hx hxc => hc2 (hxc ▸ hx)

/-- the CNOT row list: each wire with its (is-control, is-target) mask bits. -/
def cnotL {n : ℕ} (c t : Fin n) (P : PauliString n) : List (Pauli × Bool × Bool) :=
  List.ofFn fun q => (P.ops q, decide (q = c), decide (q = t))

lemma cnotL_cap {n : ℕ} (c t : Fin n) (P : PauliString n) (s : Pauli × Pauli) :
    wrun capW s (cnotL c t P) = ((P.ops c, P.ops t), List.ofFn P.ops) := by
  rw [wrun_cap, cnotL, List.ofFn_eq_map, List.foldl_map, List.foldl_map, List.map_map]
  simp only [decide_eq_true_eq]
  rw [foldl_pick_fin (fun q => P.ops q) c, foldl_pick_fin (fun q => P.ops q) t,
    List.ofFn_eq_map (f := P.ops)]
  rfl

/-- apply instance: write the CNOT table's new control / target Paulis. -/
def cnotF (A B : Pauli) : Bool → Bool → Pauli → Pauli :=
  fun mc mt a => if mc then A else if mt then B else a

lemma cnotL_apply {n : ℕ} (c t : Fin n) (hct : c ≠ t) (P : PauliString n) (s : σ) :
    wrun (fun s m1 m2 a => (s, cnotF (cnotTab (P.ops c) (P.ops t)).2.1
        (cnotTab (P.ops c) (P.ops t)).2.2 m1 m2 a)) s (cnotL c t P) =
      (s, List.ofFn (cnotPS c t P).ops) := by
  rw [wrun_map, cnotL, List.map_ofFn]
  congr 2
  funext q
  simp only [Function.comp, cnotF, cnotPS, decide_eq_true_eq]
  by_cases hqt : q = t
  · subst hqt; simp [Ne.symm hct]
  · by_cases hqc : q = c
    · subst hqc; simp [hqt]
    · simp [hqc, hqt]

/-- the (is-control, is-target) mask of a CNOT, two bits per wire, plus one trailing flush bit. -/
def mask2 (n : ℕ) (c t : Fin n) (y : Bool) : List Bool :=
  (List.ofFn fun q : Fin n => [decide (q = c), decide (q = t)]).flatten ++ [y]

lemma cnotL_enc {n : ℕ} (c t : Fin n) (P : PauliString n) (y : Bool) :
    (List.ofFn fun q => encPauli (P.ops q)).flatten =
        (cnotL c t P).flatMap (fun p => encPauli p.1) ∧
      mask2 n c t y = (cnotL c t P).flatMap (fun p => [p.2.1, p.2.2]) ++ [y] := by
  refine ⟨ofFn_flatten_flatMap' (fun q => (P.ops q, decide (q = c), decide (q = t)))
    (fun p : Pauli × Bool × Bool => encPauli p.1), ?_⟩
  rw [mask2, cnotL, ← ofFn_flatten_flatMap' (fun q => (P.ops q, decide (q = c), decide (q = t)))
    (fun p : Pauli × Bool × Bool => [p.2.1, p.2.2])]

/-- CNOT pass 1: one zip pass captures the control and target Paulis (output = the row). -/
theorem zipOut_cnotCap {n : ℕ} (c t : Fin n) (P : PauliString n) (y : Bool) (s : Pauli × Pauli) :
    zipOut (wδ capW) (wout capW) (s, none, none) (List.ofFn fun q => encPauli (P.ops q)).flatten
        (mask2 n c t y) =
      (((P.ops c, P.ops t), none, none), (List.ofFn fun q => encPauli (P.ops q)).flatten) := by
  obtain ⟨h1, h2⟩ := cnotL_enc c t P y
  rw [h2]
  conv_lhs => rw [h1]
  rw [zipOut_w, cnotL_cap, Option.toList_none, List.nil_append,
    ofFn_flatten_flatMap' P.ops encPauli]

/-- CNOT pass 2: with the captured Paulis in the finite state, one zip pass writes the
operators of `cnotPS c t P` (the phase delta is `(cnotTab Pc Pt).1`). -/
theorem zipOut_cnotApply {n : ℕ} (c t : Fin n) (hct : c ≠ t) (P : PauliString n) (y : Bool) :
    zipOut (wδ (fun (s : Unit) m1 m2 a => (s, cnotF (cnotTab (P.ops c) (P.ops t)).2.1
          (cnotTab (P.ops c) (P.ops t)).2.2 m1 m2 a)))
        (wout (fun (s : Unit) m1 m2 a => (s, cnotF (cnotTab (P.ops c) (P.ops t)).2.1
          (cnotTab (P.ops c) (P.ops t)).2.2 m1 m2 a)))
        ((), none, none) (List.ofFn fun q => encPauli (P.ops q)).flatten (mask2 n c t y) =
      (((), none, none), (List.ofFn fun q => encPauli ((cnotPS c t P).ops q)).flatten) := by
  obtain ⟨h1, h2⟩ := cnotL_enc c t P y
  rw [h1, h2, zipOut_w, cnotL_apply c t hct, Option.toList_none, List.nil_append,
    ofFn_flatten_flatMap' (cnotPS c t P).ops encPauli]

/-- phase bits update: `encPhase (c + d)` from `encPhase c` (a finite table). -/
def phaseAdd (d : ZMod 4) (h l : Bool) : List Bool :=
  encPhase (((if h then 2 else 0) + (if l then 1 else 0) : ZMod 4) + d)

lemma encPhase_bits (c : ZMod 4) :
    ∃ h l, encPhase c = [h, l] ∧ ((if h then 2 else 0) + (if l then 1 else 0) : ZMod 4) = c := by
  revert c
  decide

lemma phaseAdd_spec (c d : ZMod 4) (h l : Bool) (hc : encPhase c = [h, l]) :
    phaseAdd d h l = encPhase (c + d) := by
  obtain ⟨h', l', he, hv⟩ := encPhase_bits c
  rw [hc] at he
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [phaseAdd, hv]

end Wire

section OneHot

/-- one-hot builder scan: A = n unary marks, B = w unary marks; emit true exactly at step w. -/
def ohδ : Bool → Option Bool → Option Bool → Bool
  | fired, some _, b => fired || b.isNone
  | fired, none, _ => fired

def ohOut : Bool → Option Bool → Option Bool → Option Bool
  | fired, some _, b => some (!fired && b.isNone)
  | _, none, _ => none

lemma zipOut_oh_fired (n : ℕ) :
    zipOut ohδ ohOut true (List.replicate n true) [] = (true, List.replicate n false) := by
  induction n with
  | zero => simp [zipOut]
  | succ n ih => simp [List.replicate_succ, zipOut, ohδ, ohOut, ih]

lemma zipOut_oh (n w : ℕ) (hw : w < n) :
    zipOut ohδ ohOut false (List.replicate n true) (List.replicate w true) =
      (true, List.ofFn fun q : Fin n => decide (q.val = w)) := by
  induction n generalizing w with
  | zero => omega
  | succ n ih =>
    cases w with
    | zero =>
      simp only [List.replicate_succ, List.replicate_zero, zipOut, ohδ, ohOut, Option.isNone_none,
        Bool.or_true, Bool.not_false, Bool.and_self, Option.toList_some, zipOut_oh_fired,
        List.ofFn_succ, Fin.val_zero, Fin.val_succ, List.singleton_append]
      simp [List.ofFn_const, List.replicate]
    | succ w =>
      simp only [List.replicate_succ, zipOut, ohδ, ohOut, Option.isNone_some, Bool.or_false,
        Bool.not_false, Bool.and_false, Option.toList_some, ih w (by omega), List.ofFn_succ,
        Fin.val_zero, Fin.val_succ, List.singleton_append]
      simp

/-- the one-hot list doubled (pure `dbl` routine semantics) is the 1-wire mask body. -/
lemma mask1_eq (n : ℕ) (w : Fin n) (y : Bool) :
    mask1 n w y = ((List.ofFn fun q : Fin n => decide (q.val = w.val)).flatMap fun b => [b, b]) ++ [y] := by
  rw [mask1, ← ofFn_flatten_flatMap' (fun q : Fin n => decide (q.val = w.val)) (fun b => [b, b])]
  congr 3
  funext q
  simp [Fin.ext_iff]

end OneHot

end OCRS19TM

-- ===== merged K3 =====
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! e261f9b1 K3 (session 10): control-driven transducer `ctl` (pop a control bit, pop an optional data bit,
emit up to two bits, save the control bit). Instances: dbl (mask doubling), bounded move (row split), phase add.
On merge into K1: drop the Dup section. -/

open Turing

namespace OCRS19TM


section Ctl

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- Pure semantics: final state and emitted bits; one round per control bit. -/
def ctlOut (δ : ρ → Option Bool → Bool → ρ) (o1 o2 : ρ → Option Bool → Bool → Option Bool) :
    ρ → List Bool → List Bool → ρ × List Bool
  | r, [], _ => (r, [])
  | r, y :: B, A =>
    let p := ctlOut δ o1 o2 (δ r A.head? y) B A.tail
    (p.1, (o1 r A.head? y).toList ++ (o2 r A.head? y).toList ++ p.2)

/-- control stack `b`, data stack `a`, output `o`, save stack `s` -/
def ctlStmt (b a o s : Kb) (L E : Λ) (δ : ρ → Option Bool → Bool → ρ)
    (o1 o2 : ρ → Option Bool → Bool → Option Bool) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  let fin : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
    TM2.Stmt.load (fun v => ((none, none, v.1.2.2), δ v.2 v.1.1 (v.1.2.1.getD false)))
      (TM2.Stmt.goto fun _ => L)
  let rest : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
    TM2.Stmt.branch (fun v => (o2 v.2 v.1.1 (v.1.2.1.getD false)).isSome)
      (TM2.Stmt.push (Sum.inl o) (fun v => (o2 v.2 v.1.1 (v.1.2.1.getD false)).getD false) fin) fin
  TM2.Stmt.pop (Sum.inl b) (fun v y => ((v.1.1, y, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.2.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.push (Sum.inl s) (fun v => v.1.2.1.getD false)
        (TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
          (TM2.Stmt.branch (fun v => (o1 v.2 v.1.1 (v.1.2.1.getD false)).isSome)
            (TM2.Stmt.push (Sum.inl o) (fun v => (o1 v.2 v.1.1 (v.1.2.1.getD false)).getD false) rest)
            rest))))

lemma ctl_step (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b a o s : Kb)
    (hba : b ≠ a) (hbo : b ≠ o) (hbs : b ≠ s) (hao : a ≠ o) (has : a ≠ s) (hos : o ≠ s)
    (L E : Λ) (δ : ρ → Option Bool → Bool → ρ) (o1 o2 : ρ → Option Bool → Bool → Option Bool)
    (hM : M L = ctlStmt b a o s L E δ o1 o2)
    (c : Bool) (r : ρ) (y : Bool) (B A : List Bool) (S : ∀ k, List (BΓ Kb G k))
    (hB : S (Sum.inl b) = y :: B) (hA : S (Sum.inl a) = A) :
    TM2.step M ⟨some L, ((none, none, c), r), S⟩ =
      some ⟨some L, ((none, none, c), δ r A.head? y),
        Function.update (Function.update (Function.update (Function.update S (Sum.inl b) B)
          (Sum.inl s) (y :: S (Sum.inl s))) (Sum.inl a) A.tail)
          (Sum.inl o) ((o2 r A.head? y).toList ++ (o1 r A.head? y).toList ++ S (Sum.inl o))⟩ := by
  have hba' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl a := fun h => hba (Sum.inl_injective h)
  have hbo' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl o := fun h => hbo (Sum.inl_injective h)
  have hbs' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl s := fun h => hbs (Sum.inl_injective h)
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  have has' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl s := fun h => has (Sum.inl_injective h)
  have hos' : (Sum.inl o : Kb ⊕ R) ≠ Sum.inl s := fun h => hos (Sum.inl_injective h)
  cases h1 : o1 r A.head? y <;> cases h2 : o2 r A.head? y <;>
    simp only [TM2.step, hM, ctlStmt, TM2.stepAux, hB, List.head?_cons, List.tail_cons,
      Option.isNone_some, cond_false, cond_true, Option.getD_some, Function.update_of_ne hbs'.symm,
      Function.update_of_ne hba'.symm, Function.update_of_ne has'.symm, hA, h1, h2,
      Option.isSome_none, Option.isSome_some, Function.update_of_ne hao'.symm,
      Function.update_of_ne hos', Function.update_of_ne hbo'.symm, Function.update_self,
      Function.update_of_ne hbs', Function.update_of_ne hba', Function.update_of_ne has',
      Function.update_of_ne hao', Function.update_of_ne hos'.symm, Function.update_of_ne hbo',
      Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append,
      List.cons_append, Function.update_idem] <;>
    simp only [Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
  all_goals first
    | rfl
    | (rw [eq_comm, Function.update_eq_self_iff]
       simp only [Function.update_of_ne hao'.symm, Function.update_of_ne hos', Function.update_of_ne hbo'.symm])

lemma ctl_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b a o s : Kb)
    (hba : b ≠ a) (hbo : b ≠ o) (hbs : b ≠ s) (hao : a ≠ o) (has : a ≠ s) (hos : o ≠ s)
    (L E : Λ) (δ : ρ → Option Bool → Bool → ρ) (o1 o2 : ρ → Option Bool → Bool → Option Bool)
    (hM : M L = ctlStmt b a o s L E δ o1 o2) (c : Bool) :
    ∀ (B : List Bool) (r : ρ) (A : List Bool) (S : ∀ k, List (BΓ Kb G k)),
      S (Sum.inl b) = B → S (Sum.inl a) = A →
      ∃ S', Reach M ⟨some L, ((none, none, c), r), S⟩
          ⟨some E, ((none, none, c), (ctlOut δ o1 o2 r B A).1), S'⟩ (B.length + 1) ∧
        S' (Sum.inl b) = [] ∧ S' (Sum.inl a) = A.drop B.length ∧
        bs S' s = B.reverse ++ bs S s ∧
        bs S' o = (ctlOut δ o1 o2 r B A).2.reverse ++ bs S o ∧
        ∀ k, k ≠ Sum.inl b → k ≠ Sum.inl a → k ≠ Sum.inl o → k ≠ Sum.inl s → S' k = S k := by
  have hba' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl a := fun h => hba (Sum.inl_injective h)
  have hbo' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl o := fun h => hbo (Sum.inl_injective h)
  have hbs' : (Sum.inl b : Kb ⊕ R) ≠ Sum.inl s := fun h => hbs (Sum.inl_injective h)
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  have has' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl s := fun h => has (Sum.inl_injective h)
  have hos' : (Sum.inl o : Kb ⊕ R) ≠ Sum.inl s := fun h => hos (Sum.inl_injective h)
  intro B
  induction B with
  | nil =>
    intro r A S hB hA
    have e1 : Function.update S (Sum.inl b) [] = S := Function.update_eq_self_iff.mpr hB.symm
    refine ⟨S, ?_, hB, by simp [hA], by simp, by simp [ctlOut], fun _ _ _ _ _ => rfl⟩
    refine (Reach.single ?_).mono (by simp)
    simp only [TM2.step, hM, ctlStmt, TM2.stepAux, hB, List.head?_nil, List.tail_nil, e1,
      Option.isNone_none, cond_true, ctlOut]
  | cons y B ih =>
    intro r A S hB hA
    have hs := ctl_step M b a o s hba hbo hbs hao has hos L E δ o1 o2 hM c r y B A S hB hA
    obtain ⟨S', hR, h1, h2, h3, h4, h5⟩ := ih (δ r A.head? y) A.tail
      (Function.update (Function.update (Function.update (Function.update S (Sum.inl b) B)
          (Sum.inl s) (y :: S (Sum.inl s))) (Sum.inl a) A.tail)
          (Sum.inl o) ((o2 r A.head? y).toList ++ (o1 r A.head? y).toList ++ S (Sum.inl o)))
      (by rw [Function.update_of_ne hbo', Function.update_of_ne hba', Function.update_of_ne hbs',
            Function.update_self])
      (by rw [Function.update_of_ne hao', Function.update_self])
    refine ⟨S', ((Reach.step_trans hs hR).mono
      (by simp only [List.length_cons]; omega)).of_eq (by simp [ctlOut]), h1, ?_, ?_, ?_, ?_⟩
    · rw [h2]; simp
    · unfold bs at h3 ⊢
      rw [h3, Function.update_of_ne hos'.symm, Function.update_of_ne has'.symm, Function.update_self]
      simp
    · unfold bs at h4 ⊢
      rw [h4, Function.update_self]
      simp only [ctlOut, List.reverse_append]
      cases o1 r A.head? y <;> cases o2 r A.head? y <;> simp
    · intro k k1 k2 k3 k4
      rw [h5 k k1 k2 k3 k4, Function.update_of_ne k3, Function.update_of_ne k2, Function.update_of_ne k4,
        Function.update_of_ne k1]

/-! Instances (pure level). -/

/-- dbl: each control bit emitted twice -/
lemma ctlOut_dbl (B A : List Bool) :
    (ctlOut (fun (_ : Unit) _ _ => ()) (fun _ _ y => some y) (fun _ _ y => some y) () B A).2 =
      B.flatMap fun y => [y, y] := by
  induction B generalizing A with
  | nil => rfl
  | cons y B ih => simp [ctlOut, ih]

/-- bounded move: one data bit per control bit -/
lemma ctlOut_move (B A : List Bool) (h : B.length ≤ A.length) :
    (ctlOut (fun (_ : Unit) _ _ => ()) (fun _ x _ => x) (fun _ _ _ => none) () B A).2 =
      A.take B.length := by
  induction B generalizing A with
  | nil => rfl
  | cons y B ih =>
    cases A with
    | nil => simp at h
    | cons x A =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      simp [ctlOut, ih A h]

end Ctl


/-! Two-pop two-push statement (phase bits of a reversed row). -/
section P2

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

def p2Stmt (a o : Kb) (L : Λ) (g : ρ → Option Bool → Option Bool → Bool × Bool)
    (δ : ρ → Option Bool → Option Bool → ρ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.pop (Sum.inl a) (fun v y => ((v.1.1, y, v.1.2.2), v.2))
      (TM2.Stmt.push (Sum.inl o) (fun v => (g v.2 v.1.1 v.1.2.1).1)
        (TM2.Stmt.push (Sum.inl o) (fun v => (g v.2 v.1.1 v.1.2.1).2)
          (TM2.Stmt.load (fun v => ((none, none, v.1.2.2), δ v.2 v.1.1 v.1.2.1))
            (TM2.Stmt.goto fun _ => L)))))

lemma p2_step (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a o : Kb) (hao : a ≠ o) (L L' : Λ)
    (g : ρ → Option Bool → Option Bool → Bool × Bool) (δ : ρ → Option Bool → Option Bool → ρ)
    (hM : M L' = p2Stmt a o L g δ) (c : Bool) (r : ρ) (x y : Bool) (A : List Bool)
    (S : ∀ k, List (BΓ Kb G k)) (hA : S (Sum.inl a) = x :: y :: A) :
    TM2.step M ⟨some L', ((none, none, c), r), S⟩ =
      some ⟨some L, ((none, none, c), δ r (some x) (some y)),
        Function.update (Function.update S (Sum.inl a) A) (Sum.inl o)
          ((g r (some x) (some y)).2 :: (g r (some x) (some y)).1 :: S (Sum.inl o))⟩ := by
  have hao' : (Sum.inl a : Kb ⊕ R) ≠ Sum.inl o := fun h => hao (Sum.inl_injective h)
  simp only [TM2.step, hM, p2Stmt, TM2.stepAux, hA, List.head?_cons, List.tail_cons,
    Function.update_self, Function.update_idem, Function.update_of_ne hao'.symm, Function.update_of_ne hao']

end P2

/-! Wire transducer on a REVERSED row: control bits `m2, m1`, data bits `z, x` per Pauli; emits `z', x'`. -/
section CWire

open QAlgorithms.Stabilizer


variable {σ : Type}


def cwδ (W : σ → Bool → Bool → Pauli → σ × Pauli) :
    σ × Option (Bool × Bool) → Option Bool → Bool → σ × Option (Bool × Bool)
  | (s, none), x, m => (s, some (x.getD false, m))
  | (s, some (z, m2)), x, m1 => ((W s m1 m2 (pauliOfBits (x.getD false) z)).1, none)

def co1 (W : σ → Bool → Bool → Pauli → σ × Pauli) :
    σ × Option (Bool × Bool) → Option Bool → Bool → Option Bool
  | (_, none), _, _ => none
  | (s, some (z, m2)), x, m1 => some (zbit (W s m1 m2 (pauliOfBits (x.getD false) z)).2)

def co2 (W : σ → Bool → Bool → Pauli → σ × Pauli) :
    σ × Option (Bool × Bool) → Option Bool → Bool → Option Bool
  | (_, none), _, _ => none
  | (s, some (z, m2)), x, m1 => some (xbit (W s m1 m2 (pauliOfBits (x.getD false) z)).2)

theorem ctlOut_w (W : σ → Bool → Bool → Pauli → σ × Pauli) (l : List (Pauli × Bool × Bool)) (s : σ)
    (rest : List Bool) :
    ctlOut (cwδ W) (co1 W) (co2 W) (s, none) (l.flatMap fun p => [p.2.2, p.2.1])
        ((l.flatMap fun p => [zbit p.1, xbit p.1]) ++ rest) =
      (((wrun W s l).1, none), (wrun W s l).2.flatMap fun P => [zbit P, xbit P]) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, m1, m2⟩ := p
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, ctlOut, cwδ, co1, co2,
      List.head?_cons, List.tail_cons, Option.getD_some, pauliOfBits_bits, ih, wrun,
      Option.toList_some, Option.toList_none]

/-- the reversed encoding of a Pauli row splits as the per-Pauli `[z, x]` blocks -/
lemma rev_flatten_enc {n : ℕ} (f : Fin n → Pauli) :
    (List.ofFn fun q => encPauli (f q)).flatten.reverse =
      ((List.ofFn f).reverse.flatMap fun a => [zbit a, xbit a]) := by
  rw [List.reverse_flatten]
  simp [List.flatMap, List.map_reverse, List.map_ofFn, Function.comp_def, encPauli_bits]

end CWire


/-! Single-wire gate as a wire transducer (state = accumulated phase delta). -/
section G1

open QAlgorithms.Stabilizer

def g1W (f : Pauli → ZMod 4 × Pauli) : ZMod 4 → Bool → Bool → Pauli → ZMod 4 × Pauli :=
  fun d m1 _ a => if m1 then (d + (f a).1, (f a).2) else (d, a)

lemma wrun_g1 (f : Pauli → ZMod 4 × Pauli) (d : ZMod 4) (l : List (Pauli × Bool × Bool)) :
    wrun (g1W f) d l = (d + (l.map fun p => if p.2.1 then (f p.1).1 else 0).sum,
      l.map fun p => if p.2.1 then (f p.1).2 else p.1) := by
  induction l generalizing d with
  | nil => simp [wrun]
  | cons p l ih =>
    obtain ⟨a, m1, m2⟩ := p
    cases m1 <;> simp [wrun, g1W, ih, add_assoc]

/-- one reversed-row pass of the 1-wire gate on wire `w`: new operators and phase delta. -/
theorem wrun_g1_row {n : ℕ} (f : Pauli → ZMod 4 × Pauli) (w : Fin n) (P : PauliString n) (d : ZMod 4) :
    wrun (g1W f) d (List.ofFn fun q => (P.ops q, decide (q = w), decide (q = w))).reverse =
      (d + (f (P.ops w)).1, (List.ofFn (Function.update P.ops w (f (P.ops w)).2)).reverse) := by
  rw [wrun_g1]
  simp only [List.map_reverse, List.sum_reverse, List.map_ofFn, Function.comp_def, List.sum_ofFn,
    decide_eq_true_eq]
  refine Prod.ext ?_ ?_
  · simp [Finset.sum_ite_eq']
  · simp only
    congr 1
    apply List.ofFn_inj.mpr
    funext q
    by_cases h : q = w
    · subst h; simp
    · simp [h, Function.update_of_ne h]

end G1


/-! CNOT on a reversed row (session 11): capture pass (output = the row, reversed twice -> forward on
the output stack) and apply pass (captured Paulis in the state). -/
section CNOTR

open QAlgorithms.Stabilizer



lemma wrun_fix {σ : Type} (W : σ → Bool → Bool → Pauli → σ × Pauli) (s : σ) (F : Bool → Bool → Pauli → Pauli)
    (h : ∀ m1 m2 a, W s m1 m2 a = (s, F m1 m2 a)) (l : List (Pauli × Bool × Bool)) :
    wrun W s l = (s, l.map fun p => F p.2.1 p.2.2 p.1) := by
  induction l with
  | nil => rfl
  | cons p l ih => obtain ⟨a, m1, m2⟩ := p; simp [wrun, h, ih]

lemma foldl_pick_nodup {α β : Type} [DecidableEq α] (g : α → β) (c : α) :
    ∀ (l : List α) (b : β), l.Nodup → c ∈ l → l.foldl (fun acc q => if q = c then g q else acc) b = g c := by
  intro l
  induction l with
  | nil => intro b _ h; simp at h
  | cons x l ih =>
    intro b hnd hc
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    by_cases hx : x = c
    · subst hx
      rw [if_pos rfl]
      have key : ∀ (l' : List α) (b' : β), x ∉ l' →
          l'.foldl (fun acc q => if q = x then g q else acc) b' = b' := by
        intro l'
        induction l' with
        | nil => intro _ _; rfl
        | cons y l' ih2 =>
          intro b' h
          rw [List.foldl_cons, if_neg (by rintro rfl; exact h List.mem_cons_self),
            ih2 b' (fun h' => h (List.mem_cons_of_mem _ h'))]
      exact key l _ hnd.1
    · rw [if_neg hx]
      exact ih _ hnd.2 ((List.mem_cons.1 hc).resolve_left (Ne.symm hx))

/-- the CNOT wire list in reversed (last wire first) order -/
def cnotLR {n : ℕ} (c t : Fin n) (P : PauliString n) : List (Pauli × Bool × Bool) :=
  (List.ofFn fun q => (P.ops q, decide (q = c), decide (q = t))).reverse

/-- the reversed CNOT control mask, two bits `[is-target, is-control]` per wire, last wire first -/
def cmaskR (n : ℕ) (c t : Fin n) : List Bool :=
  (List.ofFn fun q : Fin n => [decide (q = t), decide (q = c)]).reverse.flatten

lemma cmaskR_eq {n : ℕ} (c t : Fin n) (P : PauliString n) :
    cmaskR n c t = (cnotLR c t P).flatMap fun p => [p.2.2, p.2.1] := by
  simp [cmaskR, cnotLR, List.flatMap, List.map_reverse, List.map_ofFn, Function.comp_def,
    List.flatten_reverse]

lemma encR_eq {n : ℕ} (c t : Fin n) (P : PauliString n) :
    (List.ofFn fun q => encPauli (P.ops q)).flatten.reverse =
      (cnotLR c t P).flatMap fun p => [zbit p.1, xbit p.1] := by
  rw [rev_flatten_enc]
  simp [cnotLR, List.flatMap, List.map_reverse, List.map_ofFn, Function.comp_def]

lemma wrun_capR {n : ℕ} (c t : Fin n) (P : PauliString n) (s : Pauli × Pauli) :
    wrun capW s (cnotLR c t P) = ((P.ops c, P.ops t), (List.ofFn P.ops).reverse) := by
  have hnd : (List.finRange n).reverse.Nodup := List.nodup_reverse.2 (List.nodup_finRange n)
  have hm : ∀ q : Fin n, q ∈ (List.finRange n).reverse := fun q => by simp
  rw [wrun_cap, cnotLR, List.ofFn_eq_map, ← List.map_reverse, List.foldl_map, List.foldl_map,
    List.map_map]
  simp only [decide_eq_true_eq]
  rw [foldl_pick_nodup (fun q => P.ops q) c _ _ hnd (hm c),
    foldl_pick_nodup (fun q => P.ops q) t _ _ hnd (hm t), List.ofFn_eq_map (f := P.ops),
    List.map_reverse]
  rfl

/-- apply instance: the captured Paulis select the CNOT table entry -/
def cnotAW : Pauli × Pauli → Bool → Bool → Pauli → (Pauli × Pauli) × Pauli :=
  fun s m1 m2 a => (s, cnotF (cnotTab s.1 s.2).2.1 (cnotTab s.1 s.2).2.2 m1 m2 a)

lemma wrun_applyR {n : ℕ} (c t : Fin n) (hct : c ≠ t) (P : PauliString n) :
    wrun cnotAW (P.ops c, P.ops t) (cnotLR c t P) =
      ((P.ops c, P.ops t), (List.ofFn (cnotPS c t P).ops).reverse) := by
  rw [wrun_fix cnotAW _ (cnotF (cnotTab (P.ops c) (P.ops t)).2.1 (cnotTab (P.ops c) (P.ops t)).2.2)
    (fun _ _ _ => rfl), cnotLR, List.map_reverse, List.map_ofFn]
  congr 2
  apply List.ofFn_inj.mpr
  funext q
  simp only [Function.comp, cnotF, cnotPS, decide_eq_true_eq]
  by_cases hqt : q = t
  · subst hqt; simp [Ne.symm hct]
  · by_cases hqc : q = c
    · subst hqc; simp [hqt]
    · simp [hqc, hqt]

/-- CNOT pass 1 (ctl level): consumes the reversed row ops, captures `(P_c, P_t)`, re-emits the row
(the output stack then holds the FORWARD row encoding). -/
theorem ctlOut_cnotCap {n : ℕ} (c t : Fin n) (P : PauliString n) (s : Pauli × Pauli) (rest : List Bool) :
    ctlOut (cwδ capW) (co1 capW) (co2 capW) (s, none) (cmaskR n c t)
        ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++ rest) =
      (((P.ops c, P.ops t), none), (List.ofFn fun q => encPauli (P.ops q)).flatten.reverse) := by
  conv_lhs => rw [cmaskR_eq c t P, encR_eq c t P, ctlOut_w, wrun_capR]
  rw [rev_flatten_enc]

/-- CNOT pass 2 (ctl level): with the captured Paulis, emits the reversed ops of `cnotPS c t P`. -/
theorem ctlOut_cnotApply {n : ℕ} (c t : Fin n) (hct : c ≠ t) (P : PauliString n) (rest : List Bool) :
    ctlOut (cwδ cnotAW) (co1 cnotAW) (co2 cnotAW) ((P.ops c, P.ops t), none) (cmaskR n c t)
        ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++ rest) =
      (((P.ops c, P.ops t), none),
        (List.ofFn fun q => encPauli ((cnotPS c t P).ops q)).flatten.reverse) := by
  conv_lhs => rw [cmaskR_eq c t P, encR_eq c t P, ctlOut_w, wrun_applyR c t hct]
  rw [rev_flatten_enc]

/-- 1-wire gate (ctl level) on wire `w`, mask `cmaskR n w w`. -/
theorem ctlOut_g1 {n : ℕ} (f : Pauli → ZMod 4 × Pauli) (w : Fin n) (P : PauliString n) (d : ZMod 4)
    (rest : List Bool) :
    ctlOut (cwδ (g1W f)) (co1 (g1W f)) (co2 (g1W f)) (d, none) (cmaskR n w w)
        ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++ rest) =
      ((d + (f (P.ops w)).1, none),
        (List.ofFn fun q => encPauli (Function.update P.ops w (f (P.ops w)).2 q)).flatten.reverse) := by
  have := wrun_g1_row f w P d
  conv_lhs => rw [cmaskR_eq w w P, encR_eq w w P, ctlOut_w, cnotLR, this]
  rw [rev_flatten_enc]

end CNOTR


/-! Session 11: state lens for ctl instances, and one full row pass at the TM level
(ctl pass over the reversed row ops, phase bits via p2, mask restore via mv). -/
section RowPass

lemma ctlOut_lens {ρ τ : Type} (get : ρ → τ) (set : ρ → τ → ρ) (hgs : ∀ r t, get (set r t) = t)
    (hss : ∀ r t t', set (set r t) t' = set r t') (hsg : ∀ r, set r (get r) = r)
    (δ : τ → Option Bool → Bool → τ) (o1 o2 : τ → Option Bool → Bool → Option Bool) :
    ∀ (B A : List Bool) (r : ρ),
      ctlOut (fun r x y => set r (δ (get r) x y)) (fun r x y => o1 (get r) x y)
          (fun r x y => o2 (get r) x y) r B A =
        (set r (ctlOut δ o1 o2 (get r) B A).1, (ctlOut δ o1 o2 (get r) B A).2) := by
  intro B
  induction B with
  | nil => intro A r; simp [ctlOut, hsg]
  | cons y B ih => intro A r; simp [ctlOut, ih, hgs, hss]

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

theorem rowpass_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Y s : Kb)
    (hbX : b ≠ X) (hbY : b ≠ Y) (hbs : b ≠ s) (hXY : X ≠ Y) (hXs : X ≠ s) (hYs : Y ≠ s)
    (L1 L2 L3 L0 : Λ) (δ : ρ → Option Bool → Bool → ρ) (o1 o2 : ρ → Option Bool → Bool → Option Bool)
    (g : ρ → Option Bool → Option Bool → Bool × Bool) (δp : ρ → Option Bool → Option Bool → ρ)
    (hM1 : M L1 = ctlStmt b X Y s L1 L2 δ o1 o2) (hM2 : M L2 = p2Stmt X Y L3 g δp)
    (hM3 : M L3 = mvStmt s b L3 L0)
    (c : Bool) (r r1 : ρ) (mask D out : List Bool) (x y : Bool) (rest : List Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = mask) (hX : B X = D ++ x :: y :: rest) (hs : B s = []) (hlen : D.length = mask.length)
    (hctl : ctlOut δ o1 o2 r mask (D ++ x :: y :: rest) = (r1, out)) :
    Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
      ⟨some L0, ((none, none, c), δp r1 (some x) (some y)),
        mk (Function.update (Function.update B X rest) Y
          ((g r1 (some x) (some y)).2 :: (g r1 (some x) (some y)).1 :: (out.reverse ++ B Y))) Q⟩
      (2 * mask.length + 3) := by
  obtain ⟨S1, hR1, h1b, h1X, h1s, h1Y, h1o⟩ := ctl_run M b X Y s hbX hbY hbs hXY hXs hYs L1 L2 δ o1 o2
    hM1 c mask r (D ++ x :: y :: rest) (mk B Q) (by simp [hb]) (by simp [hX])
  simp only [hctl] at hR1 h1Y
  set B1 : Kb → List Bool := Function.update (Function.update (Function.update (Function.update B b [])
      X (x :: y :: rest)) Y (out.reverse ++ B Y)) s mask.reverse with hB1
  have hS1 : S1 = mk B1 Q := by
    apply mk_ext
    · intro a
      by_cases has : a = s
      · subst has; simpa [hB1, bs, hs] using h1s
      by_cases haY : a = Y
      · subst haY; simpa [hB1, bs, hYs] using h1Y
      by_cases haX : a = X
      · subst haX; simp [hB1, hXs, hXY, h1X, hlen]
      by_cases hab : a = b
      · subst hab; simp [hB1, hbs, hbY, hbX, h1b]
      rw [h1o (Sum.inl a) (fun e => hab (Sum.inl_injective e)) (fun e => haX (Sum.inl_injective e))
        (fun e => haY (Sum.inl_injective e)) (fun e => has (Sum.inl_injective e))]
      simp [hB1, Function.update_apply, has, haY, haX, hab]
    · intro r'
      rw [h1o (Sum.inr r') (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)
        (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)]
      rfl
  subst hS1
  have hs2 := p2_step M X Y hXY L3 L2 g δp hM2 c r1 x y rest (mk B1 Q)
    (by simp [hB1, Function.update_apply, hXs, hXY])
  simp only [update_mk, mk_inl] at hs2
  have hR3 := mv_run M s b hbs.symm L3 L0 hM3 (δp r1 (some x) (some y)) c Q mask.reverse
    (Function.update (Function.update B1 X rest) Y
      ((g r1 (some x) (some y)).2 :: (g r1 (some x) (some y)).1 :: B1 Y))
    (by simp [hB1, Function.update_apply, hXs, hYs, hXs.symm, hYs.symm, hbs.symm])
  refine ((hR1.trans (Reach.step_trans hs2 hR3)).of_eq ?_).mono ?_
  · congr 1
    congr 1
    funext a
    by_cases has : a = s
    · subst has; simp [hB1, Function.update_apply, hs, hbX, hbY, hbs, hXY, hXs, hYs, hbX.symm, hbY.symm, hbs.symm, hXY.symm, hXs.symm, hYs.symm]
    by_cases haY : a = Y
    · subst haY; simp [hB1, Function.update_apply, hbX, hbY, hbs, hXY, hXs, hYs, hbX.symm, hbY.symm, hbs.symm, hXY.symm, hXs.symm, hYs.symm]
    by_cases haX : a = X
    · subst haX; simp [hB1, Function.update_apply, hbX, hbY, hbs, hXY, hXs, hYs, hbX.symm, hbY.symm, hbs.symm, hXY.symm, hXs.symm, hYs.symm]
    by_cases hab : a = b
    · subst hab; simp [hB1, Function.update_apply, hb, hbX, hbY, hbs, hXY, hXs, hYs, hbX.symm, hbY.symm, hbs.symm, hXY.symm, hXs.symm, hYs.symm]
    simp [hB1, Function.update_apply, has, haY, haX, hab]
  · simp only [List.length_reverse]; omega

end RowPass

end OCRS19TM

-- ===== session 12: G1Row =====
namespace OCRS19TM

section G1Row

open QAlgorithms.Stabilizer

/-- phase value from its two encoding bits `[h, l]` -/
def phOf (h l : Bool) : ZMod 4 := (if h then 2 else 0) + (if l then 1 else 0)

lemma phOf_enc (c : ZMod 4) : phOf (decide (2 ≤ c.val)) (decide (c.val % 2 = 1)) = c := by
  revert c; decide

/-- encoding of one tableau row (phase bits then two bits per wire) -/
def encPS {n : ℕ} (P : PauliString n) : List Bool :=
  encPhase P.phase ++ (List.ofFn fun q => encPauli (P.ops q)).flatten

lemma encodeTableau_eq {n : ℕ} (T : Tableau n) :
    encodeTableau T = (List.ofFn fun j => encPS (T j)).flatten := rfl

lemma encPauli_length (p : Pauli) : (encPauli p).length = 2 := by cases p <;> rfl

lemma opsEnc_length {n : ℕ} (P : PauliString n) :
    (List.ofFn fun q => encPauli (P.ops q)).flatten.length = 2 * n := by
  simp [List.length_flatten, Function.comp_def, encPauli_length, List.sum_ofFn]; ring

lemma cmaskR_length (n : ℕ) (c t : Fin n) : (cmaskR n c t).length = 2 * n := by
  simp [cmaskR, List.length_flatten, Function.comp_def, List.sum_ofFn, List.map_reverse,
    List.sum_reverse]; ring

lemma encPS_rev {n : ℕ} (P : PauliString n) :
    (encPS P).reverse = (List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++
      (decide (P.phase.val % 2 = 1) :: decide (2 ≤ P.phase.val) :: []) := by
  simp [encPS, encPhase]

/-- a 1-wire gate on one row (same as `conjPS` of the Q side) -/
def rowG1 {n : ℕ} (f : Pauli → ZMod 4 × Pauli) (q : Fin n) (P : PauliString n) : PauliString n :=
  ⟨P.phase + (f (P.ops q)).1, Function.update P.ops q (f (P.ops q)).2⟩

/-- phase-bit pass for a gate row: new phase = old phase + accumulated delta, bits pushed as `(l', h')` -/
def g1p2 {ρ : Type} (get : ρ → ZMod 4 × Option (Bool × Bool)) :
    ρ → Option Bool → Option Bool → Bool × Bool :=
  fun r x y =>
    (decide ((phOf (y.getD false) (x.getD false) + (get r).1).val % 2 = 1),
      decide (2 ≤ (phOf (y.getD false) (x.getD false) + (get r).1).val))

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- TM level: one tableau row through a 1-wire Clifford gate `f` on wire `w`. -/
theorem g1_row {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Y s : Kb)
    (hbX : b ≠ X) (hbY : b ≠ Y) (hbs : b ≠ s) (hXY : X ≠ Y) (hXs : X ≠ s) (hYs : Y ≠ s)
    (L1 L2 L3 L0 : Λ) (get : ρ → ZMod 4 × Option (Bool × Bool))
    (set : ρ → ZMod 4 × Option (Bool × Bool) → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r)
    (f : Pauli → ZMod 4 × Pauli) (w : Fin n)
    (hM1 : M L1 = ctlStmt b X Y s L1 L2 (fun r x y => set r (cwδ (g1W f) (get r) x y))
      (fun r x y => co1 (g1W f) (get r) x y) (fun r x y => co2 (g1W f) (get r) x y))
    (hM2 : M L2 = p2Stmt X Y L3 (g1p2 get) (fun r _ _ => set r (0, none)))
    (hM3 : M L3 = mvStmt s b L3 L0)
    (c : Bool) (r : ρ) (hr : get r = (0, none)) (P : PauliString n) (rest : List Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = cmaskR n w w) (hX : B X = (encPS P).reverse ++ rest) (hs : B s = []) :
    Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
      ⟨some L0, ((none, none, c), set r (0, none)),
        mk (Function.update (Function.update B X rest) Y (encPS (rowG1 f w P) ++ B Y)) Q⟩
      (2 * (cmaskR n w w).length + 3) := by
  have hctl := ctlOut_lens get set hgs hss hsg (cwδ (g1W f)) (co1 (g1W f)) (co2 (g1W f))
    (cmaskR n w w) ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++
      (decide (P.phase.val % 2 = 1) :: decide (2 ≤ P.phase.val) :: rest)) r
  rw [hr, ctlOut_g1] at hctl
  have h := rowpass_run M b X Y s hbX hbY hbs hXY hXs hYs L1 L2 L3 L0 _ _ _ (g1p2 get)
    (fun r _ _ => set r (0, none)) hM1 hM2 hM3 c r _ _ _ _ _ _ _ B Q hb
    (by rw [hX, encPS_rev]; simp) hs
    (by rw [List.length_reverse, opsEnc_length, cmaskR_length]) hctl
  refine h.of_eq ?_
  simp only [hss, hgs, g1p2, Option.getD_some, zero_add, phOf_enc, List.reverse_reverse, encPS, rowG1,
    encPhase, List.cons_append, List.nil_append]
  rfl

end G1Row

end OCRS19TM

-- ===== session 12: RowLoop =====
namespace OCRS19TM

section RowLoop

open QAlgorithms.Stabilizer

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}
variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

/-- loop head: peek `X`; empty -> `E`, else -> `L` (register restored) -/
def testStmt (X : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.peek (Sum.inl X) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L)))

lemma test_some (X : Kb) (L0 L E : Λ) (hM : M L0 = testStmt X L E) (r : ρ) (c : Bool)
    (Q : ∀ r, List (G r)) (B : Kb → List Bool) (x : Bool) (A : List Bool) (hX : B X = x :: A) :
    Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩ ⟨some L, ((none, none, c), r), mk B Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, testStmt, TM2.stepAux, mk_inl, hX, List.head?_cons, Option.isNone_some,
    cond_false]
lemma test_none (X : Kb) (L0 L E : Λ) (hM : M L0 = testStmt X L E) (r : ρ) (c : Bool)
    (Q : ∀ r, List (G r)) (B : Kb → List Bool) (hX : B X = []) :
    Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩ ⟨some E, ((none, none, c), r), mk B Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, testStmt, TM2.stepAux, mk_inl, hX, List.head?_nil, Option.isNone_none,
    cond_true]
/-- generic row loop: rows are popped from `X` (each stored reversed), outputs pushed on `Y`. -/
theorem rows_loop {α : Type} (X Y : Kb) (hXY : X ≠ Y) (L0 L1 E : Λ) (hM : M L0 = testStmt X L1 E)
    (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (Pinv : (Kb → List Bool) → Prop)
    (hP : ∀ B rest Yv, Pinv B → Pinv (Function.update (Function.update B X rest) Y Yv))
    (enc out : α → List Bool) (hne : ∀ a, enc a ≠ []) (t : ℕ)
    (hbody : ∀ a rest B, Pinv B → B X = (enc a).reverse ++ rest →
      Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
        ⟨some L0, ((none, none, c), r),
          mk (Function.update (Function.update B X rest) Y (out a ++ B Y)) Q⟩ t) :
    ∀ (L : List α) (B : Kb → List Bool), Pinv B → B X = (L.map fun a => (enc a).reverse).flatten →
      Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update (Function.update B X []) Y ((L.reverse.map out).flatten ++ B Y)) Q⟩
        (L.length * (t + 1) + 1) := by
  intro L
  induction L with
  | nil =>
    intro B _ hX
    refine ((test_none M X L0 L1 E hM r c Q B (by simpa using hX)).of_eq ?_).mono (by simp)
    congr 2
    funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
  | cons a L ih =>
    intro B hPB hX
    obtain ⟨x, A, hxA⟩ : ∃ x A, (enc a).reverse = x :: A := by
      cases h : (enc a).reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp h) (hne a)
      | cons x A => exact ⟨x, A, rfl⟩
    have h1 := test_some M X L0 L1 E hM r c Q B x (A ++ (L.map fun a => (enc a).reverse).flatten)
      (by rw [hX]; simp [hxA])
    have h2 := hbody a ((L.map fun a => (enc a).reverse).flatten) B hPB (by rw [hX]; simp)
    have h3 := ih _ (hP B ((L.map fun a => (enc a).reverse).flatten) (out a ++ B Y) hPB) (by simp [Function.update_apply, hXY])
    refine ((h1.trans (h2.trans h3)).of_eq ?_).mono ?_
    · congr 2
      funext k; simp only [Function.update_apply]
      split_ifs <;> simp_all [List.reverse_cons, List.map_append, List.flatten_append]
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

lemma encPS_ne {n : ℕ} (P : PauliString n) : encPS P ≠ [] := by simp [encPS, encPhase]

lemma encodeTableau_rev {n : ℕ} (T : Tableau n) :
    (encodeTableau T).reverse = (((List.ofFn T).reverse).map fun a => (encPS a).reverse).flatten := by
  rw [encodeTableau_eq, List.reverse_flatten]
  simp [List.map_reverse, List.map_ofFn, Function.comp_def]

/-- TM level: a 1-wire Clifford gate on the whole tableau stored reversed on `X`. -/
theorem g1_tab {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Y s : Kb)
    (hbX : b ≠ X) (hbY : b ≠ Y) (hbs : b ≠ s) (hXY : X ≠ Y) (hXs : X ≠ s) (hYs : Y ≠ s)
    (L0 L1 L2 L3 E : Λ) (get : ρ → ZMod 4 × Option (Bool × Bool))
    (set : ρ → ZMod 4 × Option (Bool × Bool) → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r)
    (f : Pauli → ZMod 4 × Pauli) (w : Fin n)
    (hM0 : M L0 = testStmt X L1 E)
    (hM1 : M L1 = ctlStmt b X Y s L1 L2 (fun r x y => set r (cwδ (g1W f) (get r) x y))
      (fun r x y => co1 (g1W f) (get r) x y) (fun r x y => co2 (g1W f) (get r) x y))
    (hM2 : M L2 = p2Stmt X Y L3 (g1p2 get) (fun r _ _ => set r (0, none)))
    (hM3 : M L3 = mvStmt s b L3 L0)
    (c : Bool) (r : ρ) (hr : get r = (0, none)) (T : Tableau n)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = cmaskR n w w) (hX : B X = (encodeTableau T).reverse) (hs : B s = []) :
    Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r),
        mk (Function.update (Function.update B X []) Y
          (encodeTableau (fun j => rowG1 f w (T j)) ++ B Y)) Q⟩
      (n * (2 * (cmaskR n w w).length + 4) + 1) := by
  have hr' : set r (0, none) = r := by rw [← hr, hsg]
  have key := rows_loop M X Y hXY L0 L1 E hM0 r c Q (fun B => B b = cmaskR n w w ∧ B s = [])
    (fun B rest Yv h => by simp [Function.update_apply, hbX, hbY, hbs, h.1, h.2]; simp_all [Ne.symm hXs, Ne.symm hYs])
    encPS (fun P => encPS (rowG1 f w P)) encPS_ne (2 * (cmaskR n w w).length + 3)
    (fun a rest B hPB hXa => by
      have := g1_row M b X Y s hbX hbY hbs hXY hXs hYs L1 L2 L3 L0 get set hgs hss hsg f w hM1 hM2 hM3
        c r hr a rest B Q hPB.1 hXa hPB.2
      rwa [hr'] at this)
    ((List.ofFn T).reverse) B ⟨hb, hs⟩ (by rw [hX, encodeTableau_rev])
  refine (key.of_eq ?_).mono ?_
  · congr 3
    rw [encodeTableau_eq]
    simp [List.map_ofFn, Function.comp_def]
  · simp

end RowLoop

end OCRS19TM

-- ===== session 12: CNOT rows =====
namespace OCRS19TM

section CnotRow

open QAlgorithms.Stabilizer

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- CNOT pre-pass: capture `(P_c, P_t)` (ctl pass into scratch `Z`), move `Z` back onto `X`, restore the mask.
All stacks end as they started; only the controller state changes. -/
theorem cnot_cap_pre {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Z s : Kb)
    (hbX : b ≠ X) (hbZ : b ≠ Z) (hbs : b ≠ s) (hXZ : X ≠ Z) (hXs : X ≠ s) (hZs : Z ≠ s)
    (L1 L1a L1b L2 : Λ) (get : ρ → (Pauli × Pauli) × Option (Bool × Bool))
    (set : ρ → (Pauli × Pauli) × Option (Bool × Bool) → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r) (c t : Fin n)
    (hM1 : M L1 = ctlStmt b X Z s L1 L1a (fun r x y => set r (cwδ capW (get r) x y))
      (fun r x y => co1 capW (get r) x y) (fun r x y => co2 capW (get r) x y))
    (hMa : M L1a = mvStmt Z X L1a L1b) (hMb : M L1b = mvStmt s b L1b L2)
    (cc : Bool) (r : ρ) (s0 : Pauli × Pauli) (hr : get r = (s0, none)) (P : PauliString n)
    (rest : List Bool) (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = cmaskR n c t)
    (hX : B X = (List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++ rest)
    (hs : B s = []) (hZ : B Z = []) :
    Reach M ⟨some L1, ((none, none, cc), r), mk B Q⟩
      ⟨some L2, ((none, none, cc), set r ((P.ops c, P.ops t), none)), mk B Q⟩
      (3 * (cmaskR n c t).length + 3) := by
  set F := (List.ofFn fun q => encPauli (P.ops q)).flatten with hF
  set mask := cmaskR n c t with hmask
  have hlen : F.length = mask.length := by rw [hF, hmask, opsEnc_length, cmaskR_length]
  have hctl := ctlOut_lens get set hgs hss hsg (cwδ capW) (co1 capW) (co2 capW) mask (F.reverse ++ rest) r
  rw [hr, hmask, hF, ctlOut_cnotCap] at hctl
  rw [← hF, ← hmask] at hctl
  obtain ⟨S1, hR1, h1b, h1X, h1s, h1Z, h1o⟩ := ctl_run M b X Z s hbX hbZ hbs hXZ hXs hZs L1 L1a _ _ _
    hM1 cc mask r (F.reverse ++ rest) (mk B Q) (by simp [hb]) (by simp [hX])
  simp only [hctl] at hR1 h1Z
  set B1 : Kb → List Bool := Function.update (Function.update (Function.update (Function.update B b [])
      X rest) Z F) s mask.reverse with hB1
  have hS1 : S1 = mk B1 Q := by
    apply mk_ext
    · intro a
      by_cases has : a = s
      · subst has; simpa [hB1, bs, hs] using h1s
      by_cases haZ : a = Z
      · subst haZ; simpa [hB1, bs, hZs, hZ] using h1Z
      by_cases haX : a = X
      · subst haX; simp [hB1, hXs, hXZ, h1X, ← hlen]
      by_cases hab : a = b
      · subst hab; simp [hB1, hbs, hbZ, hbX, h1b]
      rw [h1o (Sum.inl a) (fun e => hab (Sum.inl_injective e)) (fun e => haX (Sum.inl_injective e))
        (fun e => haZ (Sum.inl_injective e)) (fun e => has (Sum.inl_injective e))]
      simp [hB1, Function.update_apply, has, haZ, haX, hab]
    · intro r'
      rw [h1o (Sum.inr r') (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)
        (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)]
      rfl
  subst hS1
  have hRa := mv_run M Z X hXZ.symm L1a L1b hMa (set r ((P.ops c, P.ops t), none)) cc Q F B1
    (by simp [hB1, Function.update_apply, hZs])
  have hRb := mv_run M s b hbs.symm L1b L2 hMb (set r ((P.ops c, P.ops t), none)) cc Q mask.reverse
    (Function.update (Function.update B1 Z []) X (F.reverse ++ B1 X))
    (by simp [hB1, Function.update_apply, hXs.symm, hZs.symm])
  refine ((hR1.trans (hRa.trans hRb)).of_eq ?_).mono ?_
  · congr 2
    funext a
    by_cases has : a = s
    · subst has; simp [hB1, Function.update_apply, hs, hbs.symm, hXs.symm, hZs.symm]
    by_cases haZ : a = Z
    · subst haZ; simp [hB1, Function.update_apply, hZ, hbZ.symm, hXZ.symm, hZs]
    by_cases haX : a = X
    · subst haX; simp [hB1, Function.update_apply, hX, hbX.symm, hXZ, hXs]
    by_cases hab : a = b
    · subst hab; simp [hB1, Function.update_apply, hb, hbX, hbZ, hbs]
    simp [hB1, Function.update_apply, has, haZ, haX, hab]
  · rw [hlen, List.length_reverse]; omega

/-- phase pass for a CNOT row: delta from the captured pair -/
def gC {ρ : Type} (get : ρ → (Pauli × Pauli) × Option (Bool × Bool)) :
    ρ → Option Bool → Option Bool → Bool × Bool :=
  fun r x y =>
    (decide ((phOf (y.getD false) (x.getD false) + (cnotTab (get r).1.1 (get r).1.2).1).val % 2 = 1),
      decide (2 ≤ (phOf (y.getD false) (x.getD false) + (cnotTab (get r).1.1 (get r).1.2).1).val))

/-- TM level: one tableau row through CNOT(c, t). -/
theorem cnot_row {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Y Z s : Kb)
    (hbX : b ≠ X) (hbY : b ≠ Y) (hbZ : b ≠ Z) (hbs : b ≠ s) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hXs : X ≠ s)
    (hYs : Y ≠ s) (hZs : Z ≠ s)
    (L1 L1a L1b L2 L3 L4 L0 : Λ) (get : ρ → (Pauli × Pauli) × Option (Bool × Bool))
    (set : ρ → (Pauli × Pauli) × Option (Bool × Bool) → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r) (c t : Fin n) (hct : c ≠ t) (s0 : Pauli × Pauli)
    (hM1 : M L1 = ctlStmt b X Z s L1 L1a (fun r x y => set r (cwδ capW (get r) x y))
      (fun r x y => co1 capW (get r) x y) (fun r x y => co2 capW (get r) x y))
    (hMa : M L1a = mvStmt Z X L1a L1b) (hMb : M L1b = mvStmt s b L1b L2)
    (hM2 : M L2 = ctlStmt b X Y s L2 L3 (fun r x y => set r (cwδ cnotAW (get r) x y))
      (fun r x y => co1 cnotAW (get r) x y) (fun r x y => co2 cnotAW (get r) x y))
    (hM3 : M L3 = p2Stmt X Y L4 (gC get) (fun r _ _ => set r (s0, none)))
    (hM4 : M L4 = mvStmt s b L4 L0)
    (cc : Bool) (r : ρ) (hr : get r = (s0, none)) (P : PauliString n) (rest : List Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = cmaskR n c t) (hX : B X = (encPS P).reverse ++ rest) (hs : B s = []) (hZ : B Z = []) :
    Reach M ⟨some L1, ((none, none, cc), r), mk B Q⟩
      ⟨some L0, ((none, none, cc), r),
        mk (Function.update (Function.update B X rest) Y (encPS (cnotPS c t P) ++ B Y)) Q⟩
      (5 * (cmaskR n c t).length + 6) := by
  have hX' : B X = (List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++
      (decide (P.phase.val % 2 = 1) :: decide (2 ≤ P.phase.val) :: rest) := by
    rw [hX, encPS_rev]; simp
  have h1 := cnot_cap_pre M b X Z s hbX hbZ hbs hXZ hXs hZs L1 L1a L1b L2 get set hgs hss hsg c t
    hM1 hMa hMb cc r s0 hr P _ B Q hb hX' hs hZ
  have hctl := ctlOut_lens get set hgs hss hsg (cwδ cnotAW) (co1 cnotAW) (co2 cnotAW)
    (cmaskR n c t) ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++
      (decide (P.phase.val % 2 = 1) :: decide (2 ≤ P.phase.val) :: rest)) (set r ((P.ops c, P.ops t), none))
  rw [hgs, ctlOut_cnotApply c t hct] at hctl
  have h2 := rowpass_run M b X Y s hbX hbY hbs hXY hXs hYs L2 L3 L4 L0 _ _ _ (gC get)
    (fun r _ _ => set r (s0, none)) hM2 hM3 hM4 cc _ _ _ _ _ _ _ _ B Q hb hX' hs
    (by rw [List.length_reverse, opsEnc_length, cmaskR_length]) hctl
  have hr' : set r (s0, none) = r := by rw [← hr, hsg]
  refine ((h1.trans h2).of_eq ?_).mono ?_
  · simp only [hss, hgs, gC, Option.getD_some, phOf_enc, List.reverse_reverse, encPS, cnotPS,
      encPhase, List.cons_append, List.nil_append, hr']
    rfl
  · omega

/-- TM level: CNOT(c, t) on the whole tableau stored reversed on `X`. -/
theorem cnot_tab {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Y Z s : Kb)
    (hbX : b ≠ X) (hbY : b ≠ Y) (hbZ : b ≠ Z) (hbs : b ≠ s) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hXs : X ≠ s)
    (hYZ : Y ≠ Z) (hYs : Y ≠ s) (hZs : Z ≠ s)
    (L0 L1 L1a L1b L2 L3 L4 E : Λ) (get : ρ → (Pauli × Pauli) × Option (Bool × Bool))
    (set : ρ → (Pauli × Pauli) × Option (Bool × Bool) → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r) (c t : Fin n) (hct : c ≠ t) (s0 : Pauli × Pauli)
    (hM0 : M L0 = testStmt X L1 E)
    (hM1 : M L1 = ctlStmt b X Z s L1 L1a (fun r x y => set r (cwδ capW (get r) x y))
      (fun r x y => co1 capW (get r) x y) (fun r x y => co2 capW (get r) x y))
    (hMa : M L1a = mvStmt Z X L1a L1b) (hMb : M L1b = mvStmt s b L1b L2)
    (hM2 : M L2 = ctlStmt b X Y s L2 L3 (fun r x y => set r (cwδ cnotAW (get r) x y))
      (fun r x y => co1 cnotAW (get r) x y) (fun r x y => co2 cnotAW (get r) x y))
    (hM3 : M L3 = p2Stmt X Y L4 (gC get) (fun r _ _ => set r (s0, none)))
    (hM4 : M L4 = mvStmt s b L4 L0)
    (cc : Bool) (r : ρ) (hr : get r = (s0, none)) (T : Tableau n)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = cmaskR n c t) (hX : B X = (encodeTableau T).reverse) (hs : B s = []) (hZ : B Z = []) :
    Reach M ⟨some L0, ((none, none, cc), r), mk B Q⟩
      ⟨some E, ((none, none, cc), r),
        mk (Function.update (Function.update B X []) Y
          (encodeTableau (fun j => cnotPS c t (T j)) ++ B Y)) Q⟩
      (n * (5 * (cmaskR n c t).length + 7) + 1) := by
  have key := rows_loop M X Y hXY L0 L1 E hM0 r cc Q
    (fun B => B b = cmaskR n c t ∧ B s = [] ∧ B Z = [])
    (fun B rest Yv h => by
      simp [Function.update_apply, hbX, hbY, hbs, h.1, h.2.1, h.2.2]
      simp_all [Ne.symm hXs, Ne.symm hYs, Ne.symm hXZ, Ne.symm hYZ])
    encPS (fun P => encPS (cnotPS c t P)) encPS_ne (5 * (cmaskR n c t).length + 6)
    (fun a rest B hPB hXa => cnot_row M b X Y Z s hbX hbY hbZ hbs hXY hXZ hXs hYs hZs
      L1 L1a L1b L2 L3 L4 L0 get set hgs hss hsg c t hct s0 hM1 hMa hMb hM2 hM3 hM4 cc r hr a rest B Q
      hPB.1 hXa hPB.2.1 hPB.2.2)
    ((List.ofFn T).reverse) B ⟨hb, hs, hZ⟩ (by rw [hX, encodeTableau_rev])
  refine (key.of_eq ?_).mono ?_
  · congr 3
    rw [encodeTableau_eq]
    simp [List.map_ofFn, Function.comp_def]
  · simp

end CnotRow

end OCRS19TM

namespace OCRS19TM

section MeasRow

open QAlgorithms.Stabilizer

lemma foldl_xor_shift {α : Type} (f : α → Bool) (l : List α) (p b : Bool) :
    l.foldl (fun acc x => xor acc (f x)) (xor p b) = xor (l.foldl (fun acc x => xor acc (f x)) p) b := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [show xor (xor p b) (f a) = xor (xor p (f a)) b by
      generalize f a = d; cases p <;> cases b <;> cases d <;> rfl, ih]

lemma foldl_xor_rev {α : Type} (f : α → Bool) (l : List α) (p : Bool) :
    l.reverse.foldl (fun acc x => xor acc (f x)) p = l.foldl (fun acc x => xor acc (f x)) p := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_xor_shift]

/-- anticommutation-parity wire: the mask column is the measured Pauli; data row copied unchanged -/
def antiW : Bool → Bool → Bool → Pauli → Bool × Pauli :=
  fun s m1 m2 a => (xor s (sympB a (pauliOfBits m1 m2)), a)

def antiF (p : Pauli × Bool × Bool) : Bool := sympB p.1 (pauliOfBits p.2.1 p.2.2)

lemma wrun_anti (s : Bool) (l : List (Pauli × Bool × Bool)) :
    wrun antiW s l = (l.foldl (fun acc x => xor acc (antiF x)) s, l.map Prod.fst) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih => obtain ⟨a, m1, m2⟩ := p; simp [wrun, antiW, antiF, ih]

/-- mask of a measured Pauli string: same layout as a reversed row's ops part -/
def mmask {n : ℕ} (Mp : Fin n → Pauli) : List Bool := (List.ofFn fun q => encPauli (Mp q)).flatten.reverse

def antiLR {n : ℕ} (Mp : Fin n → Pauli) (P : PauliString n) : List (Pauli × Bool × Bool) :=
  (List.ofFn fun q => (P.ops q, xbit (Mp q), zbit (Mp q))).reverse

lemma mmask_eq {n : ℕ} (Mp : Fin n → Pauli) (P : PauliString n) :
    mmask Mp = (antiLR Mp P).flatMap fun p => [p.2.2, p.2.1] := by
  rw [mmask, rev_flatten_enc]
  simp [antiLR, List.flatMap, List.map_reverse, List.map_ofFn, Function.comp_def]

lemma encA_eq {n : ℕ} (Mp : Fin n → Pauli) (P : PauliString n) :
    (List.ofFn fun q => encPauli (P.ops q)).flatten.reverse =
      (antiLR Mp P).flatMap fun p => [zbit p.1, xbit p.1] := by
  rw [rev_flatten_enc]
  simp [antiLR, List.flatMap, List.map_reverse, List.map_ofFn, Function.comp_def]

lemma mmask_length {n : ℕ} (Mp : Fin n → Pauli) : (mmask Mp).length = 2 * n := by
  rw [mmask, List.length_reverse]; exact opsEnc_length ⟨0, Mp⟩

/-- symplectic anticommutation bit of a row against the measured Pauli -/
def antiK {n : ℕ} (P : PauliString n) (Mp : Fin n → Pauli) : Bool :=
  decide (Odd (Finset.univ.filter fun q => sympB (P.ops q) (Mp q) = true).card)

theorem ctlOut_anti {n : ℕ} (Mp : Fin n → Pauli) (P : PauliString n) (s : Bool) (rest : List Bool) :
    ctlOut (cwδ antiW) (co1 antiW) (co2 antiW) (s, none) (mmask Mp)
        ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++ rest) =
      ((xor s (antiK P Mp), none), (List.ofFn fun q => encPauli (P.ops q)).flatten.reverse) := by
  conv_lhs => rw [mmask_eq Mp P, encA_eq Mp P, ctlOut_w, wrun_anti]
  rw [rev_flatten_enc, antiLR, foldl_xor_rev antiF, foldl_xor_ofFn]
  simp [List.map_reverse, List.map_ofFn, Function.comp_def, pauliOfBits_bits, antiK, antiF]

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- TM level: scan one row against the measured Pauli; row copied to `Y`, parity xor-ed into the state -/
theorem anti_row {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Y s : Kb)
    (hbX : b ≠ X) (hbY : b ≠ Y) (hbs : b ≠ s) (hXY : X ≠ Y) (hXs : X ≠ s) (hYs : Y ≠ s)
    (L1 L2 L3 L0 : Λ) (get : ρ → Bool × Option (Bool × Bool))
    (set : ρ → Bool × Option (Bool × Bool) → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r) (Mp : Fin n → Pauli)
    (hM1 : M L1 = ctlStmt b X Y s L1 L2 (fun r x y => set r (cwδ antiW (get r) x y))
      (fun r x y => co1 antiW (get r) x y) (fun r x y => co2 antiW (get r) x y))
    (hM2 : M L2 = p2Stmt X Y L3 (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r))
    (hM3 : M L3 = mvStmt s b L3 L0)
    (c : Bool) (r : ρ) (p : Bool) (hr : get r = (p, none)) (P : PauliString n) (rest : List Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = mmask Mp) (hX : B X = (encPS P).reverse ++ rest) (hs : B s = []) :
    Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
      ⟨some L0, ((none, none, c), set r (xor p (antiK P Mp), none)),
        mk (Function.update (Function.update B X rest) Y (encPS P ++ B Y)) Q⟩
      (2 * (mmask Mp).length + 3) := by
  have hctl := ctlOut_lens get set hgs hss hsg (cwδ antiW) (co1 antiW) (co2 antiW)
    (mmask Mp) ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++
      (decide (P.phase.val % 2 = 1) :: decide (2 ≤ P.phase.val) :: rest)) r
  rw [hr, ctlOut_anti] at hctl
  have h := rowpass_run M b X Y s hbX hbY hbs hXY hXs hYs L1 L2 L3 L0 _ _ _
    (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r) hM1 hM2 hM3 c r _ _ _ _ _ _ _ B Q hb
    (by rw [hX, encPS_rev]; simp) hs
    (by rw [List.length_reverse, opsEnc_length, mmask_length]) hctl
  refine h.of_eq ?_
  simp only [Option.getD_some, List.reverse_reverse, encPS, encPhase, List.cons_append, List.nil_append]

end MeasRow

section LoopS

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}
variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

/-- push a bit computed from the state, then update the state -/
def emitStmt (A : Kb) (L : Λ) (e : ρ → Bool) (δ : ρ → ρ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.push (Sum.inl A) (fun v => e v.2)
    (TM2.Stmt.load (fun v => (v.1, δ v.2)) (TM2.Stmt.goto fun _ => L))

lemma emit_step (A : Kb) (L L' : Λ) (e : ρ → Bool) (δ : ρ → ρ) (hM : M L' = emitStmt A L e δ)
    (c : Bool) (r : ρ) (B : Kb → List Bool) (Q : ∀ r, List (G r)) :
    Reach M ⟨some L', ((none, none, c), r), mk B Q⟩
      ⟨some L, ((none, none, c), δ r), mk (Function.update B A (e r :: B A)) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, emitStmt, TM2.stepAux, mk_inl, update_mk]

/-- outputs of a state-carrying row loop (last processed row on top) -/
def loopOut {α : Type} (nxt : ρ → α → ρ) (out : ρ → α → List Bool) : ρ → List α → List Bool
  | _, [] => []
  | r, a :: L => loopOut nxt out (nxt r a) L ++ out r a

/-- generic row loop with a state carried across rows -/
theorem rows_loopS {α : Type} (X Y : Kb) (hXY : X ≠ Y) (L0 L1 E : Λ) (hM : M L0 = testStmt X L1 E)
    (c : Bool) (Q : ∀ r, List (G r)) (Pinv : (Kb → List Bool) → Prop)
    (hP : ∀ B rest Yv, Pinv B → Pinv (Function.update (Function.update B X rest) Y Yv))
    (enc : α → List Bool) (out : ρ → α → List Bool) (nxt : ρ → α → ρ) (hne : ∀ a, enc a ≠ [])
    (t : ℕ)
    (hbody : ∀ a r rest B, Pinv B → B X = (enc a).reverse ++ rest →
      Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
        ⟨some L0, ((none, none, c), nxt r a),
          mk (Function.update (Function.update B X rest) Y (out r a ++ B Y)) Q⟩ t) :
    ∀ (L : List α) (r : ρ) (B : Kb → List Bool), Pinv B →
      B X = (L.map fun a => (enc a).reverse).flatten →
      Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), L.foldl nxt r),
          mk (Function.update (Function.update B X []) Y (loopOut nxt out r L ++ B Y)) Q⟩
        (L.length * (t + 1) + 1) := by
  intro L
  induction L with
  | nil =>
    intro r B _ hX
    refine ((test_none M X L0 L1 E hM r c Q B (by simpa using hX)).of_eq ?_).mono (by simp)
    congr 2
    funext k; simp only [Function.update_apply, loopOut]; split_ifs <;> simp_all
  | cons a L ih =>
    intro r B hPB hX
    obtain ⟨x, A, hxA⟩ : ∃ x A, (enc a).reverse = x :: A := by
      cases h : (enc a).reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp h) (hne a)
      | cons x A => exact ⟨x, A, rfl⟩
    have h1 := test_some M X L0 L1 E hM r c Q B x (A ++ (L.map fun a => (enc a).reverse).flatten)
      (by rw [hX]; simp [hxA])
    have h2 := hbody a r ((L.map fun a => (enc a).reverse).flatten) B hPB (by rw [hX]; simp)
    have h3 := ih (nxt r a) _ (hP B ((L.map fun a => (enc a).reverse).flatten) (out r a ++ B Y) hPB)
      (by simp [Function.update_apply, hXY])
    refine ((h1.trans (h2.trans h3)).of_eq ?_).mono ?_
    · congr 2
      funext k; simp only [Function.update_apply]
      split_ifs <;> simp_all [List.reverse_cons, List.map_append, List.flatten_append, loopOut]
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

end LoopS

end OCRS19TM

namespace OCRS19TM

section LoopG

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}
variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

/-- stacks after a general row loop -/
def loopStk {α : Type} (nxt : ρ → α → ρ) (stk : ρ → α → (Kb → List Bool) → Kb → List Bool) :
    ρ → List α → (Kb → List Bool) → Kb → List Bool
  | _, [], B => B
  | r, a :: L, B => loopStk nxt stk (nxt r a) L (stk r a B)

/-- most general row loop: a state and arbitrary stack effects per row; only `X` must shrink by the row -/
theorem rows_loopG {α : Type} (X : Kb) (L0 L1 E : Λ) (hM : M L0 = testStmt X L1 E)
    (c : Bool) (Q : ∀ r, List (G r)) (Pinv : ρ → (Kb → List Bool) → Prop)
    (enc : α → List Bool) (hne : ∀ a, enc a ≠ []) (nxt : ρ → α → ρ)
    (stk : ρ → α → (Kb → List Bool) → Kb → List Bool) (t : ℕ)
    (hbody : ∀ a r rest B, Pinv r B → B X = (enc a).reverse ++ rest →
      stk r a B X = rest ∧ Pinv (nxt r a) (stk r a B) ∧
      Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
        ⟨some L0, ((none, none, c), nxt r a), mk (stk r a B) Q⟩ t) :
    ∀ (L : List α) (r : ρ) (B : Kb → List Bool), Pinv r B →
      B X = (L.map fun a => (enc a).reverse).flatten →
      Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), L.foldl nxt r), mk (loopStk nxt stk r L B) Q⟩
        (L.length * (t + 1) + 1) := by
  intro L
  induction L with
  | nil =>
    intro r B _ hX
    exact ((test_none M X L0 L1 E hM r c Q B (by simpa using hX))).mono (by simp)
  | cons a L ih =>
    intro r B hPB hX
    obtain ⟨x, A, hxA⟩ : ∃ x A, (enc a).reverse = x :: A := by
      cases h : (enc a).reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp h) (hne a)
      | cons x A => exact ⟨x, A, rfl⟩
    have h1 := test_some M X L0 L1 E hM r c Q B x (A ++ (L.map fun a => (enc a).reverse).flatten)
      (by rw [hX]; simp [hxA])
    obtain ⟨hX', hP', h2⟩ := hbody a r ((L.map fun a => (enc a).reverse).flatten) B hPB
      (by rw [hX]; simp)
    have h3 := ih (nxt r a) (stk r a B) hP' hX'
    refine (h1.trans (h2.trans h3)).mono ?_
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

end LoopG

end OCRS19TM

namespace OCRS19TM

section MulRow

open QAlgorithms.Stabilizer

/-- row-multiply wire: mask column = the right factor's Pauli; ZMod 4 phase accumulator -/
def mulW : ZMod 4 → Bool → Bool → Pauli → ZMod 4 × Pauli :=
  fun d m1 m2 a => (d + (Pauli.mul a (pauliOfBits m1 m2)).1, (Pauli.mul a (pauliOfBits m1 m2)).2)

lemma wrun_mul (d : ZMod 4) (l : List (Pauli × Bool × Bool)) :
    wrun mulW d l = (d + (l.map fun p => (Pauli.mul p.1 (pauliOfBits p.2.1 p.2.2)).1).sum,
      l.map fun p => (Pauli.mul p.1 (pauliOfBits p.2.1 p.2.2)).2) := by
  induction l generalizing d with
  | nil => simp [wrun]
  | cons p l ih => obtain ⟨a, m1, m2⟩ := p; simp [wrun, mulW, ih, add_assoc]

theorem ctlOut_mul {n : ℕ} (P Q : PauliString n) (d : ZMod 4) (rest : List Bool) :
    ctlOut (cwδ mulW) (co1 mulW) (co2 mulW) (d, none) (mmask Q.ops)
        ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++ rest) =
      ((d + ∑ q : Fin n, (Pauli.mul (P.ops q) (Q.ops q)).1, none),
        (List.ofFn fun q => encPauli ((P.mul Q).ops q)).flatten.reverse) := by
  conv_lhs => rw [mmask_eq Q.ops P, encA_eq Q.ops P, ctlOut_w, wrun_mul]
  rw [rev_flatten_enc]
  simp [antiLR, List.map_reverse, List.map_ofFn, Function.comp_def, pauliOfBits_bits, List.sum_reverse,
    List.sum_ofFn, PauliString.mul]

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- TM level: row `P` (reversed on `X`) times the mask row `Qr` (ops on `b`, phase preloaded in the state) -/
theorem mul_row {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b X Y s : Kb)
    (hbX : b ≠ X) (hbY : b ≠ Y) (hbs : b ≠ s) (hXY : X ≠ Y) (hXs : X ≠ s) (hYs : Y ≠ s)
    (L1 L2 L3 L0 : Λ) (get : ρ → ZMod 4 × Option (Bool × Bool))
    (set : ρ → ZMod 4 × Option (Bool × Bool) → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r)
    (hM1 : M L1 = ctlStmt b X Y s L1 L2 (fun r x y => set r (cwδ mulW (get r) x y))
      (fun r x y => co1 mulW (get r) x y) (fun r x y => co2 mulW (get r) x y))
    (hM2 : M L2 = p2Stmt X Y L3 (g1p2 get) (fun r _ _ => set r (0, none)))
    (hM3 : M L3 = mvStmt s b L3 L0)
    (c : Bool) (r : ρ) (P Qr : PauliString n) (hr : get r = (Qr.phase, none)) (rest : List Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (hb : B b = mmask Qr.ops) (hX : B X = (encPS P).reverse ++ rest) (hs : B s = []) :
    Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
      ⟨some L0, ((none, none, c), set r (0, none)),
        mk (Function.update (Function.update B X rest) Y (encPS (P.mul Qr) ++ B Y)) Q⟩
      (2 * (mmask Qr.ops).length + 3) := by
  have hctl := ctlOut_lens get set hgs hss hsg (cwδ mulW) (co1 mulW) (co2 mulW)
    (mmask Qr.ops) ((List.ofFn fun q => encPauli (P.ops q)).flatten.reverse ++
      (decide (P.phase.val % 2 = 1) :: decide (2 ≤ P.phase.val) :: rest)) r
  rw [hr, ctlOut_mul] at hctl
  have h := rowpass_run M b X Y s hbX hbY hbs hXY hXs hYs L1 L2 L3 L0 _ _ _ (g1p2 get)
    (fun r _ _ => set r (0, none)) hM1 hM2 hM3 c r _ _ _ _ _ _ _ B Q hb
    (by rw [hX, encPS_rev]; simp) hs
    (by rw [List.length_reverse, opsEnc_length, mmask_length]) hctl
  refine h.of_eq ?_
  simp only [hss, hgs, g1p2, Option.getD_some, phOf_enc, List.reverse_reverse, encPS,
    encPhase, List.cons_append, List.nil_append, PauliString.mul, add_assoc]

end MulRow

end OCRS19TM

namespace OCRS19TM

section MeasBody

open QAlgorithms.Stabilizer

/-- chaining with a fixed total budget -/
lemma Reach.cons {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} {M : Λ → TM2.Stmt Γ Λ σ}
    {c c' c'' : TM2.Cfg Γ Λ σ} {t T : ℕ} (h : Reach M c c' t) (h' : Reach M c' c'' (T - t))
    (ht : t ≤ T) : Reach M c c'' T := by
  have := h.trans h'
  rwa [Nat.add_sub_cancel' ht] at this

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}
variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

/-- pop one bit of stack `A` into the state -/
def popStStmt (A : Kb) (L : Λ) (δ : ρ → Bool → ρ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl A) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), δ v.2 (v.1.1.getD false)))
      (TM2.Stmt.goto fun _ => L))

lemma popSt_step (A : Kb) (L L' : Λ) (δ : ρ → Bool → ρ) (hM : M L' = popStStmt A L δ)
    (c : Bool) (r : ρ) (B : Kb → List Bool) (Q : ∀ r, List (G r)) (x : Bool) (rest : List Bool)
    (hA : B A = x :: rest) :
    Reach M ⟨some L', ((none, none, c), r), mk B Q⟩
      ⟨some L, ((none, none, c), δ r x), mk (Function.update B A rest) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, popStStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
    Option.getD_some, update_mk]

/-- three-way dispatch on the state -/
def dispStmt (c1 c2 : ρ → Bool) (f1 f2 f3 : ρ → ρ) (L1 L2 L3 : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.branch (fun v => c1 v.2)
    (TM2.Stmt.branch (fun v => c2 v.2)
      (TM2.Stmt.load (fun v => (v.1, f1 v.2)) (TM2.Stmt.goto fun _ => L1))
      (TM2.Stmt.load (fun v => (v.1, f2 v.2)) (TM2.Stmt.goto fun _ => L2)))
    (TM2.Stmt.load (fun v => (v.1, f3 v.2)) (TM2.Stmt.goto fun _ => L3))

lemma disp_step1 (c1 c2 : ρ → Bool) (f1 f2 f3 : ρ → ρ) (L1 L2 L3 L' : Λ)
    (hM : M L' = dispStmt c1 c2 f1 f2 f3 L1 L2 L3) (c : Bool) (r : ρ)
    (S : ∀ k : Kb ⊕ R, List (BΓ Kb G k)) (h1 : c1 r = true) (h2 : c2 r = true) :
    Reach M ⟨some L', ((none, none, c), r), S⟩ ⟨some L1, ((none, none, c), f1 r), S⟩ 1 := by
  apply Reach.single; simp [TM2.step, hM, dispStmt, TM2.stepAux, h1, h2]

lemma disp_step2 (c1 c2 : ρ → Bool) (f1 f2 f3 : ρ → ρ) (L1 L2 L3 L' : Λ)
    (hM : M L' = dispStmt c1 c2 f1 f2 f3 L1 L2 L3) (c : Bool) (r : ρ)
    (S : ∀ k : Kb ⊕ R, List (BΓ Kb G k)) (h1 : c1 r = true) (h2 : c2 r = false) :
    Reach M ⟨some L', ((none, none, c), r), S⟩ ⟨some L2, ((none, none, c), f2 r), S⟩ 1 := by
  apply Reach.single; simp [TM2.step, hM, dispStmt, TM2.stepAux, h1, h2]

lemma disp_step3 (c1 c2 : ρ → Bool) (f1 f2 f3 : ρ → ρ) (L1 L2 L3 L' : Λ)
    (hM : M L' = dispStmt c1 c2 f1 f2 f3 L1 L2 L3) (c : Bool) (r : ρ)
    (S : ∀ k : Kb ⊕ R, List (BΓ Kb G k)) (h1 : c1 r = false) :
    Reach M ⟨some L', ((none, none, c), r), S⟩ ⟨some L3, ((none, none, c), f3 r), S⟩ 1 := by
  apply Reach.single; simp [TM2.step, hM, dispStmt, TM2.stepAux, h1]

end MeasBody

section MeasRowFull

open QAlgorithms.Stabilizer

/-- concrete scan state for the random-measurement pass -/
structure MS (ε : Type) where
  an : Bool × Option (Bool × Bool)
  mu : ZMod 4 × Option (Bool × Bool)
  fd : Bool
  cp : ZMod 4
  cb : Bool
  ext : ε

variable {ε : Type}

def MS.setAn (r : MS ε) (t : Bool × Option (Bool × Bool)) : MS ε := { r with an := t }
def MS.setMu (r : MS ε) (t : ZMod 4 × Option (Bool × Bool)) : MS ε := { r with mu := t }
def msMul (r : MS ε) : MS ε := { r with an := (false, none), mu := (r.cp, none) }
def msP (r : MS ε) : MS ε := { r with an := (false, none), fd := true }
def msCopy (r : MS ε) : MS ε := r.setAn (false, none)

lemma encPS_cons {n : ℕ} (P : PauliString n) :
    encPS P = decide (2 ≤ P.phase.val) :: decide (P.phase.val % 2 = 1) ::
      (List.ofFn fun q => encPauli (P.ops q)).flatten := rfl

lemma encPS_meas {n : ℕ} (Mp : Fin n → Pauli) (cb : Bool) :
    encPS (⟨if cb then 2 else 0, Mp⟩ : PauliString n) = cb :: false :: (mmask Mp).reverse := by
  cases cb <;> simp only [encPS, encPhase, mmask, List.reverse_reverse] <;> rfl

lemma encPS_length {n : ℕ} (P : PauliString n) : (encPS P).length = 2 * n + 2 := by
  rw [encPS_cons]; simp only [List.length_cons, opsEnc_length]

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ : Type}

/-- the labels of the random-measurement row body; stacks: 0 mask(M), 1 input rows, 2 output rows,
3 Z, 4 W, 5 captured row mask, 6 temp, 7 selection bits -/
structure MeasProg (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb) (L : Fin 20 → Λ)
    (E : Λ) : Prop where
  h0 : M (L 0) = ctlStmt (K 0) (K 1) (K 3) (K 6) (L 0) (L 1)
    (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y))
    (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y)
  h1 : M (L 1) = p2Stmt (K 1) (K 3) (L 2) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r)
  h2 : M (L 2) = mvStmt (K 6) (K 0) (L 2) (L 3)
  h3 : M (L 3) = dispStmt (fun r : MS ε => r.an.1) (fun r => r.fd) msMul msP msCopy (L 7) (L 12) (L 4)
  h4 : M (L 4) = mvStmt (K 3) (K 4) (L 4) (L 5)
  h5 : M (L 5) = mvStmt (K 4) (K 2) (L 5) (L 6)
  h6 : M (L 6) = emitStmt (K 7) E (fun _ => false) id
  h7 : M (L 7) = mvStmt (K 3) (K 4) (L 7) (L 8)
  h8 : M (L 8) = ctlStmt (K 5) (K 4) (K 2) (K 6) (L 8) (L 9)
    (fun r x y => MS.setMu r (cwδ mulW (MS.mu r) x y))
    (fun r x y => co1 mulW (MS.mu r) x y) (fun r x y => co2 mulW (MS.mu r) x y)
  h9 : M (L 9) = p2Stmt (K 4) (K 2) (L 10) (g1p2 MS.mu) (fun r _ _ => MS.setMu r (0, none))
  h10 : M (L 10) = mvStmt (K 6) (K 5) (L 10) (L 11)
  h11 : M (L 11) = emitStmt (K 7) E (fun _ => false) id
  h12 : M (L 12) = popStStmt (K 3) (L 13) (fun r x => { r with cp := if x then 2 else 0 })
  h13 : M (L 13) = popStStmt (K 3) (L 14) (fun r x => { r with cp := r.cp + if x then 1 else 0 })
  h14 : M (L 14) = mvStmt (K 3) (K 5) (L 14) (L 15)
  h15 : M (L 15) = dupStmt (K 0) (K 2) (K 6) (L 15) (L 16)
  h16 : M (L 16) = mvStmt (K 6) (K 0) (L 16) (L 17)
  h17 : M (L 17) = emitStmt (K 2) (L 18) (fun _ => false) id
  h18 : M (L 18) = emitStmt (K 2) (L 19) (fun r => r.cb) id
  h19 : M (L 19) = emitStmt (K 7) E (fun _ => true) id

/-- state after one row (row `a.1`, captured row `a.2`) -/
def mNxt {n : ℕ} (Mp : Fin n → Pauli) (r : MS ε) (a : PauliString n × PauliString n) : MS ε :=
  if antiK a.1 Mp then (if r.fd then r.setMu (0, none) else { r with fd := true, cp := a.1.phase })
  else r

/-- stacks after one row -/
def mStk {n : ℕ} (K : Fin 8 → Kb) (Mp : Fin n → Pauli) (r : MS ε) (a : PauliString n × PauliString n)
    (B : Kb → List Bool) : Kb → List Bool :=
  let B1 := Function.update B (K 1) ((B (K 1)).drop (encPS a.1).length)
  if antiK a.1 Mp then
    (if r.fd then
      Function.update (Function.update B1 (K 2) (encPS (a.1.mul a.2) ++ B (K 2))) (K 7) (false :: B (K 7))
    else
      Function.update (Function.update (Function.update B1 (K 2)
        (encPS (⟨if r.cb then 2 else 0, Mp⟩ : PauliString n) ++ B (K 2))) (K 5) (mmask a.1.ops))
        (K 7) (true :: B (K 7)))
  else Function.update (Function.update B1 (K 2) (encPS a.1 ++ B (K 2))) (K 7) (false :: B (K 7))

theorem meas_copy {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (E : Λ) (hP : MeasProg M K L E)
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (a : PauliString n × PauliString n)
    (r : MS ε) (B : Kb → List Bool) (rest : List Bool)
    (hr : r.an = (false, none)) (hb : B (K 0) = mmask Mp) (hX : B (K 1) = (encPS a.1).reverse ++ rest)
    (hZ : B (K 3) = []) (hW : B (K 4) = []) (hT : B (K 6) = []) (hA : antiK a.1 Mp = false) :
    Reach M ⟨some (L 0), ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), mNxt Mp r a), mk (mStk K Mp r a B) Q⟩ (10 * n + 12) := by
  have hne : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h => hK.ne h
  have hlenM := mmask_length Mp
  have hlenP := encPS_length a.1
  have hdrop : (B (K 1)).drop (encPS a.1).length = rest := by
    rw [hX]; exact List.drop_left' (List.length_reverse)
  refine Reach.cons (anti_row M (K 0) (K 1) (K 3) (K 6) (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 0 6 (by decide)) (hne 1 3 (by decide)) (hne 1 6 (by decide)) (hne 3 6 (by decide))
    (L 0) (L 1) (L 2) (L 3) MS.an MS.setAn (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Mp
    hP.h0 hP.h1 hP.h2 c r false hr a.1 rest B Q hb hX hT) ?_ ?b1
  refine Reach.cons (disp_step3 M _ _ _ _ _ (L 7) (L 12) (L 4) (L 3) hP.h3 c _ _
    (by simp [MS.setAn, hA])) ?_ ?b2
  refine Reach.cons (mv_run M (K 3) (K 4) (hne 3 4 (by decide)) (L 4) (L 5) hP.h4 _ c Q
    (encPS a.1) _ (by simp [hZ])) ?_ ?b3
  refine Reach.cons (mv_run M (K 4) (K 2) (hne 4 2 (by decide)) (L 5) (L 6) hP.h5 _ c Q
    (encPS a.1).reverse _ (by simp [Function.update_apply, hK.eq_iff, hW])) ?_ ?b4
  refine Reach.cons (emit_step M (K 7) E (L 6) _ _ hP.h6 c _ _ Q) ?_ ?b5
  refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
  · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · simp only [mNxt, hA, msCopy, id]
      obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
      simp only at hr; subst hr; rfl
    · congr 1
      funext k
      simp only [mStk, hA, hdrop, Bool.false_eq_true, if_false, Function.update_apply,
        List.reverse_reverse]
      split_ifs <;> simp_all [hK.eq_iff]
  all_goals simp only [hlenM, hlenP, List.length_reverse]; omega

theorem meas_mul {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (E : Λ) (hP : MeasProg M K L E)
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (a : PauliString n × PauliString n)
    (r : MS ε) (B : Kb → List Bool) (rest : List Bool)
    (hr : r.an = (false, none)) (hb : B (K 0) = mmask Mp) (hX : B (K 1) = (encPS a.1).reverse ++ rest)
    (hZ : B (K 3) = []) (hW : B (K 4) = []) (hT : B (K 6) = []) (hA : antiK a.1 Mp = true)
    (hf : r.fd = true) (hcp : r.cp = a.2.phase) (hcap : B (K 5) = mmask a.2.ops) :
    Reach M ⟨some (L 0), ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), mNxt Mp r a), mk (mStk K Mp r a B) Q⟩ (10 * n + 12) := by
  have hne : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h => hK.ne h
  have hlenM := mmask_length Mp
  have hlenM2 := mmask_length a.2.ops
  have hlenP := encPS_length a.1
  have hdrop : (B (K 1)).drop (encPS a.1).length = rest := by
    rw [hX]; exact List.drop_left' (List.length_reverse)
  refine Reach.cons (anti_row M (K 0) (K 1) (K 3) (K 6) (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 0 6 (by decide)) (hne 1 3 (by decide)) (hne 1 6 (by decide)) (hne 3 6 (by decide))
    (L 0) (L 1) (L 2) (L 3) MS.an MS.setAn (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Mp
    hP.h0 hP.h1 hP.h2 c r false hr a.1 rest B Q hb hX hT) ?_ ?b1
  refine Reach.cons (disp_step1 M _ _ _ _ _ (L 7) (L 12) (L 4) (L 3) hP.h3 c _ _
    (by simp [MS.setAn, hA]) (by simp [MS.setAn, hf])) ?_ ?b2
  refine Reach.cons (mv_run M (K 3) (K 4) (hne 3 4 (by decide)) (L 7) (L 8) hP.h7 _ c Q
    (encPS a.1) _ (by simp [hZ])) ?_ ?b3
  refine Reach.cons (mul_row M (K 5) (K 4) (K 2) (K 6) (hne 5 4 (by decide)) (hne 5 2 (by decide))
    (hne 5 6 (by decide)) (hne 4 2 (by decide)) (hne 4 6 (by decide)) (hne 2 6 (by decide))
    (L 8) (L 9) (L 10) (L 11) MS.mu MS.setMu (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    hP.h8 hP.h9 hP.h10 c _ a.1 a.2 (by simp [msMul, MS.setAn, hcp]) [] _ Q
    (by simp [Function.update_apply, hK.eq_iff, hcap])
    (by simp [Function.update_apply, hK.eq_iff, hW])
    (by simp [Function.update_apply, hK.eq_iff, hT])) ?_ ?b4
  refine Reach.cons (emit_step M (K 7) E (L 11) _ _ hP.h11 c _ _ Q) ?_ ?b5
  refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
  · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · simp only [mNxt, hA, hf, if_true, msMul, id]
      obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
      simp only at hr; subst hr; rfl
    · congr 1
      funext k
      simp only [mStk, hA, hf, hdrop, if_true, Function.update_apply]
      split_ifs <;> simp_all [hK.eq_iff]
  all_goals simp only [hlenM, hlenM2, hlenP, List.length_reverse]; omega

theorem meas_p {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (E : Λ) (hP : MeasProg M K L E)
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (a : PauliString n × PauliString n)
    (r : MS ε) (B : Kb → List Bool) (rest : List Bool)
    (hr : r.an = (false, none)) (hb : B (K 0) = mmask Mp) (hX : B (K 1) = (encPS a.1).reverse ++ rest)
    (hZ : B (K 3) = []) (hT : B (K 6) = []) (hA : antiK a.1 Mp = true)
    (hf : r.fd = false) (hcap : B (K 5) = []) :
    Reach M ⟨some (L 0), ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), mNxt Mp r a), mk (mStk K Mp r a B) Q⟩ (10 * n + 12) := by
  have hne : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h => hK.ne h
  have hlenM := mmask_length Mp
  have hlenP := encPS_length a.1
  have hlenO : ((List.ofFn fun q => encPauli (a.1.ops q)).flatten).length = 2 * n := opsEnc_length a.1
  have hdrop : (B (K 1)).drop (encPS a.1).length = rest := by
    rw [hX]; exact List.drop_left' (List.length_reverse)
  refine Reach.cons (anti_row M (K 0) (K 1) (K 3) (K 6) (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 0 6 (by decide)) (hne 1 3 (by decide)) (hne 1 6 (by decide)) (hne 3 6 (by decide))
    (L 0) (L 1) (L 2) (L 3) MS.an MS.setAn (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Mp
    hP.h0 hP.h1 hP.h2 c r false hr a.1 rest B Q hb hX hT) ?_ ?b1
  refine Reach.cons (disp_step2 M _ _ _ _ _ (L 7) (L 12) (L 4) (L 3) hP.h3 c _ _
    (by simp [MS.setAn, hA]) (by simp [MS.setAn, hf])) ?_ ?b2
  refine Reach.cons (popSt_step M (K 3) (L 13) (L 12) _ hP.h12 c _ _ Q (decide (2 ≤ a.1.phase.val))
    (decide (a.1.phase.val % 2 = 1) :: (List.ofFn fun q => encPauli (a.1.ops q)).flatten)
    (by simp [hZ, encPS_cons])) ?_ ?b3
  refine Reach.cons (popSt_step M (K 3) (L 14) (L 13) _ hP.h13 c _ _ Q (decide (a.1.phase.val % 2 = 1))
    (List.ofFn fun q => encPauli (a.1.ops q)).flatten (by simp)) ?_ ?b4
  refine Reach.cons (mv_run M (K 3) (K 5) (hne 3 5 (by decide)) (L 14) (L 15) hP.h14 _ c Q
    (List.ofFn fun q => encPauli (a.1.ops q)).flatten _ (by simp)) ?_ ?b5
  refine Reach.cons (dup_run M (K 0) (K 2) (K 6) (hne 0 2 (by decide)) (hne 0 6 (by decide))
    (hne 2 6 (by decide)) (L 15) (L 16) hP.h15 _ c Q (mmask Mp) _
    (by simp [Function.update_apply, hK.eq_iff, hb])) ?_ ?b6
  refine Reach.cons (mv_run M (K 6) (K 0) (hne 6 0 (by decide)) (L 16) (L 17) hP.h16 _ c Q
    (mmask Mp).reverse _ (by simp [Function.update_apply, hK.eq_iff, hT])) ?_ ?b7
  refine Reach.cons (emit_step M (K 2) (L 18) (L 17) _ _ hP.h17 c _ _ Q) ?_ ?b8
  refine Reach.cons (emit_step M (K 2) (L 19) (L 18) _ _ hP.h18 c _ _ Q) ?_ ?b9
  refine Reach.cons (emit_step M (K 7) E (L 19) _ _ hP.h19 c _ _ Q) ?_ ?b10
  refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
  · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · have hph : (if decide (2 ≤ a.1.phase.val) = true then (2 : ZMod 4) else 0) +
          (if decide (a.1.phase.val % 2 = 1) = true then 1 else 0) = a.1.phase := phOf_enc a.1.phase
      simp only [mNxt, hA, hf, if_true, Bool.false_eq_true, if_false, msP, id]
      obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
      simp only at hr hf; subst hr hf
      simp only [MS.setAn, MS.mk.injEq, true_and, and_true]
      exact hph
    · congr 1
      funext k
      simp only [mStk, hA, hf, hdrop, if_true, Bool.false_eq_true, if_false, Function.update_apply,
        encPS_meas, id]
      by_cases h7 : k = K 7
      · subst h7; simp [hK.eq_iff]
      by_cases h5 : k = K 5
      · subst h5; simp [hK.eq_iff, hcap, mmask]
      by_cases h2 : k = K 2
      · subst h2; simp [hK.eq_iff, msP, MS.setAn]
      by_cases h1 : k = K 1
      · subst h1; simp [hK.eq_iff]
      by_cases h0 : k = K 0
      · subst h0; simp [hK.eq_iff, hb]
      by_cases h3 : k = K 3
      · subst h3; simp [hK.eq_iff, hZ]
      by_cases h6 : k = K 6
      · subst h6; simp [hK.eq_iff, hT]
      simp [h7, h5, h2, h1, h0, h3, h6]
  all_goals simp only [hlenM, hlenP, hlenO, List.length_reverse, List.length_cons,
    List.length_append, hZ, hT, List.length_nil]; omega

end MeasRowFull

end OCRS19TM

namespace OCRS19TM

section LoopG2

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}
variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

/-- a per-row side condition along a run -/
def runGood {α : Type} (nxt : ρ → α → ρ) (Good : ρ → α → Prop) : ρ → List α → Prop
  | _, [] => True
  | r, a :: L => Good r a ∧ runGood nxt Good (nxt r a) L

/-- `rows_loopG` with a state-dependent per-row side condition -/
theorem rows_loopG2 {α : Type} (X : Kb) (L0 L1 E : Λ) (hM : M L0 = testStmt X L1 E)
    (c : Bool) (Q : ∀ r, List (G r)) (Pinv : ρ → (Kb → List Bool) → Prop) (Good : ρ → α → Prop)
    (enc : α → List Bool) (hne : ∀ a, enc a ≠ []) (nxt : ρ → α → ρ)
    (stk : ρ → α → (Kb → List Bool) → Kb → List Bool) (t : ℕ)
    (hbody : ∀ a r rest B, Pinv r B → Good r a → B X = (enc a).reverse ++ rest →
      stk r a B X = rest ∧ Pinv (nxt r a) (stk r a B) ∧
      Reach M ⟨some L1, ((none, none, c), r), mk B Q⟩
        ⟨some L0, ((none, none, c), nxt r a), mk (stk r a B) Q⟩ t) :
    ∀ (L : List α) (r : ρ) (B : Kb → List Bool), Pinv r B → runGood nxt Good r L →
      B X = (L.map fun a => (enc a).reverse).flatten →
      Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), L.foldl nxt r), mk (loopStk nxt stk r L B) Q⟩
        (L.length * (t + 1) + 1) := by
  intro L
  induction L with
  | nil =>
    intro r B _ _ hX
    exact ((test_none M X L0 L1 E hM r c Q B (by simpa using hX))).mono (by simp)
  | cons a L ih =>
    intro r B hPB hG hX
    obtain ⟨x, A, hxA⟩ : ∃ x A, (enc a).reverse = x :: A := by
      cases h : (enc a).reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp h) (hne a)
      | cons x A => exact ⟨x, A, rfl⟩
    have h1 := test_some M X L0 L1 E hM r c Q B x (A ++ (L.map fun a => (enc a).reverse).flatten)
      (by rw [hX]; simp [hxA])
    obtain ⟨hX', hP', h2⟩ := hbody a r ((L.map fun a => (enc a).reverse).flatten) B hPB hG.1
      (by rw [hX]; simp)
    have h3 := ih (nxt r a) (stk r a B) hP' hG.2 hX'
    refine (h1.trans (h2.trans h3)).mono ?_
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

end LoopG2

section MeasPass

open QAlgorithms.Stabilizer

variable {ε : Type} {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ : Type}

/-- loop invariant of the random-measurement T pass (captured row `Tp`) -/
def mInv {n : ℕ} (K : Fin 8 → Kb) (Mp : Fin n → Pauli) (Tp : PauliString n) (r : MS ε)
    (B : Kb → List Bool) : Prop :=
  r.an = (false, none) ∧ B (K 0) = mmask Mp ∧ B (K 3) = [] ∧ B (K 4) = [] ∧ B (K 6) = [] ∧
    (r.fd = true → r.cp = Tp.phase ∧ B (K 5) = mmask Tp.ops) ∧ (r.fd = false → B (K 5) = [])

/-- the first anticommuting row met is the captured one -/
def mGood {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) (r : MS ε) (P : PauliString n) : Prop :=
  r.fd = false → antiK P Mp = true → P = Tp

theorem meas_body {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (E : Λ) (hP : MeasProg M K L E)
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (Tp P : PauliString n)
    (r : MS ε) (B : Kb → List Bool) (rest : List Bool) (hI : mInv K Mp Tp r B) (hG : mGood Mp Tp r P)
    (hX : B (K 1) = (encPS P).reverse ++ rest) :
    mStk K Mp r (P, Tp) B (K 1) = rest ∧ mInv K Mp Tp (mNxt Mp r (P, Tp)) (mStk K Mp r (P, Tp) B) ∧
      Reach M ⟨some (L 0), ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), mNxt Mp r (P, Tp)), mk (mStk K Mp r (P, Tp) B) Q⟩ (10 * n + 12) := by
  obtain ⟨han, hb, hZ, hW, hT, h1, h0⟩ := hI
  have hdrop : (B (K 1)).drop (encPS P).length = rest := by
    rw [hX]; exact List.drop_left' (List.length_reverse)
  refine ⟨?_, ?_, ?_⟩
  · unfold mStk; split_ifs <;> simp [Function.update_apply, hK.eq_iff, hdrop]
  · cases hA : antiK P Mp <;> cases hf : r.fd
    · simp only [mInv, mNxt, mStk, hA, hf, Bool.false_eq_true, if_false]
      simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT, h0 hf, hf]
    · simp only [mInv, mNxt, mStk, hA, hf, Bool.false_eq_true, if_false]
      simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT, h1 hf, hf]
    · have hPT := hG hf hA
      subst hPT
      simp only [mInv, mNxt, mStk, hA, hf, Bool.false_eq_true, if_false, if_true]
      simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT]
    · simp only [mInv, mNxt, mStk, hA, hf, if_true]
      simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT, h1 hf, hf, MS.setMu]
  · cases hA : antiK P Mp
    · exact meas_copy M K hK L E hP Mp c Q (P, Tp) r B rest han hb hX hZ hW hT hA
    · cases hf : r.fd
      · exact meas_p M K hK L E hP Mp c Q (P, Tp) r B rest han hb hX hZ hT hA hf (h0 hf)
      · exact meas_mul M K hK L E hP Mp c Q (P, Tp) r B rest han hb hX hZ hW hT hA hf (h1 hf).1
          (h1 hf).2

/-- the whole random-measurement T pass as one loop -/
theorem meas_pass {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (E E' : Λ) (hP : MeasProg M K L E)
    (hM0 : M E = testStmt (K 1) (L 0) E')
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r : MS ε) (B : Kb → List Bool), mInv K Mp Tp r B →
      runGood (fun r P => mNxt Mp r (P, Tp)) (mGood Mp Tp) r l →
      B (K 1) = (l.map fun a => (encPS a).reverse).flatten →
      Reach M ⟨some E, ((none, none, c), r), mk B Q⟩
        ⟨some E', ((none, none, c), l.foldl (fun r P => mNxt Mp r (P, Tp)) r),
          mk (loopStk (fun r P => mNxt Mp r (P, Tp)) (fun r P B => mStk K Mp r (P, Tp) B) r l B) Q⟩
        (l.length * (10 * n + 12 + 1) + 1) :=
  rows_loopG2 M (K 1) E (L 0) E' hM0 c Q (mInv K Mp Tp) (mGood Mp Tp) encPS encPS_ne _ _ (10 * n + 12)
    (fun a r rest B hI hG hX => meas_body M K hK L E hP Mp c Q Tp a r B rest hI hG hX)

/-- pure output row of the pass -/
def rowOut {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) (cb f : Bool) (P : PauliString n) :
    PauliString n :=
  if antiK P Mp then (if f then P.mul Tp else ⟨if cb then 2 else 0, Mp⟩) else P

/-- pure output stack of the pass (rows in processing order) -/
def passOut {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) (cb : Bool) :
    Bool → List (PauliString n) → List Bool
  | _, [] => []
  | f, P :: l => passOut Mp Tp cb (f || antiK P Mp) l ++ encPS (rowOut Mp Tp cb f P)

lemma mNxt_fd {n : ℕ} (Mp : Fin n → Pauli) (r : MS ε) (a : PauliString n × PauliString n) :
    (mNxt Mp r a).fd = (r.fd || antiK a.1 Mp) := by
  unfold mNxt; cases h : antiK a.1 Mp <;> cases hf : r.fd <;> simp [MS.setMu, hf]

lemma mNxt_cb {n : ℕ} (Mp : Fin n → Pauli) (r : MS ε) (a : PauliString n × PauliString n) :
    (mNxt Mp r a).cb = r.cb := by
  unfold mNxt; split_ifs <;> simp [MS.setMu]

lemma mStk_Y {n : ℕ} (K : Fin 8 → Kb) (hK : Function.Injective K) (Mp : Fin n → Pauli) (r : MS ε)
    (P Tp : PauliString n) (B : Kb → List Bool) :
    mStk K Mp r (P, Tp) B (K 2) = encPS (rowOut Mp Tp r.cb r.fd P) ++ B (K 2) := by
  unfold mStk rowOut; split_ifs <;> simp [Function.update_apply, hK.eq_iff]

lemma loop_Y {n : ℕ} (K : Fin 8 → Kb) (hK : Function.Injective K) (Mp : Fin n → Pauli)
    (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r : MS ε) (B : Kb → List Bool),
      loopStk (fun r P => mNxt Mp r (P, Tp)) (fun r P B => mStk K Mp r (P, Tp) B) r l B (K 2) =
        passOut Mp Tp r.cb r.fd l ++ B (K 2) := by
  intro l
  induction l with
  | nil => intro r B; simp [loopStk, passOut]
  | cons P l ih =>
    intro r B
    simp only [loopStk, passOut]
    rw [ih, mStk_Y K hK, mNxt_cb, mNxt_fd]
    simp

lemma loop_fd {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r : MS ε),
      (l.foldl (fun r P => mNxt Mp r (P, Tp)) r).fd = (r.fd || l.any fun P => antiK P Mp) := by
  intro l
  induction l with
  | nil => intro r; simp
  | cons P l ih => intro r; simp only [List.foldl_cons, List.any_cons]; rw [ih, mNxt_fd]; simp [Bool.or_assoc]

lemma passOut_ofFn {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) (cb : Bool) :
    ∀ {m : ℕ} (T : Fin m → PauliString n) (f : Bool),
      passOut Mp Tp cb f (List.ofFn T).reverse =
        (List.ofFn fun j => encPS (rowOut Mp Tp cb
          (f || decide (∃ k, j < k ∧ antiK (T k) Mp = true)) (T j))).flatten := by
  intro m
  induction m with
  | zero => intro T f; simp [passOut]
  | succ m ih =>
    intro T f
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, passOut]
    rw [ih (fun j => T j.castSucc)]
    rw [List.ofFn_succ' (fun j => encPS _), List.concat_eq_append, List.flatten_append]
    have hlast : ¬ ∃ k : Fin (m + 1), Fin.last m < k ∧ antiK (T k) Mp = true :=
      fun ⟨k, hk, _⟩ => absurd hk (not_lt.mpr (Fin.le_last k))
    have hb : ∀ j : Fin m, (f || antiK (T (Fin.last m)) Mp ||
        decide (∃ k, j < k ∧ antiK (T k.castSucc) Mp = true)) =
        (f || decide (∃ k, j.castSucc < k ∧ antiK (T k) Mp = true)) := by
      intro j
      cases f <;> cases hl : antiK (T (Fin.last m)) Mp <;>
        simp [Fin.exists_fin_succ', Fin.castSucc_lt_last, hl]
    simp only [hb]
    congr 1
    simp [hlast]

end MeasPass

end OCRS19TM

namespace OCRS19TM

section MeasClosed

open QAlgorithms.Stabilizer

variable {ε : Type}

lemma runGood_ofFn {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) :
    ∀ {m : ℕ} (T : Fin m → PauliString n) (r : MS ε),
      (∀ j, (r.fd || decide (∃ k, j < k ∧ antiK (T k) Mp = true)) = false →
        antiK (T j) Mp = true → T j = Tp) →
      runGood (fun r P => mNxt Mp r (P, Tp)) (mGood Mp Tp) r (List.ofFn T).reverse := by
  intro m
  induction m with
  | zero => intro T r _; simp [runGood]
  | succ m ih =>
    intro T r h
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, runGood]
    have hlast : ¬ ∃ k : Fin (m + 1), Fin.last m < k ∧ antiK (T k) Mp = true :=
      fun ⟨k, hk, _⟩ => absurd hk (not_lt.mpr (Fin.le_last k))
    refine ⟨fun hf hA => h (Fin.last m) (by rw [hf, Bool.false_or, decide_eq_false_iff_not]; exact hlast) hA,
      ?_⟩
    apply ih
    intro j hj hA
    rw [mNxt_fd] at hj
    refine h j.castSucc ?_ hA
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hj ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hj
    refine ⟨h1, ?_⟩
    rintro ⟨k, hk, hk'⟩
    cases k using Fin.lastCases with
    | last => exact absurd (h2.symm.trans hk') (by simp)
    | cast k => exact h3 ⟨k, by simpa using hk, hk'⟩

/-- the last anticommuting row (same shape as the matrix side's `firstAnti`) -/
def lastK {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) : Option (Fin n) :=
  (List.finRange n).reverse.find? (fun j => antiK (T j) Mp)

lemma lastK_some {n : ℕ} {T : Tableau n} {Mp : Fin n → Pauli} {p : Fin n} (h : lastK T Mp = some p) :
    antiK (T p) Mp = true ∧ ∀ k, p < k → antiK (T k) Mp = false := by
  unfold lastK at h
  rw [List.find?_eq_some_iff_append] at h
  obtain ⟨hp, as, bs, hxs, has⟩ := h
  refine ⟨hp, fun k hk => ?_⟩
  have hk_mem : k ∈ (List.finRange n).reverse := by simp
  rw [hxs] at hk_mem
  have hsort : List.Pairwise (fun a b : Fin n => b < a) (List.finRange n).reverse := by
    rw [List.pairwise_reverse]; exact List.pairwise_lt_finRange n
  rw [hxs, List.pairwise_append] at hsort
  rcases List.mem_append.mp hk_mem with h1 | h1
  · simpa using has k h1
  · rcases List.mem_cons.mp h1 with h2 | h2
    · subst h2; exact absurd hk (lt_irrefl _)
    · have := (List.pairwise_cons.mp hsort.2.1).1 k h2
      exact absurd (lt_trans this hk) (lt_irrefl _)

lemma lastK_none {n : ℕ} {T : Tableau n} {Mp : Fin n → Pauli} (h : lastK T Mp = none) :
    ∀ k, antiK (T k) Mp = false := by
  intro k
  unfold lastK at h
  have := List.find?_eq_none.mp h k (by simp)
  simpa using this

/-- the random-measurement stabilizer update, with the TM's anticommutation test -/
def updMK {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) (p : Fin n) (b : Bool) : Tableau n :=
  fun j => if j = p then ⟨if b then 2 else 0, Mp⟩ else if antiK (T j) Mp then (T j).mul (T p) else T j

theorem passOut_meas {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) (p : Fin n)
    (hp : lastK T Mp = some p) (cb : Bool) :
    passOut Mp (T p) cb false (List.ofFn T).reverse = encodeTableau (updMK T Mp p cb) := by
  obtain ⟨hpa, hmax⟩ := lastK_some hp
  rw [passOut_ofFn, encodeTableau_eq]
  congr 1; congr 1; funext j
  congr 1
  unfold rowOut updMK
  by_cases hj : j = p
  · subst hj
    have : ¬ ∃ k, j < k ∧ antiK (T k) Mp = true := fun ⟨k, hk, hk'⟩ => by
      rw [hmax k hk] at hk'; exact absurd hk' (by simp)
    simp [hpa, this]
  · simp only [hj, if_false]
    cases hA : antiK (T j) Mp
    · simp
    · have hjp : j < p := lt_of_le_of_ne (not_lt.mp fun h => by
        rw [hmax j h] at hA; exact absurd hA (by simp)) hj
      have : ∃ k, j < k ∧ antiK (T k) Mp = true := ⟨p, hjp, hpa⟩
      simp [this]

theorem passOut_det {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) (Tp : PauliString n) (cb : Bool)
    (h : lastK T Mp = none) :
    passOut Mp Tp cb false (List.ofFn T).reverse = encodeTableau T := by
  have h0 := lastK_none h
  rw [passOut_ofFn, encodeTableau_eq]
  congr 1; congr 1; funext j
  simp [rowOut, h0 j]

theorem runGood_meas {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) (p : Fin n)
    (hp : lastK T Mp = some p) (r : MS ε) (hf : r.fd = false) :
    runGood (fun r P => mNxt Mp r (P, T p)) (mGood Mp (T p)) r (List.ofFn T).reverse := by
  obtain ⟨hpa, hmax⟩ := lastK_some hp
  apply runGood_ofFn
  intro j hj hA
  rw [hf, Bool.false_or, decide_eq_false_iff_not] at hj
  have : j = p := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hj ⟨p, h, hpa⟩
    · rw [hmax j h] at hA; exact absurd hA (by simp)
  rw [this]

theorem runGood_det {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) (Tp : PauliString n)
    (h : lastK T Mp = none) (r : MS ε) :
    runGood (fun r P => mNxt Mp r (P, Tp)) (mGood Mp Tp) r (List.ofFn T).reverse := by
  apply runGood_ofFn
  intro j _ hA
  rw [lastK_none h j] at hA
  exact absurd hA (by simp)

end MeasClosed

end OCRS19TM

namespace OCRS19TM

section MeasStacks

open QAlgorithms.Stabilizer

variable {ε : Type} {Kb : Type} [DecidableEq Kb]

lemma loopStk_frame {ρ α : Type} (nxt : ρ → α → ρ) (stk : ρ → α → (Kb → List Bool) → Kb → List Bool)
    (k : Kb) (h : ∀ r a B, stk r a B k = B k) :
    ∀ (l : List α) (r : ρ) (B : Kb → List Bool), loopStk nxt stk r l B k = B k := by
  intro l
  induction l with
  | nil => intro r B; rfl
  | cons a l ih => intro r B; simp only [loopStk]; rw [ih, h]

lemma mStk_frame {n : ℕ} (K : Fin 8 → Kb) (Mp : Fin n → Pauli) (r : MS ε)
    (a : PauliString n × PauliString n) (B : Kb → List Bool) (k : Kb)
    (h1 : k ≠ K 1) (h2 : k ≠ K 2) (h5 : k ≠ K 5) (h7 : k ≠ K 7) :
    mStk K Mp r a B k = B k := by
  unfold mStk; split_ifs <;> simp [Function.update_apply, h1, h2, h5, h7]

lemma loop_X {n : ℕ} (K : Fin 8 → Kb) (hK : Function.Injective K) (Mp : Fin n → Pauli)
    (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r : MS ε) (B : Kb → List Bool) (rest : List Bool),
      B (K 1) = (l.map fun a => (encPS a).reverse).flatten ++ rest →
      loopStk (fun r P => mNxt Mp r (P, Tp)) (fun r P B => mStk K Mp r (P, Tp) B) r l B (K 1) = rest := by
  intro l
  induction l with
  | nil => intro r B rest h; simpa [loopStk] using h
  | cons P l ih =>
    intro r B rest h
    simp only [loopStk]
    apply ih
    have hd : mStk K Mp r (P, Tp) B (K 1) = (B (K 1)).drop (encPS P).length := by
      unfold mStk; split_ifs <;> simp [Function.update_apply, hK.eq_iff]
    rw [hd, h, List.map_cons, List.flatten_cons, List.append_assoc]
    exact List.drop_left' List.length_reverse

/-- selection bits pushed by the pass (rows in processing order) -/
def selOut {n : ℕ} (Mp : Fin n → Pauli) : Bool → List (PauliString n) → List Bool
  | _, [] => []
  | f, P :: l => selOut Mp (f || antiK P Mp) l ++ [!f && antiK P Mp]

lemma mStk_S {n : ℕ} (K : Fin 8 → Kb) (hK : Function.Injective K) (Mp : Fin n → Pauli) (r : MS ε)
    (P Tp : PauliString n) (B : Kb → List Bool) :
    mStk K Mp r (P, Tp) B (K 7) = (!r.fd && antiK P Mp) :: B (K 7) := by
  unfold mStk
  cases hA : antiK P Mp <;> cases hf : r.fd <;> simp [Function.update_apply, hK.eq_iff, hA, hf]

lemma loop_S {n : ℕ} (K : Fin 8 → Kb) (hK : Function.Injective K) (Mp : Fin n → Pauli)
    (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r : MS ε) (B : Kb → List Bool),
      loopStk (fun r P => mNxt Mp r (P, Tp)) (fun r P B => mStk K Mp r (P, Tp) B) r l B (K 7) =
        selOut Mp r.fd l ++ B (K 7) := by
  intro l
  induction l with
  | nil => intro r B; simp [loopStk, selOut]
  | cons P l ih =>
    intro r B
    simp only [loopStk, selOut]
    rw [ih, mStk_S K hK, mNxt_fd]
    simp

lemma selOut_ofFn {n : ℕ} (Mp : Fin n → Pauli) :
    ∀ {m : ℕ} (T : Fin m → PauliString n) (f : Bool),
      selOut Mp f (List.ofFn T).reverse =
        List.ofFn fun j => (!(f || decide (∃ k, j < k ∧ antiK (T k) Mp = true)) && antiK (T j) Mp) := by
  intro m
  induction m with
  | zero => intro T f; simp [selOut]
  | succ m ih =>
    intro T f
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, selOut]
    rw [ih (fun j => T j.castSucc)]
    rw [List.ofFn_succ', List.concat_eq_append]
    have hlast : ¬ ∃ k : Fin (m + 1), Fin.last m < k ∧ antiK (T k) Mp = true :=
      fun ⟨k, hk, _⟩ => absurd hk (not_lt.mpr (Fin.le_last k))
    have hb : ∀ j : Fin m, (f || antiK (T (Fin.last m)) Mp ||
        decide (∃ k, j < k ∧ antiK (T k.castSucc) Mp = true)) =
        (f || decide (∃ k, j.castSucc < k ∧ antiK (T k) Mp = true)) := by
      intro j
      cases f <;> cases hl : antiK (T (Fin.last m)) Mp <;>
        simp [Fin.exists_fin_succ', Fin.castSucc_lt_last, hl]
    simp only [hb]
    congr 1
    simp [hlast]

lemma selOut_meas {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) (p : Fin n) (hp : lastK T Mp = some p) :
    selOut Mp false (List.ofFn T).reverse = List.ofFn fun j => decide (j = p) := by
  obtain ⟨hpa, hmax⟩ := lastK_some hp
  rw [selOut_ofFn]
  congr 1; funext j
  by_cases hj : j = p
  · subst hj
    have : ¬ ∃ k, j < k ∧ antiK (T k) Mp = true := fun ⟨k, hk, hk'⟩ => by
      rw [hmax k hk] at hk'; exact absurd hk' (by simp)
    simp [hpa, this]
  · cases hA : antiK (T j) Mp
    · simp [hj]
    · have hjp : j < p := lt_of_le_of_ne (not_lt.mp fun h => by
        rw [hmax j h] at hA; exact absurd hA (by simp)) hj
      have : ∃ k, j < k ∧ antiK (T k) Mp = true := ⟨p, hjp, hpa⟩
      simp [this, hj]

lemma selOut_det {n : ℕ} (T : Tableau n) (Mp : Fin n → Pauli) (h : lastK T Mp = none) :
    selOut Mp false (List.ofFn T).reverse = List.ofFn fun _ : Fin n => false := by
  rw [selOut_ofFn]; simp [lastK_none h]

lemma mBody_inv {n : ℕ} (K : Fin 8 → Kb) (hK : Function.Injective K) (Mp : Fin n → Pauli)
    (Tp P : PauliString n) (r : MS ε) (B : Kb → List Bool) (hI : mInv K Mp Tp r B)
    (hG : mGood Mp Tp r P) :
    mInv K Mp Tp (mNxt Mp r (P, Tp)) (mStk K Mp r (P, Tp) B) := by
  obtain ⟨han, hb, hZ, hW, hT, h1, h0⟩ := hI
  cases hA : antiK P Mp <;> cases hf : r.fd
  · simp only [mInv, mNxt, mStk, hA, hf, Bool.false_eq_true, if_false]
    simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT, h0 hf, hf]
  · simp only [mInv, mNxt, mStk, hA, hf, Bool.false_eq_true, if_false]
    simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT, h1 hf, hf]
  · have hPT := hG hf hA
    subst hPT
    simp only [mInv, mNxt, mStk, hA, hf, Bool.false_eq_true, if_false, if_true]
    simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT]
  · simp only [mInv, mNxt, mStk, hA, hf, if_true]
    simp [Function.update_apply, hK.eq_iff, han, hb, hZ, hW, hT, h1 hf, hf, MS.setMu]

lemma loop_inv {n : ℕ} (K : Fin 8 → Kb) (hK : Function.Injective K) (Mp : Fin n → Pauli)
    (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r : MS ε) (B : Kb → List Bool), mInv K Mp Tp r B →
      runGood (fun r P => mNxt Mp r (P, Tp)) (mGood Mp Tp) r l →
      mInv K Mp Tp (l.foldl (fun r P => mNxt Mp r (P, Tp)) r)
        (loopStk (fun r P => mNxt Mp r (P, Tp)) (fun r P B => mStk K Mp r (P, Tp) B) r l B) := by
  intro l
  induction l with
  | nil => intro r B hI _; exact hI
  | cons P l ih =>
    intro r B hI hG
    simp only [List.foldl_cons, loopStk]
    exact ih _ _ (mBody_inv K hK Mp Tp P r B hI hG.1) hG.2

/-- state facts kept along the pass -/
def sKeep {n : ℕ} (Tp : PauliString n) (r0 s : MS ε) : Prop :=
  s.mu = (0, none) ∧ (s.fd = true → s.cp = Tp.phase) ∧ s.an = r0.an ∧ s.cb = r0.cb ∧ s.ext = r0.ext

lemma loop_sKeep {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r0 r : MS ε), sKeep Tp r0 r →
      runGood (fun r P => mNxt Mp r (P, Tp)) (mGood Mp Tp) r l →
      sKeep Tp r0 (l.foldl (fun r P => mNxt Mp r (P, Tp)) r) := by
  intro l
  induction l with
  | nil => intro r0 r h _; exact h
  | cons P l ih =>
    intro r0 r h hG
    simp only [List.foldl_cons]
    refine ih r0 _ ?_ hG.2
    obtain ⟨hmu, hcp, han, hcb, hext⟩ := h
    have hg := hG.1
    unfold mGood at hg
    unfold mNxt sKeep
    cases hA : antiK P Mp <;> cases hf : r.fd
    · simp [hmu, hcp, han, hcb, hext, hf]
    · simp [hmu, hcp, han, hcb, hext, hf]
    · have hPT := hg hf hA
      subst hPT
      simp [hmu, han, hcb, hext, hf]
    · simp [MS.setMu, hcp hf, han, hcb, hext, hf]

lemma loop_noanti {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) :
    ∀ (l : List (PauliString n)) (r : MS ε), (∀ P ∈ l, antiK P Mp = false) →
      l.foldl (fun r P => mNxt Mp r (P, Tp)) r = r := by
  intro l
  induction l with
  | nil => intro r _; rfl
  | cons P l ih =>
    intro r h
    simp only [List.foldl_cons]
    have : mNxt Mp r (P, Tp) = r := by unfold mNxt; simp [h P (by simp)]
    rw [this]
    exact ih r (fun Q hQ => h Q (by simp [hQ]))

variable {R : Type} [DecidableEq R] {G : R → Type} {Λ : Type}

/-- the random-measurement T pass in closed form (some row anticommutes with M) -/
theorem meas_pass_meas {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (E E' : Λ) (hP : MeasProg M K L E)
    (hM0 : M E = testStmt (K 1) (L 0) E')
    (T : Tableau n) (Mp : Fin n → Pauli) (p : Fin n) (hp : lastK T Mp = some p)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (hB : B (K 0) = mmask Mp ∧ B (K 3) = [] ∧ B (K 4) = [] ∧ B (K 6) = [] ∧ B (K 5) = [])
    (hX : B (K 1) = (encodeTableau T).reverse) :
    ∃ B' : Kb → List Bool, Reach M ⟨some E, ((none, none, c), r), mk B Q⟩
        ⟨some E', ((none, none, c), { r with fd := true, cp := (T p).phase }), mk B' Q⟩
        (n * (10 * n + 12 + 1) + 1) ∧
      B' (K 1) = [] ∧ B' (K 2) = encodeTableau (updMK T Mp p r.cb) ++ B (K 2) ∧
      B' (K 5) = mmask (T p).ops ∧ B' (K 7) = (List.ofFn fun j => decide (j = p)) ++ B (K 7) ∧
      B' (K 0) = mmask Mp ∧ B' (K 3) = [] ∧ B' (K 4) = [] ∧ B' (K 6) = [] ∧
      ∀ k, k ≠ K 1 → k ≠ K 2 → k ≠ K 5 → k ≠ K 7 → B' k = B k := by
  obtain ⟨hran, hrmu, hrfd⟩ := hr
  obtain ⟨hb0, hb3, hb4, hb6, hb5⟩ := hB
  have hI : mInv K Mp (T p) r B :=
    ⟨hran, hb0, hb3, hb4, hb6, fun h => by rw [hrfd] at h; exact absurd h (by simp), fun _ => hb5⟩
  have hG := runGood_meas T Mp p hp r hrfd
  have hXl : B (K 1) = (((List.ofFn T).reverse).map fun a => (encPS a).reverse).flatten := by
    rw [hX, encodeTableau_rev]
  have hR := meas_pass M K hK L E E' hP hM0 Mp c Q (T p) _ r B hI hG hXl
  have hk := loop_sKeep Mp (T p) (List.ofFn T).reverse r r
    ⟨hrmu, fun h => by rw [hrfd] at h; exact absurd h (by simp), rfl, rfl, rfl⟩ hG
  have hfd : ((List.ofFn T).reverse.foldl (fun r P => mNxt Mp r (P, T p)) r).fd = true := by
    rw [loop_fd, hrfd, Bool.false_or, List.any_eq_true]
    exact ⟨T p, by simp, (lastK_some hp).1⟩
  have hstate : (List.ofFn T).reverse.foldl (fun r P => mNxt Mp r (P, T p)) r =
      { r with fd := true, cp := (T p).phase } := by
    generalize (List.ofFn T).reverse.foldl (fun r P => mNxt Mp r (P, T p)) r = s at hk hfd
    obtain ⟨h1, h2, h3, h4, h5⟩ := hk
    have h2' := h2 hfd
    cases s; cases r
    simp_all
  have hI' := loop_inv K hK Mp (T p) _ r B hI hG
  rw [hstate] at hR hI'
  simp only [List.length_reverse, List.length_ofFn] at hR
  obtain ⟨_, i0, i3, i4, i6, i1, _⟩ := hI'
  refine ⟨_, hR, ?_, ?_, (i1 rfl).2, ?_, i0, i3, i4, i6, ?_⟩
  · exact loop_X K hK Mp (T p) _ r B [] (by rw [hXl, List.append_nil])
  · rw [loop_Y K hK, hrfd, passOut_meas T Mp p hp]
  · rw [loop_S K hK, hrfd, selOut_meas T Mp p hp]
  · intro k h1 h2 h5 h7
    exact loopStk_frame _ _ k (fun r a B => mStk_frame K Mp r (a, T p) B k h1 h2 h5 h7) _ r B

/-- the random-measurement T pass in closed form (no row anticommutes with M) -/
theorem meas_pass_det {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (E E' : Λ) (hP : MeasProg M K L E)
    (hM0 : M E = testStmt (K 1) (L 0) E')
    (T : Tableau n) (Mp : Fin n → Pauli) (Tp : PauliString n) (hp : lastK T Mp = none)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.fd = false)
    (hB : B (K 0) = mmask Mp ∧ B (K 3) = [] ∧ B (K 4) = [] ∧ B (K 6) = [] ∧ B (K 5) = [])
    (hX : B (K 1) = (encodeTableau T).reverse) :
    ∃ B' : Kb → List Bool, Reach M ⟨some E, ((none, none, c), r), mk B Q⟩
        ⟨some E', ((none, none, c), r), mk B' Q⟩ (n * (10 * n + 12 + 1) + 1) ∧
      B' (K 1) = [] ∧ B' (K 2) = encodeTableau T ++ B (K 2) ∧
      B' (K 5) = [] ∧ B' (K 7) = (List.ofFn fun _ : Fin n => false) ++ B (K 7) ∧
      B' (K 0) = mmask Mp ∧ B' (K 3) = [] ∧ B' (K 4) = [] ∧ B' (K 6) = [] ∧
      ∀ k, k ≠ K 1 → k ≠ K 2 → k ≠ K 5 → k ≠ K 7 → B' k = B k := by
  obtain ⟨hran, hrfd⟩ := hr
  obtain ⟨hb0, hb3, hb4, hb6, hb5⟩ := hB
  have hI : mInv K Mp Tp r B :=
    ⟨hran, hb0, hb3, hb4, hb6, fun h => by rw [hrfd] at h; exact absurd h (by simp), fun _ => hb5⟩
  have hG := runGood_det T Mp Tp hp r
  have hXl : B (K 1) = (((List.ofFn T).reverse).map fun a => (encPS a).reverse).flatten := by
    rw [hX, encodeTableau_rev]
  have hR := meas_pass M K hK L E E' hP hM0 Mp c Q Tp _ r B hI hG hXl
  have hstate : (List.ofFn T).reverse.foldl (fun r P => mNxt Mp r (P, Tp)) r = r := by
    apply loop_noanti
    intro P hPm
    simp only [List.mem_reverse, List.mem_ofFn'] at hPm
    obtain ⟨j, rfl⟩ := hPm
    exact lastK_none hp j
  have hI' := loop_inv K hK Mp Tp _ r B hI hG
  rw [hstate] at hR hI'
  simp only [List.length_reverse, List.length_ofFn] at hR
  obtain ⟨_, i0, i3, i4, i6, _, i5⟩ := hI'
  refine ⟨_, hR, ?_, ?_, i5 hrfd, ?_, i0, i3, i4, i6, ?_⟩
  · exact loop_X K hK Mp Tp _ r B [] (by rw [hXl, List.append_nil])
  · rw [loop_Y K hK, hrfd, passOut_det T Mp Tp _ hp]
  · rw [loop_S K hK, hrfd, selOut_det T Mp hp]
  · intro k h1 h2 h5 h7
    exact loopStk_frame _ _ k (fun r a B => mStk_frame K Mp r (a, Tp) B k h1 h2 h5 h7) _ r B

end MeasStacks

end OCRS19TM

namespace OCRS19TM

section DPass

open QAlgorithms.Stabilizer

variable {ε : Type} {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ : Type}

lemma clear_run' (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (a : Kb) (L E : Λ)
    (hM : M L = clearStmt a L E) (r : MS ε) (c : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = A) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk (Function.update B a []) Q⟩ (A.length + 1) := by
  have := clear_run M a L E hM r c A (mk B Q) (by simp [hA])
  rwa [update_mk] at this

def dMul (r : MS ε) : MS ε := { r with an := (false, none), mu := (r.cp, none), fd := false }
def dCp (r : MS ε) : MS ε := { r with an := (false, none), fd := false }

/-- labels of the destabilizer pass body; stacks as in `MeasProg` (7 = selection bits, row order) -/
structure DProg (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb) (L : Fin 16 → Λ)
    (E : Λ) : Prop where
  h0 : M (L 0) = popStStmt (K 7) (L 1) (fun r x => { r with fd := x })
  h1 : M (L 1) = ctlStmt (K 0) (K 1) (K 3) (K 6) (L 1) (L 2)
    (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y))
    (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y)
  h2 : M (L 2) = p2Stmt (K 1) (K 3) (L 3) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r)
  h3 : M (L 3) = mvStmt (K 6) (K 0) (L 3) (L 4)
  h4 : M (L 4) = dispStmt (fun r : MS ε => r.an.1 || r.fd) (fun r => !r.fd) dMul dCp dCp (L 7) (L 11) (L 5)
  h5 : M (L 5) = mvStmt (K 3) (K 4) (L 5) (L 6)
  h6 : M (L 6) = mvStmt (K 4) (K 2) (L 6) E
  h7 : M (L 7) = mvStmt (K 3) (K 4) (L 7) (L 8)
  h8 : M (L 8) = ctlStmt (K 5) (K 4) (K 2) (K 6) (L 8) (L 9)
    (fun r x y => MS.setMu r (cwδ mulW (MS.mu r) x y))
    (fun r x y => co1 mulW (MS.mu r) x y) (fun r x y => co2 mulW (MS.mu r) x y)
  h9 : M (L 9) = p2Stmt (K 4) (K 2) (L 10) (g1p2 MS.mu) (fun r _ _ => MS.setMu r (0, none))
  h10 : M (L 10) = mvStmt (K 6) (K 5) (L 10) E
  h11 : M (L 11) = clearStmt (K 3) (L 11) (L 12)
  h12 : M (L 12) = dupStmt (K 5) (K 2) (K 6) (L 12) (L 13)
  h13 : M (L 13) = mvStmt (K 6) (K 5) (L 13) (L 14)
  h14 : M (L 14) = emitStmt (K 2) (L 15) (fun r => decide (r.cp.val % 2 = 1)) id
  h15 : M (L 15) = emitStmt (K 2) E (fun r => decide (2 ≤ r.cp.val)) id

/-- output row of the destabilizer pass for (row, selection bit) -/
def dRow {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) (a : PauliString n × Bool) : PauliString n :=
  if a.2 then Tp else if antiK a.1 Mp then a.1.mul Tp else a.1

def dStk {n : ℕ} (K : Fin 8 → Kb) (Mp : Fin n → Pauli) (Tp : PauliString n) (a : PauliString n × Bool)
    (B : Kb → List Bool) : Kb → List Bool :=
  Function.update (Function.update (Function.update B (K 1) ((B (K 1)).drop (encPS a.1).length))
    (K 7) (B (K 7)).tail) (K 2) (encPS (dRow Mp Tp a) ++ B (K 2))

def dInv {n : ℕ} (K : Fin 8 → Kb) (Mp : Fin n → Pauli) (Tp : PauliString n) (r : MS ε)
    (B : Kb → List Bool) : Prop :=
  r.an = (false, none) ∧ r.fd = false ∧ r.mu = (0, none) ∧ r.cp = Tp.phase ∧ B (K 0) = mmask Mp ∧
    B (K 3) = [] ∧ B (K 4) = [] ∧ B (K 6) = [] ∧ B (K 5) = mmask Tp.ops

theorem d_row {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 16 → Λ) (E : Λ) (hP : DProg M K L E)
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (Tp : PauliString n)
    (a : PauliString n × Bool) (r : MS ε) (B : Kb → List Bool) (rest rest7 : List Bool)
    (hI : dInv K Mp Tp r B) (hX : B (K 1) = (encPS a.1).reverse ++ rest)
    (h7 : B (K 7) = a.2 :: rest7) :
    Reach M ⟨some (L 0), ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk (dStk K Mp Tp a B) Q⟩ (10 * n + 16) := by
  obtain ⟨P, s⟩ := a
  simp only at hX h7
  obtain ⟨han, hfd, hmu, hcp, hb, hZ, hW, hT, hcap⟩ := hI
  have hne : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h => hK.ne h
  have hlenM := mmask_length Mp
  have hlenM2 := mmask_length Tp.ops
  have hlenP := encPS_length P
  have hdrop : (B (K 1)).drop (encPS P).length = rest := by
    rw [hX]; exact List.drop_left' (List.length_reverse)
  have h1 := popSt_step M (K 7) (L 1) (L 0) (fun r x => { r with fd := x }) hP.h0 c r B Q s rest7 h7
  refine Reach.cons h1 ?_ (by omega)
  refine Reach.cons (anti_row M (K 0) (K 1) (K 3) (K 6) (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 0 6 (by decide)) (hne 1 3 (by decide)) (hne 1 6 (by decide)) (hne 3 6 (by decide))
    (L 1) (L 2) (L 3) (L 4) MS.an MS.setAn (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Mp
    hP.h1 hP.h2 hP.h3 c _ false (by exact han) P rest _ Q
    (by simp [Function.update_apply, hK.eq_iff, hb]) (by simp [Function.update_apply, hK.eq_iff, hX])
    (by simp [Function.update_apply, hK.eq_iff, hT])) ?_ (by rw [hlenM]; omega)
  cases s
  · cases hA : antiK P Mp
    · -- copy
      refine Reach.cons (disp_step3 M _ _ _ _ _ (L 7) (L 11) (L 5) (L 4) hP.h4 c _ _
        (by simp [MS.setAn, hA])) ?_ ?c2
      refine Reach.cons (mv_run M (K 3) (K 4) (hne 3 4 (by decide)) (L 5) (L 6) hP.h5 _ c Q
        (encPS P) _ (by simp [Function.update_apply, hK.eq_iff, hZ])) ?_ ?c3
      refine Reach.cons (mv_run M (K 4) (K 2) (hne 4 2 (by decide)) (L 6) E hP.h6 _ c Q
        (encPS P).reverse _ (by simp [Function.update_apply, hK.eq_iff, hW])) ?_ ?c4
      refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
      · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
        refine ⟨?_, ?_⟩
        · obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
          simp only at han hfd; subst han hfd
          simp [dCp, MS.setAn, hA]
        · congr 1
          funext k
          simp only [dStk, dRow, hA, hdrop, h7, Bool.false_eq_true, if_false, Function.update_apply,
            List.reverse_reverse, List.tail_cons]
          split_ifs <;> simp_all [hK.eq_iff]
      all_goals simp only [hlenM, hlenP, List.length_reverse]; omega
    · -- multiply by the captured row
      refine Reach.cons (disp_step1 M _ _ _ _ _ (L 7) (L 11) (L 5) (L 4) hP.h4 c _ _
        (by simp [MS.setAn, hA]) (by simp [MS.setAn])) ?_ ?m2
      refine Reach.cons (mv_run M (K 3) (K 4) (hne 3 4 (by decide)) (L 7) (L 8) hP.h7 _ c Q
        (encPS P) _ (by simp [Function.update_apply, hK.eq_iff, hZ])) ?_ ?m3
      refine Reach.cons (mul_row M (K 5) (K 4) (K 2) (K 6) (hne 5 4 (by decide)) (hne 5 2 (by decide))
        (hne 5 6 (by decide)) (hne 4 2 (by decide)) (hne 4 6 (by decide)) (hne 2 6 (by decide))
        (L 8) (L 9) (L 10) E MS.mu MS.setMu (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
        hP.h8 hP.h9 hP.h10 c _ P Tp (by simp [dMul, MS.setAn, hcp]) [] _ Q
        (by simp [Function.update_apply, hK.eq_iff, hcap])
        (by simp [Function.update_apply, hK.eq_iff, hW])
        (by simp [Function.update_apply, hK.eq_iff, hT])) ?_ ?m4
      refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
      · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
        refine ⟨?_, ?_⟩
        · obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
          simp only at han hfd hmu; subst han hfd hmu
          simp [dMul, MS.setAn, MS.setMu]
        · congr 1
          funext k
          simp only [dStk, dRow, hA, hdrop, h7, Bool.false_eq_true, if_false, if_true,
            Function.update_apply, List.tail_cons]
          split_ifs <;> simp_all [hK.eq_iff]
      all_goals simp only [hlenM, hlenM2, hlenP, List.length_reverse]; omega
  · -- the selected row: output the captured row
    refine Reach.cons (disp_step2 M _ _ _ _ _ (L 7) (L 11) (L 5) (L 4) hP.h4 c _ _
      (by simp [MS.setAn]) (by simp [MS.setAn])) ?_ ?p2
    refine Reach.cons (clear_run' M (K 3) (L 11) (L 12) hP.h11 _ c Q (encPS P) _
      (by simp [Function.update_apply, hK.eq_iff, hZ])) ?_ ?p3
    refine Reach.cons (dup_run M (K 5) (K 2) (K 6) (hne 5 2 (by decide)) (hne 5 6 (by decide))
      (hne 2 6 (by decide)) (L 12) (L 13) hP.h12 _ c Q (mmask Tp.ops) _
      (by simp [Function.update_apply, hK.eq_iff, hcap])) ?_ ?p4
    refine Reach.cons (mv_run M (K 6) (K 5) (hne 6 5 (by decide)) (L 13) (L 14) hP.h13 _ c Q
      (mmask Tp.ops).reverse _ (by simp [Function.update_apply, hK.eq_iff, hT])) ?_ ?p5
    refine Reach.cons (emit_step M (K 2) (L 15) (L 14) _ _ hP.h14 c _ _ Q) ?_ ?p6
    refine Reach.cons (emit_step M (K 2) E (L 15) _ _ hP.h15 c _ _ Q) ?_ ?p7
    refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
    · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
      refine ⟨?_, ?_⟩
      · obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
        simp only at han hfd; subst han hfd
        simp [dCp, MS.setAn]
      · congr 1
        funext k
        simp only [dStk, dRow, hdrop, h7, if_true, Function.update_apply, List.tail_cons, id]
        by_cases h2 : k = K 2
        · subst h2
          simp [hK.eq_iff, dCp, MS.setAn, hcp, encPS_cons, mmask]
        by_cases h5 : k = K 5
        · subst h5; simp [hK.eq_iff, hcap, mmask]
        by_cases h6 : k = K 6
        · subst h6; simp [hK.eq_iff, hT]
        by_cases h3 : k = K 3
        · subst h3; simp [hK.eq_iff, hZ]
        by_cases h1 : k = K 1
        · subst h1; simp [hK.eq_iff]
        by_cases h7' : k = K 7
        · subst h7'; simp [hK.eq_iff]
        by_cases h0 : k = K 0
        · subst h0; simp [hK.eq_iff, hb]
        simp [h2, h5, h6, h3, h1, h7', h0]
    all_goals simp only [hlenM, hlenM2, hlenP, List.length_reverse, List.length_cons,
      List.length_append, hZ, hT, List.length_nil]; omega

/-- outputs of the destabilizer pass (last processed row on top) -/
def dOut {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) : List (PauliString n × Bool) → List Bool
  | [] => []
  | a :: l => dOut Mp Tp l ++ encPS (dRow Mp Tp a)

lemma dOut_eq {n : ℕ} (Mp : Fin n → Pauli) (Tp : PauliString n) :
    ∀ l : List (PauliString n × Bool), dOut Mp Tp l = (l.reverse.map fun a => encPS (dRow Mp Tp a)).flatten := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp [dOut, ih]

theorem d_pass {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 16 → Λ) (E E' : Λ) (hP : DProg M K L E)
    (hM0 : M E = testStmt (K 1) (L 0) E')
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (Tp : PauliString n) :
    ∀ (l : List (PauliString n × Bool)) (r : MS ε) (B : Kb → List Bool) (rest7 : List Bool),
      dInv K Mp Tp r B → B (K 1) = (l.map fun a => (encPS a.1).reverse).flatten →
      B (K 7) = l.map Prod.snd ++ rest7 →
      Reach M ⟨some E, ((none, none, c), r), mk B Q⟩
        ⟨some E', ((none, none, c), r), mk (Function.update (Function.update (Function.update B
          (K 1) []) (K 7) rest7) (K 2) (dOut Mp Tp l ++ B (K 2))) Q⟩
        (l.length * (10 * n + 16 + 1) + 1) := by
  intro l
  induction l with
  | nil =>
    intro r B rest7 _ hX h7
    have e : Function.update (Function.update (Function.update B (K 1) []) (K 7) rest7) (K 2)
        (dOut Mp Tp [] ++ B (K 2)) = B := by
      funext k
      simp only [Function.update_apply, dOut, List.nil_append]
      split_ifs <;> simp_all
    rw [e]
    exact (test_none M (K 1) E (L 0) E' hM0 r c Q B (by simpa using hX)).mono (by simp)
  | cons a l ih =>
    intro r B rest7 hI hX h7
    obtain ⟨x, A, hxA⟩ : ∃ x A, (encPS a.1).reverse = x :: A := by
      cases h : (encPS a.1).reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp h) (encPS_ne a.1)
      | cons x A => exact ⟨x, A, rfl⟩
    have h1 := test_some M (K 1) E (L 0) E' hM0 r c Q B x
      (A ++ (l.map fun a => (encPS a.1).reverse).flatten) (by rw [hX]; simp [hxA])
    have h2 := d_row M K hK L E hP Mp c Q Tp a r B ((l.map fun a => (encPS a.1).reverse).flatten)
      (l.map Prod.snd ++ rest7) hI (by rw [hX]; simp) (by rw [h7]; simp)
    obtain ⟨han, hfd, hmu, hcp, hb, hZ, hW, hT, hcap⟩ := hI
    have hdrop : (B (K 1)).drop (encPS a.1).length = (l.map fun a => (encPS a.1).reverse).flatten := by
      rw [hX, List.map_cons, List.flatten_cons]; exact List.drop_left' (List.length_reverse)
    have hI' : dInv K Mp Tp r (dStk K Mp Tp a B) := by
      refine ⟨han, hfd, hmu, hcp, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [dStk, Function.update_apply, hK.eq_iff, hb, hZ, hW, hT, hcap]
    have h3 := ih r (dStk K Mp Tp a B) rest7 hI'
      (by simp [dStk, Function.update_apply, hK.eq_iff, hdrop])
      (by simp [dStk, Function.update_apply, hK.eq_iff, h7])
    refine ((h1.trans (h2.trans h3)).mono ?_).of_eq ?_
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · congr 2
      funext k
      simp only [dStk, Function.update_apply, dOut, List.append_assoc]
      split_ifs <;> simp_all [hK.eq_iff]

/-- the destabilizer update with the TM's anticommutation test -/
def updDMK {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) (p : Fin n) : Tableau n :=
  fun i => if i = p then T p else if antiK (D i) Mp then (D i).mul (T p) else D i

theorem dOut_closed {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) (p : Fin n) :
    dOut Mp (T p) (List.ofFn fun i => (D i, decide (i = p))).reverse = encodeTableau (updDMK T D Mp p) := by
  rw [dOut_eq, List.reverse_reverse, encodeTableau_eq, List.map_ofFn]
  congr 1; congr 1; funext i
  simp only [Function.comp_apply, dRow, updDMK, decide_eq_true_eq]

lemma dIn_X {n : ℕ} (D : Tableau n) (sel : Fin n → Bool) :
    (((List.ofFn fun i => (D i, sel i)).reverse).map fun a => (encPS a.1).reverse).flatten =
      (encodeTableau D).reverse := by
  rw [encodeTableau_rev]
  simp [List.map_reverse, List.map_ofFn, Function.comp_def]

lemma dIn_S {n : ℕ} (D : Tableau n) (sel : Fin n → Bool) :
    ((List.ofFn fun i => (D i, sel i)).reverse).map Prod.snd = (List.ofFn sel).reverse := by
  simp [List.map_reverse, List.map_ofFn, Function.comp_def]

end DPass

end OCRS19TM

namespace OCRS19TM

section XPass

open QAlgorithms.Stabilizer

variable {ε : Type} {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ : Type}

/-- labels of the deterministic-outcome pass body: stacks 0 mask(M), 1 D rows (reversed), 2 T rows
(reversed), 3 Z, 5 accumulator mask, 6 temp -/
structure XProg (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb) (L : Fin 17 → Λ)
    (E : Λ) : Prop where
  h0 : M (L 0) = ctlStmt (K 0) (K 1) (K 3) (K 6) (L 0) (L 1)
    (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y))
    (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y)
  h1 : M (L 1) = p2Stmt (K 1) (K 3) (L 2) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r)
  h2 : M (L 2) = mvStmt (K 6) (K 0) (L 2) (L 3)
  h3 : M (L 3) = clearStmt (K 3) (L 3) (L 4)
  h4 : M (L 4) = dispStmt (fun r : MS ε => r.an.1) (fun _ => true) msMul msCopy msCopy (L 5) (L 5) (L 12)
  h5 : M (L 5) = ctlStmt (K 5) (K 2) (K 3) (K 6) (L 5) (L 6)
    (fun r x y => MS.setMu r (cwδ mulW (MS.mu r) x y))
    (fun r x y => co1 mulW (MS.mu r) x y) (fun r x y => co2 mulW (MS.mu r) x y)
  h6 : M (L 6) = p2Stmt (K 2) (K 3) (L 7) (g1p2 MS.mu) (fun r _ _ => MS.setMu r (0, none))
  h7 : M (L 7) = mvStmt (K 6) (K 5) (L 7) (L 8)
  h8 : M (L 8) = clearStmt (K 5) (L 8) (L 9)
  h9 : M (L 9) = popStStmt (K 3) (L 10) (fun r x => { r with cp := if x then 2 else 0 })
  h10 : M (L 10) = popStStmt (K 3) (L 11) (fun r x => { r with cp := r.cp + if x then 1 else 0 })
  h11 : M (L 11) = mvStmt (K 3) (K 5) (L 11) E
  h12 : M (L 12) = ctlStmt (K 0) (K 2) (K 3) (K 6) (L 12) (L 13)
    (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y))
    (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y)
  h13 : M (L 13) = p2Stmt (K 2) (K 3) (L 14) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r)
  h14 : M (L 14) = mvStmt (K 6) (K 0) (L 14) (L 15)
  h15 : M (L 15) = clearStmt (K 3) (L 15) (L 16)
  h16 : M (L 16) = dispStmt (fun _ : MS ε => false) (fun _ => false) id id msCopy E E E

/-- accumulator update for one (destabilizer row, stabilizer row) pair -/
def xAcc {n : ℕ} (Mp : Fin n → Pauli) (a : PauliString n × PauliString n) (Acc : PauliString n) :
    PauliString n :=
  if antiK a.1 Mp then a.2.mul Acc else Acc

def xFold {n : ℕ} (Mp : Fin n → Pauli) (l : List (PauliString n × PauliString n)) (Acc : PauliString n) :
    PauliString n :=
  l.foldl (fun Acc a => xAcc Mp a Acc) Acc

def xInv {n : ℕ} (K : Fin 8 → Kb) (Mp : Fin n → Pauli) (Acc : PauliString n) (r : MS ε)
    (B : Kb → List Bool) : Prop :=
  r.an = (false, none) ∧ r.mu = (0, none) ∧ r.cp = Acc.phase ∧ B (K 0) = mmask Mp ∧
    B (K 3) = [] ∧ B (K 6) = [] ∧ B (K 5) = mmask Acc.ops

theorem x_row {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 17 → Λ) (E : Λ) (hP : XProg M K L E)
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) (Acc : PauliString n)
    (a : PauliString n × PauliString n) (r : MS ε) (B : Kb → List Bool) (rest1 rest2 : List Bool)
    (hI : xInv K Mp Acc r B) (hX1 : B (K 1) = (encPS a.1).reverse ++ rest1)
    (hX2 : B (K 2) = (encPS a.2).reverse ++ rest2) :
    Reach M ⟨some (L 0), ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), { r with cp := (xAcc Mp a Acc).phase }),
        mk (Function.update (Function.update (Function.update B (K 1) rest1) (K 2) rest2) (K 5)
          (mmask (xAcc Mp a Acc).ops)) Q⟩ (14 * n + 16) := by
  obtain ⟨Dr, Tr⟩ := a
  simp only at hX1 hX2
  obtain ⟨han, hmu, hcp, hb, hZ, hT, hcap⟩ := hI
  have hne : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h => hK.ne h
  have hlenM := mmask_length Mp
  have hlenA := mmask_length Acc.ops
  have hlenD := encPS_length Dr
  have hlenT := encPS_length Tr
  have hlenO : ((List.ofFn fun q => encPauli ((Tr.mul Acc).ops q)).flatten).length = 2 * n :=
    opsEnc_length _
  refine Reach.cons (anti_row M (K 0) (K 1) (K 3) (K 6) (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 0 6 (by decide)) (hne 1 3 (by decide)) (hne 1 6 (by decide)) (hne 3 6 (by decide))
    (L 0) (L 1) (L 2) (L 3) MS.an MS.setAn (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Mp
    hP.h0 hP.h1 hP.h2 c r false han Dr rest1 B Q hb hX1 hT) ?_ (by rw [hlenM]; omega)
  refine Reach.cons (clear_run' M (K 3) (L 3) (L 4) hP.h3 _ c Q (encPS Dr) _
    (by simp [Function.update_apply, hK.eq_iff, hZ])) ?_ (by rw [hlenD, hlenM]; omega)
  cases hA : antiK Dr Mp
  · -- drop the stabilizer row
    refine Reach.cons (disp_step3 M _ _ _ _ _ (L 5) (L 5) (L 12) (L 4) hP.h4 c _ _
      (by simp [MS.setAn, hA])) ?_ ?d1
    refine Reach.cons (anti_row M (K 0) (K 2) (K 3) (K 6) (hne 0 2 (by decide)) (hne 0 3 (by decide))
      (hne 0 6 (by decide)) (hne 2 3 (by decide)) (hne 2 6 (by decide)) (hne 3 6 (by decide))
      (L 12) (L 13) (L 14) (L 15) MS.an MS.setAn (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Mp
      hP.h12 hP.h13 hP.h14 c _ false (by simp [msCopy, MS.setAn]) Tr rest2 _ Q
      (by simp [Function.update_apply, hK.eq_iff, hb]) (by simp [Function.update_apply, hK.eq_iff, hX2])
      (by simp [Function.update_apply, hK.eq_iff, hT])) ?_ ?d2
    refine Reach.cons (clear_run' M (K 3) (L 15) (L 16) hP.h15 _ c Q (encPS Tr) _
      (by simp [Function.update_apply, hK.eq_iff])) ?_ ?d3
    refine Reach.cons (disp_step3 M _ _ _ _ _ E E E (L 16) hP.h16 c _ _ rfl) ?_ ?d4
    refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
    · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
      refine ⟨?_, ?_⟩
      · obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
        simp only at han hcp; subst han hcp
        simp [xAcc, hA, msCopy, MS.setAn]
      · congr 1
        funext k
        simp only [xAcc, hA, Bool.false_eq_true, if_false, Function.update_apply]
        split_ifs <;> simp_all [hK.eq_iff]
    all_goals (try simp only [hlenM, hlenA, hlenD, hlenT, List.length_reverse, List.length_cons,
      List.length_append, List.length_nil]); omega
  · -- multiply the stabilizer row into the accumulator
    refine Reach.cons (disp_step1 M _ _ _ _ _ (L 5) (L 5) (L 12) (L 4) hP.h4 c _ _
      (by simp [MS.setAn, hA]) rfl) ?_ ?e1
    refine Reach.cons (mul_row M (K 5) (K 2) (K 3) (K 6) (hne 5 2 (by decide)) (hne 5 3 (by decide))
      (hne 5 6 (by decide)) (hne 2 3 (by decide)) (hne 2 6 (by decide)) (hne 3 6 (by decide))
      (L 5) (L 6) (L 7) (L 8) MS.mu MS.setMu (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      hP.h5 hP.h6 hP.h7 c _ Tr Acc (by simp [msMul, MS.setAn, hcp]) rest2 _ Q
      (by simp [Function.update_apply, hK.eq_iff, hcap])
      (by simp [Function.update_apply, hK.eq_iff, hX2])
      (by simp [Function.update_apply, hK.eq_iff, hT])) ?_ ?e2
    refine Reach.cons (clear_run' M (K 5) (L 8) (L 9) hP.h8 _ c Q (mmask Acc.ops) _
      (by simp [Function.update_apply, hK.eq_iff, hcap])) ?_ ?e3
    refine Reach.cons (popSt_step M (K 3) (L 10) (L 9) _ hP.h9 c _ _ Q
      (decide (2 ≤ (Tr.mul Acc).phase.val))
      (decide ((Tr.mul Acc).phase.val % 2 = 1) :: (List.ofFn fun q => encPauli ((Tr.mul Acc).ops q)).flatten)
      (by simp [Function.update_apply, hK.eq_iff, encPS_cons])) ?_ ?e4
    refine Reach.cons (popSt_step M (K 3) (L 11) (L 10) _ hP.h10 c _ _ Q
      (decide ((Tr.mul Acc).phase.val % 2 = 1))
      (List.ofFn fun q => encPauli ((Tr.mul Acc).ops q)).flatten (by simp)) ?_ ?e5
    refine Reach.cons (mv_run M (K 3) (K 5) (hne 3 5 (by decide)) (L 11) E hP.h11 _ c Q
      (List.ofFn fun q => encPauli ((Tr.mul Acc).ops q)).flatten _ (by simp)) ?_ ?e6
    refine ((Reach.refl _).mono (Nat.zero_le _)).of_eq ?_
    · simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and]
      refine ⟨?_, ?_⟩
      · have hph : (if decide (2 ≤ (Tr.mul Acc).phase.val) = true then (2 : ZMod 4) else 0) +
            (if decide ((Tr.mul Acc).phase.val % 2 = 1) = true then 1 else 0) = (Tr.mul Acc).phase :=
          phOf_enc _
        obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
        simp only at han hmu; subst han hmu
        simp only [xAcc, hA, if_true, msMul, MS.setAn, MS.setMu, MS.mk.injEq, true_and, and_true]
        exact hph
      · congr 1
        funext k
        simp only [xAcc, hA, if_true, Function.update_apply]
        by_cases h5 : k = K 5
        · subst h5; simp [hK.eq_iff, mmask]
        by_cases h3 : k = K 3
        · subst h3; simp [hK.eq_iff, hZ]
        by_cases h2 : k = K 2
        · subst h2; simp [hK.eq_iff]
        by_cases h1 : k = K 1
        · subst h1; simp [hK.eq_iff]
        by_cases h6 : k = K 6
        · subst h6; simp [hK.eq_iff, hT]
        by_cases h0 : k = K 0
        · subst h0; simp [hK.eq_iff, hb]
        simp [h5, h3, h2, h1, h6, h0]
    all_goals (try simp only [hlenM, hlenA, hlenD, hlenT, hlenO, List.length_reverse, List.length_cons,
      List.length_append, List.length_nil]); omega

theorem x_pass {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L : Fin 17 → Λ) (E E' : Λ) (hP : XProg M K L E)
    (hM0 : M E = testStmt (K 1) (L 0) E')
    (Mp : Fin n → Pauli) (c : Bool) (Q : ∀ r, List (G r)) :
    ∀ (l : List (PauliString n × PauliString n)) (Acc : PauliString n) (r : MS ε)
      (B : Kb → List Bool) (rest2 : List Bool),
      xInv K Mp Acc r B → B (K 1) = (l.map fun a => (encPS a.1).reverse).flatten →
      B (K 2) = (l.map fun a => (encPS a.2).reverse).flatten ++ rest2 →
      Reach M ⟨some E, ((none, none, c), r), mk B Q⟩
        ⟨some E', ((none, none, c), { r with cp := (xFold Mp l Acc).phase }),
          mk (Function.update (Function.update (Function.update B (K 1) []) (K 2) rest2) (K 5)
            (mmask (xFold Mp l Acc).ops)) Q⟩ (l.length * (14 * n + 16 + 1) + 1) := by
  intro l
  induction l with
  | nil =>
    intro Acc r B rest2 hI hX1 hX2
    have es : ({ r with cp := (xFold Mp [] Acc).phase } : MS ε) = r := by
      simp only [xFold, List.foldl_nil]; rw [← hI.2.2.1]
    have e : Function.update (Function.update (Function.update B (K 1) []) (K 2) rest2) (K 5)
        (mmask (xFold Mp [] Acc).ops) = B := by
      have h5 := hI.2.2.2.2.2.2
      funext k
      simp only [Function.update_apply, xFold, List.foldl_nil]
      split_ifs <;> simp_all
    rw [es, e]
    exact (test_none M (K 1) E (L 0) E' hM0 r c Q B (by simpa using hX1)).mono (by simp)
  | cons a l ih =>
    intro Acc r B rest2 hI hX1 hX2
    obtain ⟨x, A, hxA⟩ : ∃ x A, (encPS a.1).reverse = x :: A := by
      cases h : (encPS a.1).reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp h) (encPS_ne a.1)
      | cons x A => exact ⟨x, A, rfl⟩
    have h1 := test_some M (K 1) E (L 0) E' hM0 r c Q B x
      (A ++ (l.map fun a => (encPS a.1).reverse).flatten) (by rw [hX1]; simp [hxA])
    have h2 := x_row M K hK L E hP Mp c Q Acc a r B ((l.map fun a => (encPS a.1).reverse).flatten)
      ((l.map fun a => (encPS a.2).reverse).flatten ++ rest2) hI (by rw [hX1]; simp)
      (by rw [hX2]; simp)
    obtain ⟨han, hmu, hcp, hb, hZ, hT, hcap⟩ := hI
    have hI' : xInv K Mp (xAcc Mp a Acc) { r with cp := (xAcc Mp a Acc).phase }
        (Function.update (Function.update (Function.update B (K 1)
          ((l.map fun a => (encPS a.1).reverse).flatten)) (K 2)
          ((l.map fun a => (encPS a.2).reverse).flatten ++ rest2)) (K 5) (mmask (xAcc Mp a Acc).ops)) := by
      refine ⟨han, hmu, rfl, ?_, ?_, ?_, ?_⟩ <;>
        simp [Function.update_apply, hK.eq_iff, hb, hZ, hT]
    have h3 := ih (xAcc Mp a Acc) _ _ rest2 hI'
      (by simp [Function.update_apply, hK.eq_iff])
      (by simp [Function.update_apply, hK.eq_iff])
    refine ((h1.trans (h2.trans h3)).mono ?_).of_eq ?_
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · congr 2
      funext k
      simp only [Function.update_apply, xFold, List.foldl_cons]
      split_ifs <;> simp_all [hK.eq_iff]

/-- the identity Pauli string (same as the matrix side's `oneP`) -/
def oneK (n : ℕ) : PauliString n := ⟨0, fun _ => .I⟩

lemma oneK_mul {n : ℕ} (P : PauliString n) : (oneK n).mul P = P := by
  have h : ∀ x : Pauli, Pauli.mul .I x = (0, x) := by intro x; cases x <;> rfl
  obtain ⟨ph, ops⟩ := P
  simp [PauliString.mul, oneK, h]

lemma xFold_rev {n : ℕ} (Mp : Fin n → Pauli) :
    ∀ (l : List (PauliString n × PauliString n)) (Acc : PauliString n),
      xFold Mp l.reverse Acc =
        (l.map fun a => if antiK a.1 Mp then a.2 else oneK n).foldr PauliString.mul Acc := by
  intro l
  induction l with
  | nil => intro Acc; rfl
  | cons a l ih =>
    intro Acc
    unfold xFold at ih ⊢
    rw [List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.foldr_cons]
    cases h : antiK a.1 Mp <;> simp [xAcc, h, oneK_mul]

theorem xFold_closed {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) (Acc : PauliString n) :
    xFold Mp (List.ofFn fun i => (D i, T i)).reverse Acc =
      (List.ofFn fun i => if antiK (D i) Mp then T i else oneK n).foldr PauliString.mul Acc := by
  rw [xFold_rev, List.map_ofFn]; rfl

lemma xIn1 {n : ℕ} (T D : Tableau n) :
    (((List.ofFn fun i => (D i, T i)).reverse).map fun a => (encPS a.1).reverse).flatten =
      (encodeTableau D).reverse := by
  rw [encodeTableau_rev]
  simp [List.map_reverse, List.map_ofFn, Function.comp_def]

lemma xIn2 {n : ℕ} (T D : Tableau n) :
    (((List.ofFn fun i => (D i, T i)).reverse).map fun a => (encPS a.2).reverse).flatten =
      (encodeTableau T).reverse := by
  rw [encodeTableau_rev]
  simp [List.map_reverse, List.map_ofFn, Function.comp_def]

end XPass

end OCRS19TM

namespace OCRS19TM

section RandMeas

open QAlgorithms.Stabilizer

variable {ε : Type} {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ : Type}

/-- random measurement on (T, D): T pass, move the selection bits, reset `fd`, D pass -/
structure RandProg (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K K' : Fin 8 → Kb) (L : Fin 20 → Λ)
    (LD : Fin 16 → Λ) (E1 E2 E3 ED E4 Eb EX : Λ) : Prop where
  meas : MeasProg M K L E1
  t1 : M E1 = testStmt (K 1) (L 0) Eb
  br : M Eb = dispStmt (fun r : MS ε => r.fd) (fun _ => true) id id id E2 E2 EX
  mvS : M E2 = mvStmt (K 7) (K' 7) E2 E3
  rst : M E3 = dispStmt (fun _ : MS ε => false) (fun _ => false) id id (fun r => { r with fd := false }) ED ED ED
  dprog : DProg M K' LD ED
  t2 : M ED = testStmt (K' 1) (LD 0) E4
  s0 : K' 0 = K 0
  s3 : K' 3 = K 3
  s4 : K' 4 = K 4
  s5 : K' 5 = K 5
  s6 : K' 6 = K 6

theorem rand_meas {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K K' : Fin 8 → Kb)
    (hK : Function.Injective K) (hK' : Function.Injective K')
    (hK'1 : ∀ i, K' 1 ≠ K i) (hK'2 : ∀ i, K' 2 ≠ K i) (hK'7 : ∀ i, K' 7 ≠ K i)
    (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (E1 E2 E3 ED E4 Eb EX : Λ) (hP : RandProg M K K' L LD E1 E2 E3 ED E4 Eb EX)
    (T D : Tableau n) (Mp : Fin n → Pauli) (p : Fin n) (hp : lastK T Mp = some p)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (hB : B (K 0) = mmask Mp ∧ B (K 3) = [] ∧ B (K 4) = [] ∧ B (K 6) = [] ∧ B (K 5) = [] ∧
      B (K 7) = [] ∧ B (K' 7) = [])
    (hX : B (K 1) = (encodeTableau T).reverse) (hXD : B (K' 1) = (encodeTableau D).reverse) :
    ∃ B' : Kb → List Bool, Reach M ⟨some E1, ((none, none, c), r), mk B Q⟩
        ⟨some E4, ((none, none, c), { r with cp := (T p).phase }), mk B' Q⟩
        ((n * (10 * n + 12 + 1) + 1) + (1 + ((n + 1) + (1 + (n * (10 * n + 16 + 1) + 1))))) ∧
      B' (K 2) = encodeTableau (updMK T Mp p r.cb) ++ B (K 2) ∧
      B' (K' 2) = encodeTableau (updDMK T D Mp p) ++ B (K' 2) ∧
      B' (K 1) = [] ∧ B' (K' 1) = [] ∧ B' (K 7) = [] ∧ B' (K' 7) = [] ∧
      B' (K 0) = mmask Mp ∧ B' (K 3) = [] ∧ B' (K 4) = [] ∧ B' (K 6) = [] ∧
      B' (K 5) = mmask (T p).ops ∧
      ∀ k, (∀ i, k ≠ K i) → (∀ i, k ≠ K' i) → B' k = B k := by
  obtain ⟨hran, hrmu, hrfd⟩ := hr
  obtain ⟨hb0, hb3, hb4, hb6, hb5, hb7, hb7'⟩ := hB
  have n1 : ∀ i, K i ≠ K' 1 := fun i h => hK'1 i h.symm
  have n2 : ∀ i, K i ≠ K' 2 := fun i h => hK'2 i h.symm
  have n7 : ∀ i, K i ≠ K' 7 := fun i h => hK'7 i h.symm
  obtain ⟨B1, hR1, b1, b2, b5, b7, b0, b3, b4, b6, bfr⟩ :=
    meas_pass_meas M K hK L E1 Eb hP.meas hP.t1 T Mp p hp c Q r B ⟨hran, hrmu, hrfd⟩
      ⟨hb0, hb3, hb4, hb6, hb5⟩ hX
  have f1 : B1 (K' 1) = B (K' 1) := bfr _ (hK'1 1) (hK'2 1 |> fun _ => hK'1 2) (hK'1 5) (hK'1 7)
  have f2 : B1 (K' 2) = B (K' 2) := bfr _ (hK'2 1) (hK'2 2) (hK'2 5) (hK'2 7)
  have f7 : B1 (K' 7) = B (K' 7) := bfr _ (hK'7 1) (hK'7 2) (hK'7 5) (hK'7 7)
  have hR2 := mv_run M (K 7) (K' 7) (n7 7) E2 E3 hP.mvS { r with fd := true, cp := (T p).phase } c Q
    (List.ofFn fun j => decide (j = p)) B1 (by rw [b7, hb7, List.append_nil])
  set B2 := Function.update (Function.update B1 (K 7) []) (K' 7)
    ((List.ofFn fun j => decide (j = p)).reverse ++ B1 (K' 7)) with hB2
  have hR3 : Reach M ⟨some E3, ((none, none, c), { r with fd := true, cp := (T p).phase }), mk B2 Q⟩
      ⟨some ED, ((none, none, c), { r with cp := (T p).phase }), mk B2 Q⟩ 1 := by
    refine (disp_step3 M (fun _ : MS ε => false) (fun _ => false) id id (fun r : MS ε => { r with fd := false })
      ED ED ED E3 hP.rst c { r with fd := true, cp := (T p).phase } (mk B2 Q) rfl).of_eq ?_
    simp only [TM2.Cfg.mk.injEq, Prod.mk.injEq, true_and, and_true]
    obtain ⟨an, mu, fd, cp, cb, ext⟩ := r
    simp only at hrfd; subst hrfd; rfl
  have hI : dInv K' Mp (T p) { r with cp := (T p).phase } B2 := by
    refine ⟨hran, hrfd, hrmu, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hB2, hP.s0, hP.s3, hP.s4, hP.s5, hP.s6, Function.update_apply, hK.eq_iff, n7, b0, b3, b4,
        b6, b5]
  have hR4 := d_pass M K' hK' LD ED E4 hP.dprog hP.t2 Mp c Q (T p)
    (List.ofFn fun i => (D i, decide (i = p))).reverse { r with cp := (T p).phase } B2 [] hI
    (by rw [dIn_X]; simp [hB2, Function.update_apply, hK'.eq_iff, n1, f1, hXD, hK'1])
    (by rw [dIn_S]; simp [hB2, Function.update_apply, f7, hb7'])
  have hRb := disp_step1 M (fun r : MS ε => r.fd) (fun _ => true) id id id E2 E2 EX Eb hP.br c
    { r with fd := true, cp := (T p).phase } (mk B1 Q) rfl rfl
  refine ⟨_, (hR1.trans (hRb.trans (hR2.trans (hR3.trans hR4)))).mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7, b2]
  · rw [dOut_closed]
    simp [hB2, Function.update_apply, hK'.eq_iff, n7, f2, hK'2]
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7, b1]
  · simp [Function.update_apply, hK'.eq_iff]
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7]
  · simp [Function.update_apply, hK'.eq_iff]
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7, b0]
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7, b3]
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7, b4]
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7, b6]
  · simp [hB2, Function.update_apply, hK.eq_iff, n1, n2, n7, b5]
  · intro k hk hk'
    have e1 := hk' 1
    have e2 := hk' 2
    have e7 := hk' 7
    have e7' := hk 7
    simp [hB2, Function.update_apply, e1, e2, e7, e7', bfr k (hk 1) (hk 2) (hk 5) (hk 7)]

end RandMeas

end OCRS19TM

namespace OCRS19TM

section DetMeas

open QAlgorithms.Stabilizer

variable {ε : Type} {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- Bool copy `a → b` and `f`-image `a → c` (both reversed) -/
def dupFStmt (a b c : Kb) (f : Bool → Bool) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.push (Sum.inl b) (fun v => v.1.1.getD false)
        (TM2.Stmt.push (Sum.inl c) (fun v => f (v.1.1.getD false))
          (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L)))))

lemma dupF_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b c : Kb) (f : Bool → Bool)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (L E : Λ)
    (hM : M L = dupFStmt a b c f L E) (r : ρ) (cr : Bool) (Q : ∀ r, List (G r)) :
    ∀ (A : List Bool) (B : Kb → List Bool), B a = A →
      Reach M ⟨some L, ((none, none, cr), r), mk B Q⟩
        ⟨some E, ((none, none, cr), r),
          mk (Function.update (Function.update (Function.update B a []) b (A.reverse ++ B b)) c
            ((A.map f).reverse ++ B c)) Q⟩ (A.length + 1) := by
  intro A
  induction A with
  | nil =>
    intro B hA
    apply (Reach.single _).mono (by simp)
    have e : Function.update (Function.update (Function.update B a []) b ([].reverse ++ B b)) c
        (([].map f).reverse ++ B c) = B := by
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
    simp only [TM2.step, hM, dupFStmt, TM2.stepAux, mk_inl, hA, List.head?_nil, List.tail_nil,
      Option.isNone_none, cond_true, e, update_mk]
    all_goals (rw [(Function.update_eq_self_iff).mpr hA.symm])
  | cons x A ih =>
    intro B hA
    have := ih (Function.update (Function.update (Function.update B a A) b (x :: B b)) c
      (f x :: B c)) (by simp [Function.update_apply, hab, hac])
    refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by simp)
    · simp only [TM2.step, hM, dupFStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
        Option.isNone_some, cond_false, Option.getD_some, update_mk,
        Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
        Function.update_of_ne hbc.symm]
      all_goals try rfl
    · congr 2
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all

/-! existential wrappers: result stacks described by values + frame -/

lemma mvE (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b : Kb) (hab : a ≠ b) (L E : Λ)
    (hM : M L = mvStmt a b L E) (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = A) :
    ∃ B' : Kb → List Bool, Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r), mk B' Q⟩ (A.length + 1) ∧
      B' a = [] ∧ B' b = A.reverse ++ B b ∧ ∀ k, k ≠ a → k ≠ b → B' k = B k :=
  ⟨_, mv_run M a b hab L E hM r c Q A B hA, by simp [Function.update_apply, hab], by simp,
    fun k h1 h2 => by simp [Function.update_apply, h1, h2]⟩

lemma dupFE (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b c : Kb) (f : Bool → Bool)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (L E : Λ)
    (hM : M L = dupFStmt a b c f L E) (r : ρ) (cr : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = A) :
    ∃ B' : Kb → List Bool, Reach M ⟨some L, ((none, none, cr), r), mk B Q⟩
        ⟨some E, ((none, none, cr), r), mk B' Q⟩ (A.length + 1) ∧
      B' a = [] ∧ B' b = A.reverse ++ B b ∧ B' c = (A.map f).reverse ++ B c ∧
      ∀ k, k ≠ a → k ≠ b → k ≠ c → B' k = B k :=
  ⟨_, dupF_run M a b c f hab hac hbc L E hM r cr Q A B hA,
    by simp [Function.update_apply, hab, hac], by simp [Function.update_apply, hbc],
    by simp, fun k h1 h2 h3 => by simp [Function.update_apply, h1, h2, h3]⟩

lemma dupE (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b c : Kb)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (L E : Λ)
    (hM : M L = dupStmt a b c L E) (r : ρ) (cr : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = A) :
    ∃ B' : Kb → List Bool, Reach M ⟨some L, ((none, none, cr), r), mk B Q⟩
        ⟨some E, ((none, none, cr), r), mk B' Q⟩ (A.length + 1) ∧
      B' a = [] ∧ B' b = A.reverse ++ B b ∧ B' c = A.reverse ++ B c ∧
      ∀ k, k ≠ a → k ≠ b → k ≠ c → B' k = B k :=
  ⟨_, dup_run M a b c hab hac hbc L E hM r cr Q A B hA,
    by simp [Function.update_apply, hab, hac], by simp [Function.update_apply, hbc],
    by simp, fun k h1 h2 h3 => by simp [Function.update_apply, h1, h2, h3]⟩

lemma clearE (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (a : Kb) (L E : Λ)
    (hM : M L = clearStmt a L E) (r : MS ε) (c : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = A) :
    ∃ B' : Kb → List Bool, Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r), mk B' Q⟩ (A.length + 1) ∧
      B' a = [] ∧ ∀ k, k ≠ a → B' k = B k :=
  ⟨_, clear_run' M a L E hM r c Q A B hA, by simp, fun k h1 => by simp [Function.update_apply, h1]⟩

lemma mmask_oneK {n : ℕ} (Mp : Fin n → Pauli) :
    mmask (oneK n).ops = (mmask Mp).map fun _ => false := by
  have h1 : mmask (oneK n).ops = List.replicate (2 * n) false := by
    rw [List.eq_replicate_iff]
    refine ⟨mmask_length _, ?_⟩
    intro b hb
    simp [mmask, oneK, encPauli] at hb
    exact hb.2
  rw [h1, List.map_const', mmask_length]

/-- deterministic-measurement tail (after the T pass found no anticommuting row):
clear Sel, copy D and T (kept on K'2 / K2 forward), build Acc = 1, run the X pass, clear Acc -/
structure DetProg (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K K' KX : Fin 8 → Kb)
    (LX : Fin 17 → Λ) (LT : Fin 11 → Λ) (E4 : Λ) : Prop where
  xp : XProg M KX LX (LT 9)
  c7 : M (LT 0) = clearStmt (K 7) (LT 0) (LT 1)
  m1 : M (LT 1) = mvStmt (K' 1) (K' 2) (LT 1) (LT 2)
  d1 : M (LT 2) = dupStmt (K' 2) (KX 1) (K' 1) (LT 2) (LT 3)
  m2 : M (LT 3) = mvStmt (K' 1) (K' 2) (LT 3) (LT 4)
  d2 : M (LT 4) = dupStmt (K 2) (KX 2) (K 1) (LT 4) (LT 5)
  m3 : M (LT 5) = mvStmt (K 1) (K 2) (LT 5) (LT 6)
  m4 : M (LT 6) = mvStmt (K 0) (K 6) (LT 6) (LT 7)
  z : M (LT 7) = dupFStmt (K 6) (K 0) (K 5) (fun _ => false) (LT 7) (LT 8)
  c0 : M (LT 8) = dispStmt (fun _ : MS ε => false) (fun _ => false) id id
    (fun r => { r with cp := 0 }) (LT 9) (LT 9) (LT 9)
  t : M (LT 9) = testStmt (KX 1) (LX 0) (LT 10)
  c5 : M (LT 10) = clearStmt (K 5) (LT 10) E4
  s0 : KX 0 = K 0
  s3 : KX 3 = K 3
  s5 : KX 5 = K 5
  s6 : KX 6 = K 6

theorem det_tail {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K K' KX : Fin 8 → Kb)
    (hK : Function.Injective K) (hK' : Function.Injective K') (hKX : Function.Injective KX)
    (hK'1 : ∀ i, K' 1 ≠ K i) (hK'2 : ∀ i, K' 2 ≠ K i)
    (hX1 : ∀ i, KX 1 ≠ K i) (hX2 : ∀ i, KX 2 ≠ K i) (hX1' : ∀ i, KX 1 ≠ K' i)
    (hX2' : ∀ i, KX 2 ≠ K' i)
    (LX : Fin 17 → Λ) (LT : Fin 11 → Λ) (E4 : Λ) (hP : DetProg M K K' KX LX LT E4)
    (T D : Tableau n) (Mp : Fin n → Pauli)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.mu = (0, none))
    (hB : B (K 0) = mmask Mp ∧ B (K 1) = [] ∧ B (K 3) = [] ∧ B (K 6) = [] ∧ B (K 5) = [] ∧
      B (K' 2) = [] ∧ B (KX 1) = [] ∧ B (KX 2) = [])
    (h7 : B (K 7) = List.ofFn fun _ : Fin n => false)
    (hT : B (K 2) = encodeTableau T) (hD : B (K' 1) = (encodeTableau D).reverse) :
    ∃ B' : Kb → List Bool, Reach M ⟨some (LT 0), ((none, none, c), r), mk B Q⟩
        ⟨some E4, ((none, none, c), { r with cp := ((List.ofFn fun i =>
          if antiK (D i) Mp then T i else oneK n).foldr PauliString.mul (oneK n)).phase }), mk B' Q⟩
        (3 * (encodeTableau D).length + 2 * (encodeTableau T).length + n * (14 * n + 17) + 7 * n + 12) ∧
      B' (K 2) = encodeTableau T ∧ B' (K' 2) = encodeTableau D ∧ B' (K 1) = [] ∧ B' (K' 1) = [] ∧
      B' (K 7) = [] ∧ B' (K 5) = [] ∧ B' (KX 1) = [] ∧ B' (KX 2) = [] ∧ B' (K 0) = mmask Mp ∧
      B' (K 3) = [] ∧ B' (K 6) = [] ∧
      ∀ k, k ≠ K 0 → k ≠ K 1 → k ≠ K 2 → k ≠ K 5 → k ≠ K 6 → k ≠ K 7 → k ≠ K' 1 → k ≠ K' 2 →
        k ≠ KX 1 → k ≠ KX 2 → B' k = B k := by
  obtain ⟨han, hmu⟩ := hr
  obtain ⟨b0, b1, b3, b6, b5, b2', bx1, bx2⟩ := hB
  have nK : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  have nK' : ∀ i j : Fin 8, i ≠ j → K' i ≠ K' j := fun i j h e => h (hK' e)
  have x12 : KX 1 ≠ KX 2 := fun e => absurd (hKX e) (by decide)
  have k12 : K' 1 ≠ K' 2 := nK' 1 2 (by decide)
  -- 1. clear Sel
  obtain ⟨B1, R1, c1, f1⟩ := clearE M (K 7) (LT 0) (LT 1) hP.c7 r c Q _ B h7
  -- 2-4. D: forward on K'2, reversed copy on KX 1
  obtain ⟨B2, R2, m2a, m2b, f2⟩ := mvE M (K' 1) (K' 2) k12 (LT 1) (LT 2) hP.m1 r c Q _ B1
    (by rw [f1 _ (hK'1 7), hD])
  have e2 : B2 (K' 2) = encodeTableau D := by
    rw [m2b, f1 _ (hK'2 7), b2', List.reverse_reverse, List.append_nil]
  obtain ⟨B3, R3, d3a, d3b, d3c, f3⟩ := dupE M (K' 2) (KX 1) (K' 1) (fun e => hX1' 2 e.symm)
    (Ne.symm k12) (hX1' 1) (LT 2) (LT 3) hP.d1 r c Q _ B2 e2
  obtain ⟨B4, R4, m4a, m4b, f4⟩ := mvE M (K' 1) (K' 2) k12 (LT 3) (LT 4) hP.m2 r c Q _ B3
    (by rw [d3c, m2a, List.append_nil])
  have e4 : B4 (K' 2) = encodeTableau D := by rw [m4b, d3a, List.reverse_reverse, List.append_nil]
  -- 5-6. T: forward on K2, reversed copy on KX 2
  have g4 : ∀ k, k ≠ K' 1 → k ≠ K' 2 → k ≠ KX 1 → k ≠ K 7 → B4 k = B k := fun k h1 h2 h3 h4 => by
    rw [f4 k h1 h2, f3 k h2 h3 h1, f2 k h1 h2, f1 k h4]
  obtain ⟨B5, R5, d5a, d5b, d5c, f5⟩ := dupE M (K 2) (KX 2) (K 1) (fun e => hX2 2 e.symm)
    (nK 2 1 (by decide)) (hX2 1) (LT 4) (LT 5) hP.d2 r c Q _ B4
    (by rw [g4 _ (fun e => hK'1 2 e.symm) (fun e => hK'2 2 e.symm) (fun e => hX1 2 e.symm)
      (nK 2 7 (by decide)), hT])
  obtain ⟨B6, R6, m6a, m6b, f6⟩ := mvE M (K 1) (K 2) (nK 1 2 (by decide)) (LT 5) (LT 6) hP.m3 r c Q _
    B5 (by rw [d5c, g4 _ (fun e => hK'1 1 e.symm) (fun e => hK'2 1 e.symm) (fun e => hX1 1 e.symm)
      (nK 1 7 (by decide)), b1, List.append_nil])
  -- 7-8. Acc mask = 2n falses on K5, mask restored on K0
  have g6 : ∀ k, k ≠ K' 1 → k ≠ K' 2 → k ≠ KX 1 → k ≠ K 7 → k ≠ K 1 → k ≠ K 2 → k ≠ KX 2 →
      B6 k = B k := fun k h1 h2 h3 h4 h5 h6 h7 => by
    rw [f6 k h5 h6, f5 k h6 h7 h5, g4 k h1 h2 h3 h4]
  have nn : ∀ i : Fin 8, i ≠ 1 → i ≠ 2 → i ≠ 7 → ∀ k, k = K i → k ≠ K' 1 ∧ k ≠ K' 2 ∧ k ≠ KX 1 ∧
      k ≠ K 7 ∧ k ≠ K 1 ∧ k ≠ K 2 ∧ k ≠ KX 2 := by
    intro i h1 h2 h7 k hk; subst hk
    exact ⟨fun e => hK'1 i e.symm, fun e => hK'2 i e.symm, fun e => hX1 i e.symm,
      nK i 7 h7, nK i 1 h1, nK i 2 h2, fun e => hX2 i e.symm⟩
  have g0 := nn 0 (by decide) (by decide) (by decide) _ rfl
  have g3 := nn 3 (by decide) (by decide) (by decide) _ rfl
  have g5 := nn 5 (by decide) (by decide) (by decide) _ rfl
  have g6' := nn 6 (by decide) (by decide) (by decide) _ rfl
  obtain ⟨B7, R7, m7a, m7b, f7⟩ := mvE M (K 0) (K 6) (nK 0 6 (by decide)) (LT 6) (LT 7) hP.m4 r c Q _
    B6 (by rw [g6 _ g0.1 g0.2.1 g0.2.2.1 g0.2.2.2.1 g0.2.2.2.2.1 g0.2.2.2.2.2.1 g0.2.2.2.2.2.2, b0])
  have e7 : B7 (K 6) = (mmask Mp).reverse := by
    rw [m7b, g6 _ g6'.1 g6'.2.1 g6'.2.2.1 g6'.2.2.2.1 g6'.2.2.2.2.1 g6'.2.2.2.2.2.1 g6'.2.2.2.2.2.2, b6,
      List.append_nil]
  obtain ⟨B8, R8, z8a, z8b, z8c, f8⟩ := dupFE M (K 6) (K 0) (K 5) (fun _ => false) (nK 6 0 (by decide))
    (nK 6 5 (by decide)) (nK 0 5 (by decide)) (LT 7) (LT 8) hP.z r c Q _ B7 e7
  have R9 := disp_step3 M (fun _ : MS ε => false) (fun _ => false) id id
    (fun r : MS ε => { r with cp := 0 }) (LT 9) (LT 9) (LT 9) (LT 8) hP.c0 c r (mk B8 Q) rfl
  -- 9. X pass
  have hI : xInv KX Mp (oneK n) { r with cp := 0 } B8 := by
    refine ⟨han, hmu, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hP.s0, z8b, List.reverse_reverse, m7a, List.append_nil]
    · rw [hP.s3, f8 _ (nK 3 6 (by decide)) (nK 3 0 (by decide)) (nK 3 5 (by decide)),
        f7 _ (nK 3 0 (by decide)) (nK 3 6 (by decide)),
        g6 _ g3.1 g3.2.1 g3.2.2.1 g3.2.2.2.1 g3.2.2.2.2.1 g3.2.2.2.2.2.1 g3.2.2.2.2.2.2, b3]
    · rw [hP.s6, z8a]
    · rw [hP.s5, z8c, f7 _ (nK 5 0 (by decide)) (nK 5 6 (by decide)),
        g6 _ g5.1 g5.2.1 g5.2.2.1 g5.2.2.2.1 g5.2.2.2.2.1 g5.2.2.2.2.2.1 g5.2.2.2.2.2.2, b5,
        List.append_nil, List.map_reverse, List.reverse_reverse, mmask_oneK Mp]
  have ex1 : B8 (KX 1) = [] ++ (encodeTableau D).reverse := by
    rw [f8 _ (hX1 6) (hX1 0) (hX1 5), f7 _ (hX1 0) (hX1 6), f6 _ (hX1 1) (hX1 2),
      f5 _ (hX1 2) x12 (hX1 1), f4 _ (hX1' 1) (hX1' 2), d3b, f2 _ (hX1' 1) (hX1' 2),
      f1 _ (hX1 7), bx1, List.append_nil, List.nil_append]
  have ex2 : B8 (KX 2) = (encodeTableau T).reverse ++ [] := by
    rw [f8 _ (hX2 6) (hX2 0) (hX2 5), f7 _ (hX2 0) (hX2 6), f6 _ (hX2 1) (hX2 2), d5b,
      g4 _ (hX2' 1) (hX2' 2) (Ne.symm x12) (hX2 7), bx2]
  have R10 := x_pass M KX hKX LX (LT 9) (LT 10) hP.xp hP.t Mp c Q
    (List.ofFn fun i => (D i, T i)).reverse (oneK n) { r with cp := 0 } B8 []
    hI (by rw [xIn1]; simpa using ex1) (by rw [xIn2]; exact ex2)
  rw [xFold_closed] at R10
  set P := (List.ofFn fun i => if antiK (D i) Mp then T i else oneK n).foldr PauliString.mul (oneK n)
    with hPdef
  set B9 := Function.update (Function.update (Function.update B8 (KX 1) []) (KX 2) []) (KX 5)
    (mmask P.ops) with hB9
  -- 10. clear Acc
  obtain ⟨B11, R11, c11, f11⟩ := clearE M (K 5) (LT 10) E4 hP.c5 { r with cp := P.phase } c Q (mmask P.ops) B9
    (by simp [hB9, ← hP.s5])
  have f9 : ∀ k, k ≠ KX 1 → k ≠ KX 2 → k ≠ K 5 → B9 k = B8 k := fun k h1 h2 h3 => by
    rw [hB9, ← hP.s5] at *; simp [Function.update_apply, h1, h2, h3]
  have ff : ∀ k, k ≠ KX 1 → k ≠ KX 2 → k ≠ K 5 → k ≠ K 6 → k ≠ K 0 → B11 k = B7 k :=
    fun k h1 h2 h3 h4 h5 => by rw [f11 k h3, f9 k h1 h2 h3, f8 k h4 h5 h3]
  refine ⟨B11, ((R1.trans (R2.trans (R3.trans (R4.trans (R5.trans (R6.trans (R7.trans (R8.trans
    (R9.trans (R10.trans R11)))))))))).mono ?_), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_reverse, List.length_ofFn, List.length_map, mmask_length]
    nlinarith
  · rw [ff _ (fun e => hX1 2 e.symm) (fun e => hX2 2 e.symm) (nK 2 5 (by decide)) (nK 2 6 (by decide))
      (nK 2 0 (by decide)), f7 _ (nK 2 0 (by decide)) (nK 2 6 (by decide)), m6b, d5a, List.reverse_reverse,
      List.append_nil]
  · rw [ff _ (fun e => hX1' 2 e.symm) (fun e => hX2' 2 e.symm) (hK'2 5) (hK'2 6) (hK'2 0),
      f7 _ (hK'2 0) (hK'2 6), f6 _ (hK'2 1) (hK'2 2), f5 _ (hK'2 2) (fun e => hX2' 2 e.symm) (hK'2 1), e4]
  · rw [ff _ (fun e => hX1 1 e.symm) (fun e => hX2 1 e.symm) (nK 1 5 (by decide)) (nK 1 6 (by decide))
      (nK 1 0 (by decide)), f7 _ (nK 1 0 (by decide)) (nK 1 6 (by decide)), m6a]
  · rw [ff _ (fun e => hX1' 1 e.symm) (fun e => hX2' 1 e.symm) (hK'1 5) (hK'1 6) (hK'1 0),
      f7 _ (hK'1 0) (hK'1 6), f6 _ (hK'1 1) (hK'1 2), f5 _ (hK'1 2) (fun e => hX2' 1 e.symm) (hK'1 1), m4a]
  · rw [ff _ (fun e => hX1 7 e.symm) (fun e => hX2 7 e.symm) (nK 7 5 (by decide)) (nK 7 6 (by decide))
      (nK 7 0 (by decide)), f7 _ (nK 7 0 (by decide)) (nK 7 6 (by decide)),
      f6 _ (nK 7 1 (by decide)) (nK 7 2 (by decide)), f5 _ (nK 7 2 (by decide))
      (fun e => hX2 7 e.symm) (nK 7 1 (by decide)), f4 _ (fun e => hK'1 7 e.symm) (fun e => hK'2 7 e.symm),
      f3 _ (fun e => hK'2 7 e.symm) (fun e => hX1 7 e.symm) (fun e => hK'1 7 e.symm),
      f2 _ (fun e => hK'1 7 e.symm) (fun e => hK'2 7 e.symm), c1]
  · exact c11
  · rw [f11 _ (hX1 5), hB9]; simp [Function.update_apply, x12, hKX.ne (show (1 : Fin 8) ≠ 5 by decide)]
  · rw [f11 _ (hX2 5), hB9]; simp [Function.update_apply, x12, hKX.ne (show (2 : Fin 8) ≠ 5 by decide)]
  · rw [f11 _ (nK 0 5 (by decide)), f9 _ (fun e => hX1 0 e.symm) (fun e => hX2 0 e.symm)
      (nK 0 5 (by decide)), z8b, List.reverse_reverse, m7a, List.append_nil]
  · rw [f11 _ (nK 3 5 (by decide)), f9 _ (fun e => hX1 3 e.symm) (fun e => hX2 3 e.symm)
      (nK 3 5 (by decide)), f8 _ (nK 3 6 (by decide)) (nK 3 0 (by decide)) (nK 3 5 (by decide)),
      f7 _ (nK 3 0 (by decide)) (nK 3 6 (by decide)),
      g6 _ g3.1 g3.2.1 g3.2.2.1 g3.2.2.2.1 g3.2.2.2.2.1 g3.2.2.2.2.2.1 g3.2.2.2.2.2.2, b3]
  · rw [f11 _ (nK 6 5 (by decide)), f9 _ (fun e => hX1 6 e.symm) (fun e => hX2 6 e.symm)
      (nK 6 5 (by decide)), z8a]
  · intro k h0 h1 h2 h5 h6 h7 h1' h2' hx1 hx2
    rw [ff k hx1 hx2 h5 h6 h0, f7 k h0 h6, g6 k h1' h2' hx1 h7 h1 h2 hx2]

/-- deterministic measurement on (T, D) in one Reach: T pass, branch on `fd`, tail -/
theorem det_meas {n : ℕ} (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K K' KX : Fin 8 → Kb)
    (hK : Function.Injective K) (hK' : Function.Injective K') (hKX : Function.Injective KX)
    (hK'1 : ∀ i, K' 1 ≠ K i) (hK'2 : ∀ i, K' 2 ≠ K i)
    (hX1 : ∀ i, KX 1 ≠ K i) (hX2 : ∀ i, KX 2 ≠ K i) (hX1' : ∀ i, KX 1 ≠ K' i)
    (hX2' : ∀ i, KX 2 ≠ K' i)
    (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (E1 E2 E3 ED E4 Eb : Λ) (LX : Fin 17 → Λ) (LT : Fin 11 → Λ)
    (E5 : Λ) (hP : RandProg M K K' L LD E1 E2 E3 ED E4 Eb (LT 0)) (hQ : DetProg M K K' KX LX LT E5)
    (T D : Tableau n) (Mp : Fin n → Pauli) (hp : lastK T Mp = none)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (hB : B (K 0) = mmask Mp ∧ B (K 3) = [] ∧ B (K 4) = [] ∧ B (K 6) = [] ∧ B (K 5) = [] ∧
      B (K 7) = [] ∧ B (K 2) = [] ∧ B (K' 2) = [] ∧ B (KX 1) = [] ∧ B (KX 2) = [])
    (hX : B (K 1) = (encodeTableau T).reverse) (hXD : B (K' 1) = (encodeTableau D).reverse) :
    ∃ B' : Kb → List Bool, Reach M ⟨some E1, ((none, none, c), r), mk B Q⟩
        ⟨some E5, ((none, none, c), { r with cp := ((List.ofFn fun i =>
          if antiK (D i) Mp then T i else oneK n).foldr PauliString.mul (oneK n)).phase }), mk B' Q⟩
        ((n * (10 * n + 12 + 1) + 1) + (1 + (3 * (encodeTableau D).length +
          2 * (encodeTableau T).length + n * (14 * n + 17) + 7 * n + 12))) ∧
      B' (K 2) = encodeTableau T ∧ B' (K' 2) = encodeTableau D ∧ B' (K 1) = [] ∧ B' (K' 1) = [] ∧
      B' (K 7) = [] ∧ B' (K 5) = [] ∧ B' (KX 1) = [] ∧ B' (KX 2) = [] ∧ B' (K 0) = mmask Mp ∧
      B' (K 3) = [] ∧ B' (K 4) = [] ∧ B' (K 6) = [] ∧
      ∀ k, k ≠ K 0 → k ≠ K 1 → k ≠ K 2 → k ≠ K 5 → k ≠ K 6 → k ≠ K 7 → k ≠ K' 1 → k ≠ K' 2 →
        k ≠ KX 1 → k ≠ KX 2 → B' k = B k := by
  obtain ⟨hran, hrmu, hrfd⟩ := hr
  obtain ⟨b0, b3, b4, b6, b5, b7, b2, b2', bx1, bx2⟩ := hB
  obtain ⟨B1, R1, c1, c2, c5, c7, c0, c3, c4, c6, f1⟩ :=
    meas_pass_det M K hK L E1 Eb hP.meas hP.t1 T Mp (oneK n) hp c Q r B ⟨hran, hrfd⟩
      ⟨b0, b3, b4, b6, b5⟩ hX
  have Rb := disp_step3 M (fun r : MS ε => r.fd) (fun _ => true) id id id E2 E2 (LT 0) Eb hP.br c r
    (mk B1 Q) hrfd
  have g : ∀ k, (∀ i : Fin 8, k ≠ K i) → B1 k = B k := fun k hk => f1 k (hk 1) (hk 2) (hk 5) (hk 7)
  obtain ⟨B', R2, d2, d2', d1, d1', d7, d5, dx1, dx2, d0, d3, d6, f2⟩ :=
    det_tail M K K' KX hK hK' hKX hK'1 hK'2 hX1 hX2 hX1' hX2' LX LT E5 hQ T D Mp c Q r B1
      ⟨hran, hrmu⟩
      ⟨c0, c1, c3, c6, c5, by rw [g _ hK'2, b2'], by rw [g _ hX1, bx1], by rw [g _ hX2, bx2]⟩
      (by rw [c7, b7, List.append_nil]) (by rw [c2, b2, List.append_nil]) (by rw [g _ hK'1, hXD])
  have nK : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  refine ⟨B', (R1.trans (Rb.trans R2)).mono le_rfl, d2, d2', d1, d1', d7, d5, dx1, dx2, d0, d3, ?_, d6,
    ?_⟩
  · rw [f2 _ (nK 4 0 (by decide)) (nK 4 1 (by decide)) (nK 4 2 (by decide)) (nK 4 5 (by decide))
      (nK 4 6 (by decide)) (nK 4 7 (by decide)) (fun e => hK'1 4 e.symm) (fun e => hK'2 4 e.symm)
      (fun e => hX1 4 e.symm) (fun e => hX2 4 e.symm), c4]
  · intro k h0 h1 h2 h5 h6 h7 h1' h2' hx1 hx2
    rw [f2 k h0 h1 h2 h5 h6 h7 h1' h2' hx1 hx2, f1 k h1 h2 h5 h7]

end DetMeas

end OCRS19TM

-- ===== session 20: FrontMask (CNOT / 1-wire mask builder from unary counters) =====
namespace OCRS19TM

section FrontMask

open QAlgorithms.Stabilizer

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- mk-level form of `ctl_run`. -/
theorem ctl_mk (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (b a o s : Kb)
    (hba : b ≠ a) (hbo : b ≠ o) (hbs : b ≠ s) (hao : a ≠ o) (has : a ≠ s) (hos : o ≠ s)
    (L E : Λ) (δ : ρ → Option Bool → Bool → ρ) (o1 o2 : ρ → Option Bool → Bool → Option Bool)
    (hM : M L = ctlStmt b a o s L E δ o1 o2) (c : Bool) (r : ρ) (B : Kb → List Bool)
    (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), (ctlOut δ o1 o2 r (B b) (B a)).1),
        mk (Function.update (Function.update (Function.update (Function.update B b [])
          a ((B a).drop (B b).length)) o ((ctlOut δ o1 o2 r (B b) (B a)).2.reverse ++ B o))
          s ((B b).reverse ++ B s)) Q⟩ ((B b).length + 1) := by
  obtain ⟨S1, hR1, h1b, h1a, h1s, h1o, h1r⟩ := ctl_run M b a o s hba hbo hbs hao has hos L E δ o1 o2
    hM c (B b) r (B a) (mk B Q) rfl rfl
  have hS1 : S1 = mk (Function.update (Function.update (Function.update (Function.update B b [])
          a ((B a).drop (B b).length)) o ((ctlOut δ o1 o2 r (B b) (B a)).2.reverse ++ B o))
          s ((B b).reverse ++ B s)) Q := by
    apply mk_ext
    · intro x
      by_cases hxs : x = s
      · subst hxs; simpa [bs] using h1s
      by_cases hxo : x = o
      · subst hxo; simpa [bs, hos] using h1o
      by_cases hxa : x = a
      · subst hxa; simp [hao, has, h1a]
      by_cases hxb : x = b
      · subst hxb; simp [hbo, hbs, hba, h1b]
      rw [h1r (Sum.inl x) (fun e => hxb (Sum.inl_injective e)) (fun e => hxa (Sum.inl_injective e))
        (fun e => hxo (Sum.inl_injective e)) (fun e => hxs (Sum.inl_injective e))]
      simp [Function.update_apply, hxs, hxo, hxa, hxb]
    · intro r'
      rw [h1r (Sum.inr r') (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)
        (fun e => Sum.inl_ne_inr e.symm) (fun e => Sum.inl_ne_inr e.symm)]
      rfl
  subst hS1
  exact hR1

/-- pass 1 (one-hot of `c`): control = `n` unary marks, data = `c` unary marks. -/
def cmδ1 : Bool → Option Bool → Bool → Bool := fun f x _ => f || x.isNone
def cmO1 : Bool → Option Bool → Bool → Option Bool := fun f x _ => some (!f && x.isNone)
def cmNo : Bool → Option Bool → Bool → Option Bool := fun _ _ _ => none
/-- pass 2 (interleave with one-hot of `t`); the flag is inverted (true = not yet fired). -/
def cmδ2 : Bool → Option Bool → Bool → Bool := fun g x _ => g && x.isSome
def cmO2a : Bool → Option Bool → Bool → Option Bool := fun _ _ y => some y
def cmO2b : Bool → Option Bool → Bool → Option Bool := fun g x _ => some (g && x.isNone)

lemma ctlOut_cm1_fired (C : List Bool) : ∀ A : List Bool,
    ctlOut cmδ1 cmO1 cmNo true C A = (true, C.map fun _ => false) := by
  induction C with
  | nil => intro A; rfl
  | cons y C ih => intro A; simp [ctlOut, cmδ1, cmO1, cmNo, ih]

lemma ctlOut_cm1 (n w : ℕ) (hw : w < n) :
    ctlOut cmδ1 cmO1 cmNo false (List.replicate n true) (List.replicate w true) =
      (true, List.ofFn fun q : Fin n => decide (q.val = w)) := by
  induction n generalizing w with
  | zero => omega
  | succ n ih =>
    cases w with
    | zero =>
      simp [List.replicate_succ, ctlOut, cmδ1, cmO1, cmNo, ctlOut_cm1_fired, List.ofFn_succ]
    | succ w =>
      have := ih w (by omega)
      simp [List.replicate_succ, ctlOut, cmδ1, cmO1, cmNo, List.ofFn_succ] at this ⊢
      rw [this]
      simp

lemma ctlOut_cm2_fired (C : List Bool) : ∀ A : List Bool,
    ctlOut cmδ2 cmO2a cmO2b false C A = (false, C.flatMap fun y => [y, false]) := by
  induction C with
  | nil => intro A; rfl
  | cons y C ih => intro A; simp [ctlOut, cmδ2, cmO2a, cmO2b, ih]

lemma ctlOut_cm2 (n t : ℕ) (ht : t < n) (h : Fin n → Bool) :
    ctlOut cmδ2 cmO2a cmO2b true (List.ofFn h) (List.replicate t true) =
      (false, (List.ofFn fun q : Fin n => [h q, decide (q.val = t)]).flatten) := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    cases t with
    | zero =>
      rw [List.ofFn_succ]
      simp only [List.replicate_zero, ctlOut, cmδ2, cmO2a, cmO2b, List.head?_nil, List.tail_nil, Option.isSome_none,
        Option.isNone_none, Bool.and_false, Bool.and_true, ctlOut_cm2_fired]
      rw [List.ofFn_succ, ← ofFn_flatten_flatMap' (fun q : Fin n => h q.succ) (fun y => [y, false])]
      simp
    | succ t =>
      have := ih t (by omega) (fun q => h q.succ)
      rw [List.ofFn_succ]
      simp only [List.replicate_succ, ctlOut, cmδ2, cmO2a, cmO2b, List.head?_cons, List.tail_cons,
        Option.isSome_some, Option.isNone_some, Bool.and_true, Bool.and_false, this]
      rw [List.ofFn_succ]
      simp

lemma cm_emit_rev (n : ℕ) (c t : Fin n) :
    (List.ofFn fun q : Fin n => [decide (q.val = c.val), decide (q.val = t.val)]).flatten.reverse =
      cmaskR n c t := by
  rw [cmaskR, List.reverse_flatten, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun q => ?_)
  simp [Fin.val_inj]

/-- Mask builder: from `n`, `c`, `t` in unary on `K 0`, `K 1`, `K 2`, push `cmaskR n c t` on `K 5`.
The counter `n` ends (as `n` marks) on `K 6`; `K 3`, `K 4`, `K 7` are scratch. -/
theorem cmask_build (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (K : Fin 8 → Kb)
    (hK : Function.Injective K) (L0 L1 L2 L3 E : Λ) (get : ρ → Bool) (set : ρ → Bool → ρ)
    (hgs : ∀ r t, get (set r t) = t) (hss : ∀ r t t', set (set r t) t' = set r t')
    (hsg : ∀ r, set r (get r) = r)
    (hM0 : M L0 = ctlStmt (K 0) (K 1) (K 3) (K 6) L0 L1 (fun r x y => set r (cmδ1 (get r) x y))
      (fun r x y => cmO1 (get r) x y) (fun r x y => cmNo (get r) x y))
    (hM1 : M L1 = mvStmt (K 3) (K 4) L1 L2)
    (hM2 : M L2 = ctlStmt (K 4) (K 2) (K 5) (K 7) L2 L3 (fun r x y => set r (cmδ2 (get r) x y))
      (fun r x y => cmO2a (get r) x y) (fun r x y => cmO2b (get r) x y))
    (hM3 : M L3 = clearStmt (K 7) L3 E)
    {n : ℕ} (cw tw : Fin n) (c : Bool) (r : ρ) (hr : get r = false)
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (h0 : B (K 0) = List.replicate n true) (h1 : B (K 1) = List.replicate cw.val true)
    (h2 : B (K 2) = List.replicate tw.val true) (h3 : B (K 3) = []) (h4 : B (K 4) = [])
    (h7 : B (K 7) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some L0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r), mk B' Q⟩ (4 * n + 4) ∧
      B' (K 5) = cmaskR n cw tw ++ B (K 5) ∧ B' (K 6) = List.replicate n true ++ B (K 6) ∧
      B' (K 0) = [] ∧ B' (K 1) = [] ∧ B' (K 2) = [] ∧ B' (K 3) = [] ∧ B' (K 4) = [] ∧ B' (K 7) = [] ∧
      ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have ne : ∀ i j : Fin 8, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  have e1 := ctlOut_lens get set hgs hss hsg cmδ1 cmO1 cmNo (B (K 0)) (B (K 1)) r
  have e1' : ctlOut cmδ1 cmO1 cmNo false (B (K 0)) (B (K 1)) =
      (true, List.ofFn fun q : Fin n => decide (q.val = cw.val)) := by
    rw [h0, h1]; exact ctlOut_cm1 n cw.val cw.isLt
  rw [hr, e1'] at e1
  have hR1 := ctl_mk M (K 0) (K 1) (K 3) (K 6) (ne 0 1 (by decide)) (ne 0 3 (by decide))
    (ne 0 6 (by decide)) (ne 1 3 (by decide)) (ne 1 6 (by decide)) (ne 3 6 (by decide)) L0 L1 _ _ _
    hM0 c r B Q
  rw [e1] at hR1
  set B1 := Function.update (Function.update (Function.update (Function.update B (K 0) [])
          (K 1) ((B (K 1)).drop (B (K 0)).length)) (K 3)
          ((true, List.ofFn fun q : Fin n => decide (q.val = cw.val)).2.reverse ++ B (K 3)))
          (K 6) ((B (K 0)).reverse ++ B (K 6)) with hB1
  have hR2 := mv_run M (K 3) (K 4) (ne 3 4 (by decide)) L1 L2 hM1 (set r true) c Q (B1 (K 3)) B1 rfl
  set B2 := Function.update (Function.update B1 (K 3) []) (K 4) ((B1 (K 3)).reverse ++ B1 (K 4))
    with hB2
  have hB2_4 : B2 (K 4) = List.ofFn fun q : Fin n => decide (q.val = cw.val) := by
    simp [hB2, hB1, Function.update_apply, hK.eq_iff, h3, h4]
  have hB2_2 : B2 (K 2) = List.replicate tw.val true := by
    simp [hB2, hB1, Function.update_apply, hK.eq_iff, h2]
  have e3 := ctlOut_lens get set hgs hss hsg cmδ2 cmO2a cmO2b (B2 (K 4)) (B2 (K 2)) (set r true)
  have e3' : ctlOut cmδ2 cmO2a cmO2b true (B2 (K 4)) (B2 (K 2)) =
      (false, (List.ofFn fun q : Fin n =>
        [decide (q.val = cw.val), decide (q.val = tw.val)]).flatten) := by
    rw [hB2_4, hB2_2]; exact ctlOut_cm2 n tw.val tw.isLt _
  have hr' : set r false = r := by rw [← hr, hsg]
  rw [hgs, e3', hss, hr'] at e3
  have hR3 := ctl_mk M (K 4) (K 2) (K 5) (K 7) (ne 4 2 (by decide)) (ne 4 5 (by decide))
    (ne 4 7 (by decide)) (ne 2 5 (by decide)) (ne 2 7 (by decide)) (ne 5 7 (by decide)) L2 L3 _ _ _
    hM2 c (set r true) B2 Q
  rw [e3] at hR3
  set B3 := Function.update (Function.update (Function.update (Function.update B2 (K 4) [])
          (K 2) ((B2 (K 2)).drop (B2 (K 4)).length)) (K 5)
          ((false, (List.ofFn fun q : Fin n =>
            [decide (q.val = cw.val), decide (q.val = tw.val)]).flatten).2.reverse ++ B2 (K 5)))
          (K 7) ((B2 (K 4)).reverse ++ B2 (K 7)) with hB3
  have hR4 := clear_mk M (K 7) L3 E hM3 r c B3 Q
  refine ⟨Function.update B3 (K 7) [], (hR1.trans (hR2.trans (hR3.trans hR4))).mono ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff, h0, h1, h2, h3, h4, h7]
    omega
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff, cm_emit_rev]
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff, h0]
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff]
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff, h0, h1]
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff, h2, h4, h3]
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff]
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff]
  · simp [hB3, hB2, hB1, Function.update_apply, hK.eq_iff]
  · intro x hx
    have := hx 0; have := hx 1; have := hx 2; have := hx 3; have := hx 4; have := hx 5
    have := hx 6; have := hx 7
    simp [hB3, hB2, hB1, Function.update_apply, *]

end FrontMask

end OCRS19TM

-- ===== session 21: Parse (encOp parser: g output -> dispatch label + unary wires / mask) =====
namespace OCRS19TM

section Parse

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

@[simp] lemma update_mk_inr (B : Kb → List Bool) (Q : ∀ r, List (G r)) (s : R) (l : List (G s)) :
    Function.update (mk B Q) (Sum.inr s) l = mk B (Function.update Q s l) := by
  funext k
  cases k with
  | inl b => rw [Function.update_of_ne (fun e => Sum.inl_ne_inr e)]; rfl
  | inr r =>
    by_cases h : r = s
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Sum.inr_injective e))]
      simp [Function.update_of_ne h]

/-- pop one bit of `a`; `true → L1`, otherwise (`false` or empty) `→ L0` -/
def bitStmt (a : Kb) (L1 L0 : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.getD false)
      (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L1))
      (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L0)))

lemma bit1_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a : Kb) (L L1 L0 : Λ)
    (hM : M L = bitStmt a L1 L0) (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = true :: A) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some L1, ((none, none, c), r), mk (Function.update B a A) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, bitStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
    Option.getD_some, cond_true, update_mk]

lemma bit0_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a : Kb) (L L1 L0 : Λ)
    (hM : M L = bitStmt a L1 L0) (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = false :: A) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some L0, ((none, none, c), r), mk (Function.update B a A) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, bitStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
    Option.getD_some, cond_false, update_mk]

/-- unary reader: move the leading `true`s of `a` to `b`, consume the terminating `false` -/
def unStmt (a b : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.getD false)
      (TM2.Stmt.push (Sum.inl b) (fun _ => true)
        (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L)))
      (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => E)))

lemma un_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b : Kb) (hab : a ≠ b) (L E : Λ)
    (hM : M L = unStmt a b L E) (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) :
    ∀ (q : ℕ) (A : List Bool) (B : Kb → List Bool), B a = List.replicate q true ++ false :: A →
      Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update (Function.update B a A) b (List.replicate q true ++ B b)) Q⟩ (q + 1) := by
  intro q
  induction q with
  | zero =>
    intro A B hA
    apply Reach.single
    have e : Function.update (Function.update B a A) b (List.replicate 0 true ++ B b) =
        Function.update B a A := by
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
    rw [e]
    simp only [List.replicate_zero, List.nil_append] at hA
    simp only [TM2.step, hM, unStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_false, update_mk]
  | succ q ih =>
    intro A B hA
    have := ih A (Function.update (Function.update B a (List.replicate q true ++ false :: A)) b
      (true :: B b)) (by simp [Function.update_apply, hab])
    refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by omega)
    · simp only [List.replicate_succ, List.cons_append] at hA
      simp only [TM2.step, hM, unStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_true, update_mk, Function.update_of_ne hab.symm]
    · have e : List.replicate q true ++ true :: B b = List.replicate (q + 1) true ++ B b := by
        rw [List.replicate_succ', List.append_assoc]; rfl
      congr 2
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all

/-- convert an `inr` stack (decoded by `dec`) onto a Bool stack (reverses) -/
def cvStmt (s : R) (dec : G s → Bool) (b : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inr s) (fun v x => ((x.map dec, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.push (Sum.inl b) (fun v => v.1.1.getD false)
        (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L))))

lemma cv_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (s : R) (dec : G s → Bool) (b : Kb) (L E : Λ)
    (hM : M L = cvStmt s dec b L E) (r : ρ) (c : Bool) :
    ∀ (A : List (G s)) (B : Kb → List Bool) (Q : ∀ r, List (G r)), Q s = A →
      Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update B b ((A.map dec).reverse ++ B b)) (Function.update Q s [])⟩
          (A.length + 1) := by
  intro A
  induction A with
  | nil =>
    intro B Q hA
    apply Reach.single
    have e1 : Function.update B b ((([] : List (G s)).map dec).reverse ++ B b) = B := by simp
    have e2 : Function.update Q s [] = Q := Function.update_eq_self_iff.mpr hA.symm
    rw [e1, e2]
    simp only [TM2.step, hM, cvStmt, TM2.stepAux, mk_inr, hA, List.head?_nil, List.tail_nil,
      Option.map_none, Option.isNone_none, cond_true]
    rw [update_mk_inr, e2]
  | cons x A ih =>
    intro B Q hA
    have := ih (Function.update B b (dec x :: B b)) (Function.update Q s A) (by simp)
    refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by simp)
    · simp only [TM2.step, hM, cvStmt, TM2.stepAux, mk_inr, hA, List.head?_cons, List.tail_cons,
        Option.map_some, Option.isNone_some, cond_false, Option.getD_some, update_mk_inr, update_mk]
      rfl
    · simp [List.map_cons, List.reverse_cons, List.append_assoc]

/-! Parser state: `Y` holds the unread suffix, `KW`/`KT`/`KM` collect wire1 / wire2 / mask. -/

/-- stacks during parsing -/
def St (Y KW KT KM : Kb) (B : Kb → List Bool) (y w t m : List Bool) : Kb → List Bool :=
  Function.update (Function.update (Function.update (Function.update B Y y) KW (w ++ B KW)) KT
    (t ++ B KT)) KM (m ++ B KM)

structure Dist4 (Y KW KT KM : Kb) : Prop where
  yw : Y ≠ KW
  yt : Y ≠ KT
  ym : Y ≠ KM
  wt : KW ≠ KT
  wm : KW ≠ KM
  tm : KT ≠ KM

variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) {Y KW KT KM : Kb} (hd : Dist4 Y KW KT KM)
include hd

lemma St_Y (B : Kb → List Bool) (y w t m : List Bool) : St Y KW KT KM B y w t m Y = y := by
  simp [St, Function.update_apply, hd.yw, hd.yt, hd.ym]

lemma st_bit1 (L L1 L0 : Λ) (hM : M L = bitStmt Y L1 L0) (r : ρ) (c : Bool) (Q : ∀ r, List (G r))
    (B : Kb → List Bool) (y w t m : List Bool) :
    Reach M ⟨some L, ((none, none, c), r), mk (St Y KW KT KM B (true :: y) w t m) Q⟩
      ⟨some L1, ((none, none, c), r), mk (St Y KW KT KM B y w t m) Q⟩ 1 := by
  refine (bit1_run M Y L L1 L0 hM r c Q y _ (St_Y hd B _ w t m)).of_eq ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  congr 2
  funext k; simp only [St, Function.update_apply]; split_ifs <;> simp_all

lemma st_bit0 (L L1 L0 : Λ) (hM : M L = bitStmt Y L1 L0) (r : ρ) (c : Bool) (Q : ∀ r, List (G r))
    (B : Kb → List Bool) (y w t m : List Bool) :
    Reach M ⟨some L, ((none, none, c), r), mk (St Y KW KT KM B (false :: y) w t m) Q⟩
      ⟨some L0, ((none, none, c), r), mk (St Y KW KT KM B y w t m) Q⟩ 1 := by
  refine (bit0_run M Y L L1 L0 hM r c Q y _ (St_Y hd B _ w t m)).of_eq ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  congr 2
  funext k; simp only [St, Function.update_apply]; split_ifs <;> simp_all

lemma st_unW (L E : Λ) (hM : M L = unStmt Y KW L E) (r : ρ) (c : Bool) (Q : ∀ r, List (G r))
    (B : Kb → List Bool) (q : ℕ) (y w t m : List Bool) :
    Reach M ⟨some L, ((none, none, c), r),
        mk (St Y KW KT KM B (List.replicate q true ++ false :: y) w t m) Q⟩
      ⟨some E, ((none, none, c), r), mk (St Y KW KT KM B y (List.replicate q true ++ w) t m) Q⟩
        (q + 1) := by
  refine (un_run M Y KW hd.yw L E hM r c Q q y _ (St_Y hd B _ w t m)).of_eq ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  congr 2
  funext k; simp only [St, Function.update_apply]
  split_ifs <;> simp_all

lemma st_unT (L E : Λ) (hM : M L = unStmt Y KT L E) (r : ρ) (c : Bool) (Q : ∀ r, List (G r))
    (B : Kb → List Bool) (q : ℕ) (y w t m : List Bool) :
    Reach M ⟨some L, ((none, none, c), r),
        mk (St Y KW KT KM B (List.replicate q true ++ false :: y) w t m) Q⟩
      ⟨some E, ((none, none, c), r), mk (St Y KW KT KM B y w (List.replicate q true ++ t) m) Q⟩
        (q + 1) := by
  refine (un_run M Y KT hd.yt L E hM r c Q q y _ (St_Y hd B _ w t m)).of_eq ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  congr 2
  funext k; simp only [St, Function.update_apply]
  split_ifs <;> simp_all

lemma st_mvM (L E : Λ) (hM : M L = mvStmt Y KM L E) (r : ρ) (c : Bool) (Q : ∀ r, List (G r))
    (B : Kb → List Bool) (y w t m : List Bool) :
    Reach M ⟨some L, ((none, none, c), r), mk (St Y KW KT KM B y w t m) Q⟩
      ⟨some E, ((none, none, c), r), mk (St Y KW KT KM B [] w t (y.reverse ++ m)) Q⟩
        (y.length + 1) := by
  refine (mv_run M Y KM hd.ym L E hM r c Q y _ (St_Y hd B _ w t m)).of_eq ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  congr 2
  funext k; simp only [St, Function.update_apply]
  split_ifs <;> simp_all

omit hd in
lemma St_init (B : Kb → List Bool) (Y KW KT KM : Kb) : St Y KW KT KM B (B Y) [] [] [] = B := by
  funext k; simp only [St, Function.update_apply]; split_ifs <;> simp_all

/-- dispatch label of a parsed op -/
def pdest {n : ℕ} (Halt PI PX PY PZ GH GS GC GM : Λ) : Option (CliffordOp n) → Λ
  | none => Halt
  | some (.pauli _ .I) => PI
  | some (.pauli _ .X) => PX
  | some (.pauli _ .Y) => PY
  | some (.pauli _ .Z) => PZ
  | some (.h _) => GH
  | some (.s _) => GS
  | some (.cnot _ _ _) => GC
  | some (.measure _) => GM

/-- first wire (unary) -/
def pW {n : ℕ} : Option (CliffordOp n) → List Bool
  | some (.pauli q _) => List.replicate q.val true
  | some (.h q) => List.replicate q.val true
  | some (.s q) => List.replicate q.val true
  | some (.cnot c _ _) => List.replicate c.val true
  | _ => []

/-- second wire (unary) -/
def pT {n : ℕ} : Option (CliffordOp n) → List Bool
  | some (.cnot _ t _) => List.replicate t.val true
  | _ => []

/-- measurement mask (= `mmask`) -/
def pM {n : ℕ} : Option (CliffordOp n) → List Bool
  | some (.measure Mp) => (List.ofFn fun q => encPauli (Mp q)).flatten.reverse
  | _ => []

/-- the parser program -/
structure ParseProg (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (Y KW KT KM : Kb) (P : Fin 15 → Λ)
    (Halt PI PX PY PZ GH GS GC GM Bad : Λ) : Prop where
  p0 : M (P 0) = bitStmt Y (P 1) Halt
  p1 : M (P 1) = bitStmt Y (P 2) (P 6)
  p2 : M (P 2) = bitStmt Y (P 3) (P 7)
  p3 : M (P 3) = bitStmt Y (P 4) (P 8)
  p4 : M (P 4) = bitStmt Y (P 5) (P 9)
  p5 : M (P 5) = bitStmt Y Bad (P 10)
  p6 : M (P 6) = unStmt Y KW (P 6) (P 11)
  p7 : M (P 7) = unStmt Y KW (P 7) GH
  p8 : M (P 8) = unStmt Y KW (P 8) GS
  p9 : M (P 9) = unStmt Y KW (P 9) (P 14)
  p10 : M (P 10) = mvStmt Y KM (P 10) GM
  p11 : M (P 11) = bitStmt Y (P 12) (P 13)
  p12 : M (P 12) = bitStmt Y PY PX
  p13 : M (P 13) = bitStmt Y PZ PI
  p14 : M (P 14) = unStmt Y KT (P 14) GC

/-- parse `encOp op` from `Y`: reach the op's dispatch label with its wires / mask collected -/
theorem parse_core {n : ℕ} (P : Fin 15 → Λ) (Halt PI PX PY PZ GH GS GC GM Bad : Λ)
    (hp : ParseProg M Y KW KT KM P Halt PI PX PY PZ GH GS GC GM Bad) (r : ρ) (c : Bool)
    (Q : ∀ r, List (G r)) (B : Kb → List Bool) (op : Option (CliffordOp n)) :
    Reach M ⟨some (P 0), ((none, none, c), r), mk (St Y KW KT KM B (encOp op) [] [] []) Q⟩
      ⟨some (pdest Halt PI PX PY PZ GH GS GC GM op), ((none, none, c), r),
        mk (St Y KW KT KM B [] (pW op) (pT op) (pM op)) Q⟩ ((encOp op).length + 1) := by
  rcases op with _ | ⟨q, P'⟩ | q | q | ⟨cw, tw, hct⟩ | Mp
  · exact ((st_bit0 M hd _ _ _ hp.p0 r c Q B [] [] [] []).mono (by simp [encOp])).of_eq
      (by simp [pdest, pW, pT, pM])
  · have pre : ∀ y : List Bool, ∀ L : Λ, M (P 11) = bitStmt Y (P 12) (P 13) →
        Reach M ⟨some (P 0), ((none, none, c), r),
          mk (St Y KW KT KM B (true :: false :: (List.replicate q.val true ++ false :: y)) [] [] []) Q⟩
          ⟨some (P 11), ((none, none, c), r),
          mk (St Y KW KT KM B y (List.replicate q.val true ++ []) [] []) Q⟩ (q.val + 3) := by
      intro y _ _
      exact (((st_bit1 M hd _ _ _ hp.p0 r c Q B _ [] [] []).trans
        ((st_bit0 M hd _ _ _ hp.p1 r c Q B _ [] [] []).trans
          (st_unW M hd _ _ hp.p6 r c Q B q.val y [] [] []))).mono (by omega))
    cases P'
    · rw [show encOp (some (CliffordOp.pauli q Pauli.I)) =
          true :: false :: (List.replicate q.val true ++ [false, false, false]) by
        simp [encOp, encNat, encPauli]]
      refine (((pre [false, false] PI hp.p11).trans ((st_bit0 M hd _ _ _ hp.p11 r c Q B _ _ [] []).trans
        (st_bit0 M hd _ _ _ hp.p13 r c Q B _ _ [] []))).mono ?_).of_eq ?_
      · simp [encOp, encNat, encPauli] <;> omega
      · simp [pdest, pW, pT, pM, encOp, encNat, encPauli]
    · rw [show encOp (some (CliffordOp.pauli q Pauli.X)) =
          true :: false :: (List.replicate q.val true ++ [false, true, false]) by
        simp [encOp, encNat, encPauli]]
      refine (((pre [true, false] PX hp.p11).trans ((st_bit1 M hd _ _ _ hp.p11 r c Q B _ _ [] []).trans
        (st_bit0 M hd _ _ _ hp.p12 r c Q B _ _ [] []))).mono ?_).of_eq ?_
      · simp [encOp, encNat, encPauli] <;> omega
      · simp [pdest, pW, pT, pM, encOp, encNat, encPauli]
    · rw [show encOp (some (CliffordOp.pauli q Pauli.Y)) =
          true :: false :: (List.replicate q.val true ++ [false, true, true]) by
        simp [encOp, encNat, encPauli]]
      refine (((pre [true, true] PY hp.p11).trans ((st_bit1 M hd _ _ _ hp.p11 r c Q B _ _ [] []).trans
        (st_bit1 M hd _ _ _ hp.p12 r c Q B _ _ [] []))).mono ?_).of_eq ?_
      · simp [encOp, encNat, encPauli] <;> omega
      · simp [pdest, pW, pT, pM, encOp, encNat, encPauli]
    · rw [show encOp (some (CliffordOp.pauli q Pauli.Z)) =
          true :: false :: (List.replicate q.val true ++ [false, false, true]) by
        simp [encOp, encNat, encPauli]]
      refine (((pre [false, true] PZ hp.p11).trans ((st_bit0 M hd _ _ _ hp.p11 r c Q B _ _ [] []).trans
        (st_bit1 M hd _ _ _ hp.p13 r c Q B _ _ [] []))).mono ?_).of_eq ?_
      · simp [encOp, encNat, encPauli] <;> omega
      · simp [pdest, pW, pT, pM, encOp, encNat, encPauli]
  · have e : encOp (some (CliffordOp.h q)) =
        true :: true :: false :: (List.replicate q.val true ++ false :: []) := by
      simp [encOp, encNat]
    rw [e]
    refine (((st_bit1 M hd _ _ _ hp.p0 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p1 r c Q B _ [] [] []).trans
      ((st_bit0 M hd _ _ _ hp.p2 r c Q B _ [] [] []).trans
      (st_unW M hd _ _ hp.p7 r c Q B q.val [] [] [] [])))).mono ?_).of_eq ?_
    · simp <;> omega
    · simp [pdest, pW, pT, pM]
  · have e : encOp (some (CliffordOp.s q)) =
        true :: true :: true :: false :: (List.replicate q.val true ++ false :: []) := by
      simp [encOp, encNat]
    rw [e]
    refine (((st_bit1 M hd _ _ _ hp.p0 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p1 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p2 r c Q B _ [] [] []).trans
      ((st_bit0 M hd _ _ _ hp.p3 r c Q B _ [] [] []).trans
      (st_unW M hd _ _ hp.p8 r c Q B q.val [] [] [] []))))).mono ?_).of_eq ?_
    · simp <;> omega
    · simp [pdest, pW, pT, pM]
  · have e : encOp (some (CliffordOp.cnot cw tw hct)) =
        true :: true :: true :: true :: false :: (List.replicate cw.val true ++ false ::
          (List.replicate tw.val true ++ false :: [])) := by
      simp [encOp, encNat]
    rw [e]
    refine (((st_bit1 M hd _ _ _ hp.p0 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p1 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p2 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p3 r c Q B _ [] [] []).trans
      ((st_bit0 M hd _ _ _ hp.p4 r c Q B _ [] [] []).trans
      ((st_unW M hd _ _ hp.p9 r c Q B cw.val _ [] [] []).trans
      (st_unT M hd _ _ hp.p14 r c Q B tw.val [] _ [] []))))))).mono ?_).of_eq ?_
    · simp <;> omega
    · simp [pdest, pW, pT, pM]
  · have e : encOp (some (CliffordOp.measure Mp)) =
        true :: true :: true :: true :: true :: false :: (List.ofFn fun q => encPauli (Mp q)).flatten := by
      simp [encOp, encNat]
    rw [e]
    refine (((st_bit1 M hd _ _ _ hp.p0 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p1 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p2 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p3 r c Q B _ [] [] []).trans
      ((st_bit1 M hd _ _ _ hp.p4 r c Q B _ [] [] []).trans
      ((st_bit0 M hd _ _ _ hp.p5 r c Q B _ [] [] []).trans
      (st_mvM M hd _ _ hp.p10 r c Q B _ [] [] []))))))).mono ?_).of_eq ?_
    · simp <;> omega
    · simp [pdest, pW, pT, pM]

theorem parse_run {n : ℕ} (P : Fin 15 → Λ) (Halt PI PX PY PZ GH GS GC GM Bad : Λ)
    (hp : ParseProg M Y KW KT KM P Halt PI PX PY PZ GH GS GC GM Bad) (r : ρ) (c : Bool)
    (Q : ∀ r, List (G r)) (B : Kb → List Bool) (op : Option (CliffordOp n)) (hY : B Y = encOp op) :
    Reach M ⟨some (P 0), ((none, none, c), r), mk B Q⟩
      ⟨some (pdest Halt PI PX PY PZ GH GS GC GM op), ((none, none, c), r),
        mk (St Y KW KT KM B [] (pW op) (pT op) (pM op)) Q⟩ ((encOp op).length + 1) := by
  have h := parse_core M hd P Halt PI PX PY PZ GH GS GC GM Bad hp r c Q B op
  rwa [show St Y KW KT KM B (encOp op) [] [] [] = B by rw [← hY, St_init]] at h

end Parse

end OCRS19TM

-- ===== session 21: Feed (copy the reversed g-input Grev onto g's input stack, keep Grev) =====
namespace OCRS19TM

section Feed

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- push a constant onto an `inr` stack -/
def pushInrStmt (s : R) (x : G s) (E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.push (Sum.inr s) (fun _ => x) (TM2.Stmt.goto fun _ => E)

/-- pop Bool stack `a`, push its `enc`-image on `inr s` and a copy on `b` -/
def dcvStmt (a : Kb) (s : R) (enc : Bool → G s) (b : Kb) (L E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.push (Sum.inr s) (fun v => enc (v.1.1.getD false))
        (TM2.Stmt.push (Sum.inl b) (fun v => v.1.1.getD false)
          (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L)))))

lemma dcv_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a : Kb) (s : R) (enc : Bool → G s) (b : Kb)
    (hab : a ≠ b) (L E : Λ) (hM : M L = dcvStmt a s enc b L E) (r : ρ) (c : Bool) :
    ∀ (A : List Bool) (B : Kb → List Bool) (Q : ∀ r, List (G r)), B a = A →
      Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update (Function.update B a []) b (A.reverse ++ B b))
            (Function.update Q s ((A.map enc).reverse ++ Q s))⟩ (A.length + 1) := by
  intro A
  induction A with
  | nil =>
    intro B Q hA
    apply Reach.single
    have e1 : Function.update (Function.update B a []) b (([] : List Bool).reverse ++ B b) = B := by
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
    have e2 : Function.update Q s ((([] : List Bool).map enc).reverse ++ Q s) = Q := by simp
    rw [e1, e2]
    simp only [TM2.step, hM, dcvStmt, TM2.stepAux, mk_inl, hA, List.head?_nil, List.tail_nil,
      Option.isNone_none, cond_true, update_mk]
    rw [(Function.update_eq_self_iff).mpr hA.symm]
  | cons x A ih =>
    intro B Q hA
    have := ih (Function.update (Function.update B a A) b (x :: B b))
      (Function.update Q s (enc x :: Q s)) (by simp [Function.update_apply, hab])
    refine (Reach.step_trans ?_ (this.of_eq ?_)).mono (by simp)
    · simp only [TM2.step, hM, dcvStmt, TM2.stepAux, mk_inl, hA, List.head?_cons, List.tail_cons,
        Option.isNone_some, cond_false, Option.getD_some, update_mk, update_mk_inr,
        Function.update_of_ne hab.symm]
      rfl
    · congr 2
      · funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
      · simp [List.map_cons, List.reverse_cons, List.append_assoc]

/-- feed: with `Gr` on `a`, put `(Gr.reverse ++ [false]).map enc` on the empty `inr s`, keep `a` -/
theorem feed_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (a b : Kb) (s : R) (enc : Bool → G s)
    (hab : a ≠ b) (LF L1 L2 E : Λ) (hF : M LF = pushInrStmt s (enc false) L1)
    (h1 : M L1 = dcvStmt a s enc b L1 L2) (h2 : M L2 = mvStmt b a L2 E) (r : ρ) (c : Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) (Gr : List Bool) (ha : B a = Gr) (hb : B b = [])
    (hs : Q s = []) :
    Reach M ⟨some LF, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk B (Function.update Q s ((Gr.reverse ++ [false]).map enc))⟩
      (2 * Gr.length + 3) := by
  have R0 : Reach M ⟨some LF, ((none, none, c), r), mk B Q⟩
      ⟨some L1, ((none, none, c), r), mk B (Function.update Q s [enc false])⟩ 1 := by
    apply Reach.single
    simp only [TM2.step, hF, pushInrStmt, TM2.stepAux, mk_inr, hs, update_mk_inr]
  have R1 := dcv_run M a s enc b hab L1 L2 h1 r c Gr B (Function.update Q s [enc false]) ha
  have R2 := mv_run M b a (Ne.symm hab) L2 E h2 r c
    (Function.update (Function.update Q s [enc false]) s ((Gr.map enc).reverse ++
      Function.update Q s [enc false] s)) Gr.reverse
    (Function.update (Function.update B a []) b (Gr.reverse ++ B b)) (by simp [hb])
  refine ((R0.trans (R1.trans R2)).mono (by simp; omega)).of_eq ?_
  congr 2
  · funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
  · simp [List.map_reverse]

end Feed

end OCRS19TM

-- ===== session 22: Poly (Horner evaluation of a fixed ℕ-polynomial in unary) =====
namespace OCRS19TM

section Poly

open Turing

/-- Horner fold: `Hor n v [c₁,…,c_k] = (…((v·n + c₁)·n + c₂)…)·n + c_k` -/
def Hor (n : ℕ) : ℕ → List ℕ → ℕ
  | v, [] => v
  | v, c :: cs => Hor n (v * n + c) cs

/-- step budget of the Horner machine -/
def HT (n : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | v, c :: cs => v * (3 * n + 4) + 4 + HT n (v * n + c) cs

lemma Hor_eq (n : ℕ) : ∀ (cs : List ℕ) (v : ℕ), Hor n v cs = v * n ^ cs.length + Hor n 0 cs
  | [], v => by simp [Hor]
  | c :: cs, v => by
    simp only [Hor, List.length_cons]
    rw [Hor_eq n cs (v * n + c), Hor_eq n cs (0 * n + c)]
    ring

/-- the coefficients of `p` from the top down, so that `Hor n 0 (coeffs p) = p.eval n` -/
def hcoeffs (p : Polynomial ℕ) : List ℕ := ((List.range (p.natDegree + 1)).reverse).map p.coeff

lemma Hor_range (f : ℕ → ℕ) (n : ℕ) : ∀ k : ℕ,
    Hor n 0 (((List.range k).reverse).map f) = ∑ i ∈ Finset.range k, f i * n ^ i
  | 0 => by simp [Hor]
  | k + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, Hor, Hor_eq, Hor_range f n k, Finset.sum_range_succ]
    simp [List.length_reverse, List.length_range]
    ring

lemma Hor_hcoeffs (p : Polynomial ℕ) (n : ℕ) : Hor n 0 (hcoeffs p) = p.eval n := by
  rw [hcoeffs, Hor_range, Polynomial.eval_eq_sum_range]

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- pop `a`; empty → `E`, else → `L1` (the popped bit is discarded) -/
def popStmt (a : Kb) (L1 E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => E)
      (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => L1)))

/-- push `k` copies of `true` on `a`, then go to `E` -/
def pushTs (a : Kb) : ℕ → Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)
  | 0, E => TM2.Stmt.goto fun _ => E
  | k + 1, E => TM2.Stmt.push (Sum.inl a) (fun _ => true) (pushTs a k E)

lemma stepAux_pushTs (a : Kb) (E : Λ) (v : Reg × ρ) : ∀ (k : ℕ) (B : Kb → List Bool)
    (Q : ∀ r, List (G r)),
    TM2.stepAux (pushTs (G := G) a k E) v (mk B Q) =
      ⟨some E, v, mk (Function.update B a (List.replicate k true ++ B a)) Q⟩
  | 0, B, Q => by simp [pushTs, TM2.stepAux]
  | k + 1, B, Q => by
    simp only [pushTs, TM2.stepAux, mk_inl, update_mk]
    rw [stepAux_pushTs a E v k]
    congr 2
    funext j; simp only [Function.update_apply]; split_ifs <;> simp_all [List.replicate_succ']

variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

lemma pop_run_nil (a : Kb) (L L1 E : Λ) (hM : M L = popStmt a L1 E) (r : ρ) (c : Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) (hB : B a = []) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩ ⟨some E, ((none, none, c), r), mk B Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, popStmt, TM2.stepAux, mk_inl, hB, List.head?_nil, List.tail_nil,
    Option.isNone_none, cond_true, update_mk]
  rw [(Function.update_eq_self_iff).mpr hB.symm]

lemma pop_run_cons (a : Kb) (L L1 E : Λ) (hM : M L = popStmt a L1 E) (r : ρ) (c : Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) (x : Bool) (A : List Bool) (hB : B a = x :: A) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some L1, ((none, none, c), r), mk (Function.update B a A) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, popStmt, TM2.stepAux, mk_inl, hB, List.head?_cons, List.tail_cons,
    Option.isNone_some, cond_false, update_mk]

lemma push_run (a : Kb) (L E : Λ) (k : ℕ) (hM : M L = pushTs a k E) (r : ρ) (c : Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk (Function.update B a (List.replicate k true ++ B a)) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, stepAux_pushTs]

/-- unary multiplication: `O += V·N`, `V` emptied, `N` restored (`T` scratch) -/
theorem umul_run (V N O T : Kb) (hVN : V ≠ N) (hVO : V ≠ O) (hVT : V ≠ T) (hNO : N ≠ O)
    (hNT : N ≠ T) (hOT : O ≠ T) (m0 m1 m2 E : Λ) (h0 : M m0 = popStmt V m1 E)
    (h1 : M m1 = dupStmt N O T m1 m2) (h2 : M m2 = mvStmt T N m2 m0) (r : ρ) (c : Bool)
    (Q : ∀ r, List (G r)) (n : ℕ) :
    ∀ (v o : ℕ) (B : Kb → List Bool), B V = List.replicate v true → B N = List.replicate n true →
      B O = List.replicate o true → B T = [] →
      Reach M ⟨some m0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update (Function.update B V []) O (List.replicate (o + v * n) true)) Q⟩
        (v * (2 * n + 3) + 1) := by
  intro v
  induction v with
  | zero =>
    intro o B hV hN hO hT
    refine ((pop_run_nil M V m0 m1 E h0 r c B Q hV).mono (by simp)).of_eq ?_
    congr 2
    funext k; simp only [Function.update_apply]; split_ifs <;> simp_all
  | succ v ih =>
    intro o B hV hN hO hT
    rw [List.replicate_succ] at hV
    have P0 := pop_run_cons M V m0 m1 E h0 r c B Q true _ hV
    have P1 := dup_run M N O T hNO hNT hOT m1 m2 h1 r c Q (List.replicate n true)
      (Function.update B V (List.replicate v true)) (by simp [Function.update_of_ne hVN.symm, hN])
    have P2 := mv_run M T N (Ne.symm hNT) m2 m0 h2 r c Q (List.replicate n true)
      (Function.update (Function.update (Function.update (Function.update B V
        (List.replicate v true)) N []) O ((List.replicate n true).reverse ++
          Function.update B V (List.replicate v true) O)) T ((List.replicate n true).reverse ++
          Function.update B V (List.replicate v true) T))
      (by simp [Function.update_apply, hT, Ne.symm hOT, Ne.symm hNT, Ne.symm hVT])
    have P3 := ih (o + n) (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B V (List.replicate v true)) N []) O ((List.replicate n true).reverse ++ (Function.update B V (List.replicate v true)) O)) T ((List.replicate n true).reverse ++ (Function.update B V (List.replicate v true)) T)) T []) N ((List.replicate n true).reverse ++ (Function.update (Function.update (Function.update (Function.update B V (List.replicate v true)) N []) O ((List.replicate n true).reverse ++ (Function.update B V (List.replicate v true)) O)) T ((List.replicate n true).reverse ++ (Function.update B V (List.replicate v true)) T)) N))
      (by simp [Function.update_apply, hVN, hVO, hVT])
      (by simp [Function.update_apply, hVN.symm, hNO, hNT, hT])
      (by simp [Function.update_apply, hVO.symm, hNO.symm, hOT, hO, List.reverse_replicate,
        ← List.replicate_add] <;> omega)
      (by simp [Function.update_apply, hNT.symm, hNT])
    have e : o + n + v * n = o + (v + 1) * n := by ring
    rw [e] at P3
    refine ((P0.trans (P1.trans (P2.trans P3))).mono
      (le_of_eq (by simp only [List.length_replicate]; ring))).of_eq ?_
    congr 2
    funext k; simp only [Function.update_apply]
    split_ifs <;> simp_all [List.reverse_replicate]

/-- one Horner stage: `V := V·N + c` (`O`, `T` empty scratch) -/
structure HStage (V N O T : Kb) (c : ℕ) (L : Fin 5 → Λ) (E : Λ) : Prop where
  h0 : M (L 0) = popStmt V (L 1) (L 3)
  h1 : M (L 1) = dupStmt N O T (L 1) (L 2)
  h2 : M (L 2) = mvStmt T N (L 2) (L 0)
  h3 : M (L 3) = mvStmt O V (L 3) (L 4)
  h4 : M (L 4) = pushTs V c E

theorem hstage_run (V N O T : Kb) (hVN : V ≠ N) (hVO : V ≠ O) (hVT : V ≠ T) (hNO : N ≠ O)
    (hNT : N ≠ T) (hOT : O ≠ T) (c : ℕ) (L : Fin 5 → Λ) (E : Λ) (hS : HStage M V N O T c L E)
    (r : ρ) (cr : Bool) (Q : ∀ r, List (G r)) (n v : ℕ) (B : Kb → List Bool)
    (hV : B V = List.replicate v true) (hN : B N = List.replicate n true) (hO : B O = [])
    (hT : B T = []) :
    Reach M ⟨some (L 0), ((none, none, cr), r), mk B Q⟩
      ⟨some E, ((none, none, cr), r), mk (Function.update B V (List.replicate (v * n + c) true)) Q⟩
      (v * (3 * n + 4) + 4) := by
  have P0 := umul_run M V N O T hVN hVO hVT hNO hNT hOT (L 0) (L 1) (L 2) (L 3) hS.h0 hS.h1 hS.h2
    r cr Q n v 0 B hV hN (by simp [hO]) hT
  have P1 := mv_run M O V hVO.symm (L 3) (L 4) hS.h3 r cr Q (List.replicate (0 + v * n) true)
    (Function.update (Function.update B V []) O (List.replicate (0 + v * n) true))
    (by simp)
  have P2 := push_run M V (L 4) E c hS.h4 r cr
    (Function.update (Function.update (Function.update (Function.update B V []) O
      (List.replicate (0 + v * n) true)) O []) V ((List.replicate (0 + v * n) true).reverse ++
        Function.update (Function.update B V []) O (List.replicate (0 + v * n) true) V)) Q
  refine ((P0.trans (P1.trans P2)).mono ?_).of_eq ?_
  · simp only [List.length_replicate]; nlinarith
  · congr 2
    rw [show v * n + c = c + v * n by ring]
    funext k
    by_cases hk : k = V
    · rw [hk]
      simp only [Function.update_self, Function.update_of_ne hVO, List.reverse_replicate,
        List.append_nil, Nat.zero_add, List.replicate_add]
    · by_cases hk2 : k = O
      · rw [hk2]; simp [Function.update_apply, hVO.symm, hO]
      · simp [Function.update_apply, hk, hk2]

/-- the Horner program: stage `i` handles coefficient `cs[i]`, then jumps to stage `i+1`'s entry;
the last stage jumps to `E`. -/
def HProg (V N O T : Kb) (cs : List ℕ) (L : ℕ → Fin 5 → Λ) (E : Λ) : Prop :=
  ∀ i (hi : i < cs.length), HStage M V N O T cs[i] (L i)
    (if i + 1 < cs.length then L (i + 1) 0 else E)

theorem horner_run (V N O T : Kb) (hVN : V ≠ N) (hVO : V ≠ O) (hVT : V ≠ T) (hNO : N ≠ O)
    (hNT : N ≠ T) (hOT : O ≠ T) (E : Λ) (r : ρ) (cr : Bool) (Q : ∀ r, List (G r)) (n : ℕ) :
    ∀ (cs : List ℕ) (L : ℕ → Fin 5 → Λ), HProg M V N O T cs L E → cs ≠ [] →
      ∀ (v : ℕ) (B : Kb → List Bool), B V = List.replicate v true →
        B N = List.replicate n true → B O = [] → B T = [] →
        Reach M ⟨some (L 0 0), ((none, none, cr), r), mk B Q⟩
          ⟨some E, ((none, none, cr), r), mk (Function.update B V (List.replicate (Hor n v cs) true)) Q⟩
          (HT n v cs) := by
  intro cs
  induction cs with
  | nil => intro L _ h; exact absurd rfl h
  | cons c cs ih =>
    intro L hP _ v B hV hN hO hT
    have hS := hP 0 (by simp)
    by_cases hcs : cs = []
    · subst hcs
      have := hstage_run M V N O T hVN hVO hVT hNO hNT hOT c (L 0) E (by simpa using hS) r cr Q n v
        B hV hN hO hT
      simpa [Hor, HT] using this
    · have hlen : 0 < cs.length := List.length_pos_iff.mpr hcs
      have P0 := hstage_run M V N O T hVN hVO hVT hNO hNT hOT c (L 0) (L 1 0)
        (by simpa [hlen] using hS) r cr Q n v B hV hN hO hT
      have hP' : HProg M V N O T cs (fun i => L (i + 1)) E := by
        intro i hi
        have := hP (i + 1) (by simp; omega)
        simpa using this
      have P1 := ih (fun i => L (i + 1)) hP' hcs (v * n + c)
        (Function.update B V (List.replicate (v * n + c) true)) (by simp)
        (by simp [Function.update_of_ne hVN.symm, hN]) (by simp [Function.update_of_ne hVO.symm, hO])
        (by simp [Function.update_of_ne hVT.symm, hT])
      refine ((P0.trans P1).mono (by simp [HT])).of_eq ?_
      simp [Hor, Function.update_idem]

end Poly

end OCRS19TM

-- ===== session 22: Take (move the first k coin pairs `1β` from the coin stack onto Grev) =====
namespace OCRS19TM

section Take

open Turing

/-- the pair code of a coin, as in `encBits` -/
def pr (β : Bool) : List Bool := [true, β]

lemma encBits_eq (l : List Bool) :
    QAlgorithms.Stabilizer.encBits l = l.flatMap pr ++ [false, false] := rfl

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- move one bit from `a` to `b` (pop, push), then go to `E` -/
def mv1Stmt (a b : Kb) (E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl a) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.push (Sum.inl b) (fun v => v.1.1.getD false)
      (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => E)))

/-- push the bits of `l` on `a` in order (so `a` gets `l.reverse ++ a`), then go to `E` -/
def pushL (a : Kb) : List Bool → Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)
  | [], E => TM2.Stmt.goto fun _ => E
  | x :: l, E => TM2.Stmt.push (Sum.inl a) (fun _ => x) (pushL a l E)

lemma stepAux_pushL (a : Kb) (E : Λ) (v : Reg × ρ) : ∀ (l : List Bool) (B : Kb → List Bool)
    (Q : ∀ r, List (G r)),
    TM2.stepAux (pushL (G := G) a l E) v (mk B Q) =
      ⟨some E, v, mk (Function.update B a (l.reverse ++ B a)) Q⟩
  | [], B, Q => by simp [pushL, TM2.stepAux]
  | x :: l, B, Q => by
    simp only [pushL, TM2.stepAux, mk_inl, update_mk]
    rw [stepAux_pushL a E v l]
    congr 2
    funext j; simp only [Function.update_apply]; split_ifs <;> simp_all

variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

lemma pushL_run (a : Kb) (L E : Λ) (l : List Bool) (hM : M L = pushL a l E) (r : ρ) (c : Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk (Function.update B a (l.reverse ++ B a)) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, stepAux_pushL]

lemma mv1_run (a b : Kb) (hab : a ≠ b) (L E : Λ) (hM : M L = mv1Stmt a b E) (r : ρ) (c : Bool)
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) (x : Bool) (A : List Bool) (hB : B a = x :: A) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk (Function.update (Function.update B a A) b (x :: B b)) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, mv1Stmt, TM2.stepAux, mk_inl, hB, List.head?_cons, List.tail_cons,
    Option.getD_some, update_mk, Function.update_of_ne hab.symm]

/-- take `k` coin pairs: counter `V` (unary `k`), coins `C`, destination `D` -/
theorem take_run (V C D : Kb) (hVC : V ≠ C) (hVD : V ≠ D) (hCD : C ≠ D) (t0 t1 t2 E : Λ)
    (h0 : M t0 = popStmt V t1 E) (h1 : M t1 = mv1Stmt C D t2) (h2 : M t2 = mv1Stmt C D t0)
    (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (C' : List Bool) :
    ∀ (k : ℕ) (P : List Bool) (B : Kb → List Bool), k ≤ P.length →
      B V = List.replicate k true → B C = P.flatMap pr ++ C' →
      Reach M ⟨some t0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update (Function.update (Function.update B V []) C
            ((P.drop k).flatMap pr ++ C')) D (((P.take k).flatMap pr).reverse ++ B D)) Q⟩
        (3 * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro P B _ hV hC
    refine ((pop_run_nil M V t0 t1 E h0 r c B Q hV).mono (by simp)).of_eq ?_
    congr 2
    funext j; simp only [Function.update_apply]; split_ifs <;> simp_all
  | succ k ih =>
    intro P B hk hV hC
    obtain ⟨β, P', rfl⟩ : ∃ β P', P = β :: P' := by
      cases P with
      | nil => simp at hk
      | cons β P' => exact ⟨β, P', rfl⟩
    rw [List.replicate_succ] at hV
    have P0 := pop_run_cons M V t0 t1 E h0 r c B Q true _ hV
    have P1 := mv1_run M C D hCD t1 t2 h1 r c (Function.update B V (List.replicate k true)) Q true
      (β :: (P'.flatMap pr ++ C')) (by simp [Function.update_of_ne hVC.symm, hC, pr])
    have P2 := mv1_run M C D hCD t2 t0 h2 r c
      (Function.update (Function.update (Function.update B V (List.replicate k true)) C
        (β :: (P'.flatMap pr ++ C'))) D (true :: Function.update B V (List.replicate k true) D))
      Q β (P'.flatMap pr ++ C') (by simp [Function.update_of_ne hCD])
    have P3 := ih P'
      (Function.update (Function.update (Function.update (Function.update (Function.update B V
        (List.replicate k true)) C (β :: (P'.flatMap pr ++ C'))) D
        (true :: Function.update B V (List.replicate k true) D)) C (P'.flatMap pr ++ C')) D
        (β :: Function.update (Function.update (Function.update B V (List.replicate k true)) C
          (β :: (P'.flatMap pr ++ C'))) D (true :: Function.update B V (List.replicate k true) D) D))
      (by simpa using hk)
      (by simp [Function.update_apply, hVC, hVD])
      (by simp [Function.update_apply, hCD])
    refine ((P0.trans (P1.trans (P2.trans P3))).mono (by omega)).of_eq ?_
    congr 2
    funext j
    by_cases hjD : j = D
    · rw [hjD]
      simp [Function.update_apply, hVD.symm, hCD.symm, pr]
    · by_cases hjC : j = C
      · rw [hjC]; simp [Function.update_apply, hCD, hVC.symm]
      · by_cases hjV : j = V
        · rw [hjV]; simp [Function.update_apply, hVC, hVD]
        · simp [Function.update_apply, hjD, hjC, hjV]

end Take

end OCRS19TM

-- ===== session 22: polynomial bound on the Horner step budget =====
namespace OCRS19TM

lemma HT_le (n : ℕ) : ∀ (cs : List ℕ) (v : ℕ),
    HT n v cs ≤ cs.length * ((v + cs.sum) * (n + 1) ^ cs.length * (3 * n + 4) + 4)
  | [], v => by simp [HT]
  | c :: cs, v => by
    have ih := HT_le n cs (v * n + c)
    simp only [HT, List.length_cons, List.sum_cons]
    set k := cs.length
    set A := v + (c + cs.sum)
    have hA1 : v * n + c + cs.sum ≤ A * (n + 1) := by
      have e : A * (n + 1) = v * n + c + cs.sum + (v + c * n + cs.sum * n) := by simp only [A]; ring
      omega
    have hpow : 1 ≤ (n + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    have h1 : (v * n + c + cs.sum) * (n + 1) ^ k ≤ A * (n + 1) ^ (k + 1) := by
      calc (v * n + c + cs.sum) * (n + 1) ^ k ≤ A * (n + 1) * (n + 1) ^ k :=
            Nat.mul_le_mul_right _ hA1
        _ = A * (n + 1) ^ (k + 1) := by ring
    have h2 : v ≤ A * (n + 1) ^ (k + 1) := by
      calc v ≤ A := by simp only [A]; omega
        _ = A * 1 := by ring
        _ ≤ A * (n + 1) ^ (k + 1) := Nat.mul_le_mul_left _ hpow
    have h3 : HT n (v * n + c) cs ≤ k * (A * (n + 1) ^ (k + 1) * (3 * n + 4) + 4) := by
      refine ih.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right ?_ _))
      exact Nat.mul_le_mul_right _ h1
    have h4 : v * (3 * n + 4) ≤ A * (n + 1) ^ (k + 1) * (3 * n + 4) := Nat.mul_le_mul_right _ h2
    nlinarith

/-- the Horner budget for evaluating `p` at `n` is polynomial in `n` -/
lemma HT_hcoeffs_le (p : Polynomial ℕ) (n : ℕ) :
    HT n 0 (hcoeffs p) ≤ (p.natDegree + 1) *
      ((hcoeffs p).sum * (n + 1) ^ (p.natDegree + 1) * (3 * n + 4) + 4) := by
  have := HT_le n (hcoeffs p) 0
  simpa [hcoeffs] using this

end OCRS19TM
-- ===== session 23: Setup (read n, read the n input bits, build Grev, evaluate rbits, take coins) =====
namespace OCRS19TM

section Setup

open Turing

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

/-- move `k` single bits from `C` onto `D` (reversed), counter `V` (unary `k`) -/
theorem takeb_run (V C D : Kb) (hVC : V ≠ C) (hVD : V ≠ D) (hCD : C ≠ D) (t0 t1 E : Λ)
    (h0 : M t0 = popStmt V t1 E) (h1 : M t1 = mv1Stmt C D t0)
    (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (C' : List Bool) :
    ∀ (k : ℕ) (P : List Bool) (B : Kb → List Bool), k ≤ P.length →
      B V = List.replicate k true → B C = P ++ C' →
      Reach M ⟨some t0, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r),
          mk (Function.update (Function.update (Function.update B V []) C
            (P.drop k ++ C')) D ((P.take k).reverse ++ B D)) Q⟩
        (2 * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro P B _ hV hC
    refine ((pop_run_nil M V t0 t1 E h0 r c B Q hV).mono (by simp)).of_eq ?_
    congr 2
    funext j; simp only [Function.update_apply]; split_ifs <;> simp_all
  | succ k ih =>
    intro P B hk hV hC
    obtain ⟨β, P', rfl⟩ : ∃ β P', P = β :: P' := by
      cases P with
      | nil => simp at hk
      | cons β P' => exact ⟨β, P', rfl⟩
    rw [List.replicate_succ] at hV
    have P0 := pop_run_cons M V t0 t1 E h0 r c B Q true _ hV
    have P1 := mv1_run M C D hCD t1 t0 h1 r c (Function.update B V (List.replicate k true)) Q β
      (P' ++ C') (by simp [Function.update_of_ne hVC.symm, hC])
    have P3 := ih P'
      (Function.update (Function.update (Function.update B V (List.replicate k true)) C
        (P' ++ C')) D (β :: Function.update B V (List.replicate k true) D))
      (by simpa using hk)
      (by simp [Function.update_apply, hVC, hVD])
      (by simp [Function.update_apply, hCD])
    refine ((P0.trans (P1.trans P3)).mono (by omega)).of_eq ?_
    congr 2
    funext j
    by_cases hjD : j = D
    · rw [hjD]
      simp [Function.update_apply, hVD.symm, hCD.symm]
    · by_cases hjC : j = C
      · rw [hjC]; simp [Function.update_apply, hCD, hVC.symm]
      · by_cases hjV : j = V
        · rw [hjV]; simp [Function.update_apply, hVC, hVD]
        · simp [Function.update_apply, hjD, hjC, hjV]

/-- the setup program: stacks `kk 0..6` = input `I`, unary `N`, bits `X`, `Grev`, Horner value `V`,
scratch `O`, `T`; labels `P 0..9` and the Horner labels `HL` -/
structure SetupProg (kk : Fin 7 → Kb) (p : Polynomial ℕ) (P : Fin 10 → Λ) (HL : ℕ → Fin 5 → Λ)
    (E : Λ) : Prop where
  s0 : M (P 0) = unStmt (kk 0) (kk 1) (P 0) (P 1)
  s1 : M (P 1) = dupStmt (kk 1) (kk 3) (kk 5) (P 1) (P 2)
  s2 : M (P 2) = dupStmt (kk 5) (kk 1) (kk 6) (P 2) (P 3)
  s3 : M (P 3) = popStmt (kk 6) (P 4) (P 5)
  s4 : M (P 4) = mv1Stmt (kk 0) (kk 2) (P 3)
  s5 : M (P 5) = pushL (kk 3) [false] (HL 0 0)
  hp : HProg M (kk 4) (kk 1) (kk 5) (kk 6) (hcoeffs p) HL (P 6)
  s6 : M (P 6) = popStmt (kk 4) (P 7) (P 9)
  s7 : M (P 7) = mv1Stmt (kk 0) (kk 3) (P 8)
  s8 : M (P 8) = mv1Stmt (kk 0) (kk 3) (P 6)
  s9 : M (P 9) = pushL (kk 3) [false, false] E

/-- the setup run: from input `encNat n ++ xs ++ encBits coins` to `N = 1^n`, `X = xs.reverse`,
`Grev = (encNat n ++ encBits (coins.take k)).reverse` with `k = p.eval n`, input left with the rest of
the coins. -/
theorem setup_run (kk : Fin 7 → Kb) (hk : Function.Injective kk) (p : Polynomial ℕ)
    (P : Fin 10 → Λ) (HL : ℕ → Fin 5 → Λ) (E : Λ) (hS : SetupProg M kk p P HL E)
    (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (n : ℕ) (xs coins : List Bool) (hxs : xs.length = n)
    (hco : p.eval n ≤ coins.length) (B : Kb → List Bool)
    (hI : B (kk 0) = QAlgorithms.Complexity.encNat n ++ xs ++ QAlgorithms.Stabilizer.encBits coins)
    (h1 : B (kk 1) = []) (h2 : B (kk 2) = []) (h3 : B (kk 3) = []) (h4 : B (kk 4) = [])
    (h5 : B (kk 5) = []) (h6 : B (kk 6) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some (P 0), ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r), mk B' Q⟩
        ((n + 1) + ((n + 1) + ((n + 1) + ((2 * n + 1) + (1 + (HT n 0 (hcoeffs p) +
          ((3 * p.eval n + 1) + 1))))))) ∧
      B' (kk 0) = QAlgorithms.Stabilizer.encBits (coins.drop (p.eval n)) ∧
      B' (kk 1) = List.replicate n true ∧ B' (kk 2) = xs.reverse ∧
      B' (kk 3) = (QAlgorithms.Complexity.encNat n ++
        QAlgorithms.Stabilizer.encBits (coins.take (p.eval n))).reverse ∧
      B' (kk 4) = [] ∧ B' (kk 5) = [] ∧ B' (kk 6) = [] ∧
      ∀ j, (∀ i, j ≠ kk i) → B' j = B j := by
  have ne : ∀ i j : Fin 7, i ≠ j → kk i ≠ kk j := fun i j h => hk.ne h
  set k := p.eval n
  -- step 0: read n
  have R0 := un_run M (kk 0) (kk 1) (ne 0 1 (by decide)) (P 0) (P 1) hS.s0 r c Q n
    (xs ++ (coins.flatMap pr ++ [false, false])) B
    (by rw [hI, encBits_eq]; simp [QAlgorithms.Complexity.encNat])
  set B0 := Function.update (Function.update B (kk 0) (xs ++ (coins.flatMap pr ++ [false, false])))
    (kk 1) (List.replicate n true ++ B (kk 1))
  -- step 1: N -> Grev, O
  have R1 := dup_run M (kk 1) (kk 3) (kk 5) (ne 1 3 (by decide)) (ne 1 5 (by decide))
    (ne 3 5 (by decide)) (P 1) (P 2) hS.s1 r c Q (List.replicate n true) B0
    (by simp [B0, Function.update_apply, ne 1 0 (by decide), h1])
  set B1 := Function.update (Function.update (Function.update B0 (kk 1) []) (kk 3)
    ((List.replicate n true).reverse ++ B0 (kk 3))) (kk 5) ((List.replicate n true).reverse ++ B0 (kk 5))
  -- step 2: O -> N, T
  have R2 := dup_run M (kk 5) (kk 1) (kk 6) (ne 5 1 (by decide)) (ne 5 6 (by decide))
    (ne 1 6 (by decide)) (P 2) (P 3) hS.s2 r c Q (List.replicate n true) B1
    (by simp [B1, B0, Function.update_apply, hk.eq_iff, h5])
  set B2 := Function.update (Function.update (Function.update B1 (kk 5) []) (kk 1)
    ((List.replicate n true).reverse ++ B1 (kk 1))) (kk 6) ((List.replicate n true).reverse ++ B1 (kk 6))
  -- step 3: read the n bits of x onto X
  have R3 := takeb_run M (kk 6) (kk 0) (kk 2) (ne 6 0 (by decide)) (ne 6 2 (by decide))
    (ne 0 2 (by decide)) (P 3) (P 4) (P 5) hS.s3 hS.s4 r c Q (coins.flatMap pr ++ [false, false])
    n xs B2 (by omega) (by simp [B2, B1, B0, Function.update_apply, hk.eq_iff, h6])
    (by simp [B2, B1, B0, Function.update_apply, hk.eq_iff])
  set B3 := Function.update (Function.update (Function.update B2 (kk 6) []) (kk 0)
    (xs.drop n ++ (coins.flatMap pr ++ [false, false]))) (kk 2) ((xs.take n).reverse ++ B2 (kk 2))
  -- step 4: push the `0` of encNat
  have R4 := pushL_run M (kk 3) (P 5) (HL 0 0) [false] hS.s5 r c B3 Q
  set B4 := Function.update B3 (kk 3) ([false].reverse ++ B3 (kk 3))
  -- step 5: Horner: V := p(n)
  have R5 := horner_run M (kk 4) (kk 1) (kk 5) (kk 6) (ne 4 1 (by decide)) (ne 4 5 (by decide))
    (ne 4 6 (by decide)) (ne 1 5 (by decide)) (ne 1 6 (by decide)) (ne 5 6 (by decide)) (P 6) r c Q n
    (hcoeffs p) HL hS.hp (by simp [hcoeffs]) 0 B4
    (by simp [B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff, h4])
    (by simp [B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff, h1])
    (by simp [B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff])
    (by simp [B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff])
  rw [Hor_hcoeffs] at R5
  set B5 := Function.update B4 (kk 4) (List.replicate k true)
  -- step 6: take k coin pairs onto Grev
  have R6 := take_run M (kk 4) (kk 0) (kk 3) (ne 4 0 (by decide)) (ne 4 3 (by decide))
    (ne 0 3 (by decide)) (P 6) (P 7) (P 8) (P 9) hS.s6 hS.s7 hS.s8 r c Q [false, false] k coins B5 hco
    (by simp [B5])
    (by simp [B5, B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff, hxs])
  set B6 := Function.update (Function.update (Function.update B5 (kk 4) []) (kk 0)
    ((coins.drop k).flatMap pr ++ [false, false])) (kk 3)
    (((coins.take k).flatMap pr).reverse ++ B5 (kk 3))
  -- step 7: push the closing `00`
  have R7 := pushL_run M (kk 3) (P 9) E [false, false] hS.s9 r c B6 Q
  refine ⟨_, (R0.trans (R1.trans (R2.trans (R3.trans (R4.trans (R5.trans (R6.trans R7))))))).mono
    (by simp only [List.length_replicate]; exact le_rfl), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [B6, Function.update_apply, hk.eq_iff, encBits_eq]
  · simp [B6, B5, B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff]
  · simp [B6, B5, B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff, h2, ← hxs]
  · simp [B6, B5, B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff, h3, h5,
      QAlgorithms.Complexity.encNat, encBits_eq, List.reverse_append]
  · simp [B6, Function.update_apply, hk.eq_iff]
  · simp [B6, B5, B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff]
  · simp [B6, B5, B4, B3, B2, B1, B0, Function.update_apply, hk.eq_iff]
  · intro j hj
    have := fun i => hj i
    simp [B6, B5, B4, B3, B2, B1, B0, Function.update_apply, this]

end Setup

end OCRS19TM
-- ===== session 23: InitK (write encodeTableau (initTab n x) and encodeTableau (initD n), forward) =====
namespace OCRS19TM

section InitK

open Turing

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ : Type}

variable (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ))

lemma rep_cons1 (m : ℕ) (x : Bool) (l : List Bool) :
    List.replicate m x ++ x :: l = List.replicate (m + 1) x ++ l := by
  rw [List.replicate_succ', List.append_assoc]; rfl

lemma rep_cons2 (m : ℕ) (x : Bool) (l : List Bool) :
    List.replicate (2 * m) x ++ x :: x :: l = List.replicate (2 * (m + 1)) x ++ l := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, List.replicate_succ', List.replicate_succ']
  simp

/-- `mvFF` loop: move the unary `a` onto `b`, pushing two `false`s on `f` and on `g` per bit -/
theorem mvFF_run (a b f g : Kb) (hab : a ≠ b) (haf : a ≠ f) (hag : a ≠ g) (hbf : b ≠ f)
    (hbg : b ≠ g) (hfg : f ≠ g) (l0 l1 l2 l3 E : Λ)
    (h0 : M l0 = popStmt a l1 E) (h1 : M l1 = pushTs b 1 l2) (h2 : M l2 = pushL f [false, false] l3)
    (h3 : M l3 = pushL g [false, false] l0) (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) :
    ∀ (m : ℕ) (B : Kb → List Bool), B a = List.replicate m true →
      ∃ B' : Kb → List Bool, Reach M ⟨some l0, ((none, none, c), r), mk B Q⟩
          ⟨some E, ((none, none, c), r), mk B' Q⟩ (4 * m + 1) ∧
        B' a = [] ∧ B' b = List.replicate m true ++ B b ∧
        B' f = List.replicate (2 * m) false ++ B f ∧ B' g = List.replicate (2 * m) false ++ B g ∧
        ∀ j, j ≠ a → j ≠ b → j ≠ f → j ≠ g → B' j = B j := by
  intro m
  induction m with
  | zero =>
    intro B hA
    exact ⟨B, pop_run_nil M a l0 l1 E h0 r c B Q (by simpa using hA), by simpa using hA, by simp,
      by simp, by simp, fun _ _ _ _ _ => rfl⟩
  | succ m ih =>
    intro B hA
    rw [List.replicate_succ] at hA
    have P0 := pop_run_cons M a l0 l1 E h0 r c B Q true _ hA
    set B1 := Function.update B a (List.replicate m true)
    have P1 := push_run M b l1 l2 1 h1 r c B1 Q
    set B2 := Function.update B1 b (List.replicate 1 true ++ B1 b)
    have P2 := pushL_run M f l2 l3 [false, false] h2 r c B2 Q
    set B3 := Function.update B2 f ([false, false].reverse ++ B2 f)
    have P3 := pushL_run M g l3 l0 [false, false] h3 r c B3 Q
    set B4 := Function.update B3 g ([false, false].reverse ++ B3 g)
    obtain ⟨B', R', e1, e2, e3, e4, e5⟩ := ih B4
      (by simp [B4, B3, B2, B1, Function.update_apply, hab, haf, hag])
    refine ⟨B', ((P0.trans (P1.trans (P2.trans (P3.trans R')))).mono (by omega)), e1, ?_, ?_, ?_, ?_⟩
    · rw [e2]; simp [B4, B3, B2, B1, Function.update_apply, hab.symm, hbf, hbg, rep_cons1]
    · rw [e3]; simp [B4, B3, B2, B1, Function.update_apply, haf.symm, hbf.symm, hfg, rep_cons2]
    · rw [e4]; simp [B4, B3, B2, B1, Function.update_apply, hag.symm, hbg.symm, hfg.symm, rep_cons2]
    · intro j j1 j2 j3 j4
      rw [e5 j j1 j2 j3 j4]; simp [B4, B3, B2, B1, Function.update_apply, j1, j2, j3, j4]

/-- reversed push order of row `j` of `initTab` (phase bit `b`) -/
def tRowR (n j : ℕ) (b : Bool) : List Bool :=
  List.replicate (2 * (n - 1 - j)) false ++ [true, false] ++ List.replicate (2 * j) false ++ [false, b]

/-- reversed push order of row `j` of `initD` -/
def dRowR (n j : ℕ) : List Bool :=
  List.replicate (2 * (n - 1 - j)) false ++ [false, true] ++ List.replicate (2 * j) false ++ [false, false]

/-- the T rows written so far (rows `0 .. ys.length - 1`, phase bits `ys`) -/
def rowsT (n : ℕ) (ys : List Bool) : List Bool := (ys.mapIdx fun j b => (tRowR n j b).reverse).flatten

/-- the D rows written so far -/
def rowsD (n m : ℕ) : List Bool := ((List.range m).map fun j => (dRowR n j).reverse).flatten

lemma rowsT_snoc (n : ℕ) (zs : List Bool) (b : Bool) :
    rowsT n (zs ++ [b]) = rowsT n zs ++ (tRowR n zs.length b).reverse := by
  simp [rowsT, List.mapIdx_append]

lemma rowsD_succ (n m : ℕ) : rowsD n (m + 1) = rowsD n m ++ (dRowR n m).reverse := by
  simp [rowsD, List.range_succ]

lemma mvE_loc (a b : Kb) (hab : a ≠ b) (L E : Λ)
    (hM : M L = mvStmt a b L E) (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (A : List Bool)
    (B : Kb → List Bool) (hA : B a = A) :
    ∃ B' : Kb → List Bool, Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
        ⟨some E, ((none, none, c), r), mk B' Q⟩ (A.length + 1) ∧
      B' a = [] ∧ B' b = A.reverse ++ B b ∧ ∀ k, k ≠ a → k ≠ b → B' k = B k :=
  ⟨_, mv_run M a b hab L E hM r c Q A B hA, by simp [Function.update_apply, hab], by simp,
    fun k h1 h2 => by simp [Function.update_apply, h1, h2]⟩

/-- the init program on stacks `kk 0..6` = `Bj, A, A', Bj', X, F, FD` -/
structure InitProg (kk : Fin 7 → Kb) (I : Fin 17 → Λ) (Ex : Λ) : Prop where
  i0 : M (I 0) = popStmt (kk 0) (I 1) Ex
  i1 : M (I 1) = popStmt (kk 1) (I 2) (I 5)
  i2 : M (I 2) = pushTs (kk 2) 1 (I 3)
  i3 : M (I 3) = pushL (kk 5) [false, false] (I 4)
  i4 : M (I 4) = pushL (kk 6) [false, false] (I 1)
  i5 : M (I 5) = pushL (kk 5) [true, false] (I 6)
  i6 : M (I 6) = pushL (kk 6) [false, true] (I 7)
  i7 : M (I 7) = popStmt (kk 0) (I 8) (I 11)
  i8 : M (I 8) = pushTs (kk 3) 1 (I 9)
  i9 : M (I 9) = pushL (kk 5) [false, false] (I 10)
  i10 : M (I 10) = pushL (kk 6) [false, false] (I 7)
  i11 : M (I 11) = pushL (kk 5) [false] (I 12)
  i12 : M (I 12) = mv1Stmt (kk 4) (kk 5) (I 13)
  i13 : M (I 13) = pushL (kk 6) [false, false] (I 14)
  i14 : M (I 14) = mvStmt (kk 3) (kk 0) (I 14) (I 15)
  i15 : M (I 15) = mvStmt (kk 2) (kk 1) (I 15) (I 16)
  i16 : M (I 16) = pushTs (kk 1) 1 (I 0)

theorem init_loop (kk : Fin 7 → Kb) (hk : Function.Injective kk) (I : Fin 17 → Λ) (Ex : Λ)
    (hP : InitProg M kk I Ex) (r : ρ) (c : Bool) (Q : ∀ r, List (G r)) (n : ℕ) (X0 : List Bool) :
    ∀ (m : ℕ), m ≤ n → ∀ (ys : List Bool) (B : Kb → List Bool), ys.length = m →
      B (kk 0) = List.replicate m true → B (kk 1) = List.replicate (n - m) true →
      B (kk 2) = [] → B (kk 3) = [] → B (kk 4) = ys.reverse ++ X0 →
      ∃ B' : Kb → List Bool, Reach M ⟨some (I 0), ((none, none, c), r), mk B Q⟩
          ⟨some Ex, ((none, none, c), r), mk B' Q⟩ (m * (6 * n + 12) + 1) ∧
        B' (kk 0) = [] ∧ B' (kk 1) = List.replicate n true ∧ B' (kk 2) = [] ∧ B' (kk 3) = [] ∧
        B' (kk 4) = X0 ∧ B' (kk 5) = rowsT n ys ++ B (kk 5) ∧ B' (kk 6) = rowsD n m ++ B (kk 6) ∧
        ∀ j, (∀ i, j ≠ kk i) → B' j = B j := by
  have ne : ∀ i j : Fin 7, i ≠ j → kk i ≠ kk j := fun i j h => hk.ne h
  intro m
  induction m with
  | zero =>
    intro _ ys B hys h0 h1 h2 h3 h4
    have hy : ys = [] := List.length_eq_zero_iff.mp hys
    subst hy
    refine ⟨B, (pop_run_nil M (kk 0) (I 0) (I 1) Ex hP.i0 r c B Q h0).mono (by omega), h0,
      by simpa using h1, h2, h3, by simpa using h4, by simp [rowsT], by simp [rowsD],
      fun _ _ => rfl⟩
  | succ m ih =>
    intro hm ys B hys h0 h1 h2 h3 h4
    obtain ⟨zs, b, rfl⟩ : ∃ zs b, ys = zs ++ [b] := by
      rcases List.eq_nil_or_concat ys with h | ⟨zs, b, h⟩
      · subst h; simp at hys
      · exact ⟨zs, b, by simpa using h⟩
    have hzs : zs.length = m := by simpa using hys
    rw [List.replicate_succ] at h0
    -- pop the row counter
    have P0 := pop_run_cons M (kk 0) (I 0) (I 1) Ex hP.i0 r c B Q true _ h0
    set B0 := Function.update B (kk 0) (List.replicate m true)
    -- leading identity columns (n - 1 - m of them)
    obtain ⟨B1, P1, a1, b1, f1, g1, fr1⟩ := mvFF_run M (kk 1) (kk 2) (kk 5) (kk 6)
      (ne 1 2 (by decide)) (ne 1 5 (by decide)) (ne 1 6 (by decide)) (ne 2 5 (by decide))
      (ne 2 6 (by decide)) (ne 5 6 (by decide)) (I 1) (I 2) (I 3) (I 4) (I 5) hP.i1 hP.i2 hP.i3 hP.i4
      r c Q (n - 1 - m) B0 (by
        rw [show n - 1 - m = n - (m + 1) by omega]
        simpa [B0, Function.update_apply, ne 1 0 (by decide)] using h1)
    have P5 := pushL_run M (kk 5) (I 5) (I 6) [true, false] hP.i5 r c B1 Q
    set B5 := Function.update B1 (kk 5) ([true, false].reverse ++ B1 (kk 5))
    have P6 := pushL_run M (kk 6) (I 6) (I 7) [false, true] hP.i6 r c B5 Q
    set B6 := Function.update B5 (kk 6) ([false, true].reverse ++ B5 (kk 6))
    -- trailing identity columns (m of them)
    obtain ⟨B7, P7, a7, b7, f7, g7, fr7⟩ := mvFF_run M (kk 0) (kk 3) (kk 5) (kk 6)
      (ne 0 3 (by decide)) (ne 0 5 (by decide)) (ne 0 6 (by decide)) (ne 3 5 (by decide))
      (ne 3 6 (by decide)) (ne 5 6 (by decide)) (I 7) (I 8) (I 9) (I 10) (I 11) hP.i7 hP.i8 hP.i9 hP.i10
      r c Q m B6 (by simp [B6, B5, B0, Function.update_apply, hk.eq_iff, fr1])
    have P11 := pushL_run M (kk 5) (I 11) (I 12) [false] hP.i11 r c B7 Q
    set B11 := Function.update B7 (kk 5) ([false].reverse ++ B7 (kk 5))
    have hX : B11 (kk 4) = b :: (zs.reverse ++ X0) := by
      simp [B11, B6, B5, B0, Function.update_apply, hk.eq_iff, fr1, fr7, h4]
    have P12 := mv1_run M (kk 4) (kk 5) (ne 4 5 (by decide)) (I 12) (I 13) hP.i12 r c B11 Q b _ hX
    set B12 := Function.update (Function.update B11 (kk 4) (zs.reverse ++ X0)) (kk 5) (b :: B11 (kk 5))
    have P13 := pushL_run M (kk 6) (I 13) (I 14) [false, false] hP.i13 r c B12 Q
    set B13 := Function.update B12 (kk 6) ([false, false].reverse ++ B12 (kk 6))
    -- restore the counters
    have h13a : B13 (kk 3) = List.replicate m true := by
      simp [B13, B12, B11, B6, B5, B0, Function.update_apply, hk.eq_iff, fr1, b7, h3]
    obtain ⟨B14, P14, a14, b14, fr14⟩ := mvE_loc M (kk 3) (kk 0) (ne 3 0 (by decide)) (I 14) (I 15)
      hP.i14 r c Q _ B13 h13a
    have h14a : B14 (kk 2) = List.replicate (n - 1 - m) true := by
      simp [B13, B12, B11, B6, B5, B0, Function.update_apply, hk.eq_iff, fr14, fr7, b1, h2]
    obtain ⟨B15, P15, a15, b15, fr15⟩ := mvE_loc M (kk 2) (kk 1) (ne 2 1 (by decide)) (I 15) (I 16)
      hP.i15 r c Q _ B14 h14a
    have P16 := push_run M (kk 1) (I 16) (I 0) 1 hP.i16 r c B15 Q
    set B16 := Function.update B15 (kk 1) (List.replicate 1 true ++ B15 (kk 1))
    have hA1 : B14 (kk 1) = [] := by
      simp [B13, B12, B11, B6, B5, Function.update_apply, hk.eq_iff, fr14, fr7, a1]
    have v0 : B16 (kk 0) = List.replicate m true := by
      simp [B16, B13, B12, B11, Function.update_apply, hk.eq_iff, fr15, b14, a7]
    have v1 : B16 (kk 1) = List.replicate (n - m) true := by
      simp only [B16, Function.update_self]
      rw [b15, hA1, List.append_nil, List.reverse_replicate, ← List.replicate_add]
      congr 1; omega
    have v4 : B16 (kk 4) = zs.reverse ++ X0 := by
      simp [B16, B13, B12, Function.update_apply, hk.eq_iff, fr15, fr14]
    have v5 : B16 (kk 5) = (tRowR n m b).reverse ++ B (kk 5) := by
      simp [B16, B13, B12, B11, B6, B5, B0, Function.update_apply, hk.eq_iff, fr15, fr14, f7, f1,
        tRowR, List.reverse_replicate]
    have v6 : B16 (kk 6) = (dRowR n m).reverse ++ B (kk 6) := by
      simp [B16, B13, B12, B11, B6, B5, B0, Function.update_apply, hk.eq_iff, fr15, fr14, g7, g1,
        dRowR, List.reverse_replicate]
    obtain ⟨B', R', e0, e1, e2, e3, e4, e5, e6, fr⟩ := ih (by omega) zs B16 hzs v0 v1
      (by simp [B16, Function.update_apply, hk.eq_iff, a15])
      (by simp [B16, Function.update_apply, hk.eq_iff, fr15, a14]) v4
    have hT : ∀ j, (∀ i, j ≠ kk i) → B16 j = B j := by
      intro j hj
      have j0 := hj 0; have j1 := hj 1; have j2 := hj 2; have j3 := hj 3; have j4 := hj 4
      have j5 := hj 5; have j6 := hj 6
      simp [B16, B13, B12, B11, B6, B5, B0, Function.update_apply, fr15, fr14, fr7, fr1,
        j0, j1, j2, j3, j4, j5, j6]
    refine ⟨B', (P0.trans (P1.trans (P5.trans (P6.trans (P7.trans (P11.trans (P12.trans
      (P13.trans (P14.trans (P15.trans (P16.trans R'))))))))))).mono ?_, e0, e1, e2, e3, e4, ?_, ?_, ?_⟩
    · simp only [List.length_replicate]
      obtain ⟨d, rfl⟩ : ∃ d, n = d + m + 1 := ⟨n - 1 - m, by omega⟩
      rw [show d + m + 1 - 1 - m = d by omega]
      nlinarith
    · rw [e5, v5, rowsT_snoc, hzs, List.append_assoc]
    · rw [e6, v6, rowsD_succ, List.append_assoc]
    · intro j hj
      rw [fr j hj]
      exact hT j hj

open QAlgorithms.Stabilizer in
lemma flat_rep2 (x : Bool) : ∀ k : ℕ, (List.replicate k [x, x]).flatten = List.replicate (2 * k) x
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, flat_rep2 x k,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
    simp only [List.cons_append, List.nil_append, ← List.replicate_succ, ← List.replicate_succ']

lemma flat_onehot (u v : List Bool) : ∀ (n j : ℕ), j < n →
    (List.ofFn fun q : Fin n => if q.val = j then u else v).flatten =
      (List.replicate j v).flatten ++ u ++ (List.replicate (n - 1 - j) v).flatten
  | 0, j, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
    rw [List.ofFn_succ]
    simp [List.ofFn_const]
  | n + 1, j + 1, h => by
    rw [List.ofFn_succ]
    have := flat_onehot u v n j (by omega)
    simp only [Fin.val_zero, Fin.val_succ, Nat.add_right_cancel_iff] at *
    simp [this, List.replicate_succ, show n + 1 - 1 - (j + 1) = n - 1 - j by omega]
    rw [show n - (j + 1) = n - 1 - j by omega]

open QAlgorithms.Stabilizer in
/-- the T rows written by the init loop are `encodeTableau (initTab n x)` -/
theorem rowsT_init (n : ℕ) (x : Fin n → Bool) :
    rowsT n (List.ofFn x) = encodeTableau (fun j : Fin n =>
      (⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : PauliString n)) := by
  unfold encodeTableau rowsT
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx, List.getElem_ofFn]
  have hi : i < n := by simpa using h2
  have hz : ∀ q : Fin n, (q = ⟨i, hi⟩) = (q.val = i) := fun q => by simp [Fin.ext_iff]
  simp only [hz, apply_ite encPauli]
  rw [flat_onehot (encPauli .Z) (encPauli .I) n i hi]
  cases x ⟨i, hi⟩ <;>
    simp [tRowR, encPhase, encPauli, flat_rep2, List.reverse_replicate] <;> decide

open QAlgorithms.Stabilizer in
/-- the D rows written by the init loop are `encodeTableau (initD n)` -/
theorem rowsD_init (n : ℕ) :
    rowsD n n = encodeTableau (fun j : Fin n =>
      (⟨0, fun q => if q = j then .X else .I⟩ : PauliString n)) := by
  unfold encodeTableau rowsD
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have hi : i < n := by simpa using h2
  have hz : ∀ q : Fin n, (q = ⟨i, hi⟩) = (q.val = i) := fun q => by simp [Fin.ext_iff]
  simp only [hz, apply_ite encPauli]
  rw [flat_onehot (encPauli .X) (encPauli .I) n i hi]
  simp [dRowR, encPhase, encPauli, flat_rep2, List.reverse_replicate]

end InitK

end OCRS19TM


-- ===== session 24: Gate1 (full single-wire gate step: mask build, T pass, D pass, hist push) =====
namespace OCRS19TM

section Gate1

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ε : Type}

/-- index map of the cmask stacks inside the 15 gate stacks -/
def g1emb : Fin 8 → Fin 15 := ![0, 2, 3, 4, 5, 6, 7, 8]

lemma g1emb_inj : Function.Injective g1emb := by decide

/-- the gate program on stacks `K 0..14` = `N KW W2 W3 c3 c4 Mk Nt c7 X F FD S H _` -/
structure G1Prog (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 15 → Kb) (Gl : Fin 18 → Λ)
    (Ex : Λ) (f : Pauli → ZMod 4 × Pauli) (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (getZ : MS ε → ZMod 4 × Option (Bool × Bool))
    (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε) : Prop where
  g0 : M (Gl 0) = dupStmt (K 1) (K 2) (K 3) (Gl 0) (Gl 1)
  g1 : M (Gl 1) = ctlStmt (K 0) (K 2) (K 4) (K 7) (Gl 1) (Gl 2)
    (fun r x y => setB r (cmδ1 (getB r) x y)) (fun r x y => cmO1 (getB r) x y)
    (fun r x y => cmNo (getB r) x y)
  g2 : M (Gl 2) = mvStmt (K 4) (K 5) (Gl 2) (Gl 3)
  g3 : M (Gl 3) = ctlStmt (K 5) (K 3) (K 6) (K 8) (Gl 3) (Gl 4)
    (fun r x y => setB r (cmδ2 (getB r) x y)) (fun r x y => cmO2a (getB r) x y)
    (fun r x y => cmO2b (getB r) x y)
  g4 : M (Gl 4) = clearStmt (K 8) (Gl 4) (Gl 5)
  g5 : M (Gl 5) = mvStmt (K 7) (K 0) (Gl 5) (Gl 6)
  g6 : M (Gl 6) = mvStmt (K 10) (K 9) (Gl 6) (Gl 7)
  g7 : M (Gl 7) = testStmt (K 9) (Gl 8) (Gl 11)
  g8 : M (Gl 8) = ctlStmt (K 6) (K 9) (K 10) (K 12) (Gl 8) (Gl 9)
    (fun r x y => setZ r (cwδ (g1W f) (getZ r) x y))
    (fun r x y => co1 (g1W f) (getZ r) x y) (fun r x y => co2 (g1W f) (getZ r) x y)
  g9 : M (Gl 9) = p2Stmt (K 9) (K 10) (Gl 10) (g1p2 getZ) (fun r _ _ => setZ r (0, none))
  g10 : M (Gl 10) = mvStmt (K 12) (K 6) (Gl 10) (Gl 7)
  g11 : M (Gl 11) = mvStmt (K 11) (K 9) (Gl 11) (Gl 12)
  g12 : M (Gl 12) = testStmt (K 9) (Gl 13) (Gl 16)
  g13 : M (Gl 13) = ctlStmt (K 6) (K 9) (K 11) (K 12) (Gl 13) (Gl 14)
    (fun r x y => setZ r (cwδ (g1W f) (getZ r) x y))
    (fun r x y => co1 (g1W f) (getZ r) x y) (fun r x y => co2 (g1W f) (getZ r) x y)
  g14 : M (Gl 14) = p2Stmt (K 9) (K 11) (Gl 15) (g1p2 getZ) (fun r _ _ => setZ r (0, none))
  g15 : M (Gl 15) = mvStmt (K 12) (K 6) (Gl 15) (Gl 12)
  g16 : M (Gl 16) = clearStmt (K 6) (Gl 16) (Gl 17)
  g17 : M (Gl 17) = pushL (K 13) [true, false, false] Ex

/-- the time of one single-wire gate step -/
def g1Time (n q m lT lD : ℕ) : ℕ :=
  (q + 1) + (4 * n + 4) + (n + 1) + (lT + 1) + (n * (2 * m + 4) + 1) + (lD + 1) +
    (n * (2 * m + 4) + 1) + (m + 1) + 1

/-- One single-wire gate step on the CHP pair `(T, D)` (both stored forward on `K 10`, `K 11`),
wire `q` in unary on `K 1`, `1^n` on `K 0`; pushes the gate transcript code onto `K 13`. -/
theorem gate1_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 15 → Kb)
    (hK : Function.Injective K) (Gl : Fin 18 → Λ) (Ex : Λ) (f : Pauli → ZMod 4 × Pauli)
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getZ : MS ε → ZMod 4 × Option (Bool × Bool))
    (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε)
    (hgsZ : ∀ r t, getZ (setZ r t) = t) (hssZ : ∀ r t t', setZ (setZ r t) t' = setZ r t')
    (hsgZ : ∀ r, setZ r (getZ r) = r)
    (hp : G1Prog M K Gl Ex f getB setB getZ setZ)
    {n : ℕ} (q : Fin n) (T D : Tableau n) (c : Bool) (r : MS ε)
    (hrB : getB r = false) (hrZ : getZ r = (0, none))
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (h0 : B (K 0) = List.replicate n true) (h1 : B (K 1) = List.replicate q.val true)
    (h2 : B (K 2) = []) (h3 : B (K 3) = []) (h4 : B (K 4) = []) (h5 : B (K 5) = [])
    (h6 : B (K 6) = []) (h7 : B (K 7) = []) (h8 : B (K 8) = []) (h9 : B (K 9) = [])
    (h10 : B (K 10) = encodeTableau T) (h11 : B (K 11) = encodeTableau D) (h12 : B (K 12) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some (Gl 0), ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), r), mk B' Q⟩
        (g1Time n q.val (cmaskR n q q).length (encodeTableau T).length (encodeTableau D).length) ∧
      B' (K 0) = List.replicate n true ∧
      B' (K 10) = encodeTableau (fun j => rowG1 f q (T j)) ∧
      B' (K 11) = encodeTableau (fun j => rowG1 f q (D j)) ∧
      B' (K 13) = [false, false, true] ++ B (K 13) ∧
      (∀ i : Fin 15, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 14) = B (K 14) ∧
      ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have ne : ∀ i j : Fin 15, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  have hKe : ∀ i j : Fin 15, K i = K j ↔ i = j := fun i j => hK.eq_iff
  -- 1. duplicate the wire
  obtain ⟨B1, R1, e1a, e1b, e1c, e1f⟩ := dupE M (K 1) (K 2) (K 3) (ne 1 2 (by decide))
    (ne 1 3 (by decide)) (ne 2 3 (by decide)) (Gl 0) (Gl 1) hp.g0 r c Q _ B h1
  -- 2. build the mask
  have hK' : Function.Injective (K ∘ g1emb) := hK.comp g1emb_inj
  obtain ⟨B2, R2, e2Mk, e2Nt, e20, e21, e22, e23, e24, e27, e2f⟩ :=
    cmask_build M (K ∘ g1emb) hK' (Gl 1) (Gl 2) (Gl 3) (Gl 4) (Gl 5) getB setB hgsB hssB hsgB
      hp.g1 hp.g2 hp.g3 hp.g4 q q c r hrB B1 Q
      (by show B1 (K 0) = _; rw [e1f _ (ne 0 1 (by decide)) (ne 0 2 (by decide))
            (ne 0 3 (by decide)), h0])
      (by show B1 (K 2) = _; rw [e1b, h2, List.reverse_replicate, List.append_nil])
      (by show B1 (K 3) = _; rw [e1c, h3, List.reverse_replicate, List.append_nil])
      (by show B1 (K 4) = _; rw [e1f _ (ne 4 1 (by decide)) (ne 4 2 (by decide))
            (ne 4 3 (by decide)), h4])
      (by show B1 (K 5) = _; rw [e1f _ (ne 5 1 (by decide)) (ne 5 2 (by decide))
            (ne 5 3 (by decide)), h5])
      (by show B1 (K 8) = _; rw [e1f _ (ne 8 1 (by decide)) (ne 8 2 (by decide))
            (ne 8 3 (by decide)), h8])
  have e2f' : ∀ x, x ≠ K 0 → x ≠ K 2 → x ≠ K 3 → x ≠ K 4 → x ≠ K 5 → x ≠ K 6 → x ≠ K 7 →
      x ≠ K 8 → B2 x = B1 x := by
    intro x a0 a2 a3 a4 a5 a6 a7 a8
    apply e2f x
    intro i
    fin_cases i
    · exact a0
    · exact a2
    · exact a3
    · exact a4
    · exact a5
    · exact a6
    · exact a7
    · exact a8
  simp only [Function.comp_apply] at e2Mk e2Nt e20 e21 e22 e23 e24 e27
  have g0' : g1emb 0 = 0 := rfl
  have g1' : g1emb 1 = 2 := rfl
  have g2' : g1emb 2 = 3 := rfl
  have g3' : g1emb 3 = 4 := rfl
  have g4' : g1emb 4 = 5 := rfl
  have g5' : g1emb 5 = 6 := rfl
  have g6' : g1emb 6 = 7 := rfl
  have g7' : g1emb 7 = 8 := rfl
  rw [g0'] at e20; rw [g1'] at e21; rw [g2'] at e22; rw [g3'] at e23; rw [g4'] at e24
  rw [g5'] at e2Mk; rw [g6'] at e2Nt; rw [g7'] at e27
  -- 3. restore 1^n
  have hNt2 : B2 (K 7) = List.replicate n true := by
    rw [e2Nt, e1f _ (ne 7 1 (by decide)) (ne 7 2 (by decide)) (ne 7 3 (by decide)), h7,
      List.append_nil]
  obtain ⟨B3, R3, e3a, e3b, e3f⟩ := mvE M (K 7) (K 0) (ne 7 0 (by decide)) (Gl 5) (Gl 6) hp.g5 r c Q
    _ B2 hNt2
  -- 4. T to X (reversed)
  have hT2 : B2 (K 10) = encodeTableau T := by
    rw [e2f' _ (ne 10 0 (by decide)) (ne 10 2 (by decide)) (ne 10 3 (by decide))
      (ne 10 4 (by decide)) (ne 10 5 (by decide)) (ne 10 6 (by decide)) (ne 10 7 (by decide))
      (ne 10 8 (by decide)), e1f _ (ne 10 1 (by decide)) (ne 10 2 (by decide))
      (ne 10 3 (by decide)), h10]
  obtain ⟨B4, R4, e4a, e4b, e4f⟩ := mvE M (K 10) (K 9) (ne 10 9 (by decide)) (Gl 6) (Gl 7) hp.g6 r c
    Q _ B3 (by rw [e3f _ (ne 10 7 (by decide)) (ne 10 0 (by decide)), hT2])
  have hX4 : B4 (K 9) = (encodeTableau T).reverse := by
    rw [e4b, e3f _ (ne 9 7 (by decide)) (ne 9 0 (by decide)),
      e2f' _ (ne 9 0 (by decide)) (ne 9 2 (by decide)) (ne 9 3 (by decide))
      (ne 9 4 (by decide)) (ne 9 5 (by decide)) (ne 9 6 (by decide)) (ne 9 7 (by decide))
      (ne 9 8 (by decide)), e1f _ (ne 9 1 (by decide)) (ne 9 2 (by decide))
      (ne 9 3 (by decide)), h9, List.append_nil]
  have hMk4 : B4 (K 6) = cmaskR n q q := by
    rw [e4f _ (ne 6 10 (by decide)) (ne 6 9 (by decide)), e3f _ (ne 6 7 (by decide))
      (ne 6 0 (by decide)), e2Mk, e1f _ (ne 6 1 (by decide)) (ne 6 2 (by decide))
      (ne 6 3 (by decide)), h6, List.append_nil]
  have hS4 : B4 (K 12) = [] := by
    rw [e4f _ (ne 12 10 (by decide)) (ne 12 9 (by decide)), e3f _ (ne 12 7 (by decide))
      (ne 12 0 (by decide)), e2f' _ (ne 12 0 (by decide)) (ne 12 2 (by decide))
      (ne 12 3 (by decide)) (ne 12 4 (by decide)) (ne 12 5 (by decide)) (ne 12 6 (by decide))
      (ne 12 7 (by decide)) (ne 12 8 (by decide)), e1f _ (ne 12 1 (by decide))
      (ne 12 2 (by decide)) (ne 12 3 (by decide)), h12]
  -- 5. gate pass on T
  have R5 := g1_tab M (K 6) (K 9) (K 10) (K 12) (ne 6 9 (by decide)) (ne 6 10 (by decide))
    (ne 6 12 (by decide)) (ne 9 10 (by decide)) (ne 9 12 (by decide)) (ne 10 12 (by decide))
    (Gl 7) (Gl 8) (Gl 9) (Gl 10) (Gl 11) getZ setZ hgsZ hssZ hsgZ f q hp.g7 hp.g8 hp.g9 hp.g10
    c r hrZ T B4 Q hMk4 hX4 hS4
  set B5 := Function.update (Function.update B4 (K 9) []) (K 10)
    (encodeTableau (fun j => rowG1 f q (T j)) ++ B4 (K 10)) with hB5
  have e5f : ∀ x, x ≠ K 9 → x ≠ K 10 → B5 x = B4 x := fun x a b => by
    rw [hB5, Function.update_of_ne b, Function.update_of_ne a]
  have e5X : B5 (K 9) = [] := by
    rw [hB5, Function.update_of_ne (ne 9 10 (by decide)), Function.update_self]
  have e5T : B5 (K 10) = encodeTableau (fun j => rowG1 f q (T j)) := by
    rw [hB5, Function.update_self, e4a, List.append_nil]
  -- 6. D to X
  have hD5 : B5 (K 11) = encodeTableau D := by
    rw [e5f _ (ne 11 9 (by decide)) (ne 11 10 (by decide)), e4f _ (ne 11 10 (by decide))
      (ne 11 9 (by decide)), e3f _ (ne 11 7 (by decide)) (ne 11 0 (by decide)),
      e2f' _ (ne 11 0 (by decide)) (ne 11 2 (by decide)) (ne 11 3 (by decide))
      (ne 11 4 (by decide)) (ne 11 5 (by decide)) (ne 11 6 (by decide)) (ne 11 7 (by decide))
      (ne 11 8 (by decide)), e1f _ (ne 11 1 (by decide)) (ne 11 2 (by decide))
      (ne 11 3 (by decide)), h11]
  obtain ⟨B6, R6, e6a, e6b, e6f⟩ := mvE M (K 11) (K 9) (ne 11 9 (by decide)) (Gl 11) (Gl 12) hp.g11
    r c Q _ B5 hD5
  have R7 := g1_tab M (K 6) (K 9) (K 11) (K 12) (ne 6 9 (by decide)) (ne 6 11 (by decide))
    (ne 6 12 (by decide)) (ne 9 11 (by decide)) (ne 9 12 (by decide)) (ne 11 12 (by decide))
    (Gl 12) (Gl 13) (Gl 14) (Gl 15) (Gl 16) getZ setZ hgsZ hssZ hsgZ f q hp.g12 hp.g13 hp.g14
    hp.g15 c r hrZ D B6 Q
    (by rw [e6f _ (ne 6 11 (by decide)) (ne 6 9 (by decide)), e5f _ (ne 6 9 (by decide))
          (ne 6 10 (by decide)), hMk4])
    (by rw [e6b, e5X, List.append_nil])
    (by rw [e6f _ (ne 12 11 (by decide)) (ne 12 9 (by decide)), e5f _ (ne 12 9 (by decide))
          (ne 12 10 (by decide)), hS4])
  set B7 := Function.update (Function.update B6 (K 9) []) (K 11)
    (encodeTableau (fun j => rowG1 f q (D j)) ++ B6 (K 11)) with hB7
  have e7f : ∀ x, x ≠ K 9 → x ≠ K 11 → B7 x = B6 x := fun x a b => by
    rw [hB7, Function.update_of_ne b, Function.update_of_ne a]
  -- 7. clear the mask
  obtain ⟨B8, R8, e8a, e8f⟩ := clearE M (K 6) (Gl 16) (Gl 17) hp.g16 r c Q _ B7
    (by rw [e7f _ (ne 6 9 (by decide)) (ne 6 11 (by decide)), e6f _ (ne 6 11 (by decide))
          (ne 6 9 (by decide)), e5f _ (ne 6 9 (by decide)) (ne 6 10 (by decide)), hMk4])
  -- 8. push the transcript code
  have R9 := pushL_run M (K 13) (Gl 17) Ex [true, false, false] hp.g17 r c B8 Q
  set B9 := Function.update B8 (K 13) ([true, false, false].reverse ++ B8 (K 13)) with hB9
  have e9f : ∀ x, x ≠ K 13 → B9 x = B8 x := fun x a => by rw [hB9, Function.update_of_ne a]
  -- frame to B through stages 1-8, for a stack untouched by all of them
  have frame : ∀ x, x ≠ K 0 → x ≠ K 1 → x ≠ K 2 → x ≠ K 3 → x ≠ K 4 → x ≠ K 5 → x ≠ K 6 →
      x ≠ K 7 → x ≠ K 8 → x ≠ K 9 → x ≠ K 10 → x ≠ K 11 → B8 x = B x := by
    intro x a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    rw [e8f _ a6, e7f _ a9 a11, e6f _ a11 a9, e5f _ a9 a10, e4f _ a10 a9, e3f _ a7 a0,
      e2f' _ a0 a2 a3 a4 a5 a6 a7 a8, e1f _ a1 a2 a3]
  have fr : ∀ j : Fin 15, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 →
      j ≠ 8 → j ≠ 9 → j ≠ 10 → j ≠ 11 → B8 (K j) = B (K j) := by
    intro j a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    exact frame _ (ne _ _ a0) (ne _ _ a1) (ne _ _ a2) (ne _ _ a3) (ne _ _ a4) (ne _ _ a5)
      (ne _ _ a6) (ne _ _ a7) (ne _ _ a8) (ne _ _ a9) (ne _ _ a10) (ne _ _ a11)
  -- B7 down to B3 for the cmask/dup stacks
  have to3 : ∀ j : Fin 15, j ≠ 6 → j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 13 → B9 (K j) = B3 (K j) := by
    intro j a6 a9 a10 a11 a13
    rw [e9f _ (ne _ _ a13), e8f _ (ne _ _ a6), e7f _ (ne _ _ a9) (ne _ _ a11),
      e6f _ (ne _ _ a11) (ne _ _ a9), e5f _ (ne _ _ a9) (ne _ _ a10),
      e4f _ (ne _ _ a10) (ne _ _ a9)]
  have to2 : ∀ j : Fin 15, j ≠ 0 → j ≠ 6 → j ≠ 7 → j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 13 →
      B9 (K j) = B2 (K j) := by
    intro j a0 a6 a7 a9 a10 a11 a13
    rw [to3 j a6 a9 a10 a11 a13, e3f _ (ne _ _ a7) (ne _ _ a0)]
  refine ⟨B9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have R := (((((((R1.trans R2).trans R3).trans R4).trans R5).trans R6).trans R7).trans R8).trans R9
    refine R.mono (le_of_eq ?_)
    simp only [g1Time, List.length_replicate, List.length_append, List.length_reverse]
  · rw [to3 0 (by decide) (by decide) (by decide) (by decide) (by decide), e3b, e20,
      List.reverse_replicate, List.append_nil]
  · rw [e9f _ (ne 10 13 (by decide)), e8f _ (ne 10 6 (by decide)), e7f _ (ne 10 9 (by decide))
      (ne 10 11 (by decide)), e6f _ (ne 10 11 (by decide)) (ne 10 9 (by decide)), e5T]
  · rw [e9f _ (ne 11 13 (by decide)), e8f _ (ne 11 6 (by decide)), hB7, Function.update_self,
      e6a, List.append_nil]
  · rw [hB9, Function.update_self, fr 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    rfl
  · intro i a0 a10 a11 a13 a14
    fin_cases i
    · show B9 (K 0) = []
      exact absurd rfl a0
    · show B9 (K 1) = []
      rw [to2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e2f' _ (ne 1 0 (by decide)) (ne 1 2 (by decide)) (ne 1 3 (by decide))
        (ne 1 4 (by decide)) (ne 1 5 (by decide)) (ne 1 6 (by decide)) (ne 1 7 (by decide))
        (ne 1 8 (by decide)), e1a]
    · show B9 (K 2) = []
      rw [to2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e21]
    · show B9 (K 3) = []
      rw [to2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e22]
    · show B9 (K 4) = []
      rw [to2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e23]
    · show B9 (K 5) = []
      rw [to2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e24]
    · show B9 (K 6) = []
      rw [e9f _ (ne 6 13 (by decide)), e8a]
    · show B9 (K 7) = []
      rw [to3 7 (by decide) (by decide) (by decide) (by decide) (by decide), e3a]
    · show B9 (K 8) = []
      rw [to2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e27]
    · show B9 (K 9) = []
      rw [e9f _ (ne 9 13 (by decide)), e8f _ (ne 9 6 (by decide)), hB7,
        Function.update_of_ne (ne 9 11 (by decide)), Function.update_self]
    · show B9 (K 10) = []
      exact absurd rfl a10
    · show B9 (K 11) = []
      exact absurd rfl a11
    · show B9 (K 12) = []
      rw [to3 12 (by decide) (by decide) (by decide) (by decide) (by decide),
        e3f _ (ne 12 7 (by decide)) (ne 12 0 (by decide)), e2f' _ (ne 12 0 (by decide))
        (ne 12 2 (by decide)) (ne 12 3 (by decide)) (ne 12 4 (by decide)) (ne 12 5 (by decide))
        (ne 12 6 (by decide)) (ne 12 7 (by decide)) (ne 12 8 (by decide)),
        e1f _ (ne 12 1 (by decide)) (ne 12 2 (by decide)) (ne 12 3 (by decide)), h12]
    · show B9 (K 13) = []
      exact absurd rfl a13
    · show B9 (K 14) = []
      exact absurd rfl a14
  · rw [e9f _ (ne 14 13 (by decide)), fr 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  · intro x hx
    rw [e9f _ (hx 13)]
    exact frame x (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) (hx 5) (hx 6) (hx 7) (hx 8) (hx 9) (hx 10)
      (hx 11)

end Gate1

end OCRS19TM


-- ===== session 24: Cnot (full CNOT step: mask build, T pass, D pass, hist push) =====
namespace OCRS19TM

section CnotStep

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ε : Type}

/-- index map of the cmask stacks inside the 15 gate stacks (CNOT layout) -/
def cnemb : Fin 8 → Fin 15 := ![0, 1, 2, 4, 5, 6, 7, 8]

lemma cnemb_inj : Function.Injective cnemb := by decide

/-- the CNOT program on stacks `K 0..14` = `N KC KT Z c3 c4 Mk Nt c7 X F FD S H _` -/
structure CNProg (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 15 → Kb) (Gl : Fin 23 → Λ)
    (Ex : Λ) (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool))
    (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε) (s0 : Pauli × Pauli) : Prop where
  g0 : M (Gl 0) = ctlStmt (K 0) (K 1) (K 4) (K 7) (Gl 0) (Gl 1)
    (fun r x y => setB r (cmδ1 (getB r) x y)) (fun r x y => cmO1 (getB r) x y)
    (fun r x y => cmNo (getB r) x y)
  g1 : M (Gl 1) = mvStmt (K 4) (K 5) (Gl 1) (Gl 2)
  g2 : M (Gl 2) = ctlStmt (K 5) (K 2) (K 6) (K 8) (Gl 2) (Gl 3)
    (fun r x y => setB r (cmδ2 (getB r) x y)) (fun r x y => cmO2a (getB r) x y)
    (fun r x y => cmO2b (getB r) x y)
  g3 : M (Gl 3) = clearStmt (K 8) (Gl 3) (Gl 4)
  g4 : M (Gl 4) = mvStmt (K 7) (K 0) (Gl 4) (Gl 5)
  g5 : M (Gl 5) = mvStmt (K 10) (K 9) (Gl 5) (Gl 6)
  t6a : M (Gl 6) = testStmt (K 9) (Gl 7) (Gl 13)
  t6b : M (Gl 7) = ctlStmt (K 6) (K 9) (K 3) (K 12) (Gl 7) (Gl 8)
    (fun r x y => setC r (cwδ capW (getC r) x y))
    (fun r x y => co1 capW (getC r) x y) (fun r x y => co2 capW (getC r) x y)
  t6c : M (Gl 8) = mvStmt (K 3) (K 9) (Gl 8) (Gl 9)
  t6d : M (Gl 9) = mvStmt (K 12) (K 6) (Gl 9) (Gl 10)
  t6e : M (Gl 10) = ctlStmt (K 6) (K 9) (K 10) (K 12) (Gl 10) (Gl 11)
    (fun r x y => setC r (cwδ cnotAW (getC r) x y))
    (fun r x y => co1 cnotAW (getC r) x y) (fun r x y => co2 cnotAW (getC r) x y)
  t6f : M (Gl 11) = p2Stmt (K 9) (K 10) (Gl 12) (gC getC) (fun r _ _ => setC r (s0, none))
  t6g : M (Gl 12) = mvStmt (K 12) (K 6) (Gl 12) (Gl 6)
  g13 : M (Gl 13) = mvStmt (K 11) (K 9) (Gl 13) (Gl 14)
  t14a : M (Gl 14) = testStmt (K 9) (Gl 15) (Gl 21)
  t14b : M (Gl 15) = ctlStmt (K 6) (K 9) (K 3) (K 12) (Gl 15) (Gl 16)
    (fun r x y => setC r (cwδ capW (getC r) x y))
    (fun r x y => co1 capW (getC r) x y) (fun r x y => co2 capW (getC r) x y)
  t14c : M (Gl 16) = mvStmt (K 3) (K 9) (Gl 16) (Gl 17)
  t14d : M (Gl 17) = mvStmt (K 12) (K 6) (Gl 17) (Gl 18)
  t14e : M (Gl 18) = ctlStmt (K 6) (K 9) (K 11) (K 12) (Gl 18) (Gl 19)
    (fun r x y => setC r (cwδ cnotAW (getC r) x y))
    (fun r x y => co1 cnotAW (getC r) x y) (fun r x y => co2 cnotAW (getC r) x y)
  t14f : M (Gl 19) = p2Stmt (K 9) (K 11) (Gl 20) (gC getC) (fun r _ _ => setC r (s0, none))
  t14g : M (Gl 20) = mvStmt (K 12) (K 6) (Gl 20) (Gl 14)
  g21 : M (Gl 21) = clearStmt (K 6) (Gl 21) (Gl 22)
  g22 : M (Gl 22) = pushL (K 13) [true, false, false] Ex

/-- the time of one CNOT step -/
def cnTime (n m lT lD : ℕ) : ℕ :=
  (4 * n + 4) + (n + 1) + (lT + 1) + (n * (5 * m + 7) + 1) + (lD + 1) +
    (n * (5 * m + 7) + 1) + (m + 1) + 1

theorem cnot_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 15 → Kb)
    (hK : Function.Injective K) (Gl : Fin 23 → Λ) (Ex : Λ)
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool))
    (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε)
    (hgsC : ∀ r t, getC (setC r t) = t) (hssC : ∀ r t t', setC (setC r t) t' = setC r t')
    (hsgC : ∀ r, setC r (getC r) = r) (s0 : Pauli × Pauli)
    (hp : CNProg M K Gl Ex getB setB getC setC s0)
    {n : ℕ} (cw tw : Fin n) (hct : cw ≠ tw) (T D : Tableau n) (c : Bool) (r : MS ε)
    (hrB : getB r = false) (hrC : getC r = (s0, none))
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (h0 : B (K 0) = List.replicate n true) (h1 : B (K 1) = List.replicate cw.val true)
    (h2 : B (K 2) = List.replicate tw.val true) (h3 : B (K 3) = []) (h4 : B (K 4) = [])
    (h5 : B (K 5) = []) (h6 : B (K 6) = []) (h7 : B (K 7) = []) (h8 : B (K 8) = [])
    (h9 : B (K 9) = []) (h10 : B (K 10) = encodeTableau T) (h11 : B (K 11) = encodeTableau D)
    (h12 : B (K 12) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some (Gl 0), ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), r), mk B' Q⟩
        (cnTime n (cmaskR n cw tw).length (encodeTableau T).length (encodeTableau D).length) ∧
      B' (K 0) = List.replicate n true ∧
      B' (K 10) = encodeTableau (fun j => cnotPS cw tw (T j)) ∧
      B' (K 11) = encodeTableau (fun j => cnotPS cw tw (D j)) ∧
      B' (K 13) = [false, false, true] ++ B (K 13) ∧
      (∀ i : Fin 15, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 14) = B (K 14) ∧
      ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have ne : ∀ i j : Fin 15, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  -- 1. build the mask
  have hK' : Function.Injective (K ∘ cnemb) := hK.comp cnemb_inj
  obtain ⟨B2, R2, e2Mk, e2Nt, e20, e21, e22, e23, e24, e27, e2f⟩ :=
    cmask_build M (K ∘ cnemb) hK' (Gl 0) (Gl 1) (Gl 2) (Gl 3) (Gl 4) getB setB hgsB hssB hsgB
      hp.g0 hp.g1 hp.g2 hp.g3 cw tw c r hrB B Q h0 h1 h2 h4 h5 h8
  have e2f' : ∀ x, x ≠ K 0 → x ≠ K 1 → x ≠ K 2 → x ≠ K 4 → x ≠ K 5 → x ≠ K 6 → x ≠ K 7 →
      x ≠ K 8 → B2 x = B x := by
    intro x a0 a1 a2 a4 a5 a6 a7 a8
    apply e2f x
    intro i
    fin_cases i
    · exact a0
    · exact a1
    · exact a2
    · exact a4
    · exact a5
    · exact a6
    · exact a7
    · exact a8
  simp only [Function.comp_apply] at e2Mk e2Nt e20 e21 e22 e23 e24 e27
  have g3' : cnemb 3 = 4 := rfl
  have g4' : cnemb 4 = 5 := rfl
  have g5' : cnemb 5 = 6 := rfl
  have g6' : cnemb 6 = 7 := rfl
  have g7' : cnemb 7 = 8 := rfl
  have g0' : cnemb 0 = 0 := rfl
  have g1' : cnemb 1 = 1 := rfl
  have g2' : cnemb 2 = 2 := rfl
  rw [g0'] at e20; rw [g1'] at e21; rw [g2'] at e22; rw [g3'] at e23; rw [g4'] at e24
  rw [g5', h6, List.append_nil] at e2Mk; rw [g6', h7, List.append_nil] at e2Nt; rw [g7'] at e27
  -- 2. restore 1^n
  obtain ⟨B3, R3, e3a, e3b, e3f⟩ := mvE M (K 7) (K 0) (ne 7 0 (by decide)) (Gl 4) (Gl 5) hp.g4 r c Q
    _ B2 e2Nt
  have fr3 : ∀ j : Fin 15, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 →
      B3 (K j) = B (K j) := by
    intro j a0 a1 a2 a4 a5 a6 a7 a8
    rw [e3f _ (ne _ _ a7) (ne _ _ a0), e2f' _ (ne _ _ a0) (ne _ _ a1) (ne _ _ a2) (ne _ _ a4)
      (ne _ _ a5) (ne _ _ a6) (ne _ _ a7) (ne _ _ a8)]
  -- 3. T to X
  obtain ⟨B4, R4, e4a, e4b, e4f⟩ := mvE M (K 10) (K 9) (ne 10 9 (by decide)) (Gl 5) (Gl 6) hp.g5 r c
    Q _ B3 (by rw [fr3 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h10])
  have hX4 : B4 (K 9) = (encodeTableau T).reverse := by
    rw [e4b, fr3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h9, List.append_nil]
  have hMk4 : B4 (K 6) = cmaskR n cw tw := by
    rw [e4f _ (ne 6 10 (by decide)) (ne 6 9 (by decide)), e3f _ (ne 6 7 (by decide))
      (ne 6 0 (by decide)), e2Mk]
  have fr4 : ∀ j : Fin 15, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 →
      j ≠ 9 → j ≠ 10 → B4 (K j) = B (K j) := by
    intro j a0 a1 a2 a4 a5 a6 a7 a8 a9 a10
    rw [e4f _ (ne _ _ a10) (ne _ _ a9), fr3 j a0 a1 a2 a4 a5 a6 a7 a8]
  have hS4 : B4 (K 12) = [] := by
    rw [fr4 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h12]
  have hZ4 : B4 (K 3) = [] := by
    rw [fr4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h3]
  -- 4. CNOT pass on T
  have R5 := cnot_tab M (K 6) (K 9) (K 10) (K 3) (K 12) (ne 6 9 (by decide)) (ne 6 10 (by decide))
    (ne 6 3 (by decide)) (ne 6 12 (by decide)) (ne 9 10 (by decide)) (ne 9 3 (by decide))
    (ne 9 12 (by decide)) (ne 10 3 (by decide)) (ne 10 12 (by decide)) (ne 3 12 (by decide))
    (Gl 6) (Gl 7) (Gl 8) (Gl 9) (Gl 10) (Gl 11) (Gl 12) (Gl 13) getC setC hgsC hssC hsgC cw tw hct
    s0 hp.t6a hp.t6b hp.t6c hp.t6d hp.t6e hp.t6f hp.t6g c r hrC T B4 Q hMk4 hX4 hS4 hZ4
  set B5 := Function.update (Function.update B4 (K 9) []) (K 10)
    (encodeTableau (fun j => cnotPS cw tw (T j)) ++ B4 (K 10)) with hB5
  have e5f : ∀ x, x ≠ K 9 → x ≠ K 10 → B5 x = B4 x := fun x a b => by
    rw [hB5, Function.update_of_ne b, Function.update_of_ne a]
  have e5X : B5 (K 9) = [] := by
    rw [hB5, Function.update_of_ne (ne 9 10 (by decide)), Function.update_self]
  have e5T : B5 (K 10) = encodeTableau (fun j => cnotPS cw tw (T j)) := by
    rw [hB5, Function.update_self, e4a, List.append_nil]
  -- 5. D to X
  obtain ⟨B6, R6, e6a, e6b, e6f⟩ := mvE M (K 11) (K 9) (ne 11 9 (by decide)) (Gl 13) (Gl 14) hp.g13
    r c Q _ B5 (by rw [e5f _ (ne 11 9 (by decide)) (ne 11 10 (by decide)), fr4 11 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h11])
  have m6 : ∀ j : Fin 15, j ≠ 9 → j ≠ 10 → j ≠ 11 → B6 (K j) = B4 (K j) := fun j a9 a10 a11 => by
    rw [e6f _ (ne _ _ a11) (ne _ _ a9), e5f _ (ne _ _ a9) (ne _ _ a10)]
  have R7 := cnot_tab M (K 6) (K 9) (K 11) (K 3) (K 12) (ne 6 9 (by decide)) (ne 6 11 (by decide))
    (ne 6 3 (by decide)) (ne 6 12 (by decide)) (ne 9 11 (by decide)) (ne 9 3 (by decide))
    (ne 9 12 (by decide)) (ne 11 3 (by decide)) (ne 11 12 (by decide)) (ne 3 12 (by decide))
    (Gl 14) (Gl 15) (Gl 16) (Gl 17) (Gl 18) (Gl 19) (Gl 20) (Gl 21) getC setC hgsC hssC hsgC cw tw
    hct s0 hp.t14a hp.t14b hp.t14c hp.t14d hp.t14e hp.t14f hp.t14g c r hrC D B6 Q
    (by rw [m6 6 (by decide) (by decide) (by decide), hMk4])
    (by rw [e6b, e5X, List.append_nil])
    (by rw [m6 12 (by decide) (by decide) (by decide), hS4])
    (by rw [m6 3 (by decide) (by decide) (by decide), hZ4])
  set B7 := Function.update (Function.update B6 (K 9) []) (K 11)
    (encodeTableau (fun j => cnotPS cw tw (D j)) ++ B6 (K 11)) with hB7
  have e7f : ∀ x, x ≠ K 9 → x ≠ K 11 → B7 x = B6 x := fun x a b => by
    rw [hB7, Function.update_of_ne b, Function.update_of_ne a]
  -- 6. clear the mask
  obtain ⟨B8, R8, e8a, e8f⟩ := clearE M (K 6) (Gl 21) (Gl 22) hp.g21 r c Q _ B7
    (by rw [e7f _ (ne 6 9 (by decide)) (ne 6 11 (by decide)), m6 6 (by decide) (by decide)
          (by decide), hMk4])
  -- 7. push the transcript code
  have R9 := pushL_run M (K 13) (Gl 22) Ex [true, false, false] hp.g22 r c B8 Q
  set B9 := Function.update B8 (K 13) ([true, false, false].reverse ++ B8 (K 13)) with hB9
  have e9f : ∀ x, x ≠ K 13 → B9 x = B8 x := fun x a => by rw [hB9, Function.update_of_ne a]
  have to4 : ∀ j : Fin 15, j ≠ 6 → j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 13 → B9 (K j) = B4 (K j) := by
    intro j a6 a9 a10 a11 a13
    rw [e9f _ (ne _ _ a13), e8f _ (ne _ _ a6), e7f _ (ne _ _ a9) (ne _ _ a11), m6 j a9 a10 a11]
  have to2 : ∀ j : Fin 15, j ≠ 0 → j ≠ 6 → j ≠ 7 → j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 13 →
      B9 (K j) = B2 (K j) := by
    intro j a0 a6 a7 a9 a10 a11 a13
    rw [to4 j a6 a9 a10 a11 a13, e4f _ (ne _ _ a10) (ne _ _ a9), e3f _ (ne _ _ a7) (ne _ _ a0)]
  refine ⟨B9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have R := ((((((R2.trans R3).trans R4).trans R5).trans R6).trans R7).trans R8).trans R9
    refine R.mono (le_of_eq ?_)
    simp only [cnTime, List.length_replicate, List.length_append, List.length_reverse]
  · rw [to4 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      e4f _ (ne 0 10 (by decide)) (ne 0 9 (by decide)), e3b, e20,
      List.reverse_replicate, List.append_nil]
  · rw [e9f _ (ne 10 13 (by decide)), e8f _ (ne 10 6 (by decide)), e7f _ (ne 10 9 (by decide))
      (ne 10 11 (by decide)), e6f _ (ne 10 11 (by decide)) (ne 10 9 (by decide)), e5T]
  · rw [e9f _ (ne 11 13 (by decide)), e8f _ (ne 11 6 (by decide)), hB7, Function.update_self,
      e6a, List.append_nil]
  · rw [hB9, Function.update_self, e8f _ (ne 13 6 (by decide)), e7f _ (ne 13 9 (by decide))
      (ne 13 11 (by decide)), m6 13 (by decide) (by decide) (by decide), fr4 13 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    rfl
  · intro i a0 a10 a11 a13 a14
    fin_cases i
    · show B9 (K 0) = []
      exact absurd rfl a0
    · show B9 (K 1) = []
      rw [to2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e21]
    · show B9 (K 2) = []
      rw [to2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e22]
    · show B9 (K 3) = []
      rw [to4 3 (by decide) (by decide) (by decide) (by decide) (by decide), hZ4]
    · show B9 (K 4) = []
      rw [to2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e23]
    · show B9 (K 5) = []
      rw [to2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e24]
    · show B9 (K 6) = []
      rw [e9f _ (ne 6 13 (by decide)), e8a]
    · show B9 (K 7) = []
      rw [to4 7 (by decide) (by decide) (by decide) (by decide) (by decide),
        e4f _ (ne 7 10 (by decide)) (ne 7 9 (by decide)), e3a]
    · show B9 (K 8) = []
      rw [to2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e27]
    · show B9 (K 9) = []
      rw [e9f _ (ne 9 13 (by decide)), e8f _ (ne 9 6 (by decide)), hB7,
        Function.update_of_ne (ne 9 11 (by decide)), Function.update_self]
    · show B9 (K 10) = []
      exact absurd rfl a10
    · show B9 (K 11) = []
      exact absurd rfl a11
    · show B9 (K 12) = []
      rw [to4 12 (by decide) (by decide) (by decide) (by decide) (by decide), hS4]
    · show B9 (K 13) = []
      exact absurd rfl a13
    · show B9 (K 14) = []
      exact absurd rfl a14
  · rw [to4 14 (by decide) (by decide) (by decide) (by decide) (by decide), fr4 14 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · intro x hx
    rw [e9f _ (hx 13), e8f _ (hx 6), e7f _ (hx 9) (hx 11), e6f _ (hx 11) (hx 9),
      e5f _ (hx 9) (hx 10), e4f _ (hx 10) (hx 9), e3f _ (hx 7) (hx 0),
      e2f' _ (hx 0) (hx 1) (hx 2) (hx 4) (hx 5) (hx 6) (hx 7) (hx 8)]

end CnotStep

end OCRS19TM

namespace OCRS19TM

/-! ### Measurement step: full measurement on `(T, D)` in the 16-stack loop layout
Stacks `K 0..15` = `N KW W2 W3 c3 c4 Mk Nt c7 X F FD S H _ X2`; mask `mmask Mp` on `K 6`. -/
section MeasStep

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ε : Type}

/-- push the transcript code `11β` of a measurement (reversed on the stack), `β` read from the state -/
def pushMStmt (a : Kb) (f : MS ε → Bool) (E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  TM2.Stmt.push (Sum.inl a) (fun _ => true) (TM2.Stmt.push (Sum.inl a) (fun _ => true)
    (TM2.Stmt.push (Sum.inl a) (fun v => f v.2) (TM2.Stmt.goto fun _ => E)))

lemma pushM_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (a : Kb) (L E : Λ)
    (f : MS ε → Bool) (hM : M L = pushMStmt a f E) (r : MS ε) (c : Bool) (B : Kb → List Bool)
    (Q : ∀ r, List (G r)) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), r), mk (Function.update B a ([f r, true, true] ++ B a)) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, pushMStmt, TM2.stepAux, mk_inl, update_mk, Function.update_self,
    Function.update_idem, List.cons_append, List.nil_append]

def memb : Fin 8 → Fin 16 := ![6, 9, 10, 1, 2, 3, 4, 5]
def demb : Fin 8 → Fin 16 := ![6, 7, 11, 1, 2, 3, 4, 8]
def xemb : Fin 8 → Fin 16 := ![6, 12, 15, 1, 2, 3, 4, 5]

lemma memb_inj : Function.Injective memb := by decide
lemma demb_inj : Function.Injective demb := by decide
lemma xemb_inj : Function.Injective xemb := by decide

/-- the measurement program: move T, D to the reversed input stacks, random/deterministic
measurement (one shared front, branching on the T pass), clean up, push the transcript code -/
structure MeasW (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb) (L : Fin 20 → Λ)
    (LD : Fin 16 → Λ) (LX : Fin 17 → Λ) (LT : Fin 11 → Λ)
    (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex : Λ) : Prop where
  w0 : M W0 = mvStmt (K 10) (K 9) W0 W1
  w1 : M W1 = mvStmt (K 11) (K 7) W1 E1
  rand : RandProg M (K ∘ memb) (K ∘ demb) L LD E1 E2 E3 ED E4 Eb (LT 0)
  det : DetProg M (K ∘ memb) (K ∘ demb) (K ∘ xemb) LX LT E5
  r0 : M E4 = clearStmt (K 3) E4 R1
  r1 : M R1 = clearStmt (K 6) R1 R2
  r2 : M R2 = pushMStmt (K 13) (fun r => r.cb) Ex
  d0 : M E5 = clearStmt (K 6) E5 D1
  d1 : M D1 = pushMStmt (K 13) (fun r => decide (r.cp = 2)) Ex

/-- the phase of the deterministic-outcome product computed by the X pass -/
def detCp {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) : ZMod 4 :=
  ((List.ofFn fun i => if antiK (D i) Mp then T i else oneK n).foldr PauliString.mul (oneK n)).phase

/-- random-outcome measurement step (outcome = the coin `r.cb`) -/
theorem meas_rand_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (LX : Fin 17 → Λ)
    (LT : Fin 11 → Λ) (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex : Λ)
    (hP : MeasW M K L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex)
    {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) (p : Fin n) (hp : lastK T Mp = some p)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (h6 : B (K 6) = mmask Mp) (h10 : B (K 10) = encodeTableau T)
    (h11 : B (K 11) = encodeTableau D)
    (he : ∀ i : Fin 16, i ≠ 0 → i ≠ 6 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some W0, ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), { r with cp := (T p).phase }), mk B' Q⟩
        (((encodeTableau T).length + 1) + (((encodeTableau D).length + 1) +
          (((n * (10 * n + 12 + 1) + 1) + (1 + ((n + 1) + (1 + (n * (10 * n + 16 + 1) + 1))))) +
          (((mmask (T p).ops).length + 1) + (((mmask Mp).length + 1) + 1))))) ∧
      B' (K 10) = encodeTableau (updMK T Mp p r.cb) ∧
      B' (K 11) = encodeTableau (updDMK T D Mp p) ∧
      B' (K 13) = [r.cb, true, true] ++ B (K 13) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 0) = B (K 0) ∧ B' (K 14) = B (K 14) ∧ ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  obtain ⟨hran, hrmu, hrfd⟩ := hr
  have ne : ∀ i j : Fin 16, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  have nm : ∀ j : Fin 16, (∀ i, j ≠ memb i) → ∀ i, K j ≠ (K ∘ memb) i := fun j h i => ne _ _ (h i)
  have nd : ∀ j : Fin 16, (∀ i, j ≠ demb i) → ∀ i, K j ≠ (K ∘ demb) i := fun j h i => ne _ _ (h i)
  obtain ⟨B1, R1', a10, a9, af⟩ := mvE M (K 10) (K 9) (ne 10 9 (by decide)) W0 W1 hP.w0 r c Q
    (encodeTableau T) B h10
  obtain ⟨B2, R2', b11, b7, bf⟩ := mvE M (K 11) (K 7) (ne 11 7 (by decide)) W1 E1 hP.w1 r c Q
    (encodeTableau D) B1 (by rw [af _ (ne 11 10 (by decide)) (ne 11 9 (by decide)), h11])
  have e2' : ∀ i : Fin 16, (i ≠ 7 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 11) → B2 (K i) = B (K i) := fun i h => by
    rw [bf _ (ne i 11 h.2.2.2) (ne i 7 h.1), af _ (ne i 10 h.2.2.1) (ne i 9 h.2.1)]
  have e2 : ∀ i : Fin 16, (i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 11 ∧ i ≠ 13 ∧ i ≠ 14) →
      B2 (K i) = [] := fun i h => by
    rw [e2' i ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩,
      he i h.1 h.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2]
  obtain ⟨B3, R3', c2, c2', c1, c1', c7, c7', c0, c3, c4, c6, c5, cf⟩ :=
    rand_meas M (K ∘ memb) (K ∘ demb) (hK.comp memb_inj) (hK.comp demb_inj)
      (nm 7 (by decide)) (nm 11 (by decide)) (nm 8 (by decide))
      L LD E1 E2 E3 ED E4 Eb (LT 0) hP.rand T D Mp p hp c Q r B2 ⟨hran, hrmu, hrfd⟩
      ⟨by show B2 (K 6) = _; rw [e2' 6 (by decide), h6], e2 1 (by decide), e2 2 (by decide),
        e2 4 (by decide), e2 3 (by decide), e2 5 (by decide), e2 8 (by decide)⟩
      (by show B2 (K 9) = _
          rw [bf _ (ne 9 11 (by decide)) (ne 9 7 (by decide)), a9,
            he 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            List.append_nil])
      (by show B2 (K 7) = _
          rw [b7, af _ (ne 7 10 (by decide)) (ne 7 9 (by decide)),
            he 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            List.append_nil])
  have c2a : B3 (K 10) = encodeTableau (updMK T Mp p r.cb) ++ B2 (K 10) := c2
  have c2b : B3 (K 11) = encodeTableau (updDMK T D Mp p) ++ B2 (K 11) := c2'
  have c5' : B3 (K 3) = mmask (T p).ops := c5
  have f3 : ∀ j : Fin 16, (∀ i, j ≠ memb i) → (∀ i, j ≠ demb i) → B3 (K j) = B2 (K j) :=
    fun j h1 h2 => cf _ (nm j h1) (nd j h2)
  obtain ⟨B4, R4', d3, df⟩ := clearE M (K 3) E4 R1 hP.r0 { r with cp := (T p).phase } c Q _ B3 c5'
  obtain ⟨B5, R5', d6, df'⟩ := clearE M (K 6) R1 R2 hP.r1 { r with cp := (T p).phase } c Q
    (mmask Mp) B4 (by rw [df _ (ne 6 3 (by decide))]; exact c0)
  have R6 := pushM_run M (K 13) R2 Ex (fun r : MS ε => r.cb) hP.r2 { r with cp := (T p).phase } c
    B5 Q
  have g3 : ∀ i : Fin 16, i ≠ 3 → i ≠ 6 → i ≠ 13 →
      Function.update B5 (K 13) ([r.cb, true, true] ++ B5 (K 13)) (K i) = B3 (K i) :=
    fun i h3 h6 h13 => by
      rw [Function.update_of_ne (ne i 13 h13), df' _ (ne i 6 h6), df _ (ne i 3 h3)]
  set Bf := Function.update B5 (K 13) ([r.cb, true, true] ++ B5 (K 13)) with hBf
  refine ⟨Bf,
    R1'.trans (R2'.trans (R3'.trans (R4'.trans (R5'.trans R6)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g3 10 (by decide) (by decide) (by decide), c2a,
      bf _ (ne 10 11 (by decide)) (ne 10 7 (by decide)), a10, List.append_nil]
  · rw [g3 11 (by decide) (by decide) (by decide), c2b, b11, List.append_nil]
  · rw [hBf, Function.update_self, df' _ (ne 13 6 (by decide)), df _ (ne 13 3 (by decide)),
      f3 13 (by decide) (by decide), e2' 13 (by decide)]
  · intro i a0 a10 a11 a13 a14
    fin_cases i
    · exact absurd rfl a0
    · show Bf (K 1) = []
      rw [g3 1 (by decide) (by decide) (by decide)]; exact c3
    · show Bf (K 2) = []
      rw [g3 2 (by decide) (by decide) (by decide)]; exact c4
    · show Bf (K 3) = []
      rw [hBf, Function.update_of_ne (ne 3 13 (by decide)), df' _ (ne 3 6 (by decide)), d3]
    · show Bf (K 4) = []
      rw [g3 4 (by decide) (by decide) (by decide)]; exact c6
    · show Bf (K 5) = []
      rw [g3 5 (by decide) (by decide) (by decide)]; exact c7
    · show Bf (K 6) = []
      rw [hBf, Function.update_of_ne (ne 6 13 (by decide)), d6]
    · show Bf (K 7) = []
      rw [g3 7 (by decide) (by decide) (by decide)]; exact c1'
    · show Bf (K 8) = []
      rw [g3 8 (by decide) (by decide) (by decide)]; exact c7'
    · show Bf (K 9) = []
      rw [g3 9 (by decide) (by decide) (by decide)]; exact c1
    · exact absurd rfl a10
    · exact absurd rfl a11
    · show Bf (K 12) = []
      rw [g3 12 (by decide) (by decide) (by decide), f3 12 (by decide) (by decide),
        e2 12 (by decide)]
    · exact absurd rfl a13
    · exact absurd rfl a14
    · show Bf (K 15) = []
      rw [g3 15 (by decide) (by decide) (by decide), f3 15 (by decide) (by decide),
        e2 15 (by decide)]
  · rw [g3 0 (by decide) (by decide) (by decide), f3 0 (by decide) (by decide),
      e2' 0 (by decide)]
  · rw [g3 14 (by decide) (by decide) (by decide), f3 14 (by decide) (by decide),
      e2' 14 (by decide)]
  · intro x hx
    rw [hBf, Function.update_of_ne (hx 13), df' _ (hx 6), df _ (hx 3),
      cf _ (fun i => hx (memb i)) (fun i => hx (demb i)), bf _ (hx 11) (hx 7), af _ (hx 10) (hx 9)]

/-- deterministic-outcome measurement step (outcome = `detCp T D Mp = 2`) -/
theorem meas_det_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (LX : Fin 17 → Λ)
    (LT : Fin 11 → Λ) (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex : Λ)
    (hP : MeasW M K L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex)
    {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) (hp : lastK T Mp = none)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (h6 : B (K 6) = mmask Mp) (h10 : B (K 10) = encodeTableau T)
    (h11 : B (K 11) = encodeTableau D)
    (he : ∀ i : Fin 16, i ≠ 0 → i ≠ 6 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some W0, ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), { r with cp := detCp T D Mp }), mk B' Q⟩
        (((encodeTableau T).length + 1) + (((encodeTableau D).length + 1) +
          (((n * (10 * n + 12 + 1) + 1) + (1 + (3 * (encodeTableau D).length +
            2 * (encodeTableau T).length + n * (14 * n + 17) + 7 * n + 12))) +
          (((mmask Mp).length + 1) + 1)))) ∧
      B' (K 10) = encodeTableau T ∧ B' (K 11) = encodeTableau D ∧
      B' (K 13) = [decide (detCp T D Mp = 2), true, true] ++ B (K 13) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 0) = B (K 0) ∧ B' (K 14) = B (K 14) ∧ ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  obtain ⟨hran, hrmu, hrfd⟩ := hr
  have ne : ∀ i j : Fin 16, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  have nm : ∀ j : Fin 16, (∀ i, j ≠ memb i) → ∀ i, K j ≠ (K ∘ memb) i := fun j h i => ne _ _ (h i)
  have nd : ∀ j : Fin 16, (∀ i, j ≠ demb i) → ∀ i, K j ≠ (K ∘ demb) i := fun j h i => ne _ _ (h i)
  obtain ⟨B1, R1', a10, a9, af⟩ := mvE M (K 10) (K 9) (ne 10 9 (by decide)) W0 W1 hP.w0 r c Q
    (encodeTableau T) B h10
  obtain ⟨B2, R2', b11, b7, bf⟩ := mvE M (K 11) (K 7) (ne 11 7 (by decide)) W1 E1 hP.w1 r c Q
    (encodeTableau D) B1 (by rw [af _ (ne 11 10 (by decide)) (ne 11 9 (by decide)), h11])
  have e2' : ∀ i : Fin 16, (i ≠ 7 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 11) → B2 (K i) = B (K i) := fun i h => by
    rw [bf _ (ne i 11 h.2.2.2) (ne i 7 h.1), af _ (ne i 10 h.2.2.1) (ne i 9 h.2.1)]
  have e2 : ∀ i : Fin 16, (i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 11 ∧ i ≠ 13 ∧ i ≠ 14) →
      B2 (K i) = [] := fun i h => by
    rw [e2' i ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩,
      he i h.1 h.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2]
  obtain ⟨B3, R3', c2, c2', c1, c1', c7, c5, cx1, cx2, c0, c3, c4, c6, cf⟩ :=
    det_meas M (K ∘ memb) (K ∘ demb) (K ∘ xemb) (hK.comp memb_inj) (hK.comp demb_inj)
      (hK.comp xemb_inj) (nm 7 (by decide)) (nm 11 (by decide)) (nm 12 (by decide))
      (nm 15 (by decide)) (nd 12 (by decide)) (nd 15 (by decide))
      L LD E1 E2 E3 ED E4 Eb LX LT E5 hP.rand hP.det T D Mp hp c Q r B2 ⟨hran, hrmu, hrfd⟩
      ⟨by show B2 (K 6) = _; rw [e2' 6 (by decide), h6], e2 1 (by decide), e2 2 (by decide),
        e2 4 (by decide), e2 3 (by decide), e2 5 (by decide),
        by show B2 (K 10) = _; rw [bf _ (ne 10 11 (by decide)) (ne 10 7 (by decide)), a10],
        b11, e2 12 (by decide), e2 15 (by decide)⟩
      (by show B2 (K 9) = _
          rw [bf _ (ne 9 11 (by decide)) (ne 9 7 (by decide)), a9,
            he 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            List.append_nil])
      (by show B2 (K 7) = _
          rw [b7, af _ (ne 7 10 (by decide)) (ne 7 9 (by decide)),
            he 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            List.append_nil])
  have f3 : ∀ j : Fin 16, (j ≠ 6 ∧ j ≠ 9 ∧ j ≠ 10 ∧ j ≠ 3 ∧ j ≠ 4 ∧ j ≠ 5 ∧ j ≠ 7 ∧ j ≠ 11 ∧
      j ≠ 12 ∧ j ≠ 15) → B3 (K j) = B2 (K j) := fun j h =>
    cf _ (ne j 6 h.1) (ne j 9 h.2.1) (ne j 10 h.2.2.1) (ne j 3 h.2.2.2.1) (ne j 4 h.2.2.2.2.1)
      (ne j 5 h.2.2.2.2.2.1) (ne j 7 h.2.2.2.2.2.2.1) (ne j 11 h.2.2.2.2.2.2.2.1)
      (ne j 12 h.2.2.2.2.2.2.2.2.1) (ne j 15 h.2.2.2.2.2.2.2.2.2)
  obtain ⟨B5, R5', d6, df'⟩ := clearE M (K 6) E5 D1 hP.d0 { r with cp := detCp T D Mp } c Q
    (mmask Mp) B3 c0
  have R6 := pushM_run M (K 13) D1 Ex (fun r : MS ε => decide (r.cp = 2)) hP.d1
    { r with cp := detCp T D Mp } c B5 Q
  have g3 : ∀ i : Fin 16, i ≠ 6 → i ≠ 13 →
      Function.update B5 (K 13) ([decide (detCp T D Mp = 2), true, true] ++ B5 (K 13)) (K i) =
        B3 (K i) :=
    fun i h6 h13 => by rw [Function.update_of_ne (ne i 13 h13), df' _ (ne i 6 h6)]
  set Bf := Function.update B5 (K 13) ([decide (detCp T D Mp = 2), true, true] ++ B5 (K 13))
    with hBf
  refine ⟨Bf,
    R1'.trans (R2'.trans (R3'.trans (R5'.trans R6))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g3 10 (by decide) (by decide)]; exact c2
  · rw [g3 11 (by decide) (by decide)]; exact c2'
  · rw [hBf, Function.update_self, df' _ (ne 13 6 (by decide)), f3 13 (by decide), e2' 13 (by decide)]
  · intro i a0 a10 a11 a13 a14
    fin_cases i
    · exact absurd rfl a0
    · show Bf (K 1) = []
      rw [g3 1 (by decide) (by decide)]; exact c3
    · show Bf (K 2) = []
      rw [g3 2 (by decide) (by decide)]; exact c4
    · show Bf (K 3) = []
      rw [g3 3 (by decide) (by decide)]; exact c5
    · show Bf (K 4) = []
      rw [g3 4 (by decide) (by decide)]; exact c6
    · show Bf (K 5) = []
      rw [g3 5 (by decide) (by decide)]; exact c7
    · show Bf (K 6) = []
      rw [hBf, Function.update_of_ne (ne 6 13 (by decide)), d6]
    · show Bf (K 7) = []
      rw [g3 7 (by decide) (by decide)]; exact c1'
    · show Bf (K 8) = []
      rw [g3 8 (by decide) (by decide), f3 8 (by decide), e2 8 (by decide)]
    · show Bf (K 9) = []
      rw [g3 9 (by decide) (by decide)]; exact c1
    · exact absurd rfl a10
    · exact absurd rfl a11
    · show Bf (K 12) = []
      rw [g3 12 (by decide) (by decide)]; exact cx1
    · exact absurd rfl a13
    · exact absurd rfl a14
    · show Bf (K 15) = []
      rw [g3 15 (by decide) (by decide)]; exact cx2
  · rw [g3 0 (by decide) (by decide), f3 0 (by decide), e2' 0 (by decide)]
  · rw [g3 14 (by decide) (by decide), f3 14 (by decide), e2' 14 (by decide)]
  · intro x hx
    rw [hBf, Function.update_of_ne (hx 13), df' _ (hx 6),
      cf _ (hx 6) (hx 9) (hx 10) (hx 3) (hx 4) (hx 5) (hx 7) (hx 11) (hx 12) (hx 15),
      bf _ (hx 11) (hx 7), af _ (hx 10) (hx 9)]

/-- pop one coin pair `[true, β]` from stack `a` into the state's coin bit `cb` -/
def coinStmt (a : Kb) (E : Λ) : TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  TM2.Stmt.pop (Sum.inl a) (fun v _ => v)
    (TM2.Stmt.pop (Sum.inl a) (fun v x => (v.1, { v.2 with cb := x.getD false }))
      (TM2.Stmt.goto fun _ => E))

lemma coin_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (a : Kb) (L E : Λ)
    (hM : M L = coinStmt a E) (r : MS ε) (c : Bool) (B : Kb → List Bool)
    (Q : ∀ r, List (G r)) (β : Bool) (A : List Bool) (hA : B a = true :: β :: A) :
    Reach M ⟨some L, ((none, none, c), r), mk B Q⟩
      ⟨some E, ((none, none, c), { r with cb := β }), mk (Function.update B a A) Q⟩ 1 := by
  apply Reach.single
  simp only [TM2.step, hM, coinStmt, TM2.stepAux, mk_inl, update_mk, Function.update_self,
    Function.update_idem, hA, List.head?_cons, List.tail_cons, Option.getD_some]

end MeasStep

end OCRS19TM

namespace OCRS19TM

section MeasRun

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ε : Type}

/-- the K-side CHP measurement update (coin `b` used only in the random case) -/
def measK {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) (b : Bool) :
    (Tableau n × Tableau n) × Option Bool :=
  match lastK T Mp with
  | some p => ((updMK T Mp p b, updDMK T D Mp p), some b)
  | none => ((T, D), some (decide (detCp T D Mp = 2)))

/-- time of the measurement run after the coin pop -/
def measTime {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli) : ℕ :=
  match lastK T Mp with
  | some p => ((encodeTableau T).length + 1) + (((encodeTableau D).length + 1) +
          (((n * (10 * n + 12 + 1) + 1) + (1 + ((n + 1) + (1 + (n * (10 * n + 16 + 1) + 1))))) +
          (((mmask (T p).ops).length + 1) + (((mmask Mp).length + 1) + 1))))
  | none => ((encodeTableau T).length + 1) + (((encodeTableau D).length + 1) +
          (((n * (10 * n + 12 + 1) + 1) + (1 + (3 * (encodeTableau D).length +
            2 * (encodeTableau T).length + n * (14 * n + 17) + 7 * n + 12))) +
          (((mmask Mp).length + 1) + 1)))

/-- one whole measurement step: pop the coin pair from `K 14`, then the random or deterministic
CHP measurement (the machine branches by itself). -/
theorem meas_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (LX : Fin 17 → Λ)
    (LT : Fin 11 → Λ) (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex Lc : Λ)
    (hP : MeasW M K L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex)
    (hc : M Lc = coinStmt (K 14) W0)
    {n : ℕ} (T D : Tableau n) (Mp : Fin n → Pauli)
    (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε) (B : Kb → List Bool)
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (h6 : B (K 6) = mmask Mp) (h10 : B (K 10) = encodeTableau T)
    (h11 : B (K 11) = encodeTableau D)
    (he : ∀ i : Fin 16, i ≠ 0 → i ≠ 6 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = [])
    (β : Bool) (A : List Bool) (h14 : B (K 14) = true :: β :: A) :
    ∃ (B' : Kb → List Bool) (cp : ZMod 4), Reach M ⟨some Lc, ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), { r with cb := β, cp := cp }), mk B' Q⟩
        (1 + measTime T D Mp) ∧
      B' (K 10) = encodeTableau (measK T D Mp β).1.1 ∧
      B' (K 11) = encodeTableau (measK T D Mp β).1.2 ∧
      B' (K 13) = [(measK T D Mp β).2.getD false, true, true] ++ B (K 13) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 0) = B (K 0) ∧ B' (K 14) = A ∧ ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have ne : ∀ i j : Fin 16, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  have hC := coin_run M (K 14) Lc W0 hc r c B Q β A h14
  set B1 := Function.update B (K 14) A with hB1
  have u : ∀ i : Fin 16, i ≠ 14 → B1 (K i) = B (K i) := fun i h =>
    Function.update_of_ne (ne i 14 h) _ _
  have h6' : B1 (K 6) = mmask Mp := by rw [u 6 (by decide), h6]
  have h10' : B1 (K 10) = encodeTableau T := by rw [u 10 (by decide), h10]
  have h11' : B1 (K 11) = encodeTableau D := by rw [u 11 (by decide), h11]
  have he' : ∀ i : Fin 16, i ≠ 0 → i ≠ 6 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B1 (K i) = [] :=
    fun i a b d e f g => by rw [u i g, he i a b d e f g]
  have u14 : B1 (K 14) = A := Function.update_self _ _ _
  have uf : ∀ x, (∀ i, x ≠ K i) → B1 x = B x := fun x hx => Function.update_of_ne (hx 14) _ _
  unfold measTime measK
  cases hl : lastK T Mp with
  | some p =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := meas_rand_run M K hK L LD LX LT
      W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex hP T D Mp p hl c Q { r with cb := β } B1 hr
      h6' h10' h11' he'
    refine ⟨B', (T p).phase, hC.trans hR, a10, a11, ?_, ae, ?_, ?_, ?_⟩
    · rw [a13, u 13 (by decide)]; rfl
    · rw [a0, u 0 (by decide)]
    · rw [a14, u14]
    · intro x hx; rw [af x hx, uf x hx]
  | none =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := meas_det_run M K hK L LD LX LT
      W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex hP T D Mp hl c Q { r with cb := β } B1 hr
      h6' h10' h11' he'
    refine ⟨B', detCp T D Mp, hC.trans hR, a10, a11, ?_, ae, ?_, ?_, ?_⟩
    · rw [a13, u 13 (by decide)]; rfl
    · rw [a0, u 0 (by decide)]
    · rw [a14, u14]
    · intro x hx; rw [af x hx, uf x hx]

/-- `gate1_run` in the 16-stack layout (`K 15` untouched) -/
theorem g1_16 (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (Gl : Fin 18 → Λ) (Ex : Λ) (f : Pauli → ZMod 4 × Pauli)
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getZ : MS ε → ZMod 4 × Option (Bool × Bool))
    (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε)
    (hgsZ : ∀ r t, getZ (setZ r t) = t) (hssZ : ∀ r t t', setZ (setZ r t) t' = setZ r t')
    (hsgZ : ∀ r, setZ r (getZ r) = r)
    (hp : G1Prog M (K ∘ Fin.castSucc) Gl Ex f getB setB getZ setZ)
    {n : ℕ} (q : Fin n) (T D : Tableau n) (c : Bool) (r : MS ε)
    (hrB : getB r = false) (hrZ : getZ r = (0, none))
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (h0 : B (K 0) = List.replicate n true) (h1 : B (K 1) = List.replicate q.val true)
    (h10 : B (K 10) = encodeTableau T) (h11 : B (K 11) = encodeTableau D)
    (he : ∀ i : Fin 16, i ≠ 0 → i ≠ 1 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some (Gl 0), ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), r), mk B' Q⟩
        (g1Time n q.val (cmaskR n q q).length (encodeTableau T).length (encodeTableau D).length) ∧
      B' (K 10) = encodeTableau (fun j => rowG1 f q (T j)) ∧
      B' (K 11) = encodeTableau (fun j => rowG1 f q (D j)) ∧
      B' (K 13) = [false, false, true] ++ B (K 13) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 0) = B (K 0) ∧ B' (K 14) = B (K 14) ∧ ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have ne : ∀ i j : Fin 16, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  obtain ⟨B', hR, a0, a10, a11, a13, ae, a14, af⟩ := gate1_run M (K ∘ Fin.castSucc)
    (hK.comp (Fin.castSucc_injective 15)) Gl Ex f getB setB hgsB hssB hsgB getZ setZ hgsZ hssZ hsgZ
    hp q T D c r hrB hrZ B Q h0 h1 (he 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    h10 h11 (he 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have fr : ∀ x, (∀ i : Fin 16, x ≠ K i) → ∀ i : Fin 15, x ≠ (K ∘ Fin.castSucc) i :=
    fun x hx i => hx _
  have a15 : B' (K 15) = B (K 15) := af _ fun i => ne 15 _ (fun e => by
    have := congrArg Fin.val e; simp at this; omega)
  refine ⟨B', hR, a10, a11, a13, ?_, a0.trans h0.symm, a14, fun x hx => af x (fr x hx)⟩
  intro i i0 i10 i11 i13 i14
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact ae j (fun e => i0 (by subst e; rfl)) (fun e => i10 (by subst e; rfl))
      (fun e => i11 (by subst e; rfl)) (fun e => i13 (by subst e; rfl)) (fun e => i14 (by subst e; rfl))
  · show B' (K 15) = []
    rw [a15]; exact he 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem cn_16 (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (Gl : Fin 23 → Λ) (Ex : Λ)
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool))
    (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε)
    (hgsC : ∀ r t, getC (setC r t) = t) (hssC : ∀ r t t', setC (setC r t) t' = setC r t')
    (hsgC : ∀ r, setC r (getC r) = r) (s0 : Pauli × Pauli)
    (hp : CNProg M (K ∘ Fin.castSucc) Gl Ex getB setB getC setC s0)
    {n : ℕ} (cw tw : Fin n) (hct : cw ≠ tw) (T D : Tableau n) (c : Bool) (r : MS ε)
    (hrB : getB r = false) (hrC : getC r = (s0, none))
    (B : Kb → List Bool) (Q : ∀ r, List (G r))
    (h0 : B (K 0) = List.replicate n true) (h1 : B (K 1) = List.replicate cw.val true)
    (h2 : B (K 2) = List.replicate tw.val true)
    (h10 : B (K 10) = encodeTableau T) (h11 : B (K 11) = encodeTableau D)
    (he : ∀ i : Fin 16, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = []) :
    ∃ B' : Kb → List Bool, Reach M ⟨some (Gl 0), ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), r), mk B' Q⟩
        (cnTime n (cmaskR n cw tw).length (encodeTableau T).length (encodeTableau D).length) ∧
      B' (K 10) = encodeTableau (fun j => cnotPS cw tw (T j)) ∧
      B' (K 11) = encodeTableau (fun j => cnotPS cw tw (D j)) ∧
      B' (K 13) = [false, false, true] ++ B (K 13) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 0) = B (K 0) ∧ B' (K 14) = B (K 14) ∧ ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have ne : ∀ i j : Fin 16, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  obtain ⟨B', hR, a0, a10, a11, a13, ae, a14, af⟩ := cnot_run M (K ∘ Fin.castSucc)
    (hK.comp (Fin.castSucc_injective 15)) Gl Ex getB setB hgsB hssB hsgB getC setC hgsC hssC hsgC
    s0 hp cw tw hct T D c r hrB hrC B Q h0 h1 h2
    (he 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    h10 h11 (he 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have fr : ∀ x, (∀ i : Fin 16, x ≠ K i) → ∀ i : Fin 15, x ≠ (K ∘ Fin.castSucc) i :=
    fun x hx i => hx _
  have a15 : B' (K 15) = B (K 15) := af _ fun i => ne 15 _ (fun e => by
    have := congrArg Fin.val e; simp at this; omega)
  refine ⟨B', hR, a10, a11, a13, ?_, a0.trans h0.symm, a14, fun x hx => af x (fr x hx)⟩
  intro i i0 i10 i11 i13 i14
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact ae j (fun e => i0 (by subst e; rfl)) (fun e => i10 (by subst e; rfl))
      (fun e => i11 (by subst e; rfl)) (fun e => i13 (by subst e; rfl)) (fun e => i14 (by subst e; rfl))
  · show B' (K 15) = []
    rw [a15]; exact he 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- K-side copies of the one-qubit conjugation tables (same bodies as gate.lean) -/
def kconjH : Pauli → ZMod 4 × Pauli
  | .I => (0, .I) | .X => (0, .Z) | .Y => (2, .Y) | .Z => (0, .X)

def kconjS : Pauli → ZMod 4 × Pauli
  | .I => (0, .I) | .X => (0, .Y) | .Y => (2, .X) | .Z => (0, .Z)

def kconjP (P Q : Pauli) : ZMod 4 × Pauli :=
  (if P = .I ∨ Q = .I ∨ P = Q then 0 else 2, Q)

/-- K-side gate update on a tableau -/
def kupdG {n : ℕ} : CliffordOp n → Tableau n → Tableau n
  | .pauli q P, T => fun j => rowG1 (kconjP P) q (T j)
  | .h q, T => fun j => rowG1 kconjH q (T j)
  | .s q, T => fun j => rowG1 kconjS q (T j)
  | .cnot c t _, T => fun j => cnotPS c t (T j)
  | .measure _, T => T

/-- K-side CHP step on (stabilizers, destabilizers) with coin `b` -/
def stepK {n : ℕ} (op : CliffordOp n) (T D : Tableau n) (b : Bool) :
    (Tableau n × Tableau n) × Option Bool :=
  match op with
  | .measure Mp => measK T D Mp b
  | _ => ((kupdG op T, kupdG op D), none)

/-- history code pushed by one step -/
def histK {n : ℕ} (op : CliffordOp n) (T D : Tableau n) (b : Bool) : List Bool :=
  match op with
  | .measure Mp => [(measK T D Mp b).2.getD false, true, true]
  | _ => [false, false, true]

/-- coin stack after one step -/
def popK {n : ℕ} (op : CliffordOp n) (l : List Bool) : List Bool :=
  match op with
  | .measure _ => l.drop 2
  | _ => l

/-- time of one dispatched step -/
def stepTimeK {n : ℕ} (op : CliffordOp n) (T D : Tableau n) : ℕ :=
  match op with
  | .pauli q _ => g1Time n q.val (cmaskR n q q).length (encodeTableau T).length (encodeTableau D).length
  | .h q => g1Time n q.val (cmaskR n q q).length (encodeTableau T).length (encodeTableau D).length
  | .s q => g1Time n q.val (cmaskR n q q).length (encodeTableau T).length (encodeTableau D).length
  | .cnot c t _ => cnTime n (cmaskR n c t).length (encodeTableau T).length (encodeTableau D).length
  | .measure Mp => 1 + measTime T D Mp

/-- one dispatched step: from the op's dispatch label (as produced by `parse_run`) to `Ex` -/
theorem op_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (GlI GlX GlY GlZ GlH GlS : Fin 18 → Λ) (GlC : Fin 23 → Λ)
    (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (LX : Fin 17 → Λ)
    (LT : Fin 11 → Λ) (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex Lc Halt : Λ)
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getZ : MS ε → ZMod 4 × Option (Bool × Bool))
    (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε)
    (hgsZ : ∀ r t, getZ (setZ r t) = t) (hssZ : ∀ r t t', setZ (setZ r t) t' = setZ r t')
    (hsgZ : ∀ r, setZ r (getZ r) = r)
    (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool))
    (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε)
    (hgsC : ∀ r t, getC (setC r t) = t) (hssC : ∀ r t t', setC (setC r t) t' = setC r t')
    (hsgC : ∀ r, setC r (getC r) = r) (s0 : Pauli × Pauli)
    (hpI : G1Prog M (K ∘ Fin.castSucc) GlI Ex (kconjP .I) getB setB getZ setZ)
    (hpX : G1Prog M (K ∘ Fin.castSucc) GlX Ex (kconjP .X) getB setB getZ setZ)
    (hpY : G1Prog M (K ∘ Fin.castSucc) GlY Ex (kconjP .Y) getB setB getZ setZ)
    (hpZ : G1Prog M (K ∘ Fin.castSucc) GlZ Ex (kconjP .Z) getB setB getZ setZ)
    (hpH : G1Prog M (K ∘ Fin.castSucc) GlH Ex kconjH getB setB getZ setZ)
    (hpS : G1Prog M (K ∘ Fin.castSucc) GlS Ex kconjS getB setB getZ setZ)
    (hpC : CNProg M (K ∘ Fin.castSucc) GlC Ex getB setB getC setC s0)
    (hP : MeasW M K L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex)
    (hc : M Lc = coinStmt (K 14) W0)
    {n : ℕ} (op : CliffordOp n) (T D : Tableau n) (c : Bool) (Q : ∀ r, List (G r)) (r : MS ε)
    (hrB : getB r = false) (hrZ : getZ r = (0, none)) (hrC : getC r = (s0, none))
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (B : Kb → List Bool)
    (h0 : B (K 0) = List.replicate n true) (h1 : B (K 1) = pW (some op))
    (h2 : B (K 2) = pT (some op)) (h6 : B (K 6) = pM (some op))
    (h10 : B (K 10) = encodeTableau T) (h11 : B (K 11) = encodeTableau D)
    (he : ∀ i : Fin 16, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 6 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 →
      B (K i) = [])
    (β : Bool) (h14 : ∀ Mp, op = .measure Mp → ∃ A, B (K 14) = true :: β :: A) :
    ∃ (B' : Kb → List Bool) (cb : Bool) (cp : ZMod 4),
      Reach M ⟨some (pdest Halt (GlI 0) (GlX 0) (GlY 0) (GlZ 0) (GlH 0) (GlS 0) (GlC 0) Lc (some op)),
          ((none, none, c), r), mk B Q⟩
        ⟨some Ex, ((none, none, c), { r with cb := cb, cp := cp }), mk B' Q⟩ (stepTimeK op T D) ∧
      B' (K 10) = encodeTableau (stepK op T D β).1.1 ∧
      B' (K 11) = encodeTableau (stepK op T D β).1.2 ∧
      B' (K 13) = histK op T D β ++ B (K 13) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 0) = B (K 0) ∧ B' (K 14) = popK op (B (K 14)) ∧
      ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  cases op with
  | pauli q P =>
    cases P with
    | I =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := g1_16 M K hK GlI Ex (kconjP .I) getB setB hgsB hssB
      hsgB getZ setZ hgsZ hssZ hsgZ hpI q T D c r hrB hrZ B Q h0 h1 h10 h11
      (fun i a b d e f' g => by
        by_cases i2 : i = 2
        · subst i2; exact h2
        by_cases i6 : i = 6
        · subst i6; exact h6
        exact he i a b i2 i6 d e f' g)
    exact ⟨B', r.cb, r.cp, hR, a10, a11, a13, ae, a0, a14, af⟩
    | X =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := g1_16 M K hK GlX Ex (kconjP .X) getB setB hgsB hssB
      hsgB getZ setZ hgsZ hssZ hsgZ hpX q T D c r hrB hrZ B Q h0 h1 h10 h11
      (fun i a b d e f' g => by
        by_cases i2 : i = 2
        · subst i2; exact h2
        by_cases i6 : i = 6
        · subst i6; exact h6
        exact he i a b i2 i6 d e f' g)
    exact ⟨B', r.cb, r.cp, hR, a10, a11, a13, ae, a0, a14, af⟩
    | Y =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := g1_16 M K hK GlY Ex (kconjP .Y) getB setB hgsB hssB
      hsgB getZ setZ hgsZ hssZ hsgZ hpY q T D c r hrB hrZ B Q h0 h1 h10 h11
      (fun i a b d e f' g => by
        by_cases i2 : i = 2
        · subst i2; exact h2
        by_cases i6 : i = 6
        · subst i6; exact h6
        exact he i a b i2 i6 d e f' g)
    exact ⟨B', r.cb, r.cp, hR, a10, a11, a13, ae, a0, a14, af⟩
    | Z =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := g1_16 M K hK GlZ Ex (kconjP .Z) getB setB hgsB hssB
      hsgB getZ setZ hgsZ hssZ hsgZ hpZ q T D c r hrB hrZ B Q h0 h1 h10 h11
      (fun i a b d e f' g => by
        by_cases i2 : i = 2
        · subst i2; exact h2
        by_cases i6 : i = 6
        · subst i6; exact h6
        exact he i a b i2 i6 d e f' g)
    exact ⟨B', r.cb, r.cp, hR, a10, a11, a13, ae, a0, a14, af⟩
  | h q =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := g1_16 M K hK GlH Ex kconjH getB setB hgsB hssB
      hsgB getZ setZ hgsZ hssZ hsgZ hpH q T D c r hrB hrZ B Q h0 h1 h10 h11
      (fun i a b d e f' g => by
        by_cases i2 : i = 2
        · subst i2; exact h2
        by_cases i6 : i = 6
        · subst i6; exact h6
        exact he i a b i2 i6 d e f' g)
    exact ⟨B', r.cb, r.cp, hR, a10, a11, a13, ae, a0, a14, af⟩
  | s q =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := g1_16 M K hK GlS Ex kconjS getB setB hgsB hssB
      hsgB getZ setZ hgsZ hssZ hsgZ hpS q T D c r hrB hrZ B Q h0 h1 h10 h11
      (fun i a b d e f' g => by
        by_cases i2 : i = 2
        · subst i2; exact h2
        by_cases i6 : i = 6
        · subst i6; exact h6
        exact he i a b i2 i6 d e f' g)
    exact ⟨B', r.cb, r.cp, hR, a10, a11, a13, ae, a0, a14, af⟩
  | cnot cw tw hct =>
    obtain ⟨B', hR, a10, a11, a13, ae, a0, a14, af⟩ := cn_16 M K hK GlC Ex getB setB hgsB hssB
      hsgB getC setC hgsC hssC hsgC s0 hpC cw tw hct T D c r hrB hrC B Q h0 h1 h2 h10 h11
      (fun i a b b2 d e f' g => by
        by_cases i6 : i = 6
        · subst i6; exact h6
        exact he i a b b2 i6 d e f' g)
    exact ⟨B', r.cb, r.cp, hR, a10, a11, a13, ae, a0, a14, af⟩
  | measure Mp =>
    obtain ⟨A, hA⟩ := h14 Mp rfl
    obtain ⟨B', cp, hR, a10, a11, a13, ae, a0, a14, af⟩ := meas_run M K hK L LD LX LT
      W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Ex Lc hP hc T D Mp c Q r B hr h6 h10 h11
      (fun i a b d e f' g => by
        by_cases i1 : i = 1
        · subst i1; exact h1
        by_cases i2 : i = 2
        · subst i2; exact h2
        exact he i a i1 i2 b d e f' g) β A hA
    refine ⟨B', β, cp, hR, a10, a11, a13, ae, a0, ?_, af⟩
    show B' (K 14) = (B (K 14)).drop 2
    rw [a14, hA]; rfl

end MeasRun

end OCRS19TM

-- ===== session 27: Iter (front half of one loop iteration: feed -> g -> cv -> mv -> parse) =====
namespace OCRS19TM

section Iter

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ρ ε : Type}

/-- front half of one iteration: feed the controller input `Grev.reverse ++ [false]` from `K 13`,
run the controller `g` (abstracted as `hg`), convert its answer onto `K 15` and parse it. -/
theorem front_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (LF L1 L2 Lg Lr Lm : Λ) (P : Fin 15 → Λ)
    (Halt PI PX PY PZ GH GS GC GM Bad : Λ) (s0 s1 : R) (enc : Bool → G s0) (dec : G s1 → Bool)
    (hF : M LF = pushInrStmt s0 (enc false) L1) (h1 : M L1 = dcvStmt (K 13) s0 enc (K 3) L1 L2)
    (h2 : M L2 = mvStmt (K 3) (K 13) L2 Lg)
    (hcv : M Lr = cvStmt s1 dec (K 3) Lr Lm) (hmv : M Lm = mvStmt (K 3) (K 15) Lm (P 0))
    (hp : ParseProg M (K 15) (K 1) (K 2) (K 6) P Halt PI PX PY PZ GH GS GC GM Bad)
    {n : ℕ} (gS : List Bool → List Bool) (gT : ℕ → ℕ) (Rv : ρ → Prop)
    (hg : ∀ (w : List Bool) (B : Kb → List Bool) (r : ρ), Rv r → ∀ c : Bool,
      ∃ Q' : ∀ s, List (G s),
        Reach M ⟨some Lg, ((none, none, c), r), mk B (Function.update (fun _ => []) s0 (w.map enc))⟩
          ⟨some Lr, ((none, none, c), r), mk B Q'⟩ (gT w.length) ∧
        (Q' s1).map dec = gS w ∧ ∀ s, s ≠ s1 → Q' s = [])
    (r : ρ) (hr : Rv r) (c : Bool) (B : Kb → List Bool) (Grev : List Bool)
    (op : Option (CliffordOp n)) (hop : gS (Grev.reverse ++ [false]) = encOp op)
    (h13 : B (K 13) = Grev) (h3 : B (K 3) = []) (h15 : B (K 15) = []) (hb1 : B (K 1) = [])
    (hb2 : B (K 2) = []) (hb6 : B (K 6) = []) :
    ∃ B' : Kb → List Bool,
      Reach M ⟨some LF, ((none, none, c), r), mk B (fun _ => [])⟩
        ⟨some (pdest Halt PI PX PY PZ GH GS GC GM op), ((none, none, c), r), mk B' (fun _ => [])⟩
        (2 * Grev.length + 3 + gT (Grev.length + 1) + 3 * ((encOp op).length + 1)) ∧
      B' (K 1) = pW op ∧ B' (K 2) = pT op ∧ B' (K 6) = pM op ∧
      ∀ x, x ≠ K 1 → x ≠ K 2 → x ≠ K 6 → B' x = B x := by
  have ne : ∀ i j : Fin 16, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  have hd : Dist4 (K 15) (K 1) (K 2) (K 6) := ⟨ne 15 1 (by decide), ne 15 2 (by decide),
    ne 15 6 (by decide), ne 1 2 (by decide), ne 1 6 (by decide), ne 2 6 (by decide)⟩
  have RF := feed_run M (K 13) (K 3) s0 enc (ne 13 3 (by decide)) LF L1 L2 Lg hF h1 h2 r c B
    (fun _ => []) Grev h13 h3 rfl
  obtain ⟨Q', RG, hQ1, hQo⟩ := hg (Grev.reverse ++ [false]) B r hr c
  rw [hop] at hQ1
  have hlen : (Q' s1).length = (encOp op).length := by rw [← hQ1, List.length_map]
  have RC := cv_run M s1 dec (K 3) Lr Lm hcv r c (Q' s1) B Q' rfl
  rw [hQ1, h3, List.append_nil] at RC
  have hQ0 : Function.update Q' s1 [] = fun _ => [] := by
    funext s
    by_cases hs : s = s1
    · subst hs; simp
    · rw [Function.update_of_ne hs, hQo s hs]
  rw [hQ0] at RC
  set B1 := Function.update B (K 3) (encOp op).reverse with hB1
  have RM := mv_run M (K 3) (K 15) (ne 3 15 (by decide)) Lm (P 0) hmv r c (fun _ => [])
    (encOp op).reverse B1 (by simp [B1])
  set B2 := Function.update (Function.update B1 (K 3) []) (K 15)
    ((encOp op).reverse.reverse ++ B1 (K 15)) with hB2
  have hY : B2 (K 15) = encOp op := by
    simp [B2, B1, Function.update_of_ne (ne 15 3 (by decide)), h15]
  have RP := parse_run M hd P Halt PI PX PY PZ GH GS GC GM Bad hp r c (fun _ => []) B2 op hY
  have e1 : B2 (K 1) = [] := by
    simp [B2, B1, Function.update_of_ne (ne 1 3 (by decide)), Function.update_of_ne (ne 1 15 (by decide)), hb1]
  have e2 : B2 (K 2) = [] := by
    simp [B2, B1, Function.update_of_ne (ne 2 3 (by decide)), Function.update_of_ne (ne 2 15 (by decide)), hb2]
  have e6 : B2 (K 6) = [] := by
    simp [B2, B1, Function.update_of_ne (ne 6 3 (by decide)), Function.update_of_ne (ne 6 15 (by decide)), hb6]
  refine ⟨St (K 15) (K 1) (K 2) (K 6) B2 [] (pW op) (pT op) (pM op),
    (RF.trans (RG.trans (RC.trans (RM.trans RP)))).mono ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_reverse, List.length_singleton, hlen]
    omega
  · simp only [St]
    rw [Function.update_of_ne (ne 1 6 (by decide)), Function.update_of_ne (ne 1 2 (by decide)),
      Function.update_self, e1, List.append_nil]
  · simp only [St]
    rw [Function.update_of_ne (ne 2 6 (by decide)), Function.update_self, e2, List.append_nil]
  · simp only [St]
    rw [Function.update_self, e6, List.append_nil]
  · intro x a b d
    simp only [St]
    rw [Function.update_of_ne d, Function.update_of_ne b, Function.update_of_ne a]
    by_cases e15 : x = K 15
    · subst e15; rw [Function.update_self, h15]
    rw [Function.update_of_ne e15, hB2, Function.update_of_ne e15]
    by_cases e3 : x = K 3
    · subst e3; rw [Function.update_self, h3]
    rw [Function.update_of_ne e3, hB1, Function.update_of_ne e3]


/-- one full iteration for a returned operation `o`: front half then the dispatched step, back to `LF` -/
theorem iter_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (LF L1 L2 Lg Lr Lm : Λ) (P : Fin 15 → Λ) (Halt Bad : Λ)
    (sI sO : R) (enc : Bool → G sI) (dec : G sO → Bool)
    (hF : M LF = pushInrStmt sI (enc false) L1) (h1 : M L1 = dcvStmt (K 13) sI enc (K 3) L1 L2)
    (h2 : M L2 = mvStmt (K 3) (K 13) L2 Lg)
    (hcv : M Lr = cvStmt sO dec (K 3) Lr Lm) (hmv : M Lm = mvStmt (K 3) (K 15) Lm (P 0))
    (GlI GlX GlY GlZ GlH GlS : Fin 18 → Λ) (GlC : Fin 23 → Λ)
    (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (LX : Fin 17 → Λ)
    (LT : Fin 11 → Λ) (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Lc : Λ)
    (hp : ParseProg M (K 15) (K 1) (K 2) (K 6) P Halt (GlI 0) (GlX 0) (GlY 0) (GlZ 0) (GlH 0)
      (GlS 0) (GlC 0) Lc Bad)
    (gS : List Bool → List Bool) (gT : ℕ → ℕ) (Rv : MS ε → Prop)
    (hg : ∀ (w : List Bool) (B : Kb → List Bool) (r : MS ε), Rv r → ∀ c : Bool,
      ∃ Q' : ∀ s, List (G s),
        Reach M ⟨some Lg, ((none, none, c), r), mk B (Function.update (fun _ => []) sI (w.map enc))⟩
          ⟨some Lr, ((none, none, c), r), mk B Q'⟩ (gT w.length) ∧
        (Q' sO).map dec = gS w ∧ ∀ s, s ≠ sO → Q' s = [])
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getZ : MS ε → ZMod 4 × Option (Bool × Bool))
    (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε)
    (hgsZ : ∀ r t, getZ (setZ r t) = t) (hssZ : ∀ r t t', setZ (setZ r t) t' = setZ r t')
    (hsgZ : ∀ r, setZ r (getZ r) = r)
    (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool))
    (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε)
    (hgsC : ∀ r t, getC (setC r t) = t) (hssC : ∀ r t t', setC (setC r t) t' = setC r t')
    (hsgC : ∀ r, setC r (getC r) = r) (s0 : Pauli × Pauli)
    (hpI : G1Prog M (K ∘ Fin.castSucc) GlI LF (kconjP .I) getB setB getZ setZ)
    (hpX : G1Prog M (K ∘ Fin.castSucc) GlX LF (kconjP .X) getB setB getZ setZ)
    (hpY : G1Prog M (K ∘ Fin.castSucc) GlY LF (kconjP .Y) getB setB getZ setZ)
    (hpZ : G1Prog M (K ∘ Fin.castSucc) GlZ LF (kconjP .Z) getB setB getZ setZ)
    (hpH : G1Prog M (K ∘ Fin.castSucc) GlH LF kconjH getB setB getZ setZ)
    (hpS : G1Prog M (K ∘ Fin.castSucc) GlS LF kconjS getB setB getZ setZ)
    (hpC : CNProg M (K ∘ Fin.castSucc) GlC LF getB setB getC setC s0)
    (hP : MeasW M K L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 LF)
    (hc : M Lc = coinStmt (K 14) W0)
    {n : ℕ} (o : CliffordOp n) (T D : Tableau n) (c : Bool) (r : MS ε) (hRv : Rv r)
    (hrB : getB r = false) (hrZ : getZ r = (0, none)) (hrC : getC r = (s0, none))
    (hr : r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (B : Kb → List Bool) (Grev : List Bool) (hop : gS (Grev.reverse ++ [false]) = encOp (some o))
    (h0 : B (K 0) = List.replicate n true) (h10 : B (K 10) = encodeTableau T)
    (h11 : B (K 11) = encodeTableau D) (h13 : B (K 13) = Grev)
    (he : ∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = [])
    (β : Bool) (h14 : ∀ Mp, o = .measure Mp → ∃ A, B (K 14) = true :: β :: A) :
    ∃ (B' : Kb → List Bool) (cb : Bool) (cp : ZMod 4),
      Reach M ⟨some LF, ((none, none, c), r), mk B (fun _ => [])⟩
        ⟨some LF, ((none, none, c), { r with cb := cb, cp := cp }), mk B' (fun _ => [])⟩
        (2 * Grev.length + 3 + gT (Grev.length + 1) + 3 * ((encOp (some o)).length + 1) +
          stepTimeK o T D) ∧
      B' (K 10) = encodeTableau (stepK o T D β).1.1 ∧
      B' (K 11) = encodeTableau (stepK o T D β).1.2 ∧
      B' (K 13) = histK o T D β ++ Grev ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
      B' (K 0) = B (K 0) ∧ B' (K 14) = popK o (B (K 14)) ∧
      ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have ne : ∀ i j : Fin 16, i ≠ j → K i ≠ K j := fun i j h e => h (hK e)
  obtain ⟨B1, RF, f1, f2, f6, ff⟩ := front_run M K hK LF L1 L2 Lg Lr Lm P Halt (GlI 0) (GlX 0)
    (GlY 0) (GlZ 0) (GlH 0) (GlS 0) (GlC 0) Lc Bad sI sO enc dec hF h1 h2 hcv hmv hp gS gT Rv hg
    r hRv c B Grev (some o) hop h13 (he 3 (by decide) (by decide) (by decide) (by decide) (by decide)) (he 15 (by decide) (by decide) (by decide) (by decide) (by decide)) (he 1 (by decide) (by decide) (by decide) (by decide) (by decide)) (he 2 (by decide) (by decide) (by decide) (by decide) (by decide)) (he 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  have gg : ∀ i : Fin 16, i ≠ 1 → i ≠ 2 → i ≠ 6 → B1 (K i) = B (K i) :=
    fun i a b d => ff _ (ne i 1 a) (ne i 2 b) (ne i 6 d)
  obtain ⟨B', cb, cp, RO, a10, a11, a13, ae, a0, a14, af⟩ := op_run M K hK GlI GlX GlY GlZ GlH GlS
    GlC L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 LF Lc Halt getB setB hgsB hssB hsgB
    getZ setZ hgsZ hssZ hsgZ getC setC hgsC hssC hsgC s0 hpI hpX hpY hpZ hpH hpS hpC hP hc o T D c
    (fun _ => []) r hrB hrZ hrC hr B1
    (by rw [gg 0 (by decide) (by decide) (by decide)]; exact h0) f1 f2 f6
    (by rw [gg 10 (by decide) (by decide) (by decide)]; exact h10)
    (by rw [gg 11 (by decide) (by decide) (by decide)]; exact h11)
    (fun i a b d e f' g' h' k => by rw [gg i b d e]; exact he i a f' g' h' k) β
    (fun Mp hM => by rw [gg 14 (by decide) (by decide) (by decide)]; exact h14 Mp hM)
  refine ⟨B', cb, cp, RF.trans RO, a10, a11, ?_, ae, ?_, ?_, ?_⟩
  · rw [a13, gg 13 (by decide) (by decide) (by decide), h13]
  · rw [a0, gg 0 (by decide) (by decide) (by decide)]
  · rw [a14, gg 14 (by decide) (by decide) (by decide)]
  · intro x hx
    rw [af x hx]
    exact ff x (hx 1) (hx 2) (hx 6)


/-- transcript code of one step (the `encHist` code) -/
def hcode : Option Bool → List Bool
  | none => [true, false, false]
  | some β => [true, true, β]

lemma flat_hcode_len : ∀ h : List (Option Bool), (h.flatMap hcode).length = 3 * h.length
  | [] => rfl
  | x :: h => by
    simp only [List.flatMap_cons, List.length_append, flat_hcode_len h, List.length_cons]
    cases x <;> simp [hcode] <;> omega

lemma histK_eq {n : ℕ} (o : CliffordOp n) (T D : Tableau n) (b : Bool) :
    histK o T D b = (hcode (stepK o T D b).2).reverse := by
  cases o <;> first | rfl | (simp only [histK, stepK, measK]; split <;> rfl)

/-- coin list after one step -/
def popC {n : ℕ} (o : CliffordOp n) (cs : List Bool) : List Bool :=
  match o with
  | .measure _ => cs.tail
  | _ => cs

/-- the K-side loop with fuel -/
def kloop {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) :
    ℕ → Tableau n × Tableau n → List (Option Bool) → List Bool →
      (Tableau n × Tableau n) × List (Option Bool) × List Bool
  | 0, TD, h, cs => (TD, h, cs)
  | k + 1, TD, h, cs =>
    match ctl h with
    | none => (TD, h, cs)
    | some o => kloop ctl k (stepK o TD.1 TD.2 (cs.headD false)).1
        (h ++ [(stepK o TD.1 TD.2 (cs.headD false)).2]) (popC o cs)

/-- time of the front half with transcript `h` -/
def fT {n : ℕ} (pl : ℕ) (gT : ℕ → ℕ) (h : List (Option Bool)) (op : Option (CliffordOp n)) : ℕ :=
  2 * (pl + 3 * h.length) + 3 + gT (pl + 3 * h.length + 1) + 3 * ((encOp op).length + 1)

/-- time of the loop with fuel -/
def kTime {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) (pl : ℕ) (gT : ℕ → ℕ) :
    ℕ → Tableau n × Tableau n → List (Option Bool) → List Bool → ℕ
  | 0, _, h, _ => fT pl gT h (none : Option (CliffordOp n))
  | k + 1, TD, h, cs =>
    match ctl h with
    | none => fT pl gT h (none : Option (CliffordOp n))
    | some o => fT pl gT h (some o) + stepTimeK o TD.1 TD.2 +
        kTime ctl pl gT k (stepK o TD.1 TD.2 (cs.headD false)).1
          (h ++ [(stepK o TD.1 TD.2 (cs.headD false)).2]) (popC o cs)

/-- the halting front half: the controller says halt, reach `Halt` with the stacks unchanged -/
theorem halt_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (LF L1 L2 Lg Lr Lm : Λ) (P : Fin 15 → Λ) (Halt Bad : Λ)
    (sI sO : R) (enc : Bool → G sI) (dec : G sO → Bool)
    (hF : M LF = pushInrStmt sI (enc false) L1) (h1 : M L1 = dcvStmt (K 13) sI enc (K 3) L1 L2)
    (h2 : M L2 = mvStmt (K 3) (K 13) L2 Lg)
    (hcv : M Lr = cvStmt sO dec (K 3) Lr Lm) (hmv : M Lm = mvStmt (K 3) (K 15) Lm (P 0))
    (GlI GlX GlY GlZ GlH GlS : Fin 18 → Λ) (GlC : Fin 23 → Λ)
    (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (LX : Fin 17 → Λ)
    (LT : Fin 11 → Λ) (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Lc : Λ)
    (hp : ParseProg M (K 15) (K 1) (K 2) (K 6) P Halt (GlI 0) (GlX 0) (GlY 0) (GlZ 0) (GlH 0)
      (GlS 0) (GlC 0) Lc Bad)
    (gS : List Bool → List Bool) (gT : ℕ → ℕ) (Rv : MS ε → Prop)
    (hg : ∀ (w : List Bool) (B : Kb → List Bool) (r : MS ε), Rv r → ∀ c : Bool,
      ∃ Q' : ∀ s, List (G s),
        Reach M ⟨some Lg, ((none, none, c), r), mk B (Function.update (fun _ => []) sI (w.map enc))⟩
          ⟨some Lr, ((none, none, c), r), mk B Q'⟩ (gT w.length) ∧
        (Q' sO).map dec = gS w ∧ ∀ s, s ≠ sO → Q' s = [])
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getZ : MS ε → ZMod 4 × Option (Bool × Bool))
    (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε)
    (hgsZ : ∀ r t, getZ (setZ r t) = t) (hssZ : ∀ r t t', setZ (setZ r t) t' = setZ r t')
    (hsgZ : ∀ r, setZ r (getZ r) = r)
    (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool))
    (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε)
    (hgsC : ∀ r t, getC (setC r t) = t) (hssC : ∀ r t t', setC (setC r t) t' = setC r t')
    (hsgC : ∀ r, setC r (getC r) = r) (s0 : Pauli × Pauli)
    (hpI : G1Prog M (K ∘ Fin.castSucc) GlI LF (kconjP .I) getB setB getZ setZ)
    (hpX : G1Prog M (K ∘ Fin.castSucc) GlX LF (kconjP .X) getB setB getZ setZ)
    (hpY : G1Prog M (K ∘ Fin.castSucc) GlY LF (kconjP .Y) getB setB getZ setZ)
    (hpZ : G1Prog M (K ∘ Fin.castSucc) GlZ LF (kconjP .Z) getB setB getZ setZ)
    (hpH : G1Prog M (K ∘ Fin.castSucc) GlH LF kconjH getB setB getZ setZ)
    (hpS : G1Prog M (K ∘ Fin.castSucc) GlS LF kconjS getB setB getZ setZ)
    (hpC : CNProg M (K ∘ Fin.castSucc) GlC LF getB setB getC setC s0)
    (hP : MeasW M K L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 LF)
    (hc : M Lc = coinStmt (K 14) W0)
    {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) (pre : List Bool)
    (hctl : ∀ h, gS (pre ++ h.flatMap hcode ++ [false]) = encOp (ctl h))
    (h : List (Option Bool)) (hn : ctl h = none) (r : MS ε) (hRv : Rv r) (c : Bool)
    (B : Kb → List Bool) (h13 : B (K 13) = (pre ++ h.flatMap hcode).reverse)
    (hb1 : B (K 1) = []) (hb2 : B (K 2) = []) (hb3 : B (K 3) = []) (hb6 : B (K 6) = [])
    (hb15 : B (K 15) = []) :
    Reach M ⟨some LF, ((none, none, c), r), mk B (fun _ => [])⟩
        ⟨some Halt, ((none, none, c), r), mk B (fun _ => [])⟩
        (fT pre.length gT h (none : Option (CliffordOp n))) := by
  have hGl : (pre ++ h.flatMap hcode).reverse.length = pre.length + 3 * h.length := by
    rw [List.length_reverse, List.length_append, flat_hcode_len]
  obtain ⟨B1, RF, f1, f2, f6, ff⟩ := front_run M K hK LF L1 L2 Lg Lr Lm P Halt (GlI 0) (GlX 0)
    (GlY 0) (GlZ 0) (GlH 0) (GlS 0) (GlC 0) Lc Bad sI sO enc dec hF h1 h2 hcv hmv hp gS gT Rv hg
    r hRv c B _ none (by rw [List.reverse_reverse, hctl h, hn]) h13 hb3 hb15 hb1 hb2 hb6
  have e : B1 = B := by
    funext x
    by_cases x1 : x = K 1
    · subst x1; rw [f1, hb1]; rfl
    by_cases x2 : x = K 2
    · subst x2; rw [f2, hb2]; rfl
    by_cases x6 : x = K 6
    · subst x6; rw [f6, hb6]; rfl
    exact ff x x1 x2 x6
  subst e
  refine RF.mono (le_of_eq ?_)
  unfold fT; rw [← hGl]

/-- the whole loop, by induction on the fuel -/
theorem loop_run (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 16 → Kb)
    (hK : Function.Injective K) (LF L1 L2 Lg Lr Lm : Λ) (P : Fin 15 → Λ) (Halt Bad : Λ)
    (sI sO : R) (enc : Bool → G sI) (dec : G sO → Bool)
    (hF : M LF = pushInrStmt sI (enc false) L1) (h1 : M L1 = dcvStmt (K 13) sI enc (K 3) L1 L2)
    (h2 : M L2 = mvStmt (K 3) (K 13) L2 Lg)
    (hcv : M Lr = cvStmt sO dec (K 3) Lr Lm) (hmv : M Lm = mvStmt (K 3) (K 15) Lm (P 0))
    (GlI GlX GlY GlZ GlH GlS : Fin 18 → Λ) (GlC : Fin 23 → Λ)
    (L : Fin 20 → Λ) (LD : Fin 16 → Λ) (LX : Fin 17 → Λ)
    (LT : Fin 11 → Λ) (W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Lc : Λ)
    (hp : ParseProg M (K 15) (K 1) (K 2) (K 6) P Halt (GlI 0) (GlX 0) (GlY 0) (GlZ 0) (GlH 0)
      (GlS 0) (GlC 0) Lc Bad)
    (gS : List Bool → List Bool) (gT : ℕ → ℕ) (Rv : MS ε → Prop)
    (hg : ∀ (w : List Bool) (B : Kb → List Bool) (r : MS ε), Rv r → ∀ c : Bool,
      ∃ Q' : ∀ s, List (G s),
        Reach M ⟨some Lg, ((none, none, c), r), mk B (Function.update (fun _ => []) sI (w.map enc))⟩
          ⟨some Lr, ((none, none, c), r), mk B Q'⟩ (gT w.length) ∧
        (Q' sO).map dec = gS w ∧ ∀ s, s ≠ sO → Q' s = [])
    (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε)
    (hgsB : ∀ r t, getB (setB r t) = t) (hssB : ∀ r t t', setB (setB r t) t' = setB r t')
    (hsgB : ∀ r, setB r (getB r) = r)
    (getZ : MS ε → ZMod 4 × Option (Bool × Bool))
    (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε)
    (hgsZ : ∀ r t, getZ (setZ r t) = t) (hssZ : ∀ r t t', setZ (setZ r t) t' = setZ r t')
    (hsgZ : ∀ r, setZ r (getZ r) = r)
    (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool))
    (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε)
    (hgsC : ∀ r t, getC (setC r t) = t) (hssC : ∀ r t t', setC (setC r t) t' = setC r t')
    (hsgC : ∀ r, setC r (getC r) = r) (s0 : Pauli × Pauli)
    (hpI : G1Prog M (K ∘ Fin.castSucc) GlI LF (kconjP .I) getB setB getZ setZ)
    (hpX : G1Prog M (K ∘ Fin.castSucc) GlX LF (kconjP .X) getB setB getZ setZ)
    (hpY : G1Prog M (K ∘ Fin.castSucc) GlY LF (kconjP .Y) getB setB getZ setZ)
    (hpZ : G1Prog M (K ∘ Fin.castSucc) GlZ LF (kconjP .Z) getB setB getZ setZ)
    (hpH : G1Prog M (K ∘ Fin.castSucc) GlH LF kconjH getB setB getZ setZ)
    (hpS : G1Prog M (K ∘ Fin.castSucc) GlS LF kconjS getB setB getZ setZ)
    (hpC : CNProg M (K ∘ Fin.castSucc) GlC LF getB setB getC setC s0)
    (hP : MeasW M K L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 LF)
    (hc : M Lc = coinStmt (K 14) W0)
    {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) (pre : List Bool)
    (hctl : ∀ h, gS (pre ++ h.flatMap hcode ++ [false]) = encOp (ctl h))
    (Iv : MS ε → Prop)
    (hIv : ∀ r, Iv r → Rv r ∧ getB r = false ∧ getZ r = (0, none) ∧ getC r = (s0, none) ∧
      r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false)
    (hIvU : ∀ r cb cp, Iv r → Iv { r with cb := cb, cp := cp }) (rest : List Bool) (c : Bool) :
    ∀ (k : ℕ) (TD : Tableau n × Tableau n) (h : List (Option Bool)) (cs : List Bool)
      (B : Kb → List Bool) (r : MS ε), Iv r → k ≤ cs.length → ctl (kloop ctl k TD h cs).2.1 = none →
      B (K 0) = List.replicate n true → B (K 10) = encodeTableau TD.1 →
      B (K 11) = encodeTableau TD.2 → B (K 13) = (pre ++ h.flatMap hcode).reverse →
      B (K 14) = cs.flatMap pr ++ rest →
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = []) →
      ∃ (B' : Kb → List Bool) (r' : MS ε), Iv r' ∧
        Reach M ⟨some LF, ((none, none, c), r), mk B (fun _ => [])⟩
          ⟨some Halt, ((none, none, c), r'), mk B' (fun _ => [])⟩ (kTime ctl pre.length gT k TD h cs) ∧
        B' (K 10) = encodeTableau (kloop ctl k TD h cs).1.1 ∧
        B' (K 11) = encodeTableau (kloop ctl k TD h cs).1.2 ∧
        B' (K 13) = (pre ++ (kloop ctl k TD h cs).2.1.flatMap hcode).reverse ∧
        B' (K 14) = (kloop ctl k TD h cs).2.2.flatMap pr ++ rest ∧
        B' (K 0) = B (K 0) ∧
        (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
        ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
  have base : ∀ (TD : Tableau n × Tableau n) (h : List (Option Bool)) (cs : List Bool)
      (B : Kb → List Bool) (r : MS ε), Iv r → ctl h = none →
      B (K 0) = List.replicate n true → B (K 10) = encodeTableau TD.1 →
      B (K 11) = encodeTableau TD.2 → B (K 13) = (pre ++ h.flatMap hcode).reverse →
      B (K 14) = cs.flatMap pr ++ rest →
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B (K i) = []) →
      ∃ (B' : Kb → List Bool) (r' : MS ε), Iv r' ∧
        Reach M ⟨some LF, ((none, none, c), r), mk B (fun _ => [])⟩
          ⟨some Halt, ((none, none, c), r'), mk B' (fun _ => [])⟩
          (fT pre.length gT h (none : Option (CliffordOp n))) ∧
        B' (K 10) = encodeTableau TD.1 ∧ B' (K 11) = encodeTableau TD.2 ∧
        B' (K 13) = (pre ++ h.flatMap hcode).reverse ∧ B' (K 14) = cs.flatMap pr ++ rest ∧
        B' (K 0) = B (K 0) ∧
        (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' (K i) = []) ∧
        ∀ x, (∀ i, x ≠ K i) → B' x = B x := by
    intro TD h cs B r hI hn h0 h10 h11 h13 h14 he
    have R := halt_run M K hK LF L1 L2 Lg Lr Lm P Halt Bad sI sO enc dec hF h1 h2 hcv hmv GlI GlX GlY GlZ GlH GlS GlC L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Lc hp gS gT Rv hg getB setB hgsB hssB hsgB getZ setZ hgsZ hssZ hsgZ getC setC hgsC hssC hsgC s0 hpI hpX hpY hpZ hpH hpS hpC hP hc ctl pre hctl h hn r (hIv r hI).1 c B h13
      (he 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (he 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (he 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (he 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (he 15 (by decide) (by decide) (by decide) (by decide) (by decide))
    exact ⟨B, r, hI, R, h10, h11, h13, h14, rfl, he, fun _ _ => rfl⟩
  intro k
  induction k with
  | zero =>
    intro TD h cs B r hI _ hn h0 h10 h11 h13 h14 he
    exact base TD h cs B r hI hn h0 h10 h11 h13 h14 he
  | succ k ih =>
    intro TD h cs B r hI hk hn h0 h10 h11 h13 h14 he
    cases hco : ctl h with
    | none =>
      simp only [kloop, kTime, hco]
      exact base TD h cs B r hI hco h0 h10 h11 h13 h14 he
    | some o =>
      obtain ⟨c0, cs', rfl⟩ := List.exists_cons_of_length_pos (show 0 < cs.length by omega)
      simp only [kloop, kTime, hco] at hn ⊢
      obtain ⟨hRv, hB, hZ, hC, han, hmu, hfd⟩ := hIv r hI
      have hGl : (pre ++ h.flatMap hcode).reverse.length = pre.length + 3 * h.length := by
        rw [List.length_reverse, List.length_append, flat_hcode_len]
      obtain ⟨B1, cb, cp, R1, a10, a11, a13, ae, a0, a14, af⟩ := iter_run M K hK LF L1 L2 Lg Lr Lm P Halt Bad sI sO enc dec hF h1 h2 hcv hmv GlI GlX GlY GlZ GlH GlS GlC L LD LX LT W0 W1 E1 E2 E3 ED E4 Eb E5 R1 R2 D1 Lc hp gS gT Rv hg getB setB hgsB hssB hsgB getZ setZ hgsZ hssZ hsgZ getC setC hgsC hssC hsgC s0 hpI hpX hpY hpZ hpH hpS hpC hP hc o TD.1 TD.2 c r
        hRv hB hZ hC ⟨han, hmu, hfd⟩ B _ (by rw [List.reverse_reverse, hctl h, hco]) h0 h10 h11 h13 he
        c0 (fun Mp _ => ⟨cs'.flatMap pr ++ rest, by rw [h14]; simp [pr]⟩)
      have hk' : k ≤ (popC o (c0 :: cs')).length := by
        cases o <;> simp [popC] at hk ⊢ <;> omega
      obtain ⟨B', r', hI', R2, b10, b11, b13, b14, b0, be, bf⟩ := ih _ _ _ B1 _ (hIvU r cb cp hI)
        hk' hn (by rw [a0, h0]) a10 a11
        (by rw [a13, histK_eq, List.flatMap_append, ← List.append_assoc, List.reverse_append]
            simp)
        (by rw [a14, h14]; cases o <;> simp [popK, popC, pr])
        ae
      refine ⟨B', r', hI', (R1.trans R2).mono (le_of_eq ?_), b10, b11, b13, b14, ?_, be, ?_⟩
      · simp only [List.headD_cons]; unfold fT; rw [hGl]
      · rw [b0, a0]
      · intro x hx; rw [bf x hx, af x hx]

end Iter

end OCRS19TM

namespace OCRS19TM

open QAlgorithms.Stabilizer

section Ctrl

lemma hcode_encHist (h : List (Option Bool)) : encHist h = h.flatMap hcode ++ [false] := by
  unfold encHist
  congr 1

/-- the controller hypothesis of `loop_run` from `MCCFamily.polytime` -/
lemma ctrl_hctl (F : MCCFamily) (g : List Bool → List Bool)
    (hg : ∀ n r hist, g (encCtrlInput n r hist) = encOp (F.ctrl n r hist)) (n : ℕ) (rr : List Bool) :
    ∀ h, g ((QAlgorithms.Complexity.encNat n ++ encBits rr) ++ h.flatMap hcode ++ [false]) = encOp (F.ctrl n rr h) := by
  intro h
  rw [← hg, encCtrlInput, hcode_encHist]
  simp only [List.append_assoc]

lemma kloop_len {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) :
    ∀ (k : ℕ) (TD : Tableau n × Tableau n) (h : List (Option Bool)) (cs : List Bool),
      ctl (kloop ctl k TD h cs).2.1 = none ∨ (kloop ctl k TD h cs).2.1.length = h.length + k
  | 0, TD, h, cs => Or.inr (by simp [kloop])
  | k + 1, TD, h, cs => by
    cases hc : ctl h with
    | none => left; simp only [kloop, hc]
    | some o =>
      simp only [kloop, hc]
      exact (kloop_len ctl k _ _ _).imp id
        (fun e => by rw [e, List.length_append, List.length_singleton]; omega)

/-- with fuel `steps(n)` the K-side loop always ends at a halting transcript -/
lemma kloop_halts (F : MCCFamily) (n : ℕ) (rr : List Bool) (TD : Tableau n × Tableau n)
    (cs : List Bool) :
    F.ctrl n rr (kloop (F.ctrl n rr) (F.steps.eval n) TD [] cs).2.1 = none := by
  rcases kloop_len (F.ctrl n rr) (F.steps.eval n) TD [] cs with e | e
  · exact e
  · exact F.halts _ _ _ (by rw [e]; simp)

/-- the transcript of the K-side loop only grows -/
lemma kloop_hist_len {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) :
    ∀ (k : ℕ) (TD : Tableau n × Tableau n) (h : List (Option Bool)) (cs : List Bool),
      (kloop ctl k TD h cs).2.1.length ≤ h.length + k
  | 0, TD, h, cs => by simp [kloop]
  | k + 1, TD, h, cs => by
    cases hc : ctl h with
    | none => simp only [kloop, hc]; omega
    | some o =>
      simp only [kloop, hc]
      refine (kloop_hist_len ctl k _ _ _).trans ?_
      rw [List.length_append, List.length_singleton]; omega

/-! ### time bounds -/

lemma encodeTableau_length {n : ℕ} (T : Tableau n) : (encodeTableau T).length = n * (2 * n + 2) := by
  rw [encodeTableau_eq, List.length_flatten]
  simp [Function.comp_def, encPS_length, List.sum_ofFn]

lemma stepTimeK_le {n : ℕ} (o : CliffordOp n) (T D : Tableau n) :
    stepTimeK o T D ≤ 200 * (n + 1) ^ 2 := by
  have hT := encodeTableau_length T
  have hD := encodeTableau_length D
  cases o with
  | pauli q P =>
    simp only [stepTimeK, g1Time, cmaskR_length, hT, hD]; have := q.isLt; nlinarith
  | h q =>
    simp only [stepTimeK, g1Time, cmaskR_length, hT, hD]; have := q.isLt; nlinarith
  | s q =>
    simp only [stepTimeK, g1Time, cmaskR_length, hT, hD]; have := q.isLt; nlinarith
  | cnot c t _ =>
    simp only [stepTimeK, cnTime, cmaskR_length, hT, hD]; nlinarith
  | measure Mp =>
    simp only [stepTimeK, measTime]
    split <;> simp only [mmask_length, hT, hD] <;> nlinarith

lemma encOp_length_le {n : ℕ} (op : Option (CliffordOp n)) : (encOp op).length ≤ 3 * n + 10 := by
  rcases op with _ | o
  · simp [encOp]
  · cases o with
    | pauli q P =>
      have := q.isLt
      simp only [encOp, QAlgorithms.Complexity.encNat, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil, encPauli_length]; omega
    | h q =>
      have := q.isLt
      simp only [encOp, QAlgorithms.Complexity.encNat, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]; omega
    | s q =>
      have := q.isLt
      simp only [encOp, QAlgorithms.Complexity.encNat, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]; omega
    | cnot c t _ =>
      have := c.isLt
      have := t.isLt
      simp only [encOp, QAlgorithms.Complexity.encNat, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]; omega
    | measure M =>
      have hm := mmask_length M
      simp only [mmask, List.length_reverse] at hm
      simp only [encOp, QAlgorithms.Complexity.encNat, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil, hm]; omega

lemma fT_le {n : ℕ} (pl : ℕ) (gT : ℕ → ℕ) (hm : Monotone gT) (A : ℕ) (h : List (Option Bool))
    (op : Option (CliffordOp n)) (hA : h.length ≤ A) :
    fT pl gT h op ≤ 2 * (pl + 3 * A) + 3 + gT (pl + 3 * A + 1) + 3 * (3 * n + 11) := by
  have e1 := encOp_length_le op
  have e2 := hm (show pl + 3 * h.length + 1 ≤ pl + 3 * A + 1 by omega)
  unfold fT; omega

lemma kTime_le {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) (pl : ℕ) (gT : ℕ → ℕ)
    (A Bd S : ℕ) (hS : ∀ (o : CliffordOp n) (T D : Tableau n), stepTimeK o T D ≤ S)
    (hF : ∀ (h' : List (Option Bool)) (op : Option (CliffordOp n)), h'.length ≤ A →
      fT pl gT h' op ≤ Bd) :
    ∀ (k : ℕ) (TD : Tableau n × Tableau n) (h : List (Option Bool)) (cs : List Bool),
      h.length + k ≤ A → kTime ctl pl gT k TD h cs ≤ (k + 1) * (Bd + S)
  | 0, TD, h, cs, hA => by
    simp only [kTime]; have := hF h none (by omega); nlinarith
  | k + 1, TD, h, cs, hA => by
    cases hc : ctl h with
    | none => simp only [kTime, hc]; have := hF h none (by omega); nlinarith
    | some o =>
      simp only [kTime, hc]
      have e1 := hF h (some o) (by omega)
      have e2 := hS o TD.1 TD.2
      have e3 := kTime_le ctl pl gT A Bd S hS hF k (stepK o TD.1 TD.2 (cs.headD false)).1
        (h ++ [(stepK o TD.1 TD.2 (cs.headD false)).2]) (popC o cs)
        (by rw [List.length_append, List.length_singleton]; omega)
      nlinarith

/-- the whole controller loop time, from the empty transcript with fuel `k` -/
lemma kTime_bound {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) (pl : ℕ)
    (gT : ℕ → ℕ) (hm : Monotone gT) (k : ℕ) (TD : Tableau n × Tableau n) (cs : List Bool) :
    kTime ctl pl gT k TD [] cs ≤ (k + 1) * ((2 * (pl + 3 * k) + 3 + gT (pl + 3 * k + 1) +
      3 * (3 * n + 11)) + 200 * (n + 1) ^ 2) :=
  kTime_le ctl pl gT k _ _ (fun o T D => stepTimeK_le o T D)
    (fun h' op hA => fT_le pl gT hm k h' op hA) k TD [] cs (by simp)

lemma poly_mono (p : Polynomial ℕ) : Monotone (fun m => p.eval m) := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

lemma poly_le_pow (p : Polynomial ℕ) : ∃ c d : ℕ, ∀ m, p.eval m ≤ (m + c) ^ d := by
  refine ⟨(∑ i ∈ p.support, p.coeff i) + 1, p.natDegree + 1, fun m => ?_⟩
  have hS : ∀ i ∈ p.support, p.coeff i * m ^ i ≤ p.coeff i * (m + 1) ^ p.natDegree :=
    fun i hi => Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ m) i).trans
      (Nat.pow_le_pow_right (Nat.succ_pos m) (Polynomial.le_natDegree_of_mem_supp i hi)))
  calc p.eval m = ∑ i ∈ p.support, p.coeff i * m ^ i := by
        rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ ≤ ∑ i ∈ p.support, p.coeff i * (m + 1) ^ p.natDegree := Finset.sum_le_sum hS
    _ = (∑ i ∈ p.support, p.coeff i) * (m + 1) ^ p.natDegree := by rw [Finset.sum_mul]
    _ ≤ (m + ((∑ i ∈ p.support, p.coeff i) + 1)) *
          (m + ((∑ i ∈ p.support, p.coeff i) + 1)) ^ p.natDegree :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [pow_succ']

end Ctrl

end OCRS19TM

-- ===== session 29: Pre (setup + init wired in the 16-stack layout, ready for loop_run at LF) =====
namespace OCRS19TM

section Pre

open Turing QAlgorithms.Stabilizer

variable {R : Type} [DecidableEq R] {G : R → Type} {Λ ρ : Type}

/-- setup stacks: input/coins = 14, unary `n` = 1, input bits = 2, `Grev` = 13, scratch 3,4,5 -/
def kkS : Fin 7 → Fin 16 := ![14, 1, 2, 13, 3, 4, 5]
/-- init stacks: counter = 1, `N` = 0, scratch 3,4, bits = 2, `T` = 10, `D` = 11 -/
def kkI : Fin 7 → Fin 16 := ![1, 0, 3, 4, 2, 10, 11]

lemma kkS_inj : Function.Injective kkS := by decide
lemma kkI_inj : Function.Injective kkI := by decide

/-- the setup budget of `setup_run` -/
def setupT (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  (n + 1) + ((n + 1) + ((n + 1) + ((2 * n + 1) + (1 + (HT n 0 (hcoeffs p) +
    ((3 * p.eval n + 1) + 1))))))

/-- setup then init: from the raw input on stack 14 to the loop entry `LF` with the
`loop_run` stack invariants (transcript empty) -/
theorem pre_run (M : Λ → TM2.Stmt (BΓ (Fin 16) G) Λ (Reg × ρ)) (p : Polynomial ℕ)
    (P : Fin 10 → Λ) (HL : ℕ → Fin 5 → Λ) (I : Fin 17 → Λ) (LF : Λ)
    (hS : SetupProg M kkS p P HL (I 0)) (hI : InitProg M kkI I LF)
    (r : ρ) (c : Bool) (n : ℕ) (x : Fin n → Bool) (coins : List Bool)
    (hco : p.eval n ≤ coins.length) :
    ∃ B' : Fin 16 → List Bool,
      Reach M ⟨some (P 0), ((none, none, c), r),
          mk (Function.update (fun _ => []) 14
            (QAlgorithms.Complexity.encNat n ++ List.ofFn x ++ encBits coins)) (fun _ => [])⟩
        ⟨some LF, ((none, none, c), r), mk B' (fun _ => [])⟩
        (setupT p n + (n * (6 * n + 12) + 1)) ∧
      B' 0 = List.replicate n true ∧ B' 10 = rowsT n (List.ofFn x) ∧ B' 11 = rowsD n n ∧
      B' 13 = (QAlgorithms.Complexity.encNat n ++ encBits (coins.take (p.eval n))).reverse ∧
      B' 14 = (coins.drop (p.eval n)).flatMap pr ++ [false, false] ∧
      ∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' i = [] := by
  set B0 : Fin 16 → List Bool := Function.update (fun _ => []) 14
    (QAlgorithms.Complexity.encNat n ++ List.ofFn x ++ encBits coins) with hB0
  obtain ⟨B1, R1, e0, e1, e2, e3, e4, e5, e6, fr1⟩ := setup_run M kkS kkS_inj p P HL (I 0) hS r c
    (fun _ => []) n (List.ofFn x) coins (by simp) hco B0 (by simp [B0, kkS])
    (by simp [B0, kkS]) (by simp [B0, kkS]) (by simp [B0, kkS]) (by simp [B0, kkS])
    (by simp [B0, kkS]) (by simp [B0, kkS])
  simp only [kkS, Matrix.cons_val] at e0 e1 e2 e3 e4 e5 e6
  have f1 : ∀ j : Fin 16, j ≠ 14 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 3 → j ≠ 4 → j ≠ 5 → B1 j = [] := by
    intro j a b c' d e f g
    rw [fr1 j (by intro i; fin_cases i <;> simp [kkS] <;> assumption)]
    simp [B0, a]
  obtain ⟨B2, R2, g0, g1, g2, g3, g4, g5, g6, fr2⟩ := init_loop M kkI kkI_inj I LF hI r c
    (fun _ => []) n [] n le_rfl (List.ofFn x) B1 (by simp)
    (by simpa [kkI] using e1) (by simp [kkI, f1 0 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)])
    (by simpa [kkI] using e4) (by simpa [kkI] using e5) (by simpa [kkI] using e2)
  simp only [kkI, Matrix.cons_val] at g0 g1 g2 g3 g4 g5 g6
  have k2 : ∀ j : Fin 16, j ≠ 1 → j ≠ 0 → j ≠ 3 → j ≠ 4 → j ≠ 2 → j ≠ 10 → j ≠ 11 → B2 j = B1 j :=
    fun j a b c' d e f g => fr2 j (by intro i; fin_cases i <;> simp [kkI] <;> assumption)
  refine ⟨B2, R1.trans R2, g1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g5, f1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), List.append_nil]
  · rw [g6, f1 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), List.append_nil]
  · rw [k2 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), e3]
  · rw [k2 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), e0, encBits_eq]
  · intro i h0 h10 h11 h13 h14
    fin_cases i
    all_goals first
      | (exfalso; revert h0 h10 h11 h13 h14; decide)
      | assumption
      | (simp only [Fin.reduceFinMk, Fin.isValue] at *; first | exact g0 | exact g2 | exact g3 | exact g4 | skip)
    all_goals first
      | rfl
      | (rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; first
          | exact e6
          | exact f1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide))

end Pre

end OCRS19TM

namespace OCRS19TM

section Mach

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

variable {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ ε ρ : Type}

/-- canonical code of `MeasProg` -/
def MeasProg.code (K : Fin 8 → Kb) (L : Fin 20 → Λ) (E : Λ) :
    Fin 20 → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  ![ctlStmt (K 0) (K 1) (K 3) (K 6) (L 0) (L 1) (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y)) (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y),
    p2Stmt (K 1) (K 3) (L 2) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r),
    mvStmt (K 6) (K 0) (L 2) (L 3),
    dispStmt (fun r : MS ε => r.an.1) (fun r => r.fd) msMul msP msCopy (L 7) (L 12) (L 4),
    mvStmt (K 3) (K 4) (L 4) (L 5),
    mvStmt (K 4) (K 2) (L 5) (L 6),
    emitStmt (K 7) E (fun _ => false) id,
    mvStmt (K 3) (K 4) (L 7) (L 8),
    ctlStmt (K 5) (K 4) (K 2) (K 6) (L 8) (L 9) (fun r x y => MS.setMu r (cwδ mulW (MS.mu r) x y)) (fun r x y => co1 mulW (MS.mu r) x y) (fun r x y => co2 mulW (MS.mu r) x y),
    p2Stmt (K 4) (K 2) (L 10) (g1p2 MS.mu) (fun r _ _ => MS.setMu r (0, none)),
    mvStmt (K 6) (K 5) (L 10) (L 11),
    emitStmt (K 7) E (fun _ => false) id,
    popStStmt (K 3) (L 13) (fun r x => { r with cp := if x then 2 else 0 }),
    popStStmt (K 3) (L 14) (fun r x => { r with cp := r.cp + if x then 1 else 0 }),
    mvStmt (K 3) (K 5) (L 14) (L 15),
    dupStmt (K 0) (K 2) (K 6) (L 15) (L 16),
    mvStmt (K 6) (K 0) (L 16) (L 17),
    emitStmt (K 2) (L 18) (fun _ => false) id,
    emitStmt (K 2) (L 19) (fun r => r.cb) id,
    emitStmt (K 7) E (fun _ => true) id]

theorem MeasProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb) (L : Fin 20 → Λ) (E : Λ)
    (h : ∀ i, M (L i) = MeasProg.code K L E i) :
    MeasProg M K L E :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11, h 12, h 13, h 14, h 15, h 16, h 17, h 18, h 19⟩

/-- canonical code of `DProg` -/
def DProg.code (K : Fin 8 → Kb) (L : Fin 16 → Λ) (E : Λ) :
    Fin 16 → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  ![popStStmt (K 7) (L 1) (fun r x => { r with fd := x }),
    ctlStmt (K 0) (K 1) (K 3) (K 6) (L 1) (L 2) (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y)) (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y),
    p2Stmt (K 1) (K 3) (L 3) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r),
    mvStmt (K 6) (K 0) (L 3) (L 4),
    dispStmt (fun r : MS ε => r.an.1 || r.fd) (fun r => !r.fd) dMul dCp dCp (L 7) (L 11) (L 5),
    mvStmt (K 3) (K 4) (L 5) (L 6),
    mvStmt (K 4) (K 2) (L 6) E,
    mvStmt (K 3) (K 4) (L 7) (L 8),
    ctlStmt (K 5) (K 4) (K 2) (K 6) (L 8) (L 9) (fun r x y => MS.setMu r (cwδ mulW (MS.mu r) x y)) (fun r x y => co1 mulW (MS.mu r) x y) (fun r x y => co2 mulW (MS.mu r) x y),
    p2Stmt (K 4) (K 2) (L 10) (g1p2 MS.mu) (fun r _ _ => MS.setMu r (0, none)),
    mvStmt (K 6) (K 5) (L 10) E,
    clearStmt (K 3) (L 11) (L 12),
    dupStmt (K 5) (K 2) (K 6) (L 12) (L 13),
    mvStmt (K 6) (K 5) (L 13) (L 14),
    emitStmt (K 2) (L 15) (fun r => decide (r.cp.val % 2 = 1)) id,
    emitStmt (K 2) E (fun r => decide (2 ≤ r.cp.val)) id]

theorem DProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb) (L : Fin 16 → Λ) (E : Λ)
    (h : ∀ i, M (L i) = DProg.code K L E i) :
    DProg M K L E :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11, h 12, h 13, h 14, h 15⟩

/-- canonical code of `XProg` -/
def XProg.code (K : Fin 8 → Kb) (L : Fin 17 → Λ) (E : Λ) :
    Fin 17 → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  ![ctlStmt (K 0) (K 1) (K 3) (K 6) (L 0) (L 1) (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y)) (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y),
    p2Stmt (K 1) (K 3) (L 2) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r),
    mvStmt (K 6) (K 0) (L 2) (L 3),
    clearStmt (K 3) (L 3) (L 4),
    dispStmt (fun r : MS ε => r.an.1) (fun _ => true) msMul msCopy msCopy (L 5) (L 5) (L 12),
    ctlStmt (K 5) (K 2) (K 3) (K 6) (L 5) (L 6) (fun r x y => MS.setMu r (cwδ mulW (MS.mu r) x y)) (fun r x y => co1 mulW (MS.mu r) x y) (fun r x y => co2 mulW (MS.mu r) x y),
    p2Stmt (K 2) (K 3) (L 7) (g1p2 MS.mu) (fun r _ _ => MS.setMu r (0, none)),
    mvStmt (K 6) (K 5) (L 7) (L 8),
    clearStmt (K 5) (L 8) (L 9),
    popStStmt (K 3) (L 10) (fun r x => { r with cp := if x then 2 else 0 }),
    popStStmt (K 3) (L 11) (fun r x => { r with cp := r.cp + if x then 1 else 0 }),
    mvStmt (K 3) (K 5) (L 11) E,
    ctlStmt (K 0) (K 2) (K 3) (K 6) (L 12) (L 13) (fun r x y => MS.setAn r (cwδ antiW (MS.an r) x y)) (fun r x y => co1 antiW (MS.an r) x y) (fun r x y => co2 antiW (MS.an r) x y),
    p2Stmt (K 2) (K 3) (L 14) (fun _ x y => (x.getD false, y.getD false)) (fun r _ _ => r),
    mvStmt (K 6) (K 0) (L 14) (L 15),
    clearStmt (K 3) (L 15) (L 16),
    dispStmt (fun _ : MS ε => false) (fun _ => false) id id msCopy E E E]

theorem XProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 8 → Kb) (L : Fin 17 → Λ) (E : Λ)
    (h : ∀ i, M (L i) = XProg.code K L E i) :
    XProg M K L E :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11, h 12, h 13, h 14, h 15, h 16⟩

/-- canonical code of `DetProg` -/
def DetProg.code (K K' KX : Fin 8 → Kb) (LX : Fin 17 → Λ) (LT : Fin 11 → Λ) (E4 : Λ) :
    Fin 11 → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  ![clearStmt (K 7) (LT 0) (LT 1),
    mvStmt (K' 1) (K' 2) (LT 1) (LT 2),
    dupStmt (K' 2) (KX 1) (K' 1) (LT 2) (LT 3),
    mvStmt (K' 1) (K' 2) (LT 3) (LT 4),
    dupStmt (K 2) (KX 2) (K 1) (LT 4) (LT 5),
    mvStmt (K 1) (K 2) (LT 5) (LT 6),
    mvStmt (K 0) (K 6) (LT 6) (LT 7),
    dupFStmt (K 6) (K 0) (K 5) (fun _ => false) (LT 7) (LT 8),
    dispStmt (fun _ : MS ε => false) (fun _ => false) id id (fun r => { r with cp := 0 }) (LT 9) (LT 9) (LT 9),
    testStmt (KX 1) (LX 0) (LT 10),
    clearStmt (K 5) (LT 10) E4]

theorem DetProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K K' KX : Fin 8 → Kb) (LX : Fin 17 → Λ) (LT : Fin 11 → Λ) (E4 : Λ)
    (h : ∀ i, M (LT i) = DetProg.code K K' KX LX LT E4 i)
    (h_xp : XProg M KX LX (LT 9))
    (h_s0 : KX 0 = K 0)
    (h_s3 : KX 3 = K 3)
    (h_s5 : KX 5 = K 5)
    (h_s6 : KX 6 = K 6) :
    DetProg M K K' KX LX LT E4 :=
  ⟨h_xp, h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h_s0, h_s3, h_s5, h_s6⟩

/-- canonical code of `ParseProg` -/
def ParseProg.code (Y KW KT KM : Kb) (P : Fin 15 → Λ) (Halt PI PX PY PZ GH GS GC GM Bad : Λ) :
    Fin 15 → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  ![bitStmt Y (P 1) Halt,
    bitStmt Y (P 2) (P 6),
    bitStmt Y (P 3) (P 7),
    bitStmt Y (P 4) (P 8),
    bitStmt Y (P 5) (P 9),
    bitStmt Y Bad (P 10),
    unStmt Y KW (P 6) (P 11),
    unStmt Y KW (P 7) GH,
    unStmt Y KW (P 8) GS,
    unStmt Y KW (P 9) (P 14),
    mvStmt Y KM (P 10) GM,
    bitStmt Y (P 12) (P 13),
    bitStmt Y PY PX,
    bitStmt Y PZ PI,
    unStmt Y KT (P 14) GC]

theorem ParseProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (Y KW KT KM : Kb) (P : Fin 15 → Λ) (Halt PI PX PY PZ GH GS GC GM Bad : Λ)
    (h : ∀ i, M (P i) = ParseProg.code Y KW KT KM P Halt PI PX PY PZ GH GS GC GM Bad i) :
    ParseProg M Y KW KT KM P Halt PI PX PY PZ GH GS GC GM Bad :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11, h 12, h 13, h 14⟩

/-- canonical code of `HStage` -/
def HStage.code (V N O T : Kb) (c : ℕ) (L : Fin 5 → Λ) (E : Λ) :
    Fin 5 → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  ![popStmt V (L 1) (L 3),
    dupStmt N O T (L 1) (L 2),
    mvStmt T N (L 2) (L 0),
    mvStmt O V (L 3) (L 4),
    pushTs V c E]

theorem HStage.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (V N O T : Kb) (c : ℕ) (L : Fin 5 → Λ) (E : Λ)
    (h : ∀ i, M (L i) = HStage.code V N O T c L E i) :
    HStage M V N O T c L E :=
  ⟨h 0, h 1, h 2, h 3, h 4⟩

/-- canonical code of `SetupProg` -/
def SetupProg.code (kk : Fin 7 → Kb) (p : Polynomial ℕ) (P : Fin 10 → Λ) (HL : ℕ → Fin 5 → Λ) (E : Λ) :
    Fin 10 → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  ![unStmt (kk 0) (kk 1) (P 0) (P 1),
    dupStmt (kk 1) (kk 3) (kk 5) (P 1) (P 2),
    dupStmt (kk 5) (kk 1) (kk 6) (P 2) (P 3),
    popStmt (kk 6) (P 4) (P 5),
    mv1Stmt (kk 0) (kk 2) (P 3),
    pushL (kk 3) [false] (HL 0 0),
    popStmt (kk 4) (P 7) (P 9),
    mv1Stmt (kk 0) (kk 3) (P 8),
    mv1Stmt (kk 0) (kk 3) (P 6),
    pushL (kk 3) [false, false] E]

theorem SetupProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (kk : Fin 7 → Kb) (p : Polynomial ℕ) (P : Fin 10 → Λ) (HL : ℕ → Fin 5 → Λ) (E : Λ)
    (h : ∀ i, M (P i) = SetupProg.code kk p P HL E i)
    (h_hp : HProg M (kk 4) (kk 1) (kk 5) (kk 6) (hcoeffs p) HL (P 6)) :
    SetupProg M kk p P HL E :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h_hp, h 6, h 7, h 8, h 9⟩

/-- canonical code of `InitProg` -/
def InitProg.code (kk : Fin 7 → Kb) (I : Fin 17 → Λ) (Ex : Λ) :
    Fin 17 → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ) :=
  ![popStmt (kk 0) (I 1) Ex,
    popStmt (kk 1) (I 2) (I 5),
    pushTs (kk 2) 1 (I 3),
    pushL (kk 5) [false, false] (I 4),
    pushL (kk 6) [false, false] (I 1),
    pushL (kk 5) [true, false] (I 6),
    pushL (kk 6) [false, true] (I 7),
    popStmt (kk 0) (I 8) (I 11),
    pushTs (kk 3) 1 (I 9),
    pushL (kk 5) [false, false] (I 10),
    pushL (kk 6) [false, false] (I 7),
    pushL (kk 5) [false] (I 12),
    mv1Stmt (kk 4) (kk 5) (I 13),
    pushL (kk 6) [false, false] (I 14),
    mvStmt (kk 3) (kk 0) (I 14) (I 15),
    mvStmt (kk 2) (kk 1) (I 15) (I 16),
    pushTs (kk 1) 1 (I 0)]

theorem InitProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × ρ)) (kk : Fin 7 → Kb) (I : Fin 17 → Λ) (Ex : Λ)
    (h : ∀ i, M (I i) = InitProg.code kk I Ex i) :
    InitProg M kk I Ex :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11, h 12, h 13, h 14, h 15, h 16⟩

/-- canonical code of `G1Prog` -/
def G1Prog.code (K : Fin 15 → Kb) (Gl : Fin 18 → Λ) (Ex : Λ) (f : Pauli → ZMod 4 × Pauli) (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε) (getZ : MS ε → ZMod 4 × Option (Bool × Bool)) (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε) :
    Fin 18 → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  ![dupStmt (K 1) (K 2) (K 3) (Gl 0) (Gl 1),
    ctlStmt (K 0) (K 2) (K 4) (K 7) (Gl 1) (Gl 2) (fun r x y => setB r (cmδ1 (getB r) x y)) (fun r x y => cmO1 (getB r) x y) (fun r x y => cmNo (getB r) x y),
    mvStmt (K 4) (K 5) (Gl 2) (Gl 3),
    ctlStmt (K 5) (K 3) (K 6) (K 8) (Gl 3) (Gl 4) (fun r x y => setB r (cmδ2 (getB r) x y)) (fun r x y => cmO2a (getB r) x y) (fun r x y => cmO2b (getB r) x y),
    clearStmt (K 8) (Gl 4) (Gl 5),
    mvStmt (K 7) (K 0) (Gl 5) (Gl 6),
    mvStmt (K 10) (K 9) (Gl 6) (Gl 7),
    testStmt (K 9) (Gl 8) (Gl 11),
    ctlStmt (K 6) (K 9) (K 10) (K 12) (Gl 8) (Gl 9) (fun r x y => setZ r (cwδ (g1W f) (getZ r) x y)) (fun r x y => co1 (g1W f) (getZ r) x y) (fun r x y => co2 (g1W f) (getZ r) x y),
    p2Stmt (K 9) (K 10) (Gl 10) (g1p2 getZ) (fun r _ _ => setZ r (0, none)),
    mvStmt (K 12) (K 6) (Gl 10) (Gl 7),
    mvStmt (K 11) (K 9) (Gl 11) (Gl 12),
    testStmt (K 9) (Gl 13) (Gl 16),
    ctlStmt (K 6) (K 9) (K 11) (K 12) (Gl 13) (Gl 14) (fun r x y => setZ r (cwδ (g1W f) (getZ r) x y)) (fun r x y => co1 (g1W f) (getZ r) x y) (fun r x y => co2 (g1W f) (getZ r) x y),
    p2Stmt (K 9) (K 11) (Gl 15) (g1p2 getZ) (fun r _ _ => setZ r (0, none)),
    mvStmt (K 12) (K 6) (Gl 15) (Gl 12),
    clearStmt (K 6) (Gl 16) (Gl 17),
    pushL (K 13) [true, false, false] Ex]

theorem G1Prog.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 15 → Kb) (Gl : Fin 18 → Λ) (Ex : Λ) (f : Pauli → ZMod 4 × Pauli) (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε) (getZ : MS ε → ZMod 4 × Option (Bool × Bool)) (setZ : MS ε → ZMod 4 × Option (Bool × Bool) → MS ε)
    (h : ∀ i, M (Gl i) = G1Prog.code K Gl Ex f getB setB getZ setZ i) :
    G1Prog M K Gl Ex f getB setB getZ setZ :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11, h 12, h 13, h 14, h 15, h 16, h 17⟩

/-- canonical code of `CNProg` -/
def CNProg.code (K : Fin 15 → Kb) (Gl : Fin 23 → Λ) (Ex : Λ) (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε) (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool)) (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε) (s0 : Pauli × Pauli) :
    Fin 23 → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε) :=
  ![ctlStmt (K 0) (K 1) (K 4) (K 7) (Gl 0) (Gl 1) (fun r x y => setB r (cmδ1 (getB r) x y)) (fun r x y => cmO1 (getB r) x y) (fun r x y => cmNo (getB r) x y),
    mvStmt (K 4) (K 5) (Gl 1) (Gl 2),
    ctlStmt (K 5) (K 2) (K 6) (K 8) (Gl 2) (Gl 3) (fun r x y => setB r (cmδ2 (getB r) x y)) (fun r x y => cmO2a (getB r) x y) (fun r x y => cmO2b (getB r) x y),
    clearStmt (K 8) (Gl 3) (Gl 4),
    mvStmt (K 7) (K 0) (Gl 4) (Gl 5),
    mvStmt (K 10) (K 9) (Gl 5) (Gl 6),
    testStmt (K 9) (Gl 7) (Gl 13),
    ctlStmt (K 6) (K 9) (K 3) (K 12) (Gl 7) (Gl 8) (fun r x y => setC r (cwδ capW (getC r) x y)) (fun r x y => co1 capW (getC r) x y) (fun r x y => co2 capW (getC r) x y),
    mvStmt (K 3) (K 9) (Gl 8) (Gl 9),
    mvStmt (K 12) (K 6) (Gl 9) (Gl 10),
    ctlStmt (K 6) (K 9) (K 10) (K 12) (Gl 10) (Gl 11) (fun r x y => setC r (cwδ cnotAW (getC r) x y)) (fun r x y => co1 cnotAW (getC r) x y) (fun r x y => co2 cnotAW (getC r) x y),
    p2Stmt (K 9) (K 10) (Gl 12) (gC getC) (fun r _ _ => setC r (s0, none)),
    mvStmt (K 12) (K 6) (Gl 12) (Gl 6),
    mvStmt (K 11) (K 9) (Gl 13) (Gl 14),
    testStmt (K 9) (Gl 15) (Gl 21),
    ctlStmt (K 6) (K 9) (K 3) (K 12) (Gl 15) (Gl 16) (fun r x y => setC r (cwδ capW (getC r) x y)) (fun r x y => co1 capW (getC r) x y) (fun r x y => co2 capW (getC r) x y),
    mvStmt (K 3) (K 9) (Gl 16) (Gl 17),
    mvStmt (K 12) (K 6) (Gl 17) (Gl 18),
    ctlStmt (K 6) (K 9) (K 11) (K 12) (Gl 18) (Gl 19) (fun r x y => setC r (cwδ cnotAW (getC r) x y)) (fun r x y => co1 cnotAW (getC r) x y) (fun r x y => co2 cnotAW (getC r) x y),
    p2Stmt (K 9) (K 11) (Gl 20) (gC getC) (fun r _ _ => setC r (s0, none)),
    mvStmt (K 12) (K 6) (Gl 20) (Gl 14),
    clearStmt (K 6) (Gl 21) (Gl 22),
    pushL (K 13) [true, false, false] Ex]

theorem CNProg.ofCode (M : Λ → TM2.Stmt (BΓ Kb G) Λ (Reg × MS ε)) (K : Fin 15 → Kb) (Gl : Fin 23 → Λ) (Ex : Λ) (getB : MS ε → Bool) (setB : MS ε → Bool → MS ε) (getC : MS ε → (Pauli × Pauli) × Option (Bool × Bool)) (setC : MS ε → (Pauli × Pauli) × Option (Bool × Bool) → MS ε) (s0 : Pauli × Pauli)
    (h : ∀ i, M (Gl i) = CNProg.code K Gl Ex getB setB getC setC s0 i) :
    CNProg M K Gl Ex getB setB getC setC s0 :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11, h 12, h 13, h 14, h 15, h 16, h 17, h 18, h 19, h 20, h 21, h 22⟩

end Mach

end OCRS19TM

namespace OCRS19TM

section Conc

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- finiteness of the one-qubit Pauli alphabet -/
def pauliFintype : Fintype Pauli :=
  Fintype.ofList [Pauli.I, Pauli.X, Pauli.Y, Pauli.Z] (by intro x; cases x <;> simp)

attribute [local instance] pauliFintype

/-- the concrete scan state is finite -/
def msFintype (ε : Type) [Fintype ε] : Fintype (MS ε) :=
  Fintype.ofEquiv ((Bool × Option (Bool × Bool)) × (ZMod 4 × Option (Bool × Bool)) × Bool × ZMod 4 ×
      Bool × ε)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
      invFun := fun r => (r.an, r.mu, r.fd, r.cp, r.cb, r.ext)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- labels of the concrete machine: one constructor per program block; `TL` = labels of `g` -/
inductive Lb (TL : Type) (m : ℕ) : Type
  | g1 : Fin 6 → Fin 18 → Lb TL m
  | cn : Fin 23 → Lb TL m
  | mL : Fin 20 → Lb TL m
  | mD : Fin 16 → Lb TL m
  | mX : Fin 17 → Lb TL m
  | mT : Fin 11 → Lb TL m
  | pa : Fin 15 → Lb TL m
  | su : Fin 10 → Lb TL m
  | ho : Fin m → Fin 5 → Lb TL m
  | ini : Fin 17 → Lb TL m
  | lF : Lb TL m
  | l1 : Lb TL m
  | l2 : Lb TL m
  | lr : Lb TL m
  | lm : Lb TL m
  | halt : Lb TL m
  | bad : Lb TL m
  | w0 : Lb TL m
  | w1 : Lb TL m
  | e1 : Lb TL m
  | e2 : Lb TL m
  | e3 : Lb TL m
  | eD : Lb TL m
  | e4 : Lb TL m
  | eb : Lb TL m
  | e5 : Lb TL m
  | r1 : Lb TL m
  | r2 : Lb TL m
  | d1 : Lb TL m
  | lc : Lb TL m
  | sub : TL → Lb TL m
  deriving Fintype

variable (T : FinTM2)

/-- extra state: gate bit, gate scan, CNOT scan, and `g`'s own state -/
abbrev εc : Type :=
  Bool × (ZMod 4 × Option (Bool × Bool)) × ((Pauli × Pauli) × Option (Bool × Bool)) × T.σ

def cGetB (r : MS (εc T)) : Bool := r.ext.1
def cSetB (r : MS (εc T)) (t : Bool) : MS (εc T) := { r with ext := (t, r.ext.2) }
def cGetZ (r : MS (εc T)) : ZMod 4 × Option (Bool × Bool) := r.ext.2.1
def cSetZ (r : MS (εc T)) (t : ZMod 4 × Option (Bool × Bool)) : MS (εc T) :=
  { r with ext := (r.ext.1, t, r.ext.2.2) }
def cGetC (r : MS (εc T)) : (Pauli × Pauli) × Option (Bool × Bool) := r.ext.2.2.1
def cSetC (r : MS (εc T)) (t : (Pauli × Pauli) × Option (Bool × Bool)) : MS (εc T) :=
  { r with ext := (r.ext.1, r.ext.2.1, t, r.ext.2.2.2) }

/-- the one-wire gate tables in the order I X Y Z H S -/
def gfT : Fin 6 → Pauli → ZMod 4 × Pauli :=
  ![kconjP .I, kconjP .X, kconjP .Y, kconjP .Z, kconjH, kconjS]

/-- the slot hosting `g` -/
def slotc (m : ℕ) : Slot T (Fin 16 ⊕ T.K) (BΓ (Fin 16) T.Γ) (Lb T.Λ m) (Reg × MS (εc T)) where
  kf := Sum.inr
  kf_inj := Sum.inr_injective
  gin := fun _ a => a
  gout := fun _ a => a
  gout_gin := fun _ _ => rfl
  sget := fun v => v.2.ext.2.2.2
  sset := fun v s => (v.1, { v.2 with ext := (v.2.ext.1, v.2.ext.2.1, v.2.ext.2.2.1, s) })
  get_set := fun _ _ => rfl
  set_set := fun _ _ _ => rfl
  lf := Lb.sub
  ret := Lb.lr

variable (p : Polynomial ℕ)

/-- Horner stage labels -/
def HLc : ℕ → Fin 5 → Lb T.Λ (hcoeffs p).length :=
  fun i j => if h : i < (hcoeffs p).length then Lb.ho ⟨i, h⟩ j else Lb.bad

variable (enc : Bool → T.Γ T.k₀) (dec : T.Γ T.k₁ → Bool)

/-- the concrete machine -/
def Mc : Lb T.Λ (hcoeffs p).length →
    TM2.Stmt (BΓ (Fin 16) T.Γ) (Lb T.Λ (hcoeffs p).length) (Reg × MS (εc T))
  | .g1 g i => G1Prog.code (id ∘ Fin.castSucc) (Lb.g1 g) (Lb.lF) (gfT g) (cGetB T) (cSetB T)
      (cGetZ T) (cSetZ T) i
  | .cn i => CNProg.code (id ∘ Fin.castSucc) Lb.cn (Lb.lF) (cGetB T) (cSetB T) (cGetC T)
      (cSetC T) (Pauli.I, Pauli.I) i
  | .mL i => MeasProg.code (id ∘ memb) Lb.mL (Lb.e1) i
  | .mD i => DProg.code (id ∘ demb) Lb.mD (Lb.eD) i
  | .mX i => XProg.code (id ∘ xemb) Lb.mX (Lb.mT 9) i
  | .mT i => DetProg.code (id ∘ memb) (id ∘ demb) (id ∘ xemb) Lb.mX Lb.mT (Lb.e5) i
  | .pa i => ParseProg.code (id 15) (id 1) (id 2) (id 6) Lb.pa (Lb.halt) (Lb.g1 0 0) (Lb.g1 1 0)
      (Lb.g1 2 0) (Lb.g1 3 0) (Lb.g1 4 0) (Lb.g1 5 0) (Lb.cn 0) (Lb.lc) (Lb.bad) i
  | .su i => SetupProg.code kkS p Lb.su (HLc T p) (Lb.ini 0) i
  | .ho i j => HStage.code (kkS 4) (kkS 1) (kkS 5) (kkS 6) ((hcoeffs p)[i.1]'i.2) (HLc T p i.1)
      (if i.1 + 1 < (hcoeffs p).length then HLc T p (i.1 + 1) 0 else Lb.su 6) j
  | .ini i => InitProg.code kkI Lb.ini (Lb.lF) i
  | .lF => pushInrStmt T.k₀ (enc false) (Lb.l1)
  | .l1 => dcvStmt 13 T.k₀ enc 3 (Lb.l1) (Lb.l2)
  | .l2 => mvStmt 3 13 (Lb.l2) (Lb.sub T.main)
  | .lr => cvStmt T.k₁ dec 3 (Lb.lr) (Lb.lm)
  | .lm => mvStmt 3 15 (Lb.lm) (Lb.pa 0)
  | .halt => TM2.Stmt.halt
  | .bad => TM2.Stmt.halt
  | .w0 => mvStmt 10 9 (Lb.w0) (Lb.w1)
  | .w1 => mvStmt 11 7 (Lb.w1) (Lb.e1)
  | .e1 => testStmt ((id ∘ memb) 1) (Lb.mL 0) (Lb.eb)
  | .e2 => mvStmt ((id ∘ memb) 7) ((id ∘ demb) 7) (Lb.e2) (Lb.e3)
  | .e3 => dispStmt (fun _ : MS (εc T) => false) (fun _ => false) id id (fun r => { r with fd := false }) (Lb.eD) (Lb.eD) (Lb.eD)
  | .eD => testStmt ((id ∘ demb) 1) (Lb.mD 0) (Lb.e4)
  | .e4 => clearStmt 3 (Lb.e4) (Lb.r1)
  | .eb => dispStmt (fun r : MS (εc T) => r.fd) (fun _ => true) id id id (Lb.e2) (Lb.e2) (Lb.mT 0)
  | .e5 => clearStmt 6 (Lb.e5) (Lb.d1)
  | .r1 => clearStmt 6 (Lb.r1) (Lb.r2)
  | .r2 => pushMStmt 13 (fun r => r.cb) (Lb.lF)
  | .d1 => pushMStmt 13 (fun r => decide (r.cp = 2)) (Lb.lF)
  | .lc => coinStmt 14 (Lb.w0)
  | .sub l => (slotc T (hcoeffs p).length).tr (T.m l)

theorem mc_g1 (g : Fin 6) :
    G1Prog (Mc T p enc dec) (id ∘ Fin.castSucc) (Lb.g1 g) (Lb.lF) (gfT g) (cGetB T) (cSetB T)
      (cGetZ T) (cSetZ T) :=
  G1Prog.ofCode _ _ _ _ _ _ _ _ _ (fun _ => rfl)

theorem mc_cn : CNProg (Mc T p enc dec) (id ∘ Fin.castSucc) Lb.cn (Lb.lF) (cGetB T) (cSetB T)
    (cGetC T) (cSetC T) (Pauli.I, Pauli.I) :=
  CNProg.ofCode _ _ _ _ _ _ _ _ _ (fun _ => rfl)

theorem mc_parse : ParseProg (Mc T p enc dec) (id 15) (id 1) (id 2) (id 6) Lb.pa (Lb.halt)
    (Lb.g1 0 0) (Lb.g1 1 0) (Lb.g1 2 0) (Lb.g1 3 0) (Lb.g1 4 0) (Lb.g1 5 0) (Lb.cn 0) (Lb.lc)
    (Lb.bad) :=
  ParseProg.ofCode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => rfl)

theorem mc_rmeas : MeasProg (Mc T p enc dec) (id ∘ memb) Lb.mL Lb.e1 :=
  MeasProg.ofCode _ _ _ _ (fun _ => rfl)

theorem mc_rd : DProg (Mc T p enc dec) (id ∘ demb) Lb.mD Lb.eD :=
  DProg.ofCode _ _ _ _ (fun _ => rfl)

theorem mc_rbr : Mc T p enc dec Lb.eb = dispStmt (fun r : MS (εc T) => r.fd) (fun _ => true) id id id
    Lb.e2 Lb.e2 (Lb.mT 0) := rfl

theorem mc_rst : Mc T p enc dec Lb.e3 = dispStmt (fun _ : MS (εc T) => false) (fun _ => false) id id
    (fun r => { r with fd := false }) Lb.eD Lb.eD Lb.eD := rfl

theorem mc_rs : (id ∘ demb) 0 = (id ∘ memb) 0 ∧ (id ∘ demb) 3 = (id ∘ memb) 3 ∧
    (id ∘ demb) 4 = (id ∘ memb) 4 ∧ (id ∘ demb) 5 = (id ∘ memb) 5 ∧ (id ∘ demb) 6 = (id ∘ memb) 6 := by
  decide

set_option maxHeartbeats 1000000 in
theorem mc_rand : RandProg (Mc T p enc dec) (id ∘ memb) (id ∘ demb) Lb.mL Lb.mD Lb.e1 Lb.e2 Lb.e3
    Lb.eD Lb.e4 Lb.eb (Lb.mT 0) :=
  ⟨mc_rmeas T p enc dec, rfl, mc_rbr T p enc dec, rfl, mc_rst T p enc dec,
    mc_rd T p enc dec, rfl, mc_rs.1, mc_rs.2.1, mc_rs.2.2.1, mc_rs.2.2.2.1, mc_rs.2.2.2.2⟩

theorem mc_det : DetProg (Mc T p enc dec) (id ∘ memb) (id ∘ demb) (id ∘ xemb) Lb.mX Lb.mT Lb.e5 :=
  DetProg.ofCode _ _ _ _ _ _ _ (fun _ => rfl) (XProg.ofCode _ _ _ _ (fun _ => rfl))
    rfl rfl rfl rfl

theorem mc_measW : MeasW (Mc T p enc dec) id Lb.mL Lb.mD Lb.mX Lb.mT (Lb.w0) (Lb.w1)
    (Lb.e1) (Lb.e2) (Lb.e3) (Lb.eD) (Lb.e4) (Lb.eb) (Lb.e5) (Lb.r1)
    (Lb.r2) (Lb.d1) (Lb.lF) where
  w0 := rfl
  w1 := rfl
  rand := mc_rand T p enc dec
  det := mc_det T p enc dec
  r0 := rfl
  r1 := rfl
  r2 := rfl
  d0 := rfl
  d1 := rfl

theorem mc_setup : SetupProg (Mc T p enc dec) kkS p Lb.su (HLc T p) (Lb.ini 0) := by
  refine SetupProg.ofCode _ _ _ _ _ _ (fun _ => rfl) ?_
  intro i hi
  have e : ∀ j, HLc T p i j = Lb.ho ⟨i, hi⟩ j := fun j => dif_pos hi
  refine HStage.ofCode _ _ _ _ _ _ _ _ (fun j => ?_)
  rw [e j]
  rfl

theorem mc_init : InitProg (Mc T p enc dec) kkI Lb.ini (Lb.lF) :=
  InitProg.ofCode _ _ _ _ (fun _ => rfl)

theorem mc_hosts : (slotc T (hcoeffs p).length).Hosts (Mc T p enc dec) := fun _ => rfl

end Conc

end OCRS19TM

namespace OCRS19TM

-- ===== session 36: hg (the controller g runs in the slot) =====
section Hg

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (T : FinTM2) (p : Polynomial ℕ) (enc : Bool → T.Γ T.k₀) (dec : T.Γ T.k₁ → Bool)

theorem mc_hg (gS : List Bool → List Bool) (gT : ℕ → ℕ) (decI : Bool → T.Γ T.k₁)
    (hdec : ∀ b, dec (decI b) = b)
    (hrun : ∀ w : List Bool, TM2OutputsInTime T (w.map enc) (some ((gS w).map decI)) (gT w.length)) :
    ∀ (w : List Bool) (B : Fin 16 → List Bool) (r : MS (εc T)), r.ext.2.2.2 = T.initialState →
      ∀ c : Bool, ∃ Q' : ∀ s, List (T.Γ s),
        Reach (Mc T p enc dec)
          ⟨some (Lb.sub T.main), ((none, none, c), r),
            mk B (Function.update (fun _ => []) T.k₀ (w.map enc))⟩
          ⟨some Lb.lr, ((none, none, c), r), mk B Q'⟩ (gT w.length) ∧
        (Q' T.k₁).map dec = gS w ∧ ∀ s, s ≠ T.k₁ → Q' s = [] := by
  intro w B r hr c
  have hrel : (slotc T (hcoeffs p).length).Rel (initList T (w.map enc)).stk
      (mk B (Function.update (fun _ => []) T.k₀ (w.map enc))) (mk B (fun _ => [])) := by
    refine ⟨fun k => ?_, fun k' hk' => ?_⟩
    · by_cases hk : k = T.k₀
      · subst hk; simp [initList, slotc, mk]
      · simp [initList, slotc, mk, hk, Function.update_of_ne hk]
    · rcases k' with a | k
      · rfl
      · exact absurd rfl (hk' k)
  obtain ⟨S', hS', hreach⟩ := (slotc T (hcoeffs p).length).sub_run (Mc T p enc dec)
    (mc_hosts T p enc dec) ((none, none, c), r) (mk B (fun _ => []))
    (mk B (Function.update (fun _ => []) T.k₀ (w.map enc))) (hrun w) hrel
  have hv : (slotc T (hcoeffs p).length).sset ((none, none, c), r) T.initialState =
      ((none, none, c), r) := by
    show ((none, none, c), { r with ext := (r.ext.1, r.ext.2.1, r.ext.2.2.1, T.initialState) }) = _
    rw [← hr]
  have hS : S' = mk B (fun s => S' (Sum.inr s)) := by
    funext k
    rcases k with a | k
    · exact hS'.2 (Sum.inl a) (fun k h => Sum.inr_ne_inl h)
    · rfl
  refine ⟨fun s => S' (Sum.inr s), ?_, ?_, ?_⟩
  · rw [hv] at hreach
    have e : (slotc T (hcoeffs p).length).lf T.main = Lb.sub T.main := rfl
    have e2 : (slotc T (hcoeffs p).length).ret = Lb.lr := rfl
    rw [e, e2] at hreach
    rw [← hS]
    exact hreach
  · have h1 := hS'.1 T.k₁
    change S' (Sum.inr T.k₁) = ((haltList T ((gS w).map decI)).stk T.k₁).map (fun a => a) at h1
    show List.map dec (S' (Sum.inr T.k₁)) = gS w
    rw [h1]
    simp [haltList, hdec, Function.comp_def]
  · intro s hs
    have h1 := hS'.1 s
    change S' (Sum.inr s) = ((haltList T ((gS w).map decI)).stk s).map (fun a => a) at h1
    show S' (Sum.inr s) = []
    rw [h1]
    simp [haltList, hs]

/-- loop invariant of the concrete scan state -/
def Ivc (r : MS (εc T)) : Prop :=
  r.ext.2.2.2 = T.initialState ∧ cGetB T r = false ∧ cGetZ T r = (0, none) ∧
    cGetC T r = ((Pauli.I, Pauli.I), none) ∧ r.an = (false, none) ∧ r.mu = (0, none) ∧ r.fd = false

set_option maxHeartbeats 1000000 in
theorem mc_loop (gS : List Bool → List Bool) (gT : ℕ → ℕ) (decI : Bool → T.Γ T.k₁)
    (hdec : ∀ b, dec (decI b) = b)
    (hrun : ∀ w : List Bool, TM2OutputsInTime T (w.map enc) (some ((gS w).map decI)) (gT w.length))
    {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n)) (pre : List Bool)
    (hctl : ∀ h, gS (pre ++ h.flatMap hcode ++ [false]) = encOp (ctl h))
    (rest : List Bool) (c : Bool) :
    ∀ (k : ℕ) (TD : Tableau n × Tableau n) (h : List (Option Bool)) (cs : List Bool)
      (B : Fin 16 → List Bool) (r : MS (εc T)), Ivc T r → k ≤ cs.length →
      ctl (kloop ctl k TD h cs).2.1 = none →
      B 0 = List.replicate n true → B 10 = encodeTableau TD.1 →
      B 11 = encodeTableau TD.2 → B 13 = (pre ++ h.flatMap hcode).reverse →
      B 14 = cs.flatMap pr ++ rest →
      (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B i = []) →
      ∃ (B' : Fin 16 → List Bool) (r' : MS (εc T)), Ivc T r' ∧
        Reach (Mc T p enc dec) ⟨some Lb.lF, ((none, none, c), r), mk B (fun _ => [])⟩
          ⟨some Lb.halt, ((none, none, c), r'), mk B' (fun _ => [])⟩
          (kTime ctl pre.length gT k TD h cs) ∧
        B' 10 = encodeTableau (kloop ctl k TD h cs).1.1 ∧
        B' 11 = encodeTableau (kloop ctl k TD h cs).1.2 ∧
        B' 13 = (pre ++ (kloop ctl k TD h cs).2.1.flatMap hcode).reverse ∧
        B' 14 = (kloop ctl k TD h cs).2.2.flatMap pr ++ rest ∧
        B' 0 = B 0 ∧
        (∀ i : Fin 16, i ≠ 0 → i ≠ 10 → i ≠ 11 → i ≠ 13 → i ≠ 14 → B' i = []) ∧
        ∀ x, (∀ i, x ≠ id i) → B' x = B x :=
  loop_run (Mc T p enc dec) id Function.injective_id Lb.lF Lb.l1 Lb.l2 (Lb.sub T.main) Lb.lr Lb.lm
    Lb.pa Lb.halt Lb.bad T.k₀ T.k₁ enc dec rfl rfl rfl rfl rfl
    (Lb.g1 0) (Lb.g1 1) (Lb.g1 2) (Lb.g1 3) (Lb.g1 4) (Lb.g1 5) Lb.cn Lb.mL Lb.mD Lb.mX Lb.mT
    Lb.w0 Lb.w1 Lb.e1 Lb.e2 Lb.e3 Lb.eD Lb.e4 Lb.eb Lb.e5 Lb.r1 Lb.r2 Lb.d1 Lb.lc
    (mc_parse T p enc dec) gS gT (fun r => r.ext.2.2.2 = T.initialState)
    (fun w B r hr c => mc_hg T p enc dec gS gT decI hdec hrun w B r hr c)
    (cGetB T) (cSetB T) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (cGetZ T) (cSetZ T) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (cGetC T) (cSetC T) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (Pauli.I, Pauli.I)
    (mc_g1 T p enc dec 0) (mc_g1 T p enc dec 1) (mc_g1 T p enc dec 2) (mc_g1 T p enc dec 3)
    (mc_g1 T p enc dec 4) (mc_g1 T p enc dec 5) (mc_cn T p enc dec) (mc_measW T p enc dec) rfl
    ctl pre hctl (Ivc T) (fun _ h => ⟨h.1, h.2⟩) (fun _ _ _ h => h) rest c

set_option maxHeartbeats 1000000 in
theorem mc_full (gS : List Bool → List Bool) (gT : ℕ → ℕ) (decI : Bool → T.Γ T.k₁)
    (hdec : ∀ b, dec (decI b) = b)
    (hrun : ∀ w : List Bool, TM2OutputsInTime T (w.map enc) (some ((gS w).map decI)) (gT w.length))
    (n : ℕ) (x : Fin n → Bool) (coins : List Bool) (hco : p.eval n ≤ coins.length)
    (ctl : List (Option Bool) → Option (CliffordOp n))
    (hctl : ∀ h, gS ((QAlgorithms.Complexity.encNat n ++ encBits (coins.take (p.eval n))) ++
      h.flatMap hcode ++ [false]) = encOp (ctl h))
    (k : ℕ) (hk : k ≤ (coins.drop (p.eval n)).length)
    (hstop : ctl (kloop ctl k
      ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
        (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) [] (coins.drop (p.eval n))).2.1 = none)
    (r : MS (εc T)) (hr : Ivc T r) (c : Bool) :
    ∃ (B' : Fin 16 → List Bool) (r' : MS (εc T)),
      Reach (Mc T p enc dec) ⟨some (Lb.su 0), ((none, none, c), r),
          mk (Function.update (fun _ => []) 14
            (QAlgorithms.Complexity.encNat n ++ List.ofFn x ++ encBits coins)) (fun _ => [])⟩
        ⟨some Lb.halt, ((none, none, c), r'), mk B' (fun _ => [])⟩
        (setupT p n + (n * (6 * n + 12) + 1) +
          kTime ctl (QAlgorithms.Complexity.encNat n ++ encBits (coins.take (p.eval n))).length gT k
            ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
              (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) [] (coins.drop (p.eval n))) ∧
      B' 10 = encodeTableau (kloop ctl k
        ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
          (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) [] (coins.drop (p.eval n))).1.1 := by
  obtain ⟨B1, h1, e0, e10, e11, e13, e14, fr⟩ := pre_run (Mc T p enc dec) p Lb.su (HLc T p) Lb.ini
    Lb.lF (mc_setup T p enc dec) (mc_init T p enc dec) r c n x coins hco
  obtain ⟨B', r', -, h2, o10, -⟩ := mc_loop T p enc dec gS gT decI hdec hrun ctl
    (QAlgorithms.Complexity.encNat n ++ encBits (coins.take (p.eval n))) hctl [false, false] c k
    _ [] (coins.drop (p.eval n)) B1 r hr hk hstop e0 (by rw [e10, rowsT_init])
    (by rw [e11, rowsD_init]) (by rw [e13]; simp) e14 fr
  exact ⟨B', r', h1.trans h2, o10⟩

end Hg

section Fin2

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (T : FinTM2) (p : Polynomial ℕ) (enc : Bool → T.Γ T.k₀) (dec : T.Γ T.k₁ → Bool)

/-- the initial extra state of the machine -/
def r0 : MS (εc T) :=
  ⟨(false, none), (0, none), false, 0, false,
    (false, (0, none), ((Pauli.I, Pauli.I), none), T.initialState)⟩

lemma ivc_r0 : Ivc T (r0 T) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- one more step from the `halt` label stops the machine -/
lemma reach_halt_step {c : TM2.Cfg (BΓ (Fin 16) T.Γ) (Lb T.Λ (hcoeffs p).length) (Reg × MS (εc T))}
    {v : Reg × MS (εc T)} {S : ∀ k, List (BΓ (Fin 16) T.Γ k)} {t : ℕ}
    (h : Reach (Mc T p enc dec) c ⟨some Lb.halt, v, S⟩ t) :
    ∃ t' ≤ t, (flip bind (TM2.step (Mc T p enc dec)))^[t' + 1] (some c) = some ⟨none, v, S⟩ := by
  obtain ⟨t', ht', e⟩ := h
  refine ⟨t', ht', ?_⟩
  rw [Function.iterate_succ_apply', e]
  rfl

/-- the input stack layout of `mc_full` is the standard one (input on stack `14`) -/
lemma init_stk (L : List Bool) :
    mk (G := T.Γ) (Function.update (fun _ => ([] : List Bool)) (14 : Fin 16) L) (fun _ => []) =
      Function.update (fun k => ([] : List (BΓ (Fin 16) T.Γ k))) (Sum.inl 14)
        (L.map (Equiv.refl Bool).symm) := by
  funext k
  rcases k with a | r
  · by_cases ha : a = 14
    · subst ha
      rw [Function.update_self]
      simp [mk]
    · rw [Function.update_of_ne (by simpa using ha)]
      simp [mk, Function.update_of_ne ha]
  · rw [Function.update_of_ne (by simp)]
    rfl

set_option maxHeartbeats 1000000 in
/-- `mc_full` from the standard start configuration, run to the stopped configuration -/
theorem mc_halt (gS : List Bool → List Bool) (gT : ℕ → ℕ) (decI : Bool → T.Γ T.k₁)
    (hdec : ∀ b, dec (decI b) = b)
    (hrun : ∀ w : List Bool, TM2OutputsInTime T (w.map enc) (some ((gS w).map decI)) (gT w.length))
    (n : ℕ) (x : Fin n → Bool) (coins : List Bool) (hco : p.eval n ≤ coins.length)
    (ctl : List (Option Bool) → Option (CliffordOp n))
    (hctl : ∀ h, gS ((QAlgorithms.Complexity.encNat n ++ encBits (coins.take (p.eval n))) ++
      h.flatMap hcode ++ [false]) = encOp (ctl h))
    (k : ℕ) (hk : k ≤ (coins.drop (p.eval n)).length)
    (hstop : ctl (kloop ctl k
      ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
        (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) [] (coins.drop (p.eval n))).2.1 = none) :
    ∃ t ≤ setupT p n + (n * (6 * n + 12) + 1) +
          kTime ctl (QAlgorithms.Complexity.encNat n ++ encBits (coins.take (p.eval n))).length gT k
            ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
              (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) [] (coins.drop (p.eval n)),
      ∃ cf : TM2.Cfg (BΓ (Fin 16) T.Γ) (Lb T.Λ (hcoeffs p).length) (Reg × MS (εc T)),
        (flip bind (TM2.step (Mc T p enc dec)))^[t + 1]
          (some ⟨some (Lb.su 0), ((none, none, false), r0 T),
            Function.update (fun k => ([] : List (BΓ (Fin 16) T.Γ k))) (Sum.inl 14)
              ((encInput n x ++ encBits coins).map (Equiv.refl Bool).symm)⟩) = some cf ∧
        cf.l = none ∧
        cf.stk (Sum.inl 10) = (encodeTableau (kloop ctl k
          ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
            (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) []
              (coins.drop (p.eval n))).1.1).map (Equiv.refl Bool).symm := by
  obtain ⟨B', r', hR, h10⟩ := mc_full T p enc dec gS gT decI hdec hrun n x coins hco ctl hctl k hk
    hstop (r0 T) (ivc_r0 T) false
  obtain ⟨t', ht', e⟩ := reach_halt_step T p enc dec hR
  refine ⟨t', ht', ⟨none, ((none, none, false), r'), mk B' (fun _ => [])⟩, ?_, rfl, ?_⟩
  · rw [← init_stk T (encInput n x ++ encBits coins)]
    exact e
  · show B' 10 = _
    rw [h10]
    simp

end Fin2

section PB

lemma poly_mono' (p : Polynomial ℕ) : Monotone (fun m => p.eval m) := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

/-- `f` is bounded by a polynomial -/
def PB (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

lemma PB.const (a : ℕ) : PB (fun _ => a) := ⟨Polynomial.C a, fun n => by simp⟩

lemma PB.id : PB (fun n => n) := ⟨Polynomial.X, fun n => by simp⟩

lemma PB.poly (p : Polynomial ℕ) : PB (fun n => p.eval n) := ⟨p, fun _ => le_rfl⟩

lemma PB.add {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun n => by rw [Polynomial.eval_add]; exact Nat.add_le_add (hp n) (hq n)⟩

lemma PB.mul {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun n => by rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hp n) (hq n)⟩

lemma PB.pow {f : ℕ → ℕ} (hf : PB f) (k : ℕ) : PB (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using PB.const 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

lemma PB.comp {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB (fun n => f (g n)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p.comp q, fun n => by
    rw [Polynomial.eval_comp]; exact (hp (g n)).trans (poly_mono' p (hq n))⟩

lemma PB.mono {f g : ℕ → ℕ} (hg : PB g) (h : ∀ n, f n ≤ g n) : PB f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩

lemma poly_le_pow' (p : Polynomial ℕ) : ∃ c d : ℕ, ∀ m, p.eval m ≤ (m + c) ^ d := by
  refine ⟨(∑ i ∈ p.support, p.coeff i) + 1, p.natDegree + 1, fun m => ?_⟩
  have hS : ∀ i ∈ p.support, p.coeff i * m ^ i ≤ p.coeff i * (m + 1) ^ p.natDegree :=
    fun i hi => Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ m) i).trans
      (Nat.pow_le_pow_right (Nat.succ_pos m) (Polynomial.le_natDegree_of_mem_supp i hi)))
  calc p.eval m = ∑ i ∈ p.support, p.coeff i * m ^ i := by
        rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ ≤ ∑ i ∈ p.support, p.coeff i * (m + 1) ^ p.natDegree := Finset.sum_le_sum hS
    _ = (∑ i ∈ p.support, p.coeff i) * (m + 1) ^ p.natDegree := by rw [Finset.sum_mul]
    _ ≤ (m + ((∑ i ∈ p.support, p.coeff i) + 1)) *
          (m + ((∑ i ∈ p.support, p.coeff i) + 1)) ^ p.natDegree :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [pow_succ']

/-- a polynomially bounded step count, measured against any `m ≥ n`, fits `(m + c) ^ d` -/
lemma PB.pow_bound {f : ℕ → ℕ} (hf : PB f) : ∃ c d : ℕ, ∀ n m, n ≤ m → f n ≤ (m + c) ^ d := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨c, d, h⟩ := poly_le_pow' p
  exact ⟨c, d, fun n m hnm => (hp n).trans ((h n).trans (Nat.pow_le_pow_left (by omega) d))⟩

/-- the whole controller loop bound of `kTime_bound` is polynomial in `n` once the transcript prefix
length `pl`, the fuel `k` and the controller time `gT` are -/
lemma loop_pb (pl kf gT : ℕ → ℕ) (hpl : PB pl) (hk : PB kf) (hg : PB gT) :
    PB (fun n => (kf n + 1) * ((2 * (pl n + 3 * kf n) + 3 + gT (pl n + 3 * kf n + 1) +
      3 * (3 * n + 11)) + 200 * (n + 1) ^ 2)) := by
  have hA : PB (fun n => pl n + 3 * kf n) := hpl.add ((PB.const 3).mul hk)
  have hA1 : PB (fun n => pl n + 3 * kf n + 1) := hA.add (PB.const 1)
  refine (hk.add (PB.const 1)).mul (((((PB.const 2).mul hA).add (PB.const 3)).add
    (hg.comp hA1)).add ((PB.const 3).mul (((PB.const 3).mul PB.id).add (PB.const 11))) |>.add
    ((PB.const 200).mul ((PB.id.add (PB.const 1)).pow 2)))

/-- the initial-tableau loop `n * (6 n + 12) + 1` -/
lemma init_pb : PB (fun n => n * (6 * n + 12) + 1) :=
  (PB.id.mul (((PB.const 6).mul PB.id).add (PB.const 12))).add (PB.const 1)

/-- the setup time of `setup_run`, given the Horner budget `ht` -/
lemma setup_pb (p : Polynomial ℕ) (S : ℕ) (ht : ℕ → ℕ)
    (hht : ∀ n, ht n ≤ (p.natDegree + 1) * (S * (n + 1) ^ (p.natDegree + 1) * (3 * n + 4) + 4)) :
    PB (fun n => (n + 1) + ((n + 1) + ((n + 1) + ((2 * n + 1) + (1 + (ht n +
          ((3 * p.eval n + 1) + 1))))))) := by
  have h1 : PB (fun n => n + 1) := PB.id.add (PB.const 1)
  have hH : PB ht := PB.mono ((PB.const (p.natDegree + 1)).mul
    ((((PB.const S).mul (h1.pow (p.natDegree + 1))).mul
      (((PB.const 3).mul PB.id).add (PB.const 4))).add (PB.const 4))) hht
  exact h1.add (h1.add (h1.add ((((PB.const 2).mul PB.id).add (PB.const 1)).add
    ((PB.const 1).add (hH.add ((((PB.const 3).mul (PB.poly p)).add (PB.const 1)).add
      (PB.const 1)))))))

end PB


section Inst

open Turing QAlgorithms.Stabilizer QAlgorithms.Complexity

set_option autoImplicit false

/-- the controller machine of `MCCFamily.polytime`, in the shape `mc_halt` consumes -/
theorem ctrl_inst (F : MCCFamily) : ∃ (T : FinTM2) (enc : Bool → T.Γ T.k₀) (dec : T.Γ T.k₁ → Bool)
    (decI : Bool → T.Γ T.k₁) (gS : List Bool → List Bool) (P : Polynomial ℕ),
    (∀ b, dec (decI b) = b) ∧
    (∀ w : List Bool, Nonempty (TM2OutputsInTime T (w.map enc) (some ((gS w).map decI)) (P.eval w.length))) ∧
    (∀ n r hist, gS (encCtrlInput n r hist) = encOp (F.ctrl n r hist)) := by
  obtain ⟨g, ⟨H⟩, hg⟩ := F.polytime
  exact ⟨H.tm, H.inputAlphabet.invFun, H.outputAlphabet, H.outputAlphabet.invFun, g, H.time,
    fun b => H.outputAlphabet.right_inv b, fun w => ⟨H.outputsFun w⟩, hg⟩

end Inst

end OCRS19TM


namespace OCRS19TM
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity
set_option autoImplicit false

lemma sympB_eq' (a b : Pauli) : sympB a b = decide (a ≠ .I ∧ b ≠ .I ∧ a ≠ b) := by
  cases a <;> cases b <;> decide

/-- the K-side loop is the iterate of one controller step, for any step function agreeing with `stepK` -/
lemma kloop_iter {n : ℕ} (ctl : List (Option Bool) → Option (CliffordOp n))
    (st : CliffordOp n → Tableau n × Tableau n → Bool → (Tableau n × Tableau n) × Option Bool)
    (hst : ∀ o T D b, stepK o T D b = st o (T, D) b) :
    ∀ (k : ℕ) (TD : Tableau n × Tableau n) (h : List (Option Bool)) (cs : List Bool),
      kloop ctl k TD h cs =
        (fun s : (Tableau n × Tableau n) × List (Option Bool) × List Bool =>
          match ctl s.2.1 with
          | none => s
          | some o => ((st o s.1 (s.2.2.headD false)).1, s.2.1 ++ [(st o s.1 (s.2.2.headD false)).2],
              match o with
              | .measure _ => s.2.2.tail
              | _ => s.2.2))^[k] (TD, h, cs)
  | 0, TD, h, cs => rfl
  | k + 1, TD, h, cs => by
    rw [Function.iterate_succ_apply]
    cases hc : ctl h with
    | none =>
      simp only [kloop, hc]
      exact (Function.iterate_fixed (by simp only [hc]) k).symm
    | some o =>
      simp only [kloop, hc]
      rw [kloop_iter ctl st hst k, hst]
      cases o <;> rfl

lemma encBits_len (l : List Bool) : (encBits l).length = 2 * l.length + 2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encBits, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

end OCRS19TM

set_option maxHeartbeats 4000000 in
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity OCRS19TM in
theorem solution (F : MCCFamily) :
    let chpUpd : (n : ℕ) → CliffordOp n → Tableau n × Tableau n → Bool →
        (Tableau n × Tableau n) × Option Bool := fun n =>
      let px : Pauli → Bool := fun | .I => false | .X => true | .Y => true | .Z => false
      let pz : Pauli → Bool := fun | .I => false | .X => false | .Y => true | .Z => true
      let conjH : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Z) | .Y => (2, .Y) | .Z => (0, .X)
      let conjS : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Y) | .Y => (2, .X) | .Z => (0, .Z)
      let conjP : Pauli → Pauli → ZMod 4 × Pauli := fun P Q => (if P = .I ∨ Q = .I ∨ P = Q then 0 else 2, Q)
      let conjPS : (Pauli → ZMod 4 × Pauli) → Fin n → PauliString n → PauliString n := fun f q P =>
        ⟨P.phase + (f (P.ops q)).1, Function.update P.ops q (f (P.ops q)).2⟩
      let cnotTab : Pauli → Pauli → ZMod 4 × Pauli × Pauli := fun Pc Pt =>
        (if px Pc && pz Pt && (px Pt == pz Pc) then 2 else 0,
          pauliOfBits (px Pc) (xor (pz Pc) (pz Pt)), pauliOfBits (xor (px Pt) (px Pc)) (pz Pt))
      let cnotPS : Fin n → Fin n → PauliString n → PauliString n := fun c t P =>
        ⟨P.phase + (cnotTab (P.ops c) (P.ops t)).1,
          Function.update (Function.update P.ops c (cnotTab (P.ops c) (P.ops t)).2.1) t
            (cnotTab (P.ops c) (P.ops t)).2.2⟩
      let updG : CliffordOp n → Tableau n → Tableau n := fun op T =>
        match op with
        | .pauli q P => fun j => conjPS (conjP P) q (T j)
        | .h q => fun j => conjPS conjH q (T j)
        | .s q => fun j => conjPS conjS q (T j)
        | .cnot c t _ => fun j => cnotPS c t (T j)
        | .measure _ => T
      let antiPair : Pauli → Pauli → Bool := fun a b => decide (a ≠ .I ∧ b ≠ .I ∧ a ≠ b)
      let antiB : PauliString n → PauliString n → Bool := fun P Q =>
        decide (Odd (Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card)
      let oneP : PauliString n := ⟨0, fun _ => .I⟩
      let prodSel : (Fin n → PauliString n) → Finset (Fin n) → PauliString n := fun T s =>
        (List.ofFn fun i => if i ∈ s then T i else oneP).foldr PauliString.mul oneP
      let firstAnti : Tableau n → (Fin n → Pauli) → Option (Fin n) := fun T M =>
        (List.finRange n).reverse.find? (fun j => antiB (T j) ⟨0, M⟩)
      let detSel : Tableau n → (Fin n → Pauli) → Finset (Fin n) := fun D M =>
        Finset.univ.filter fun j => antiB (D j) ⟨0, M⟩ = true
      let updM : Tableau n → (Fin n → Pauli) → Fin n → Bool → Tableau n := fun T M p b =>
        fun j => if j = p then ⟨if b then 2 else 0, M⟩
          else if antiB (T j) ⟨0, M⟩ then (T j).mul (T p) else T j
      let updDM : Tableau n → Tableau n → (Fin n → Pauli) → Fin n → Tableau n := fun T D M p =>
        fun i => if i = p then T p else if antiB (D i) ⟨0, M⟩ then (D i).mul (T p) else D i
      fun op TD b =>
        match op with
        | .measure M =>
          match firstAnti TD.1 M with
          | some p => ((updM TD.1 M p b, updDM TD.1 TD.2 M p), some b)
          | none => (TD, some (decide ((prodSel TD.1 (detSel TD.2 M)).phase = 2)))
        | _ => ((updG op TD.1, updG op TD.2), none)
    let simLoop : (n : ℕ) → Tableau n × Tableau n → List Bool →
        (Tableau n × Tableau n) × List (Option Bool) × List Bool := fun n s0 bits =>
      (fun st : (Tableau n × Tableau n) × List (Option Bool) × List Bool =>
        match F.ctrl n (bits.take (F.rbits.eval n)) st.2.1 with
        | none => st
        | some o => ((chpUpd n o st.1 (st.2.2.headD false)).1,
            st.2.1 ++ [(chpUpd n o st.1 (st.2.2.headD false)).2],
            match o with
            | .measure _ => st.2.2.tail
            | _ => st.2.2))^[F.steps.eval n] (s0, [], bits.drop (F.rbits.eval n))
    ∃ R : Polynomial ℕ, (∀ (n : ℕ) (x : Qubits n),
        F.rbits.eval n + F.steps.eval n ≤ R.eval (encInput n x).length) ∧
      ∃ (K : Type) (_ : DecidableEq K) (_ : Fintype K) (Γ : K → Type) (k0 k1 : K) (_ : Inhabited (Γ k0))
        (Λ σ : Type) (_ : Fintype Λ) (_ : Fintype σ) (_ : Fintype (Γ k0)) (M : Λ → Turing.TM2.Stmt Γ Λ σ)
        (main : Λ) (c d : ℕ) (s0 : σ) (e0 : Γ k0 ≃ Bool) (e1 : Γ k1 ≃ Bool),
        ∀ (n : ℕ) (x : Qubits n) (bits : List Bool), bits.length = R.eval (encInput n x).length →
          ∃ t ≤ ((encInput n x ++ encBits bits).length + c) ^ d, ∃ cf : Turing.TM2.Cfg Γ Λ σ,
            (flip bind (Turing.TM2.step M))^[t + 1]
              (some ⟨some main, s0, Function.update (fun k => ([] : List (Γ k))) k0
                ((encInput n x ++ encBits bits).map e0.symm)⟩) = some cf ∧ cf.l = none ∧
            cf.stk k1 = (encodeTableau (simLoop n
                ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
                  (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) bits).1.1).map e1.symm := by
  intro chpUpd simLoop
  have hsim : ∀ (n : ℕ) (bits : List Bool) (TD : Tableau n × Tableau n),
      kloop (F.ctrl n (bits.take (F.rbits.eval n))) (F.steps.eval n) TD [] (bits.drop (F.rbits.eval n)) =
        simLoop n TD bits := by
    intro n bits TD
    have hstep : ∀ (o : CliffordOp n) (T D : Tableau n) (b : Bool), stepK o T D b = chpUpd n o (T, D) b := by
      intro o T D b
      cases o with
      | measure M =>
        simp only [chpUpd, stepK, measK, lastK, detCp, antiK, sympB_eq', oneK]
        rcases hf : List.find? (fun j => decide (Odd (Finset.univ.filter fun x =>
            decide ((T j).ops x ≠ Pauli.I ∧ M x ≠ Pauli.I ∧ (T j).ops x ≠ M x) = true).card))
            (List.finRange n).reverse with _ | p
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        · unfold updMK updDMK antiK
          simp only [sympB_eq']
      | pauli q P => rfl
      | h q => rfl
      | s q => rfl
      | cnot c t hct => rfl
    exact kloop_iter _ (chpUpd n) hstep _ _ _ _
  obtain ⟨T, enc, dec, decI, gS, P, hdec, hrun, hg⟩ := ctrl_inst F
  have hlen : ∀ (n : ℕ) (x : Qubits n), n ≤ (encInput n x).length := by
    intro n x
    simp only [encInput, QAlgorithms.Complexity.encNat, List.length_append, List.length_replicate,
      List.length_singleton, List.length_ofFn]
    omega
  have hR : ∀ (n : ℕ) (x : Qubits n), F.rbits.eval n + F.steps.eval n ≤
      (F.rbits + F.steps).eval (encInput n x).length := by
    intro n x
    rw [Polynomial.eval_add]
    exact Nat.add_le_add (poly_mono' _ (hlen n x)) (poly_mono' _ (hlen n x))
  have hplB : PB (fun n => (n + 1) + (2 * F.rbits.eval n + 2)) :=
    (PB.id.add (PB.const 1)).add (((PB.const 2).mul (PB.poly F.rbits)).add (PB.const 2))
  have hf : PB (fun n => setupT F.rbits n + (n * (6 * n + 12) + 1) +
      (F.steps.eval n + 1) * ((2 * (((n + 1) + (2 * F.rbits.eval n + 2)) + 3 * F.steps.eval n) + 3 +
        P.eval (((n + 1) + (2 * F.rbits.eval n + 2)) + 3 * F.steps.eval n + 1) +
        3 * (3 * n + 11)) + 200 * (n + 1) ^ 2)) :=
    ((setup_pb F.rbits (hcoeffs F.rbits).sum (fun n => HT n 0 (hcoeffs F.rbits))
      (HT_hcoeffs_le F.rbits)).add init_pb).add
      (loop_pb _ (fun n => F.steps.eval n) (fun n => P.eval n) hplB (PB.poly _) (PB.poly P))
  obtain ⟨c, d, hcd⟩ := PB.pow_bound hf
  set_option linter.style.haveILetI false in
  letI := pauliFintype
  letI : Fintype T.σ := T.σFin
  letI : Fintype T.Λ := T.ΛFin
  letI : DecidableEq T.K := T.kDecidableEq
  letI : Fintype T.K := T.kFin
  letI : Fintype (MS (εc T)) := msFintype (εc T)
  refine ⟨F.rbits + F.steps, hR, Fin 16 ⊕ T.K, inferInstance, inferInstance, BΓ (Fin 16) T.Γ,
    Sum.inl 14, Sum.inl 10, (⟨false⟩ : Inhabited Bool), Lb T.Λ (hcoeffs F.rbits).length,
    Reg × MS (εc T), inferInstance, inferInstance, (inferInstance : Fintype Bool),
    Mc T F.rbits enc dec, Lb.su 0, c, d, ((none, none, false), r0 T), Equiv.refl Bool, Equiv.refl Bool, ?_⟩
  intro n x bits hb
  have hb' : F.rbits.eval n + F.steps.eval n ≤ bits.length := hb ▸ hR n x
  have hco : F.rbits.eval n ≤ bits.length := by omega
  have hk : F.steps.eval n ≤ (bits.drop (F.rbits.eval n)).length := by
    rw [List.length_drop]; omega
  obtain ⟨t, ht, cf, h1, h2, h3⟩ := mc_halt T F.rbits enc dec gS (fun m => P.eval m) decI hdec
    (fun w => (hrun w).some) n x bits hco (F.ctrl n (bits.take (F.rbits.eval n)))
    (ctrl_hctl F gS hg n _) (F.steps.eval n) hk (kloop_halts F n _ _ _)
  refine ⟨t, ?_, cf, h1, h2, ?_⟩
  · refine ht.trans (le_trans ?_ (hcd n _ (by
      simp only [List.length_append]; have := hlen n x; omega)))
    refine Nat.add_le_add_left ((kTime_bound _ _ _ (poly_mono' P) _ _ _).trans ?_) _
    have hpl : (QAlgorithms.Complexity.encNat n ++ encBits (bits.take (F.rbits.eval n))).length ≤
        (n + 1) + (2 * F.rbits.eval n + 2) := by
      simp only [List.length_append, QAlgorithms.Complexity.encNat, List.length_replicate,
        List.length_singleton, encBits_len, List.length_take]
      omega
    have hP := poly_mono' P (show (QAlgorithms.Complexity.encNat n ++
      encBits (bits.take (F.rbits.eval n))).length + 3 * F.steps.eval n + 1 ≤
        ((n + 1) + (2 * F.rbits.eval n + 2)) + 3 * F.steps.eval n + 1 by omega)
    simp only at hP ⊢
    exact Nat.mul_le_mul_left _ (by linarith)
  · rw [← hsim]
    exact h3
