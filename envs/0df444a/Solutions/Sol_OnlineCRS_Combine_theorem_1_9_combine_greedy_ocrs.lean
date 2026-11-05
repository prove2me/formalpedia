-- Prove2me | solution 1 for OnlineCRS.Combine.theorem_1_9_combine_greedy_ocrs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T21:20:52.66563+00:00
-- url     : https://prove2.me/submissions/33ca7ed3-cacd-45a6-afd0-c612eef828f4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_DownClosed
import Definitions.Def_OnlineCRS_Combine_IsRelaxation
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS
import Definitions.Def_OnlineCRS_Combine_IsSelectable
import Definitions.Def_OnlineCRS_Combine_IsEfficient
import Definitions.Def_OnlineCRS_Combine_encQuery
import Definitions.Def_OnlineCRS_Combine_encSampler

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false


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
    cases x <;> cases c <;> simp at ih ⊢ <;> nlinarith
  | case3 c y b ih =>
    simp only [subL, subB, val_cons, List.length_cons, pow_succ] at ih ⊢
    cases y <;> cases c <;> simp at ih ⊢ <;> nlinarith
  | case4 c x a y b ih =>
    simp only [subL, subB, val_cons, List.length_cons, pow_succ] at ih ⊢
    cases x <;> cases y <;> cases c <;> simp at ih ⊢ <;> nlinarith

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

end OCRS19TM


/-! L7: concrete work stacks `W` and the multiplication loop (shift-and-add). -/

namespace OCRS19TM

open Turing

/-- the multiplication loop, LSB-first multiplier -/
def mulLoop : List Bool → List Bool → List Bool → List Bool × List Bool
  | acc, X, [] => (acc, X)
  | acc, X, y :: Y => mulLoop (if y then addL false acc X else acc) (false :: X) Y

lemma val_mulLoop (acc X Y : List Bool) :
    val (mulLoop acc X Y).1 = val acc + val X * val Y := by
  induction Y generalizing acc X with
  | nil => simp [mulLoop]
  | cons y Y ih =>
    rw [mulLoop, ih]
    cases y <;> simp [val_addL] <;> ring

/-- time bound of the multiplication loop (`s` bounds the accumulator and multiplicand lengths) -/
def mulT (s n : ℕ) : ℕ := (n + 1) * (6 * s + 12 * n + 10)

/-- work stacks -/
inductive W
  | out | acc | x | y | x1 | x2 | x3 | t | u | v
  deriving DecidableEq

section Mul

variable {R : Type} [DecidableEq R] {G : R → Type} {Λ ρ : Type}
variable (M : Λ → TM2.Stmt (BΓ W G) Λ (Reg × ρ))

/-- loop head: pop a multiplier bit -/
def mulStmt (EXIT DUP SHIFT : Λ) : TM2.Stmt (BΓ W G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl W.y) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => EXIT)
      (TM2.Stmt.branch (fun v => v.1.1.getD false)
        (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => DUP))
        (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => SHIFT))))

/-- double the multiplicand -/
def shiftStmt (MUL : Λ) : TM2.Stmt (BΓ W G) Λ (Reg × ρ) :=
  TM2.Stmt.push (Sum.inl W.x) (fun _ => false) (TM2.Stmt.goto fun _ => MUL)

/-- the program of the multiplication loop -/
structure MulProg (MUL DUP R1 R2 ADD R3 SHIFT EXIT : Λ) : Prop where
  hMUL : M MUL = mulStmt EXIT DUP SHIFT
  hDUP : M DUP = dupStmt W.x W.x1 W.x2 DUP R1
  hR1 : M R1 = mvStmt W.x1 W.x R1 R2
  hR2 : M R2 = mvStmt W.x2 W.x3 R2 ADD
  hADD : M ADD = addStmt W.acc W.x3 W.t ADD R3
  hR3 : M R3 = mvStmt W.t W.acc R3 SHIFT
  hSHIFT : M SHIFT = shiftStmt MUL

variable {M}
variable {MUL DUP R1 R2 ADD R3 SHIFT EXIT : Λ} (P : MulProg M MUL DUP R1 R2 ADD R3 SHIFT EXIT)
  (r : ρ) (Q : ∀ r, List (G r))
include P

lemma mul_head_some (B : W → List Bool) (b : Bool) (Ys : List Bool) (h : B W.y = b :: Ys) :
    TM2.step M ⟨some MUL, ((none, none, false), r), mk B Q⟩ =
      some ⟨some (if b then DUP else SHIFT), ((none, none, false), r),
        mk (Function.update B W.y Ys) Q⟩ := by
  simp only [TM2.step, P.hMUL, mulStmt, TM2.stepAux, mk_inl, h, List.head?_cons, List.tail_cons,
    Option.isNone_some, cond_false, Option.getD_some, update_mk]
  cases b <;> rfl

lemma mul_head_nil (B : W → List Bool) (h : B W.y = []) :
    TM2.step M ⟨some MUL, ((none, none, false), r), mk B Q⟩ =
      some ⟨some EXIT, ((none, none, false), r), mk B Q⟩ := by
  simp only [TM2.step, P.hMUL, mulStmt, TM2.stepAux, mk_inl, h, List.head?_nil, List.tail_nil,
    Option.isNone_none, cond_true, update_mk]
  rw [(Function.update_eq_self_iff).mpr h.symm]

lemma shift_step (B : W → List Bool) :
    TM2.step M ⟨some SHIFT, ((none, none, false), r), mk B Q⟩ =
      some ⟨some MUL, ((none, none, false), r), mk (Function.update B W.x (false :: B W.x)) Q⟩ := by
  simp only [TM2.step, P.hSHIFT, shiftStmt, TM2.stepAux, mk_inl, update_mk]

set_option maxHeartbeats 1000000 in
lemma mul_loop :
    ∀ (Ys : List Bool) (B : W → List Bool) (s : ℕ), B W.y = Ys → B W.x1 = [] → B W.x2 = [] →
      B W.x3 = [] → B W.t = [] → (B W.acc).length ≤ s → (B W.x).length ≤ s →
      Reach M ⟨some MUL, ((none, none, false), r), mk B Q⟩
        ⟨some EXIT, ((none, none, false), r), mk (Function.update (Function.update
          (Function.update B W.y []) W.acc (mulLoop (B W.acc) (B W.x) Ys).1) W.x
          (mulLoop (B W.acc) (B W.x) Ys).2) Q⟩ (mulT s Ys.length) := by
  intro Ys
  induction Ys with
  | nil =>
    intro B s hy _ _ _ _ _ _
    refine ((Reach.single (mul_head_nil P r Q B hy)).of_eq ?_).mono (by simp [mulT])
    congr 2
    funext k; cases k <;> simp [mulLoop, hy]
  | cons b Ys ih =>
    intro B s hy hx1 hx2 hx3 ht ha hx
    cases b with
    | true =>
      have r0 := Reach.single (mul_head_some P r Q B true Ys hy)
      simp only [if_true] at r0
      have r1 := r0.trans (dup_run M W.x W.x1 W.x2 (by decide) (by decide) (by decide) DUP R1 P.hDUP
        r false Q (B W.x) _ (by simp [Function.update_apply]))
      have r2 := r1.trans (mv_run M W.x1 W.x (by decide) R1 R2 P.hR1 r false Q ((B W.x).reverse) _
        (by simp [Function.update_apply, hx1]))
      have r3 := r2.trans (mv_run M W.x2 W.x3 (by decide) R2 ADD P.hR2 r false Q ((B W.x).reverse) _
        (by simp [Function.update_apply, hx2]))
      have r4 := r3.trans (add_mk M W.acc W.x3 W.t (by decide) (by decide) (by decide) ADD R3 P.hADD
        r false _ Q)
      have r5 := r4.trans (mv_run M W.t W.acc (by decide) R3 SHIFT P.hR3 r false Q
        ((addL false (B W.acc) (B W.x)).reverse) _ (by simp [Function.update_apply, hx3, ht]))
      have r6 := r5.trans (Reach.single (shift_step P r Q _))
      have hl := length_addL false (B W.acc) (B W.x)
      have r7 := r6.trans (ih _ (s + 1) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
        (by simp [Function.update_apply]; omega) (by simp [Function.update_apply]; omega))
      refine (r7.of_eq ?_).mono ?_
      · congr 2
        funext k; cases k <;> simp [mulLoop, hy, hx1, hx2, hx3, ht]
      · have hm := max_le ha hx
        simp [hx3, hl, mulT]
        nlinarith
    | false =>
      have r0 := Reach.single (mul_head_some P r Q B false Ys hy)
      simp only [Bool.false_eq_true, if_false] at r0
      have r6 := r0.trans (Reach.single (shift_step P r Q _))
      have r7 := r6.trans (ih _ (s + 1) (by simp [Function.update_apply])
        (by simp [Function.update_apply, hx1]) (by simp [Function.update_apply, hx2])
        (by simp [Function.update_apply, hx3]) (by simp [Function.update_apply, ht])
        (by simp [Function.update_apply]; omega) (by simp [Function.update_apply]; omega))
      refine (r7.of_eq ?_).mono ?_
      · congr 2
        funext k; cases k <;> simp [mulLoop, hy, hx1, hx2, hx3, ht]
      · simp [mulT]
        nlinarith

end Mul

end OCRS19TM


/-! L8: long division (pure semantics; machine loop next). Dividend bits MSB first. -/

namespace OCRS19TM

/-- MSB-first value, continuing from `n` -/
def valM : ℕ → List Bool → ℕ
  | n, [] => n
  | n, z :: Z => valM (2 * n + z.toNat) Z

lemma valM_eq (n : ℕ) (Z : List Bool) : valM n Z = n * 2 ^ Z.length + valM 0 Z := by
  induction Z generalizing n with
  | nil => simp [valM]
  | cons z Z ih =>
    rw [valM, valM, ih, ih (2 * 0 + z.toNat)]
    simp [pow_succ]; ring

/-- the long-division loop: remainder, quotient (LSB-first, new bits pushed on top) -/
def divLoop (D : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | rem, u, [] => (rem, u)
  | rem, u, z :: Z =>
      if subB false (z :: rem) D then divLoop D (z :: rem) (false :: u) Z
      else divLoop D (subL false (z :: rem) D) (true :: u) Z

lemma divLoop_spec (D : List Bool) (hd : 0 < val D) :
    ∀ (Z rem u : List Bool), val rem < val D →
      val D * val (divLoop D rem u Z).2 + val (divLoop D rem u Z).1 =
          valM (val D * val u + val rem) Z ∧
        val (divLoop D rem u Z).1 < val D := by
  intro Z
  induction Z with
  | nil => intro rem u h; simp [divLoop, valM, h]
  | cons z Z ih =>
    intro rem u h
    rw [divLoop]
    by_cases hb : subB false (z :: rem) D = true
    · rw [if_pos hb]
      have hlt : val (z :: rem) < val D := by
        by_contra hc
        have := (subB_false_iff (z :: rem) D).mpr (not_lt.mp hc)
        rw [this] at hb; exact Bool.false_ne_true hb
      obtain ⟨h1, h2⟩ := ih (z :: rem) (false :: u) hlt
      refine ⟨?_, h2⟩
      rw [h1, valM]
      congr 1
      simp; ring
    · rw [if_neg hb]
      have hb' : subB false (z :: rem) D = false := by simpa using hb
      have hle := (subB_false_iff (z :: rem) D).mp hb'
      have hv := val_subL (z :: rem) D hle
      have hlt : val (subL false (z :: rem) D) < val D := by
        rw [hv]
        cases z <;> simp only [val_cons, Bool.toNat_false, Bool.toNat_true] at hle ⊢ <;> omega
      obtain ⟨h1, h2⟩ := ih _ (true :: u) hlt
      refine ⟨?_, h2⟩
      rw [h1, valM, hv]
      congr 1
      have e : val D * val (true :: u) = val D + 2 * (val D * val u) := by simp; ring
      rw [e]
      cases z <;> simp only [val_cons, Bool.toNat_false, Bool.toNat_true] at hle ⊢ <;> omega

/-- division of an MSB-first bit list by `val D` -/
lemma divLoop_divmod (D Z : List Bool) (hd : 0 < val D) :
    val (divLoop D [] [] Z).2 = valM 0 Z / val D ∧
      val (divLoop D [] [] Z).1 = valM 0 Z % val D := by
  obtain ⟨h1, h2⟩ := divLoop_spec D hd Z [] [] (by simpa using hd)
  simp only [val_nil, mul_zero, add_zero] at h1
  constructor
  · rw [← h1, Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h2, zero_add]
  · rw [← h1, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

lemma valM_snoc (n : ℕ) (L : List Bool) (b : Bool) :
    valM n (L ++ [b]) = 2 * valM n L + b.toNat := by
  induction L generalizing n with
  | nil => simp [valM]
  | cons z L ih => simp [valM, ih]

/-- MSB-first reading of a reversed LSB-first list -/
lemma valM_reverse (l : List Bool) : valM 0 l.reverse = val l := by
  have key : ∀ (l : List Bool) (n : ℕ), valM n l.reverse = n * 2 ^ l.length + val l := by
    intro l
    induction l with
    | nil => intro n; simp [valM]
    | cons b l ih =>
      intro n
      rw [List.reverse_cons, valM_snoc, ih]
      simp [pow_succ]
      ring
  simpa using key l 0

/-- lengths in the division loop -/
lemma divLoop_len (D : List Bool) :
    ∀ (Z rem u : List Bool), (divLoop D rem u Z).1.length ≤ max rem.length D.length + Z.length ∧
      (divLoop D rem u Z).2.length = u.length + Z.length := by
  intro Z
  induction Z with
  | nil => intro rem u; simp [divLoop]
  | cons z Z ih =>
    intro rem u
    rw [divLoop]
    split_ifs
    · obtain ⟨h1, h2⟩ := ih (z :: rem) (false :: u)
      simp at h1 h2 ⊢; omega
    · obtain ⟨h1, h2⟩ := ih (subL false (z :: rem) D) (true :: u)
      rw [length_subL] at h1
      simp at h1 h2 ⊢; omega

end OCRS19TM


/-! L9: the long-division loop machine (semantics `divLoop` of L8). Uses W (L7), mk/mv/dup/sub/clear (L6). -/

namespace OCRS19TM

open Turing

/-- time bound of the division loop -/
def divT (s n : ℕ) : ℕ := (n + 1) * (10 * s + 10 * n + 40)

section Div

variable {R : Type} [DecidableEq R] {G : R → Type} {Λ ρ : Type}
variable (M : Λ → TM2.Stmt (BΓ W G) Λ (Reg × ρ))

/-- loop head: pop the next dividend bit (MSB first) and push it on the remainder -/
def divStmt (EXIT D1 : Λ) : TM2.Stmt (BΓ W G) Λ (Reg × ρ) :=
  TM2.Stmt.pop (Sum.inl W.y) (fun v x => ((x, v.1.2.1, v.1.2.2), v.2))
    (TM2.Stmt.branch (fun v => v.1.1.isNone)
      (TM2.Stmt.goto fun _ => EXIT)
      (TM2.Stmt.push (Sum.inl W.acc) (fun v => v.1.1.getD false)
        (TM2.Stmt.load (fun v => ((none, v.1.2.1, v.1.2.2), v.2)) (TM2.Stmt.goto fun _ => D1))))

/-- decide on the borrow: push the quotient bit and reset the flag -/
def decStmt (CT CA : Λ) : TM2.Stmt (BΓ W G) Λ (Reg × ρ) :=
  TM2.Stmt.branch (fun v => v.1.2.2)
    (TM2.Stmt.push (Sum.inl W.u) (fun _ => false)
      (TM2.Stmt.load (fun v => ((none, none, false), v.2)) (TM2.Stmt.goto fun _ => CT)))
    (TM2.Stmt.push (Sum.inl W.u) (fun _ => true)
      (TM2.Stmt.load (fun v => ((none, none, false), v.2)) (TM2.Stmt.goto fun _ => CA)))

/-- the program of the division loop (divisor on `x`, remainder on `acc`, dividend MSB-first on `y`,
quotient pushed on `u`) -/
structure DivProg (DIV D1 D2 D3 D4 D5 D6 D7 D8 CT CA MVT EXIT : Λ) : Prop where
  hDIV : M DIV = divStmt EXIT D1
  hD1 : M D1 = dupStmt W.acc W.x1 W.x2 D1 D2
  hD2 : M D2 = mvStmt W.x1 W.acc D2 D3
  hD3 : M D3 = mvStmt W.x2 W.x3 D3 D4
  hD4 : M D4 = dupStmt W.x W.v W.x1 D4 D5
  hD5 : M D5 = mvStmt W.v W.x D5 D6
  hD6 : M D6 = mvStmt W.x1 W.x2 D6 D7
  hD7 : M D7 = subStmt W.x3 W.x2 W.t D7 D8
  hD8 : M D8 = decStmt CT CA
  hCT : M CT = clearStmt W.t CT DIV
  hCA : M CA = clearStmt W.acc CA MVT
  hMVT : M MVT = mvStmt W.t W.acc MVT DIV

variable {M}
variable {DIV D1 D2 D3 D4 D5 D6 D7 D8 CT CA MVT EXIT : Λ}
  (P : DivProg M DIV D1 D2 D3 D4 D5 D6 D7 D8 CT CA MVT EXIT) (r : ρ) (Q : ∀ r, List (G r))
include P

lemma div_head_some (B : W → List Bool) (b : Bool) (Ys : List Bool) (h : B W.y = b :: Ys) :
    TM2.step M ⟨some DIV, ((none, none, false), r), mk B Q⟩ =
      some ⟨some D1, ((none, none, false), r),
        mk (Function.update (Function.update B W.y Ys) W.acc (b :: B W.acc)) Q⟩ := by
  simp only [TM2.step, P.hDIV, divStmt, TM2.stepAux, mk_inl, h, List.head?_cons, List.tail_cons,
    Option.isNone_some, cond_false, Option.getD_some, update_mk,
    Function.update_of_ne (show W.acc ≠ W.y by decide)]

lemma div_head_nil (B : W → List Bool) (h : B W.y = []) :
    TM2.step M ⟨some DIV, ((none, none, false), r), mk B Q⟩ =
      some ⟨some EXIT, ((none, none, false), r), mk B Q⟩ := by
  simp only [TM2.step, P.hDIV, divStmt, TM2.stepAux, mk_inl, h, List.head?_nil, List.tail_nil,
    Option.isNone_none, cond_true, update_mk]
  rw [(Function.update_eq_self_iff).mpr h.symm]

lemma dec_step_t (B : W → List Bool) (c : Bool) (hc : c = true) :
    TM2.step M ⟨some D8, ((none, none, c), r), mk B Q⟩ =
      some ⟨some CT, ((none, none, false), r), mk (Function.update B W.u (false :: B W.u)) Q⟩ := by
  subst hc
  simp only [TM2.step, P.hD8, decStmt, TM2.stepAux, mk_inl, update_mk, cond_true]

lemma dec_step_f (B : W → List Bool) (c : Bool) (hc : c = false) :
    TM2.step M ⟨some D8, ((none, none, c), r), mk B Q⟩ =
      some ⟨some CA, ((none, none, false), r), mk (Function.update B W.u (true :: B W.u)) Q⟩ := by
  subst hc
  simp only [TM2.step, P.hD8, decStmt, TM2.stepAux, mk_inl, update_mk, cond_false]

set_option maxHeartbeats 2000000 in
lemma div_loop :
    ∀ (Ys : List Bool) (B : W → List Bool) (s : ℕ), B W.y = Ys → B W.x1 = [] → B W.x2 = [] →
      B W.x3 = [] → B W.t = [] → B W.v = [] → (B W.acc).length ≤ s → (B W.x).length ≤ s →
      Reach M ⟨some DIV, ((none, none, false), r), mk B Q⟩
        ⟨some EXIT, ((none, none, false), r), mk (Function.update (Function.update
          (Function.update B W.y []) W.acc (divLoop (B W.x) (B W.acc) (B W.u) Ys).1) W.u
          (divLoop (B W.x) (B W.acc) (B W.u) Ys).2) Q⟩ (divT s Ys.length) := by
  intro Ys
  induction Ys with
  | nil =>
    intro B s hy _ _ _ _ _ _ _
    refine ((Reach.single (div_head_nil P r Q B hy)).of_eq ?_).mono (by simp [divT])
    congr 2
    funext k; cases k <;> simp [divLoop, hy]
  | cons b Ys ih =>
    intro B s hy hx1 hx2 hx3 ht hv ha hx
    have r0 := Reach.single (div_head_some P r Q B b Ys hy)
    have r1 := r0.trans (dup_run M W.acc W.x1 W.x2 (by decide) (by decide) (by decide) D1 D2 P.hD1
      r false Q (b :: B W.acc) _ (by simp [Function.update_apply]))
    have r2 := r1.trans (mv_run M W.x1 W.acc (by decide) D2 D3 P.hD2 r false Q
      ((b :: B W.acc).reverse) _ (by simp [Function.update_apply, hx1]))
    have r3 := r2.trans (mv_run M W.x2 W.x3 (by decide) D3 D4 P.hD3 r false Q
      ((b :: B W.acc).reverse) _ (by simp [Function.update_apply, hx2]))
    have r4 := r3.trans (dup_run M W.x W.v W.x1 (by decide) (by decide) (by decide) D4 D5 P.hD4
      r false Q (B W.x) _ (by simp [Function.update_apply]))
    have r5 := r4.trans (mv_run M W.v W.x (by decide) D5 D6 P.hD5 r false Q
      ((B W.x).reverse) _ (by simp [Function.update_apply, hv]))
    have r6 := r5.trans (mv_run M W.x1 W.x2 (by decide) D6 D7 P.hD6 r false Q
      ((B W.x).reverse) _ (by simp [Function.update_apply]))
    have r7 := r6.trans (sub_mk M W.x3 W.x2 W.t (by decide) (by decide) (by decide) D7 D8 P.hD7
      r false _ Q)
    have hl := length_subL false (b :: B W.acc) (B W.x)
    have hmax : max ((B W.acc).length + 1) (B W.x).length ≤ s + 1 := max_le (by omega) (by omega)
    cases hc : subB false (b :: B W.acc) (B W.x) with
    | true =>
      have r8 := r7.trans (Reach.single (dec_step_t P r Q _ _
        (by simpa [Function.update_apply, hx1, hx2, hx3] using hc)))
      have r9 := r8.trans (clear_mk M W.t CT DIV P.hCT r false _ Q)
      have r10 := r9.trans (ih _ (s + 1) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
        (by simp [Function.update_apply, hv])
        (by simp [Function.update_apply]; omega) (by simp [Function.update_apply]; omega))
      refine (r10.of_eq ?_).mono ?_
      · congr 2
        funext k; cases k <;> simp [divLoop, hy, hc, hx1, hx2, hx3, ht, hv]
      · simp [hx1, hx2, hx3, ht, hv, hl, hc, divT, Function.update_apply]
        nlinarith
    | false =>
      have r8 := r7.trans (Reach.single (dec_step_f P r Q _ _
        (by simpa [Function.update_apply, hx1, hx2, hx3] using hc)))
      have r9 := r8.trans (clear_mk M W.acc CA MVT P.hCA r false _ Q)
      have r10 := r9.trans (mv_run M W.t W.acc (by decide) MVT DIV P.hMVT r false Q
        _ _ rfl)
      have r11 := r10.trans (ih _ (s + 1) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
        (by simp [Function.update_apply, hv])
        (by simp [Function.update_apply, hl, hx1, hx2, hx3, ht, hv]; omega) (by simp [Function.update_apply]; omega))
      refine (r11.of_eq ?_).mono ?_
      · congr 2
        funext k; cases k <;> simp [divLoop, hy, hc, hx1, hx2, hx3, ht, hv]
      · simp [hx1, hx2, hx3, ht, hv, hl, hc, divT, Function.update_apply]
        nlinarith

end Div

end OCRS19TM


/-! L10: the machine for `TMm`: from machines for `m₁`, `m₂` (same input encoding) a machine for
`(m₁ + 1) * (m₂ + 1) - 1 = a + b + a * b`. Definitions and the Bool phases. -/

namespace OCRS19TM

open Turing

scoped instance : Fintype W :=
  Fintype.ofList [W.out, W.acc, W.x, W.y, W.x1, W.x2, W.x3, W.t, W.u, W.v]
    (by intro x; cases x <;> simp)

lemma mulLoop_len : ∀ (Y acc X : List Bool),
    (mulLoop acc X Y).1.length ≤ max acc.length X.length + Y.length ∧
      (mulLoop acc X Y).2.length = X.length + Y.length := by
  intro Y
  induction Y with
  | nil => intro acc X; simp [mulLoop]
  | cons y Y ih =>
    intro acc X
    rw [mulLoop]
    obtain ⟨h1, h2⟩ := ih (if y then addL false acc X else acc) (false :: X)
    refine ⟨h1.trans ?_, by simp [h2]; omega⟩
    cases y <;> simp [length_addL] <;> omega

@[simp] lemma update_mk_inr {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type}
    (B : Kb → List Bool) (Q : ∀ r, List (G r)) (r : R) (l : List (G r)) :
    Function.update (mk B Q) (Sum.inr r) l = mk B (Function.update Q r l) := by
  funext k
  cases k with
  | inl a => rw [Function.update_of_ne (fun e => Sum.inl_ne_inr e)]; rfl
  | inr q =>
    by_cases h : q = r
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Sum.inr_injective e))]
      simp [Function.update_of_ne h]

/-- own labels of the `TMm` machine -/
inductive OLm
  | rev | cp | o1 | o1b | o2 | o2b | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8
  | mul | dup | r1 | r2 | add | r3 | shift | cx | f1 | f2 | hlt
  deriving DecidableEq

scoped instance : Fintype OLm :=
  Fintype.ofList [.rev, .cp, .o1, .o1b, .o2, .o2b, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .a8,
    .mul, .dup, .r1, .r2, .add, .r3, .shift, .cx, .f1, .f2, .hlt]
    (by intro x; cases x <;> simp)

section TMm

variable (A : Type) [Inhabited A] (T1 T2 : FinTM2)

/-- non-Bool stacks: own `A` stacks (`false` = input, `true` = temp) and the sub-machines' stacks -/
abbrev RM : Type := Bool ⊕ (T1.K ⊕ T2.K)

/-- their alphabets -/
abbrev GM (r : RM T1 T2) : Type :=
  Sum.casesOn (motive := fun _ => Type) r (fun _ => A)
    (fun r' => Sum.casesOn (motive := fun _ => Type) r' T1.Γ T2.Γ)

/-- labels -/
abbrev LM : Type := OLm ⊕ (T1.Λ ⊕ T2.Λ)

/-- the non-register part of the state: an `A` register and the two sub-states -/
abbrev ρM : Type := Option A × (T1.σ × T2.σ)

abbrev StM : Type := TM2.Stmt (BΓ W (GM A T1 T2)) (LM T1 T2) (Reg × ρM A T1 T2)

/-- slot of the first sub-machine -/
def slot1 : Slot T1 (W ⊕ RM T1 T2) (BΓ W (GM A T1 T2)) (LM T1 T2) (Reg × ρM A T1 T2) where
  kf k := Sum.inr (Sum.inr (Sum.inl k))
  kf_inj a b h := by simpa using h
  gin _ a := a
  gout _ a := a
  gout_gin _ _ := rfl
  sget v := v.2.2.1
  sset v s := (v.1, v.2.1, s, v.2.2.2)
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  lf l := Sum.inr (Sum.inl l)
  ret := Sum.inl OLm.o1

/-- slot of the second sub-machine -/
def slot2 : Slot T2 (W ⊕ RM T1 T2) (BΓ W (GM A T1 T2)) (LM T1 T2) (Reg × ρM A T1 T2) where
  kf k := Sum.inr (Sum.inr (Sum.inr k))
  kf_inj a b h := by simpa using h
  gin _ a := a
  gout _ a := a
  gout_gin _ _ := rfl
  sget v := v.2.2.2
  sset v s := (v.1, v.2.1, v.2.2.1, s)
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  lf l := Sum.inr (Sum.inr l)
  ret := Sum.inl OLm.o2

variable (e1 : T1.Γ T1.k₀ ≃ A) (e2 : T2.Γ T2.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (o2 : T2.Γ T2.k₁ ≃ Bool)

/-- update of the `A` register -/
def updA (v : Reg × ρM A T1 T2) (o : Option A) : Reg × ρM A T1 T2 := (v.1, o, v.2.2)

/-- update of the Bool register with a converted sub-machine output symbol -/
def updO {Γ : Type} (o : Γ ≃ Bool) (v : Reg × ρM A T1 T2) (x : Option Γ) : Reg × ρM A T1 T2 :=
  ((x.map o, v.1.2.1, v.1.2.2), v.2)

/-- the own code -/
def ownM : OLm → StM A T1 T2
  | .rev => TM2.Stmt.pop (Sum.inr (Sum.inl false)) (updA A T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLm.cp)
        (TM2.Stmt.push (Sum.inr (Sum.inl true)) (fun v => v.2.1.getD default)
          (TM2.Stmt.goto fun _ => Sum.inl OLm.rev)))
  | .cp => TM2.Stmt.pop (Sum.inr (Sum.inl true)) (updA A T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inr (Sum.inl T1.main))
        (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inl T1.k₀))) (fun v => e1.symm (v.2.1.getD default))
          (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr T2.k₀))) (fun v => e2.symm (v.2.1.getD default))
            (TM2.Stmt.goto fun _ => Sum.inl OLm.cp))))
  | .o1 => TM2.Stmt.pop (Sum.inr (Sum.inr (Sum.inl T1.k₁))) (updO A T1 T2 o1)
      (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLm.o1b)
        (TM2.Stmt.push (Sum.inl W.x1) (fun v => v.1.1.getD false)
          (TM2.Stmt.goto fun _ => Sum.inl OLm.o1)))
  | .o1b => mvStmt W.x1 W.x (Sum.inl OLm.o1b) (Sum.inr (Sum.inr T2.main))
  | .o2 => TM2.Stmt.pop (Sum.inr (Sum.inr (Sum.inr T2.k₁))) (updO A T1 T2 o2)
      (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLm.o2b)
        (TM2.Stmt.push (Sum.inl W.x1) (fun v => v.1.1.getD false)
          (TM2.Stmt.goto fun _ => Sum.inl OLm.o2)))
  | .o2b => mvStmt W.x1 W.y (Sum.inl OLm.o2b) (Sum.inl OLm.a1)
  | .a1 => dupStmt W.x W.x1 W.x2 (Sum.inl OLm.a1) (Sum.inl OLm.a2)
  | .a2 => mvStmt W.x1 W.x (Sum.inl OLm.a2) (Sum.inl OLm.a3)
  | .a3 => mvStmt W.x2 W.x3 (Sum.inl OLm.a3) (Sum.inl OLm.a4)
  | .a4 => dupStmt W.y W.v W.x1 (Sum.inl OLm.a4) (Sum.inl OLm.a5)
  | .a5 => mvStmt W.v W.y (Sum.inl OLm.a5) (Sum.inl OLm.a6)
  | .a6 => mvStmt W.x1 W.x2 (Sum.inl OLm.a6) (Sum.inl OLm.a7)
  | .a7 => addStmt W.x3 W.x2 W.t (Sum.inl OLm.a7) (Sum.inl OLm.a8)
  | .a8 => mvStmt W.t W.acc (Sum.inl OLm.a8) (Sum.inl OLm.mul)
  | .mul => mulStmt (Sum.inl OLm.cx) (Sum.inl OLm.dup) (Sum.inl OLm.shift)
  | .dup => dupStmt W.x W.x1 W.x2 (Sum.inl OLm.dup) (Sum.inl OLm.r1)
  | .r1 => mvStmt W.x1 W.x (Sum.inl OLm.r1) (Sum.inl OLm.r2)
  | .r2 => mvStmt W.x2 W.x3 (Sum.inl OLm.r2) (Sum.inl OLm.add)
  | .add => addStmt W.acc W.x3 W.t (Sum.inl OLm.add) (Sum.inl OLm.r3)
  | .r3 => mvStmt W.t W.acc (Sum.inl OLm.r3) (Sum.inl OLm.shift)
  | .shift => shiftStmt (Sum.inl OLm.mul)
  | .cx => clearStmt W.x (Sum.inl OLm.cx) (Sum.inl OLm.f1)
  | .f1 => mvStmt W.acc W.t (Sum.inl OLm.f1) (Sum.inl OLm.f2)
  | .f2 => stripStmt W.t W.out (Sum.inl OLm.f2) (Sum.inl OLm.hlt)
  | .hlt => TM2.Stmt.halt

/-- the whole program -/
def progM : LM T1 T2 → StM A T1 T2
  | Sum.inl o => ownM A T1 T2 e1 e2 o1 o2 o
  | Sum.inr (Sum.inl l) => (slot1 A T1 T2).tr (T1.m l)
  | Sum.inr (Sum.inr l) => (slot2 A T1 T2).tr (T2.m l)

/-- the machine -/
def tmM [Fintype A] : FinTM2 where
  K := W ⊕ RM T1 T2
  kDecidableEq := inferInstance
  kFin := by letI := T1.kFin; letI := T2.kFin; exact inferInstance
  k₀ := Sum.inr (Sum.inl false)
  k₁ := Sum.inl W.out
  Γ := BΓ W (GM A T1 T2)
  Λ := LM T1 T2
  main := Sum.inl OLm.rev
  ΛFin := by letI := T1.ΛFin; letI := T2.ΛFin; exact inferInstance
  σ := Reg × ρM A T1 T2
  initialState := ((none, none, false), none, T1.initialState, T2.initialState)
  σFin := by letI := T1.σFin; letI := T2.σFin; letI : Fintype A := ‹_›; exact inferInstance
  Γk₀Fin := (inferInstance : Fintype A)
  m := progM A T1 T2 e1 e2 o1 o2

lemma mulProg_M : MulProg (progM A T1 T2 e1 e2 o1 o2) (Sum.inl OLm.mul) (Sum.inl OLm.dup)
    (Sum.inl OLm.r1) (Sum.inl OLm.r2) (Sum.inl OLm.add) (Sum.inl OLm.r3) (Sum.inl OLm.shift)
    (Sum.inl OLm.cx) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- phase A: `acc := x + y`, keeping `x`, `y` -/
lemma phaseA (r : ρM A T1 T2) (B : W → List Bool) (Q : ∀ r, List (GM A T1 T2 r))
    (hx1 : B W.x1 = []) (hx2 : B W.x2 = []) (hx3 : B W.x3 = []) (ht : B W.t = [])
    (hv : B W.v = []) (hacc : B W.acc = []) :
    Reach (progM A T1 T2 e1 e2 o1 o2) ⟨some (Sum.inl OLm.a1), ((none, none, false), r), mk B Q⟩
      ⟨some (Sum.inl OLm.mul), ((none, none, false), r),
        mk (Function.update B W.acc (addL false (B W.x) (B W.y))) Q⟩
      (5 * ((B W.x).length + (B W.y).length) + 10) := by
  have r1 := dup_run (progM A T1 T2 e1 e2 o1 o2) W.x W.x1 W.x2 (by decide) (by decide) (by decide)
    (Sum.inl OLm.a1) (Sum.inl OLm.a2) rfl r false Q (B W.x) B rfl
  have r2 := r1.trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.x1 W.x (by decide) _ _ rfl r false Q
    _ _ rfl)
  have r3 := r2.trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.x2 W.x3 (by decide) _ _ rfl r false Q
    _ _ rfl)
  have r4 := r3.trans (dup_run (progM A T1 T2 e1 e2 o1 o2) W.y W.v W.x1 (by decide) (by decide)
    (by decide) _ _ rfl r false Q _ _ rfl)
  have r5 := r4.trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.v W.y (by decide) _ _ rfl r false Q
    _ _ rfl)
  have r6 := r5.trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.x1 W.x2 (by decide) _ _ rfl r false Q
    _ _ rfl)
  have r7 := r6.trans (add_mk (progM A T1 T2 e1 e2 o1 o2) W.x3 W.x2 W.t (by decide) (by decide)
    (by decide) _ _ rfl r false _ Q)
  have r8 := r7.trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.t W.acc (by decide) _ _ rfl r false Q
    _ _ rfl)
  refine (r8.of_eq ?_).mono ?_
  · congr 2
    funext k; cases k <;> simp [Function.update_apply, hx1, hx2, hx3, ht, hv, hacc]
  · simp [Function.update_apply, hx1, hx2, hx3, ht, hv, hacc, length_addL]
    omega

/-- final phase: clear `x`, `out := strip acc` -/
lemma phaseF (r : ρM A T1 T2) (B : W → List Bool) (Q : ∀ r, List (GM A T1 T2 r))
    (ht : B W.t = []) (hout : B W.out = []) :
    Reach (progM A T1 T2 e1 e2 o1 o2) ⟨some (Sum.inl OLm.cx), ((none, none, false), r), mk B Q⟩
      ⟨some (Sum.inl OLm.hlt), ((none, none, false), r),
        mk (Function.update (Function.update (Function.update B W.x []) W.acc []) W.out
          (strip (B W.acc))) Q⟩
      ((B W.x).length + 2 * (B W.acc).length + 3) := by
  have r1 := clear_mk (progM A T1 T2 e1 e2 o1 o2) W.x (Sum.inl OLm.cx) (Sum.inl OLm.f1) rfl r false B Q
  have r2 := r1.trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.acc W.t (by decide) _ _ rfl r false Q
    _ _ rfl)
  have r3 := r2.trans (strip_mk (progM A T1 T2 e1 e2 o1 o2) W.t W.out (by decide) _ _ rfl r false
    _ Q)
  refine (r3.of_eq ?_).mono ?_
  · congr 2
    funext k; cases k <;> simp [Function.update_apply, ht, hout, stripPush, strip]
  · simp [Function.update_apply, ht, hout]
    omega

end TMm

end OCRS19TM


/-! L11: `TMm` input phase (reverse + copy to both sub-machines) and the first slot phase. -/

namespace OCRS19TM

open Turing

section TMm2

variable (A : Type) [Inhabited A] (T1 T2 : FinTM2)
variable (e1 : T1.Γ T1.k₀ ≃ A) (e2 : T2.Γ T2.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (o2 : T2.Γ T2.k₁ ≃ Bool)

/-- input phase: the input `w` is copied (in order) to the input stacks of both sub-machines -/
lemma phaseIn (c : Reg) (s : T1.σ × T2.σ) (B : W → List Bool) (Q : ∀ r, List (GM A T1 T2 r))
    (w : List A) (hin : Q (Sum.inl false) = w) (htmp : Q (Sum.inl true) = [])
    (h1 : Q (Sum.inr (Sum.inl T1.k₀)) = []) (h2 : Q (Sum.inr (Sum.inr T2.k₀)) = []) :
    ∃ Q' : ∀ r, List (GM A T1 T2 r),
      Reach (progM A T1 T2 e1 e2 o1 o2) ⟨some (Sum.inl OLm.rev), (c, none, s), mk B Q⟩
        ⟨some (Sum.inr (Sum.inl T1.main)), (c, none, s), mk B Q'⟩ (2 * w.length + 2) ∧
      Q' (Sum.inl false) = [] ∧ Q' (Sum.inl true) = [] ∧
      Q' (Sum.inr (Sum.inl T1.k₀)) = w.map e1.symm ∧
      Q' (Sum.inr (Sum.inr T2.k₀)) = w.map e2.symm ∧
      (∀ k, k ≠ T1.k₀ → Q' (Sum.inr (Sum.inl k)) = Q (Sum.inr (Sum.inl k))) ∧
      (∀ k, k ≠ T2.k₀ → Q' (Sum.inr (Sum.inr k)) = Q (Sum.inr (Sum.inr k))) := by
  have r1 := transfer (progM A T1 T2 e1 e2 o1 o2) (Sum.inl OLm.rev) (Sum.inr (Sum.inl false))
    (Sum.inr (Sum.inl true)) (by simp) (updA A T1 T2) (fun v => v.2.1.isNone)
    (fun _ => Sum.inl OLm.cp) (fun v => v.2.1.getD default) id (fun _ => True) rfl
    (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) [] w (mk B Q) (c, none, s) (by simp)
    (by simp [hin]) rfl
  obtain ⟨S', r2, ka, kb, kc, kr⟩ := copy2 (progM A T1 T2 e1 e2 o1 o2) (Sum.inl OLm.cp)
    (Sum.inr (Sum.inl true)) (Sum.inr (Sum.inr (Sum.inl T1.k₀)))
    (Sum.inr (Sum.inr (Sum.inr T2.k₀))) (by simp) (by simp) (by simp) (updA A T1 T2)
    (fun v => v.2.1.isNone) (fun _ => Sum.inr (Sum.inl T1.main))
    (fun v => e1.symm (v.2.1.getD default)) (fun v => e2.symm (v.2.1.getD default))
    e1.symm e2.symm rfl (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩)
    ((w.map id).reverse ++ (mk B Q) (Sum.inr (Sum.inl true)))
    (Function.update (Function.update (mk B Q) (Sum.inr (Sum.inl false)) [])
      (Sum.inr (Sum.inl true)) ((w.map id).reverse ++ (mk B Q) (Sum.inr (Sum.inl true))))
    (c, none, s) (by simp)
  have hS : S' = mk B (fun r => S' (Sum.inr r)) := by
    apply mk_ext
    · intro a
      rw [kr (Sum.inl a) (by simp) (by simp) (by simp)]
      simp
    · intro r; rfl
  refine ⟨fun r => S' (Sum.inr r), ((r1.trans r2).of_eq ?_).mono ?_, ?_, ka, ?_, ?_, ?_, ?_⟩
  · rw [← hS]; rfl
  · simp [htmp]; omega
  · show S' (Sum.inr (Sum.inl false)) = []
    rw [kr (Sum.inr (Sum.inl false)) (by simp) (by simp) (by simp)]
    simp
  · show S' (Sum.inr (Sum.inr (Sum.inl T1.k₀))) = _
    rw [kb]
    simp [htmp, h1, List.map_reverse]
  · show S' (Sum.inr (Sum.inr (Sum.inr T2.k₀))) = _
    rw [kc]
    simp [htmp, h2, List.map_reverse]
  · intro k hk
    show S' (Sum.inr (Sum.inr (Sum.inl k))) = _
    rw [kr (Sum.inr (Sum.inr (Sum.inl k))) (by simp) (by simpa using hk) (by simp)]
    simp
  · intro k hk
    show S' (Sum.inr (Sum.inr (Sum.inr k))) = _
    rw [kr (Sum.inr (Sum.inr (Sum.inr k))) (by simp) (by simp) (by simpa using hk)]
    simp

/-- slot phase 1: run the first sub-machine, move its output (LSB on top) to `x` -/
lemma phaseS1 (s2 : T2.σ) (B : W → List Bool) (Q : ∀ r, List (GM A T1 T2 r))
    (inp : List (T1.Γ T1.k₀)) (out : List Bool) (t : ℕ)
    (hrun : TM2OutputsInTime T1 inp (some (out.map o1.symm)) t)
    (hQ : ∀ k, Q (Sum.inr (Sum.inl k)) = (initList T1 inp).stk k)
    (hx1 : B W.x1 = []) (hx : B W.x = []) :
    ∃ Q' : ∀ r, List (GM A T1 T2 r),
      Reach (progM A T1 T2 e1 e2 o1 o2)
        ⟨some (Sum.inr (Sum.inl T1.main)), ((none, none, false), none, T1.initialState, s2), mk B Q⟩
        ⟨some (Sum.inr (Sum.inr T2.main)), ((none, none, false), none, T1.initialState, s2),
          mk (Function.update B W.x out) Q'⟩ (t + 2 * out.length + 2) ∧
      (∀ k, Q' (Sum.inr (Sum.inl k)) = []) ∧ (∀ b, Q' (Sum.inl b) = Q (Sum.inl b)) ∧
      (∀ k, Q' (Sum.inr (Sum.inr k)) = Q (Sum.inr (Sum.inr k))) := by
  obtain ⟨S1, hR, r1⟩ := (slot1 A T1 T2).sub_run (progM A T1 T2 e1 e2 o1 o2) (fun _ => rfl)
    ((none, none, false), none, T1.initialState, s2) (mk B Q) (mk B Q) hrun
    ⟨fun k => by simp [slot1, hQ k], fun _ _ => rfl⟩
  have hk1 : S1 (Sum.inr (Sum.inr (Sum.inl T1.k₁))) = out.map o1.symm ++ [] := by
    have := hR.1 T1.k₁
    simp only [slot1] at this
    rw [this, haltList_stk_k1]
    simp
  have r2 := r1.trans (transfer (progM A T1 T2 e1 e2 o1 o2) (Sum.inl OLm.o1)
    (Sum.inr (Sum.inr (Sum.inl T1.k₁))) (Sum.inl W.x1) (by simp) (updO A T1 T2 o1)
    (fun v => v.1.1.isNone) (fun _ => Sum.inl OLm.o1b) (fun v => v.1.1.getD false) o1
    (fun _ => True) rfl (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) [] (out.map o1.symm) S1
    ((none, none, false), none, T1.initialState, s2) (by simp) hk1 rfl)
  have hfr : ∀ k', (∀ k, Sum.inr (Sum.inr (Sum.inl k)) ≠ k') → S1 k' = mk B Q k' := hR.2
  set S2 := Function.update (Function.update S1 (Sum.inr (Sum.inr (Sum.inl T1.k₁))) [].tail)
    (Sum.inl W.x1) (((out.map o1.symm).map o1).reverse ++ S1 (Sum.inl W.x1)) with hS2
  have hB2 : ∀ a, S2 (Sum.inl a) = Function.update B W.x1 out.reverse a := by
    intro a
    rw [hS2]
    by_cases ha : a = W.x1
    · subst ha
      rw [Function.update_self, hfr (Sum.inl W.x1) (by simp)]
      simp [hx1, Function.comp_def]
    · rw [Function.update_of_ne (fun e => ha (Sum.inl_injective e)), Function.update_of_ne (by simp),
        hfr (Sum.inl a) (by simp), Function.update_of_ne ha]
      rfl
  have hS2m : S2 = mk (Function.update B W.x1 out.reverse) (fun r => S2 (Sum.inr r)) :=
    mk_ext _ hB2 (fun _ => rfl)
  have r3 := (r2.of_eq (c₂ := ⟨some (Sum.inl OLm.o1b), ((none, none, false), none, T1.initialState, s2),
    mk (Function.update B W.x1 out.reverse) (fun r => S2 (Sum.inr r))⟩) (by rw [← hS2m]; rfl)).trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.x1 W.x
    (by decide) (Sum.inl OLm.o1b) (Sum.inr (Sum.inr T2.main)) rfl _ false _ out.reverse _
    (by simp))
  refine ⟨fun r => S2 (Sum.inr r), (r3.of_eq ?_).mono ?_, ?_, ?_, ?_⟩
  · congr 2
    funext a
    by_cases ha : a = W.x1
    · subst ha; simp [hx1]
    by_cases hb : a = W.x
    · subst hb; simp [hx]
    · simp [Function.update_apply, ha, hb]
  · simp
    omega
  · intro k
    show S2 _ = []
    rw [hS2, Function.update_of_ne (by simp)]
    by_cases hk : k = T1.k₁
    · subst hk; simp
    · rw [Function.update_of_ne (by simpa using hk)]
      have := hR.1 k
      simp only [slot1] at this
      rw [this, haltList_stk_ne _ _ _ hk]
      simp
  · intro b
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      hfr (Sum.inr (Sum.inl b)) (by simp)]
    rfl
  · intro k
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      hfr (Sum.inr (Sum.inr (Sum.inr k))) (by simp)]
    rfl

/-- slot phase 2: run the second sub-machine, move its output (LSB on top) to `y` -/
lemma phaseS2 (s1 : T1.σ) (B : W → List Bool) (Q : ∀ r, List (GM A T1 T2 r))
    (inp : List (T2.Γ T2.k₀)) (out : List Bool) (t : ℕ)
    (hrun : TM2OutputsInTime T2 inp (some (out.map o2.symm)) t)
    (hQ : ∀ k, Q (Sum.inr (Sum.inr k)) = (initList T2 inp).stk k)
    (hx1 : B W.x1 = []) (hy : B W.y = []) :
    ∃ Q' : ∀ r, List (GM A T1 T2 r),
      Reach (progM A T1 T2 e1 e2 o1 o2)
        ⟨some (Sum.inr (Sum.inr T2.main)), ((none, none, false), none, s1, T2.initialState), mk B Q⟩
        ⟨some (Sum.inl OLm.a1), ((none, none, false), none, s1, T2.initialState),
          mk (Function.update B W.y out) Q'⟩ (t + 2 * out.length + 2) ∧
      (∀ k, Q' (Sum.inr (Sum.inr k)) = []) ∧ (∀ b, Q' (Sum.inl b) = Q (Sum.inl b)) ∧
      (∀ k, Q' (Sum.inr (Sum.inl k)) = Q (Sum.inr (Sum.inl k))) := by
  obtain ⟨S1, hR, r1⟩ := (slot2 A T1 T2).sub_run (progM A T1 T2 e1 e2 o1 o2) (fun _ => rfl)
    ((none, none, false), none, s1, T2.initialState) (mk B Q) (mk B Q) hrun
    ⟨fun k => by simp [slot2, hQ k], fun _ _ => rfl⟩
  have hk1 : S1 (Sum.inr (Sum.inr (Sum.inr T2.k₁))) = out.map o2.symm ++ [] := by
    have := hR.1 T2.k₁
    simp only [slot2] at this
    rw [this, haltList_stk_k1]
    simp
  have r2 := r1.trans (transfer (progM A T1 T2 e1 e2 o1 o2) (Sum.inl OLm.o2)
    (Sum.inr (Sum.inr (Sum.inr T2.k₁))) (Sum.inl W.x1) (by simp) (updO A T1 T2 o2)
    (fun v => v.1.1.isNone) (fun _ => Sum.inl OLm.o2b) (fun v => v.1.1.getD false) o2
    (fun _ => True) rfl (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) [] (out.map o2.symm) S1
    ((none, none, false), none, s1, T2.initialState) (by simp) hk1 rfl)
  have hfr : ∀ k', (∀ k, Sum.inr (Sum.inr (Sum.inr k)) ≠ k') → S1 k' = mk B Q k' := hR.2
  set S2 := Function.update (Function.update S1 (Sum.inr (Sum.inr (Sum.inr T2.k₁))) [].tail)
    (Sum.inl W.x1) (((out.map o2.symm).map o2).reverse ++ S1 (Sum.inl W.x1)) with hS2
  have hB2 : ∀ a, S2 (Sum.inl a) = Function.update B W.x1 out.reverse a := by
    intro a
    rw [hS2]
    by_cases ha : a = W.x1
    · subst ha
      rw [Function.update_self, hfr (Sum.inl W.x1) (by simp)]
      simp [hx1, Function.comp_def]
    · rw [Function.update_of_ne (fun e => ha (Sum.inl_injective e)), Function.update_of_ne (by simp),
        hfr (Sum.inl a) (by simp), Function.update_of_ne ha]
      rfl
  have hS2m : S2 = mk (Function.update B W.x1 out.reverse) (fun r => S2 (Sum.inr r)) :=
    mk_ext _ hB2 (fun _ => rfl)
  have r3 := (r2.of_eq (c₂ := ⟨some (Sum.inl OLm.o2b), ((none, none, false), none, s1, T2.initialState),
    mk (Function.update B W.x1 out.reverse) (fun r => S2 (Sum.inr r))⟩) (by rw [← hS2m]; rfl)).trans (mv_run (progM A T1 T2 e1 e2 o1 o2) W.x1 W.y
    (by decide) (Sum.inl OLm.o2b) (Sum.inl OLm.a1) rfl _ false _ out.reverse _
    (by simp))
  refine ⟨fun r => S2 (Sum.inr r), (r3.of_eq ?_).mono ?_, ?_, ?_, ?_⟩
  · congr 2
    funext a
    by_cases ha : a = W.x1
    · subst ha; simp [hx1]
    by_cases hb : a = W.y
    · subst hb; simp [hy]
    · simp [Function.update_apply, ha, hb]
  · simp
    omega
  · intro k
    show S2 _ = []
    rw [hS2, Function.update_of_ne (by simp)]
    by_cases hk : k = T2.k₁
    · subst hk; simp
    · rw [Function.update_of_ne (by simpa using hk)]
      have := hR.1 k
      simp only [slot2] at this
      rw [this, haltList_stk_ne _ _ _ hk]
      simp
  · intro b
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      hfr (Sum.inr (Sum.inl b)) (by simp)]
    rfl
  · intro k
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      hfr (Sum.inr (Sum.inr (Sum.inl k))) (by simp)]
    rfl

end TMm2

end OCRS19TM


/-! L12: the `TMm` top theorem: a polytime machine for `(m₁ + 1) * (m₂ + 1) - 1`. -/

namespace OCRS19TM

open Turing

lemma tmm_arith (n t1 t2 c1 c2 a b m1 m2 : ℕ) (ha : a ≤ n + c1 * t1) (hb : b ≤ n + c2 * t2)
    (hm1 : m1 ≤ a + 2 * b + 2) (hm2 : m2 ≤ a + b + 1) :
    2 * n + 2 + (t1 + 2 * a + 2) + (t2 + 2 * b + 2) + (5 * (a + b) + 10) + mulT (a + b + 2) b
      + (m2 + 2 * m1 + 3) + 1 ≤ 100 * (n + (c1 + c2 + 1) * (t1 + t2) + 1) ^ 2 := by
  have h1 : c1 * t1 ≤ (c1 + c2 + 1) * (t1 + t2) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : c2 * t2 ≤ (c1 + c2 + 1) * (t1 + t2) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : t1 + t2 ≤ (c1 + c2 + 1) * (t1 + t2) := Nat.le_mul_of_pos_left _ (by omega)
  generalize hL : n + (c1 + c2 + 1) * (t1 + t2) = L
  have haL : a ≤ L := by omega
  have hbL : b ≤ L := by omega
  have htL : t1 + t2 ≤ L := by omega
  have hnL : n ≤ L := by omega
  have hmul : mulT (a + b + 2) b ≤ (L + 1) * (24 * L + 22) := by
    unfold mulT; exact Nat.mul_le_mul (by omega) (by omega)
  nlinarith

lemma cfg_eq_haltList (T : FinTM2) (out : List (T.Γ T.k₁)) (c : T.Cfg) (hl : c.l = none)
    (hv : c.var = T.initialState) (h1 : c.stk T.k₁ = out)
    (hne : ∀ k, k ≠ T.k₁ → c.stk k = []) : c = haltList T out := by
  obtain ⟨l, v, S⟩ := c
  simp only at hl hv h1 hne
  subst hl hv
  have : S = (haltList T out).stk := by
    funext k
    by_cases hk : k = T.k₁
    · subst hk; rw [h1, haltList_stk_k1]
    · rw [hne k hk, haltList_stk_ne _ _ _ hk]
  subst this; rfl

section TMmTop

variable {A : Type} [Inhabited A] [Fintype A] (T1 T2 : FinTM2)
variable (e1 : T1.Γ T1.k₀ ≃ A) (e2 : T2.Γ T2.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (o2 : T2.Γ T2.k₁ ≃ Bool)

lemma tmm_halt (out : List Bool) (B : W → List Bool) (Q : ∀ r, List (GM A T1 T2 r))
    (hB : B W.out = out) (hB' : ∀ a, a ≠ W.out → B a = []) (hQ : ∀ r, Q r = []) :
    (⟨none, ((none, none, false), none, T1.initialState, T2.initialState), mk B Q⟩ :
      TM2.Cfg (BΓ W (GM A T1 T2)) (LM T1 T2) (Reg × ρM A T1 T2)) =
      haltList (tmM A T1 T2 e1 e2 o1 o2) (List.map (Equiv.refl Bool).invFun out) := by
  apply cfg_eq_haltList (tmM A T1 T2 e1 e2 o1 o2) _ _ rfl rfl
  · exact hB.trans (List.map_id out).symm
  · intro k hk
    rcases k with a | r
    · exact hB' a (fun h => hk (by rw [h]; rfl))
    · exact hQ r

lemma tmm_run (w : List A) (n1 n2 t1 t2 N T : ℕ)
    (hr1 : TM2OutputsInTime T1 (w.map e1.symm)
      (some ((Computability.encodeNat n1).map o1.symm)) t1)
    (hr2 : TM2OutputsInTime T2 (w.map e2.symm)
      (some ((Computability.encodeNat n2).map o2.symm)) t2)
    (hN : N = n1 + n2 + n1 * n2)
    (hT : 100 * (w.length + (pushC T1 + pushC T2 + 1) * (t1 + t2) + 1) ^ 2 ≤ T) :
    Nonempty (TM2OutputsInTime (tmM A T1 T2 e1 e2 o1 o2) (List.map (Equiv.refl A).invFun w)
      (some (List.map (Equiv.refl Bool).invFun (Computability.encodeNat N))) T) := by
  have hl1 := out_len T1 hr1
  have hl2 := out_len T2 hr2
  simp only [List.length_map] at hl1 hl2
  let Q0 : ∀ r, List (GM A T1 T2 r) := Function.update (fun _ => []) (Sum.inl false) w
  obtain ⟨Q1, R1, q1a, q1b, q1c, q1d, q1e, q1f⟩ := phaseIn A T1 T2 e1 e2 o1 o2 (none, none, false)
    (T1.initialState, T2.initialState) (fun _ => []) Q0 w (by simp [Q0]) (by simp [Q0])
    (by simp [Q0]) (by simp [Q0])
  have hQ1 : ∀ k, Q1 (Sum.inr (Sum.inl k)) = (initList T1 (w.map e1.symm)).stk k := by
    intro k
    by_cases hk : k = T1.k₀
    · subst hk; rw [q1c, initList_stk_k0]
    · rw [q1e k hk, initList_stk_ne T1 _ k hk]; simp [Q0]
  obtain ⟨Q2, R2, q2a, q2b, q2c⟩ := phaseS1 A T1 T2 e1 e2 o1 o2 T2.initialState (fun _ => []) Q1
    (w.map e1.symm) (Computability.encodeNat n1) t1 hr1 hQ1 rfl rfl
  have hQ2 : ∀ k, Q2 (Sum.inr (Sum.inr k)) = (initList T2 (w.map e2.symm)).stk k := by
    intro k
    rw [q2c k]
    by_cases hk : k = T2.k₀
    · subst hk; rw [q1d, initList_stk_k0]
    · rw [q1f k hk, initList_stk_ne T2 _ k hk]; simp [Q0]
  obtain ⟨Q3, R3, q3a, q3b, q3c⟩ := phaseS2 A T1 T2 e1 e2 o1 o2 T1.initialState
    (Function.update (fun _ => []) W.x (Computability.encodeNat n1)) Q2 (w.map e2.symm)
    (Computability.encodeNat n2) t2 hr2 hQ2 (by simp) (by simp)
  have R4 := phaseA A T1 T2 e1 e2 o1 o2 (none, T1.initialState, T2.initialState)
    (Function.update (Function.update (fun _ => []) W.x (Computability.encodeNat n1)) W.y
      (Computability.encodeNat n2)) Q3 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have R5 := mul_loop (mulProg_M A T1 T2 e1 e2 o1 o2) (none, T1.initialState, T2.initialState) Q3
    (Computability.encodeNat n2)
    (Function.update (Function.update (Function.update (fun _ => []) W.x
      (Computability.encodeNat n1)) W.y (Computability.encodeNat n2)) W.acc
      (addL false ((Function.update (Function.update (fun _ => []) W.x
        (Computability.encodeNat n1)) W.y (Computability.encodeNat n2)) W.x)
        ((Function.update (Function.update (fun _ => []) W.x
        (Computability.encodeNat n1)) W.y (Computability.encodeNat n2)) W.y)))
    ((Computability.encodeNat n1).length + (Computability.encodeNat n2).length + 2)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp [length_addL]; omega) (by simp; omega)
  have R := R1.trans (R2.trans (R3.trans (R4.trans (R5.trans ((phaseF A T1 T2 e1 e2 o1 o2
    (none, T1.initialState, T2.initialState) _ Q3 (by simp) (by simp)).trans
    (Reach.single (c' := ⟨none, _, _⟩) rfl))))))
  have h0 : initList (tmM A T1 T2 e1 e2 o1 o2) (List.map (Equiv.refl A).invFun w) = ⟨some (Sum.inl OLm.rev),
      ((none, none, false), none, T1.initialState, T2.initialState), mk (fun _ => []) Q0⟩ := by
    have e : (initList (tmM A T1 T2 e1 e2 o1 o2) (List.map (Equiv.refl A).invFun w)).stk =
        mk (fun _ => []) Q0 := by
      funext k
      rcases k with a | r
      · exact initList_stk_ne (tmM A T1 T2 e1 e2 o1 o2) _ (Sum.inl a)
          (fun h => Sum.inl_ne_inr h)
      · by_cases hr : r = Sum.inl false
        · subst hr
          refine (initList_stk_k0 (tmM A T1 T2 e1 e2 o1 o2) _).trans ?_
          exact List.map_id w
        · refine (initList_stk_ne (tmM A T1 T2 e1 e2 o1 o2) _ (Sum.inr r)
            (fun h => hr (Sum.inr_injective h))).trans ?_
          show ([] : List (GM A T1 T2 r)) = Q0 r
          simp only [Q0]
          rw [Function.update_of_ne hr]
    rw [← e]; rfl
  obtain ⟨k, hk, e⟩ := R
  refine ⟨⟨⟨k, ?_⟩, hk.trans ?_⟩⟩
  · rw [h0]
    change _ = some (haltList (tmM A T1 T2 e1 e2 o1 o2) _)
    refine e.trans (congrArg some ?_)
    apply tmm_halt T1 T2 e1 e2 o1 o2 (Computability.encodeNat N)
    · simp only [Function.update_self]
      rw [hN, ← encodeNat_val]
      congr 1
      simp [Function.update_apply, val_mulLoop, val_addL, val_encodeNat]
    · intro a ha
      cases a <;> first | exact absurd rfl ha | simp [Function.update_apply]
    · intro r
      rcases r with b | k | k
      · rw [q3b, q2b]
        cases b
        · exact q1a
        · exact q1b
      · rw [q3c, q2a]
      · exact q3a k
  · refine le_trans ?_ ((tmm_arith w.length t1 t2 (pushC T1) (pushC T2)
      (Computability.encodeNat n1).length (Computability.encodeNat n2).length
      (mulLoop (addL false (Computability.encodeNat n1) (Computability.encodeNat n2))
        (Computability.encodeNat n1) (Computability.encodeNat n2)).1.length
      (mulLoop (addL false (Computability.encodeNat n1) (Computability.encodeNat n2))
        (Computability.encodeNat n1) (Computability.encodeNat n2)).2.length hl1 hl2 ?_ ?_).trans hT)
    · simp [Function.update_apply]
      omega
    · have := (mulLoop_len (Computability.encodeNat n2)
        (addL false (Computability.encodeNat n1) (Computability.encodeNat n2))
        (Computability.encodeNat n1)).1
      simp only [length_addL] at this
      omega
    · have := (mulLoop_len (Computability.encodeNat n2)
        (addL false (Computability.encodeNat n1) (Computability.encodeNat n2))
        (Computability.encodeNat n1)).2
      omega

end TMmTop

/-- the polytime machine for `(m₁ + 1) * (m₂ + 1) - 1` -/
noncomputable def tmmPoly {A : Type} [Inhabited A] [Fintype A] {α : Type} (ea : α → List A)
    (m₁ m₂ : α → ℕ) (h1 : TM2ComputableInPolyTime ea Computability.encodeNat m₁)
    (h2 : TM2ComputableInPolyTime ea Computability.encodeNat m₂) :
    TM2ComputableInPolyTime ea Computability.encodeNat (fun a => (m₁ a + 1) * (m₂ a + 1) - 1) where
  tm := tmM A h1.tm h2.tm h1.inputAlphabet h2.inputAlphabet h1.outputAlphabet h2.outputAlphabet
  inputAlphabet := Equiv.refl A
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 100 * (Polynomial.X + Polynomial.C (pushC h1.tm + pushC h2.tm + 1) *
    (h1.time + h2.time) + 1) ^ 2
  outputsFun a := (tmm_run h1.tm h2.tm h1.inputAlphabet h2.inputAlphabet h1.outputAlphabet
    h2.outputAlphabet (ea a) (m₁ a) (m₂ a) _ _ _ _ (h1.outputsFun a) (h2.outputsFun a)
    (by have : (m₁ a + 1) * (m₂ a + 1) = m₁ a + m₂ a + m₁ a * m₂ a + 1 := by ring
        omega)
    (le_of_eq (by simp))).some

theorem tmm_poly {A : Type} [Inhabited A] [Fintype A] {α : Type} (ea : α → List A)
    (m₁ m₂ : α → ℕ) (h1 : Nonempty (TM2ComputableInPolyTime ea Computability.encodeNat m₁))
    (h2 : Nonempty (TM2ComputableInPolyTime ea Computability.encodeNat m₂)) :
    Nonempty (TM2ComputableInPolyTime ea Computability.encodeNat
      (fun a => (m₁ a + 1) * (m₂ a + 1) - 1)) :=
  ⟨tmmPoly ea m₁ m₂ h1.some h2.some⟩

end OCRS19TM


/-! L13: the machine for `TMD`. Input `w = P ++ R.map bitA ++ [sep] ++ S` (P ends in `sep`,
`S` has no `sep`). It runs `TM` (sampler range `m₁`) on `P`, computes `D = m₁ + 1`,
`R / D`, `R % D`, builds `P ++ enc(R % D) ++ [sep] ++ S` for `T1` and `P ++ enc(R / D) ++ [sep] ++ S`
for `T2`, runs both, and outputs the AND of their one-bit answers. Definitions only. -/

namespace OCRS19TM

open Turing

/-- own `A` stacks of the `TMD` machine -/
inductive SA
  | inp | rv | sS | sP
  deriving DecidableEq

scoped instance : Fintype SA :=
  Fintype.ofList [.inp, .rv, .sS, .sP] (by intro x; cases x <;> simp)

/-- own labels of the `TMD` machine -/
inductive OLd
  | rev | sS | sR | mvR | pre | cpP | oM | oMb | i1 | i2 | i3
  | dv | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | ct | ca | mvt
  | cx | rS | cS | sp | n1a | n1b | n1c | n1d | n2a | n2b | n2c | n2d | rP | cP
  | o1 | o2 | band | hlt
  deriving DecidableEq

scoped instance : Fintype OLd :=
  Fintype.ofList [.rev, .sS, .sR, .mvR, .pre, .cpP, .oM, .oMb, .i1, .i2, .i3,
    .dv, .d1, .d2, .d3, .d4, .d5, .d6, .d7, .d8, .ct, .ca, .mvt,
    .cx, .rS, .cS, .sp, .n1a, .n1b, .n1c, .n1d, .n2a, .n2b, .n2c, .n2d, .rP, .cP,
    .o1, .o2, .band, .hlt]
    (by intro x; cases x <;> simp)

/-- stop test for the split loops: empty stack or the separator -/
def isSep {A : Type} [DecidableEq A] (sep : A) : Option A → Bool
  | none => true
  | some a => decide (a = sep)

section TMD

variable (A : Type) [Inhabited A] [DecidableEq A] (TM T1 T2 : FinTM2)

/-- non-Bool stacks -/
abbrev RD : Type := SA ⊕ (TM.K ⊕ (T1.K ⊕ T2.K))

/-- their alphabets -/
abbrev GD (r : RD TM T1 T2) : Type :=
  Sum.casesOn (motive := fun _ => Type) r (fun _ => A)
    (fun r' => Sum.casesOn (motive := fun _ => Type) r' TM.Γ
      (fun r'' => Sum.casesOn (motive := fun _ => Type) r'' T1.Γ T2.Γ))

/-- labels -/
abbrev LD : Type := OLd ⊕ (TM.Λ ⊕ (T1.Λ ⊕ T2.Λ))

/-- non-register state: an `A` register and the three sub-states -/
abbrev ρD : Type := Option A × (TM.σ × (T1.σ × T2.σ))

abbrev StD : Type := TM2.Stmt (BΓ W (GD A TM T1 T2)) (LD TM T1 T2) (Reg × ρD A TM T1 T2)

/-- slot of the sampler-range machine -/
def slotM : Slot TM (W ⊕ RD TM T1 T2) (BΓ W (GD A TM T1 T2)) (LD TM T1 T2)
    (Reg × ρD A TM T1 T2) where
  kf k := Sum.inr (Sum.inr (Sum.inl k))
  kf_inj a b h := by simpa using h
  gin _ a := a
  gout _ a := a
  gout_gin _ _ := rfl
  sget v := v.2.2.1
  sset v s := (v.1, v.2.1, s, v.2.2.2)
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  lf l := Sum.inr (Sum.inl l)
  ret := Sum.inl OLd.oM

/-- slot of the first oracle -/
def slotT1 : Slot T1 (W ⊕ RD TM T1 T2) (BΓ W (GD A TM T1 T2)) (LD TM T1 T2)
    (Reg × ρD A TM T1 T2) where
  kf k := Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))
  kf_inj a b h := by simpa using h
  gin _ a := a
  gout _ a := a
  gout_gin _ _ := rfl
  sget v := v.2.2.2.1
  sset v s := (v.1, v.2.1, v.2.2.1, s, v.2.2.2.2)
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  lf l := Sum.inr (Sum.inr (Sum.inl l))
  ret := Sum.inl OLd.o1

/-- slot of the second oracle -/
def slotT2 : Slot T2 (W ⊕ RD TM T1 T2) (BΓ W (GD A TM T1 T2)) (LD TM T1 T2)
    (Reg × ρD A TM T1 T2) where
  kf k := Sum.inr (Sum.inr (Sum.inr (Sum.inr k)))
  kf_inj a b h := by simpa using h
  gin _ a := a
  gout _ a := a
  gout_gin _ _ := rfl
  sget v := v.2.2.2.2
  sset v s := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, s)
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  lf l := Sum.inr (Sum.inr (Sum.inr l))
  ret := Sum.inl OLd.o2

/-- update of the `A` register -/
def updAD (v : Reg × ρD A TM T1 T2) (o : Option A) : Reg × ρD A TM T1 T2 := (v.1, o, v.2.2)

/-- update of the first Bool register with a converted symbol -/
def updOD {Γ : Type} (o : Γ ≃ Bool) (v : Reg × ρD A TM T1 T2) (x : Option Γ) :
    Reg × ρD A TM T1 T2 :=
  ((x.map o, v.1.2.1, v.1.2.2), v.2)

/-- update of the first Bool register -/
def updBD (v : Reg × ρD A TM T1 T2) (x : Option Bool) : Reg × ρD A TM T1 T2 :=
  ((x, v.1.2.1, v.1.2.2), v.2)

variable (sep : A) (bitA : Bool → A) (decA : A → Bool)
  (eM : TM.Γ TM.k₀ ≃ A) (oM : TM.Γ TM.k₁ ≃ Bool)
  (e1 : T1.Γ T1.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (e2 : T2.Γ T2.k₀ ≃ A) (o2 : T2.Γ T2.k₁ ≃ Bool)

/-- the own code -/
def ownD : OLd → StD A TM T1 T2
  | .rev => TM2.Stmt.pop (Sum.inr (Sum.inl SA.inp)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.sS)
        (TM2.Stmt.push (Sum.inr (Sum.inl SA.rv)) (fun v => v.2.1.getD default)
          (TM2.Stmt.goto fun _ => Sum.inl OLd.rev)))
  | .sS => TM2.Stmt.pop (Sum.inr (Sum.inl SA.rv)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => isSep sep v.2.1) (TM2.Stmt.goto fun _ => Sum.inl OLd.sR)
        (TM2.Stmt.push (Sum.inr (Sum.inl SA.sS)) (fun v => v.2.1.getD default)
          (TM2.Stmt.goto fun _ => Sum.inl OLd.sS)))
  | .sR => TM2.Stmt.pop (Sum.inr (Sum.inl SA.rv)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => isSep sep v.2.1) (TM2.Stmt.goto fun _ => Sum.inl OLd.mvR)
        (TM2.Stmt.push (Sum.inl W.x1) (fun v => decA (v.2.1.getD default))
          (TM2.Stmt.goto fun _ => Sum.inl OLd.sR)))
  | .mvR => mvStmt W.x1 W.y (Sum.inl OLd.mvR) (Sum.inl OLd.pre)
  | .pre => TM2.Stmt.push (Sum.inr (Sum.inl SA.sP)) (fun _ => sep)
      (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inl TM.k₀))) (fun _ => eM.symm sep)
        (TM2.Stmt.goto fun _ => Sum.inl OLd.cpP))
  | .cpP => TM2.Stmt.pop (Sum.inr (Sum.inl SA.rv)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inr (Sum.inl TM.main))
        (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inl TM.k₀))) (fun v => eM.symm (v.2.1.getD default))
          (TM2.Stmt.push (Sum.inr (Sum.inl SA.sP)) (fun v => v.2.1.getD default)
            (TM2.Stmt.goto fun _ => Sum.inl OLd.cpP))))
  | .oM => TM2.Stmt.pop (Sum.inr (Sum.inr (Sum.inl TM.k₁))) (updOD A TM T1 T2 oM)
      (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.oMb)
        (TM2.Stmt.push (Sum.inl W.x1) (fun v => v.1.1.getD false)
          (TM2.Stmt.goto fun _ => Sum.inl OLd.oM)))
  | .oMb => mvStmt W.x1 W.x (Sum.inl OLd.oMb) (Sum.inl OLd.i1)
  | .i1 => TM2.Stmt.push (Sum.inl W.x2) (fun _ => true) (TM2.Stmt.goto fun _ => Sum.inl OLd.i2)
  | .i2 => addStmt W.x W.x2 W.t (Sum.inl OLd.i2) (Sum.inl OLd.i3)
  | .i3 => mvStmt W.t W.x (Sum.inl OLd.i3) (Sum.inl OLd.dv)
  | .dv => divStmt (Sum.inl OLd.cx) (Sum.inl OLd.d1)
  | .d1 => dupStmt W.acc W.x1 W.x2 (Sum.inl OLd.d1) (Sum.inl OLd.d2)
  | .d2 => mvStmt W.x1 W.acc (Sum.inl OLd.d2) (Sum.inl OLd.d3)
  | .d3 => mvStmt W.x2 W.x3 (Sum.inl OLd.d3) (Sum.inl OLd.d4)
  | .d4 => dupStmt W.x W.v W.x1 (Sum.inl OLd.d4) (Sum.inl OLd.d5)
  | .d5 => mvStmt W.v W.x (Sum.inl OLd.d5) (Sum.inl OLd.d6)
  | .d6 => mvStmt W.x1 W.x2 (Sum.inl OLd.d6) (Sum.inl OLd.d7)
  | .d7 => subStmt W.x3 W.x2 W.t (Sum.inl OLd.d7) (Sum.inl OLd.d8)
  | .d8 => decStmt (Sum.inl OLd.ct) (Sum.inl OLd.ca)
  | .ct => clearStmt W.t (Sum.inl OLd.ct) (Sum.inl OLd.dv)
  | .ca => clearStmt W.acc (Sum.inl OLd.ca) (Sum.inl OLd.mvt)
  | .mvt => mvStmt W.t W.acc (Sum.inl OLd.mvt) (Sum.inl OLd.dv)
  | .cx => clearStmt W.x (Sum.inl OLd.cx) (Sum.inl OLd.rS)
  | .rS => TM2.Stmt.pop (Sum.inr (Sum.inl SA.sS)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.cS)
        (TM2.Stmt.push (Sum.inr (Sum.inl SA.rv)) (fun v => v.2.1.getD default)
          (TM2.Stmt.goto fun _ => Sum.inl OLd.rS)))
  | .cS => TM2.Stmt.pop (Sum.inr (Sum.inl SA.rv)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.sp)
        (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₀))))
          (fun v => e1.symm (v.2.1.getD default))
          (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₀))))
            (fun v => e2.symm (v.2.1.getD default))
            (TM2.Stmt.goto fun _ => Sum.inl OLd.cS))))
  | .sp => TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₀)))) (fun _ => e1.symm sep)
      (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₀)))) (fun _ => e2.symm sep)
        (TM2.Stmt.goto fun _ => Sum.inl OLd.n1a))
  | .n1a => mvStmt W.acc W.t (Sum.inl OLd.n1a) (Sum.inl OLd.n1b)
  | .n1b => stripStmt W.t W.x2 (Sum.inl OLd.n1b) (Sum.inl OLd.n1c)
  | .n1c => mvStmt W.x2 W.x1 (Sum.inl OLd.n1c) (Sum.inl OLd.n1d)
  | .n1d => TM2.Stmt.pop (Sum.inl W.x1) (updBD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.n2a)
        (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₀))))
          (fun v => e1.symm (bitA (v.1.1.getD false)))
          (TM2.Stmt.goto fun _ => Sum.inl OLd.n1d)))
  | .n2a => mvStmt W.u W.t (Sum.inl OLd.n2a) (Sum.inl OLd.n2b)
  | .n2b => stripStmt W.t W.x2 (Sum.inl OLd.n2b) (Sum.inl OLd.n2c)
  | .n2c => mvStmt W.x2 W.x1 (Sum.inl OLd.n2c) (Sum.inl OLd.n2d)
  | .n2d => TM2.Stmt.pop (Sum.inl W.x1) (updBD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.rP)
        (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₀))))
          (fun v => e2.symm (bitA (v.1.1.getD false)))
          (TM2.Stmt.goto fun _ => Sum.inl OLd.n2d)))
  | .rP => TM2.Stmt.pop (Sum.inr (Sum.inl SA.sP)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.cP)
        (TM2.Stmt.push (Sum.inr (Sum.inl SA.rv)) (fun v => v.2.1.getD default)
          (TM2.Stmt.goto fun _ => Sum.inl OLd.rP)))
  | .cP => TM2.Stmt.pop (Sum.inr (Sum.inl SA.rv)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone)
        (TM2.Stmt.goto fun _ => Sum.inr (Sum.inr (Sum.inl T1.main)))
        (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₀))))
          (fun v => e1.symm (v.2.1.getD default))
          (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₀))))
            (fun v => e2.symm (v.2.1.getD default))
            (TM2.Stmt.goto fun _ => Sum.inl OLd.cP))))
  | .o1 => TM2.Stmt.pop (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₁)))) (updOD A TM T1 T2 o1)
      (TM2.Stmt.branch (fun v => v.1.1.isNone)
        (TM2.Stmt.goto fun _ => Sum.inr (Sum.inr (Sum.inr T2.main)))
        (TM2.Stmt.push (Sum.inl W.v) (fun v => v.1.1.getD false)
          (TM2.Stmt.goto fun _ => Sum.inl OLd.o1)))
  | .o2 => TM2.Stmt.pop (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₁)))) (updOD A TM T1 T2 o2)
      (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl OLd.band)
        (TM2.Stmt.push (Sum.inl W.t) (fun v => v.1.1.getD false)
          (TM2.Stmt.goto fun _ => Sum.inl OLd.o2)))
  | .band => TM2.Stmt.pop (Sum.inl W.v) (updBD A TM T1 T2)
      (TM2.Stmt.pop (Sum.inl W.t) (fun v x => ((v.1.1, x, v.1.2.2), v.2))
        (TM2.Stmt.push (Sum.inl W.out) (fun v => v.1.1.getD false && v.1.2.1.getD false)
          (TM2.Stmt.load (fun v => ((none, none, false), v.2))
            (TM2.Stmt.goto fun _ => Sum.inl OLd.hlt))))
  | .hlt => TM2.Stmt.halt

/-- the whole program -/
def progD : LD TM T1 T2 → StD A TM T1 T2
  | Sum.inl o => ownD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 o
  | Sum.inr (Sum.inl l) => (slotM A TM T1 T2).tr (TM.m l)
  | Sum.inr (Sum.inr (Sum.inl l)) => (slotT1 A TM T1 T2).tr (T1.m l)
  | Sum.inr (Sum.inr (Sum.inr l)) => (slotT2 A TM T1 T2).tr (T2.m l)

/-- the machine -/
def tmD [Fintype A] : FinTM2 where
  K := W ⊕ RD TM T1 T2
  kDecidableEq := inferInstance
  kFin := by letI := TM.kFin; letI := T1.kFin; letI := T2.kFin; exact inferInstance
  k₀ := Sum.inr (Sum.inl SA.inp)
  k₁ := Sum.inl W.out
  Γ := BΓ W (GD A TM T1 T2)
  Λ := LD TM T1 T2
  main := Sum.inl OLd.rev
  ΛFin := by letI := TM.ΛFin; letI := T1.ΛFin; letI := T2.ΛFin; exact inferInstance
  σ := Reg × ρD A TM T1 T2
  initialState := ((none, none, false), none, TM.initialState, T1.initialState, T2.initialState)
  σFin := by
    letI := TM.σFin; letI := T1.σFin; letI := T2.σFin; letI : Fintype A := ‹_›; exact inferInstance
  Γk₀Fin := (inferInstance : Fintype A)
  m := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2

lemma divProg_D : DivProg (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2) (Sum.inl OLd.dv)
    (Sum.inl OLd.d1) (Sum.inl OLd.d2) (Sum.inl OLd.d3) (Sum.inl OLd.d4) (Sum.inl OLd.d5)
    (Sum.inl OLd.d6) (Sum.inl OLd.d7) (Sum.inl OLd.d8) (Sum.inl OLd.ct) (Sum.inl OLd.ca)
    (Sum.inl OLd.mvt) (Sum.inl OLd.cx) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TMD

end OCRS19TM


/-! L14: `TMD` parse phase: split `P' ++ [sep] ++ R.map bitA ++ [sep] ++ S`, store `S`, `R`
(MSB-first on `y`), `P = P' ++ [sep]` (on `sP` and as the sampler input). -/

namespace OCRS19TM

open Turing

section TMDin

variable (A : Type) [Inhabited A] [DecidableEq A] (TM T1 T2 : FinTM2)
variable (sep : A) (bitA : Bool → A) (decA : A → Bool)
  (eM : TM.Γ TM.k₀ ≃ A) (oM : TM.Γ TM.k₁ ≃ Bool)
  (e1 : T1.Γ T1.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (e2 : T2.Γ T2.k₀ ≃ A) (o2 : T2.Γ T2.k₁ ≃ Bool)

lemma reach_gen {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    {M : Λ → TM2.Stmt Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {l : Option Λ} {v : σ} {S : ∀ k, List (Γ k)}
    {t : ℕ} (h : Reach M c ⟨l, v, S⟩ t) : ∃ S', S' = S ∧ Reach M c ⟨l, v, S'⟩ t :=
  ⟨S, rfl, h⟩

lemma phaseP (s : TM.σ × (T1.σ × T2.σ)) (oa : Option A) (B : W → List Bool)
    (Q : ∀ r, List (GD A TM T1 T2 r)) (P' S : List A) (R : List Bool)
    (hS : ∀ x ∈ S, x ≠ sep) (hbit : ∀ b, bitA b ≠ sep) (hdec : ∀ b, decA (bitA b) = b)
    (hin : Q (Sum.inl SA.inp) = P' ++ [sep] ++ R.map bitA ++ [sep] ++ S)
    (hrv : Q (Sum.inl SA.rv) = []) (hsS : Q (Sum.inl SA.sS) = []) (hsP : Q (Sum.inl SA.sP) = [])
    (hx1 : B W.x1 = []) (hy : B W.y = []) :
    ∃ Q' : ∀ r, List (GD A TM T1 T2 r),
      Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        ⟨some (Sum.inl OLd.rev), ((none, none, false), oa, s), mk B Q⟩
        ⟨some (Sum.inr (Sum.inl TM.main)), ((none, none, false), none, s),
          mk (Function.update B W.y R.reverse) Q'⟩
        (3 * (P'.length + R.length + S.length + 2) + 6) ∧
      Q' (Sum.inl SA.inp) = [] ∧ Q' (Sum.inl SA.rv) = [] ∧ Q' (Sum.inl SA.sS) = S ∧
      Q' (Sum.inl SA.sP) = P' ++ [sep] ++ Q (Sum.inl SA.sP) ∧
      Q' (Sum.inr (Sum.inl TM.k₀)) =
        (P' ++ [sep]).map eM.symm ++ Q (Sum.inr (Sum.inl TM.k₀)) ∧
      (∀ k, k ≠ TM.k₀ → Q' (Sum.inr (Sum.inl k)) = Q (Sum.inr (Sum.inl k))) ∧
      (∀ k, Q' (Sum.inr (Sum.inr k)) = Q (Sum.inr (Sum.inr k))) := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  set w := P' ++ [sep] ++ R.map bitA ++ [sep] ++ S with hw
  -- 1. reverse the input onto `rv`
  have r1 := transfer M (Sum.inl OLd.rev) (Sum.inr (Sum.inl SA.inp))
    (Sum.inr (Sum.inl SA.rv)) (by simp) (updAD A TM T1 T2) (fun v => v.2.1.isNone)
    (fun _ => Sum.inl OLd.sS) (fun v => v.2.1.getD default) id (fun _ => True) rfl
    (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) [] w (mk B Q) ((none, none, false), oa, s)
    (by simp) (by simp [hin, hw]) rfl
  -- 2. `S` (reversed twice) onto `sS`, stop at the last separator
  have r2 := r1.trans (transfer M (Sum.inl OLd.sS) (Sum.inr (Sum.inl SA.rv))
    (Sum.inr (Sum.inl SA.sS)) (by simp) (updAD A TM T1 T2) (fun v => isSep sep v.2.1)
    (fun _ => Sum.inl OLd.sR) (fun v => v.2.1.getD default) id (fun x => x ≠ sep) rfl
    (fun _ _ _ => rfl) (fun _ x hx => ⟨by simp [updAD, isSep, hx], rfl⟩)
    (sep :: ((R.map bitA).reverse ++ sep :: P'.reverse)) S.reverse _ _
    (by simpa using hS) (by simp [hw, hrv]) (by simp [updAD, isSep]))
  -- 3. the bits of `R` onto `x1` (decoded), stop at the separator ending `P`
  have r3 := r2.trans (transfer M (Sum.inl OLd.sR) (Sum.inr (Sum.inl SA.rv))
    (Sum.inl W.x1) (by simp) (updAD A TM T1 T2) (fun v => isSep sep v.2.1)
    (fun _ => Sum.inl OLd.mvR) (fun v => decA (v.2.1.getD default)) decA (fun x => x ≠ sep) rfl
    (fun _ _ _ => rfl) (fun _ x hx => ⟨by simp [updAD, isSep, hx], rfl⟩)
    (sep :: P'.reverse) (R.map bitA).reverse _ _
    (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx); exact hbit b)
    (by simp) (by simp [updAD, isSep]))
  obtain ⟨S3, hS3, r3'⟩ := reach_gen r3
  have f1 : ∀ a, a ≠ W.x1 → S3 (Sum.inl a) = B a := by
    intro a ha; rw [hS3]; simp [ha]
  have f2 : S3 (Sum.inl W.x1) = R := by
    rw [hS3]; simp [hx1, List.map_reverse, Function.comp_def, hdec]
  have hmk3 : S3 = mk (fun a => S3 (Sum.inl a)) (fun r => S3 (Sum.inr r)) :=
    mk_ext _ (fun _ => rfl) (fun _ => rfl)
  have r4 := (r3'.of_eq (c₂ := ⟨some (Sum.inl OLd.mvR), ((none, none, false), some sep, s),
    mk (fun a => S3 (Sum.inl a)) (fun r => S3 (Sum.inr r))⟩) (by rw [← hmk3]; rfl)).trans
    (mv_run M W.x1 W.y (by decide) (Sum.inl OLd.mvR) (Sum.inl OLd.pre) rfl (some sep, s) false
      (fun r => S3 (Sum.inr r)) R (fun a => S3 (Sum.inl a)) f2)
  have r5 := r4.trans (Reach.single (c' := ⟨some (Sum.inl OLd.cpP), _, _⟩) rfl)
  obtain ⟨S5, hS5, r5'⟩ := reach_gen r5
  have h5rv : S5 (Sum.inr (Sum.inl SA.rv)) = P'.reverse := by
    rw [hS5]; simp; rw [hS3]; simp
  obtain ⟨S6, r6, ka, kb, kc, kr⟩ := copy2 M (Sum.inl OLd.cpP) (Sum.inr (Sum.inl SA.rv))
    (Sum.inr (Sum.inr (Sum.inl TM.k₀))) (Sum.inr (Sum.inl SA.sP)) (by simp) (by simp) (by simp)
    (updAD A TM T1 T2) (fun v => v.2.1.isNone) (fun _ => Sum.inr (Sum.inl TM.main))
    (fun v => eM.symm (v.2.1.getD default)) (fun v => v.2.1.getD default) eM.symm id rfl
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) P'.reverse S5
    ((none, none, false), some sep, s) h5rv
  have hfin : S6 = mk (Function.update B W.y R.reverse) (fun r => S6 (Sum.inr r)) := by
    refine mk_ext _ (fun a => ?_) (fun _ => rfl)
    rw [kr (Sum.inl a) (by simp) (by simp) (by simp), hS5]
    simp only [Function.update_of_ne (show (Sum.inl a : W ⊕ RD TM T1 T2) ≠
      Sum.inr (Sum.inr (Sum.inl TM.k₀)) by simp), Function.update_of_ne (show
      (Sum.inl a : W ⊕ RD TM T1 T2) ≠ Sum.inr (Sum.inl SA.sP) by simp), mk_inl]
    by_cases hay : a = W.y
    · subst hay; simp [f1 W.y (by decide), hy]
    · by_cases hax : a = W.x1
      · subst hax; simp [hx1]
      · simp [Function.update_of_ne hay, Function.update_of_ne hax, f1 a hax]
  refine ⟨fun r => S6 (Sum.inr r), ((r5'.trans r6).of_eq (by rw [hfin]; rfl)).mono ?_,
    ?_, ka, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hw]
    omega
  · show S6 _ = _
    rw [kr _ (by simp) (by simp) (by simp), hS5]; simp; rw [hS3]; simp
  · show S6 _ = _
    rw [kr _ (by simp) (by simp) (by simp), hS5]; simp; rw [hS3]; simp [hsS]
  · show S6 _ = _
    rw [kc, hS5]; simp; rw [hS3]; simp
  · show S6 _ = _
    rw [kb, hS5]; simp; rw [hS3]; simp
  · intro k hk
    show S6 _ = _
    rw [kr _ (by simp) (by simpa using hk) (by simp), hS5]; simp [hk]; rw [hS3]; simp
  · intro k
    show S6 _ = _
    rw [kr _ (by simp) (by simp) (by simp), hS5]; simp; rw [hS3]; simp

end TMDin

end OCRS19TM


/-! L15: `TMD` middle phases: run the sampler-range machine (`x := enc m₁`), `x := x + 1`,
long division of `y` (MSB-first `R`) by `x`, clear `x`. -/

namespace OCRS19TM

open Turing

section TMDmid

variable (A : Type) [Inhabited A] [DecidableEq A] (TM T1 T2 : FinTM2)
variable (sep : A) (bitA : Bool → A) (decA : A → Bool)
  (eM : TM.Γ TM.k₀ ≃ A) (oM : TM.Γ TM.k₁ ≃ Bool)
  (e1 : T1.Γ T1.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (e2 : T2.Γ T2.k₀ ≃ A) (o2 : T2.Γ T2.k₁ ≃ Bool)

/-- run the sampler-range machine, its output (LSB on top) goes to `x` -/
lemma phaseM (oa : Option A) (s1 : T1.σ) (s2 : T2.σ) (B : W → List Bool)
    (Q : ∀ r, List (GD A TM T1 T2 r))
    (inp : List (TM.Γ TM.k₀)) (out : List Bool) (t : ℕ)
    (hrun : TM2OutputsInTime TM inp (some (out.map oM.symm)) t)
    (hQ : ∀ k, Q (Sum.inr (Sum.inl k)) = (initList TM inp).stk k)
    (hx1 : B W.x1 = []) (hx : B W.x = []) :
    ∃ Q' : ∀ r, List (GD A TM T1 T2 r),
      Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        ⟨some (Sum.inr (Sum.inl TM.main)), ((none, none, false), oa, TM.initialState, s1, s2),
          mk B Q⟩
        ⟨some (Sum.inl OLd.i1), ((none, none, false), oa, TM.initialState, s1, s2),
          mk (Function.update B W.x out) Q'⟩ (t + 2 * out.length + 2) ∧
      (∀ k, Q' (Sum.inr (Sum.inl k)) = []) ∧ (∀ b, Q' (Sum.inl b) = Q (Sum.inl b)) ∧
      (∀ k, Q' (Sum.inr (Sum.inr k)) = Q (Sum.inr (Sum.inr k))) := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  obtain ⟨S1, hR, r1⟩ := (slotM A TM T1 T2).sub_run M (fun _ => rfl)
    ((none, none, false), oa, TM.initialState, s1, s2) (mk B Q) (mk B Q) hrun
    ⟨fun k => by simp [slotM, hQ k], fun _ _ => rfl⟩
  have hk1 : S1 (Sum.inr (Sum.inr (Sum.inl TM.k₁))) = out.map oM.symm ++ [] := by
    have := hR.1 TM.k₁
    simp only [slotM] at this
    rw [this, haltList_stk_k1]
    simp
  have r2 := r1.trans (transfer M (Sum.inl OLd.oM)
    (Sum.inr (Sum.inr (Sum.inl TM.k₁))) (Sum.inl W.x1) (by simp) (updOD A TM T1 T2 oM)
    (fun v => v.1.1.isNone) (fun _ => Sum.inl OLd.oMb) (fun v => v.1.1.getD false) oM
    (fun _ => True) rfl (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) [] (out.map oM.symm) S1
    ((none, none, false), oa, TM.initialState, s1, s2) (by simp) hk1 rfl)
  have hfr : ∀ k', (∀ k, Sum.inr (Sum.inr (Sum.inl k)) ≠ k') → S1 k' = mk B Q k' := hR.2
  set S2 := Function.update (Function.update S1 (Sum.inr (Sum.inr (Sum.inl TM.k₁))) [].tail)
    (Sum.inl W.x1) (((out.map oM.symm).map oM).reverse ++ S1 (Sum.inl W.x1)) with hS2
  have hB2 : ∀ a, S2 (Sum.inl a) = Function.update B W.x1 out.reverse a := by
    intro a
    rw [hS2]
    by_cases ha : a = W.x1
    · subst ha
      rw [Function.update_self, hfr (Sum.inl W.x1) (by simp)]
      simp [hx1, Function.comp_def]
    · rw [Function.update_of_ne (fun e => ha (Sum.inl_injective e)), Function.update_of_ne (by simp),
        hfr (Sum.inl a) (by simp), Function.update_of_ne ha]
      rfl
  have hS2m : S2 = mk (Function.update B W.x1 out.reverse) (fun r => S2 (Sum.inr r)) :=
    mk_ext _ hB2 (fun _ => rfl)
  have r3 := (r2.of_eq (c₂ := ⟨some (Sum.inl OLd.oMb),
    ((none, none, false), oa, TM.initialState, s1, s2),
    mk (Function.update B W.x1 out.reverse) (fun r => S2 (Sum.inr r))⟩)
      (by rw [← hS2m]; rfl)).trans (mv_run M W.x1 W.x
    (by decide) (Sum.inl OLd.oMb) (Sum.inl OLd.i1) rfl _ false _ out.reverse _
    (by simp))
  refine ⟨fun r => S2 (Sum.inr r), (r3.of_eq ?_).mono ?_, ?_, ?_, ?_⟩
  · congr 2
    funext a
    by_cases ha : a = W.x1
    · subst ha; simp [hx1]
    by_cases hb : a = W.x
    · subst hb; simp [hx]
    · simp [Function.update_apply, ha, hb]
  · simp
    omega
  · intro k
    show S2 _ = []
    rw [hS2, Function.update_of_ne (by simp)]
    by_cases hk : k = TM.k₁
    · subst hk; simp
    · rw [Function.update_of_ne (by simpa using hk)]
      have := hR.1 k
      simp only [slotM] at this
      rw [this, haltList_stk_ne _ _ _ hk]
      simp
  · intro b
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      hfr (Sum.inr (Sum.inl b)) (by simp)]
    rfl
  · intro k
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simp),
      hfr (Sum.inr (Sum.inr (Sum.inr k))) (by simp)]
    rfl

/-- `x := x + 1` -/
lemma phaseI (r : ρD A TM T1 T2) (B : W → List Bool) (Q : ∀ r, List (GD A TM T1 T2 r))
    (hx2 : B W.x2 = []) (ht : B W.t = []) :
    Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
      ⟨some (Sum.inl OLd.i1), ((none, none, false), r), mk B Q⟩
      ⟨some (Sum.inl OLd.dv), ((none, none, false), r),
        mk (Function.update B W.x (addL false (B W.x) [true])) Q⟩
      (2 * (B W.x).length + 6) := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  have r1 : Reach M ⟨some (Sum.inl OLd.i1), ((none, none, false), r), mk B Q⟩
      ⟨some (Sum.inl OLd.i2), ((none, none, false), r), mk (Function.update B W.x2 [true]) Q⟩ 1 := by
    apply Reach.single
    rw [← update_mk]
    simp [M, TM2.step, TM2.stepAux, progD, ownD, hx2]
  have r2 := r1.trans (add_mk M W.x W.x2 W.t (by decide) (by decide) (by decide)
    (Sum.inl OLd.i2) (Sum.inl OLd.i3) rfl r false _ Q)
  have r3 := r2.trans (mv_run M W.t W.x (by decide) (Sum.inl OLd.i3) (Sum.inl OLd.dv) rfl r false Q
    _ _ rfl)
  refine (r3.of_eq ?_).mono ?_
  · congr 2
    funext a
    by_cases ha : a = W.x
    · subst ha; simp [hx2, ht]
    by_cases hb : a = W.x2
    · subst hb; simp [hx2]
    by_cases hc : a = W.t
    · subst hc; simp [ht]
    · simp [ha, hb, hc]
  · simp [length_addL, hx2, ht]
    omega

/-- long division `y / x`, remainder on `acc`, quotient on `u`, then clear `x` -/
lemma phaseDv (r : ρD A TM T1 T2) (B : W → List Bool) (Q : ∀ r, List (GD A TM T1 T2 r))
    (hx1 : B W.x1 = []) (hx2 : B W.x2 = []) (hx3 : B W.x3 = []) (ht : B W.t = [])
    (hv : B W.v = []) (hacc : B W.acc = []) (hu : B W.u = []) :
    Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
      ⟨some (Sum.inl OLd.dv), ((none, none, false), r), mk B Q⟩
      ⟨some (Sum.inl OLd.rS), ((none, none, false), r),
        mk (Function.update (Function.update (Function.update (Function.update B W.y []) W.acc
          (divLoop (B W.x) [] [] (B W.y)).1) W.u (divLoop (B W.x) [] [] (B W.y)).2) W.x []) Q⟩
      (divT (B W.x).length (B W.y).length + (B W.x).length + 1) := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  have r1 := div_loop (divProg_D A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2) r Q (B W.y) B
    (B W.x).length rfl hx1 hx2 hx3 ht hv (by simp [hacc]) le_rfl
  rw [hacc, hu] at r1
  have r2 := r1.trans (clear_mk M W.x (Sum.inl OLd.cx) (Sum.inl OLd.rS) rfl r false _ Q)
  refine r2.mono ?_
  simp only [Function.update_self, Function.update_of_ne (show W.x ≠ W.u by decide),
    Function.update_of_ne (show W.x ≠ W.acc by decide), Function.update_of_ne (show W.x ≠ W.y by decide)]
  omega

end TMDmid

end OCRS19TM


/-! L16: `TMD` query building: copy `S` (with a leading separator), the two numbers
(stripped, as `bitA` symbols) and `P` onto the input stacks of both oracles. -/

namespace OCRS19TM

open Turing

lemma reach_genB {Kb R : Type} [DecidableEq Kb] [DecidableEq R] {G : R → Type} {Λ σ : Type}
    {M : Λ → TM2.Stmt (BΓ Kb G) Λ σ} {c : TM2.Cfg (BΓ Kb G) Λ σ} {l : Option Λ} {v : σ}
    {B : Kb → List Bool} {Q : ∀ r, List (G r)} {t : ℕ}
    (h : Reach M c ⟨l, v, mk B Q⟩ t) : ∃ B', B' = B ∧ Reach M c ⟨l, v, mk B' Q⟩ t :=
  ⟨B, rfl, h⟩

lemma strip_rev (l : List Bool) : (strip l).reverse = l.reverse.dropWhile (fun b => !b) := by
  simp [strip]

lemma length_strip (l : List Bool) : (strip l).length ≤ l.length := by
  rw [strip, List.length_reverse]
  exact (List.dropWhile_suffix _).length_le.trans (by simp)

section TMDq

variable (A : Type) [Inhabited A] [DecidableEq A] (TM T1 T2 : FinTM2)
variable (sep : A) (bitA : Bool → A) (decA : A → Bool)
  (eM : TM.Γ TM.k₀ ≃ A) (oM : TM.Γ TM.k₁ ≃ Bool)
  (e1 : T1.Γ T1.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (e2 : T2.Γ T2.k₀ ≃ A) (o2 : T2.Γ T2.k₁ ≃ Bool)

/-- reverse an `A` stack onto `rv`, then copy it onto both oracle inputs -/
lemma rcblock (src : SA) (hsrc : src ≠ SA.rv) (L1 L2 : OLd) (Ln : LD TM T1 T2)
    (h1 : progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 (Sum.inl L1) =
      TM2.Stmt.pop (Sum.inr (Sum.inl src)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl L2)
        (TM2.Stmt.push (Sum.inr (Sum.inl SA.rv)) (fun v => v.2.1.getD default)
          (TM2.Stmt.goto fun _ => Sum.inl L1))))
    (h2 : progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 (Sum.inl L2) =
      TM2.Stmt.pop (Sum.inr (Sum.inl SA.rv)) (updAD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.2.1.isNone) (TM2.Stmt.goto fun _ => Ln)
        (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₀))))
          (fun v => e1.symm (v.2.1.getD default))
          (TM2.Stmt.push (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₀))))
            (fun v => e2.symm (v.2.1.getD default))
            (TM2.Stmt.goto fun _ => Sum.inl L2)))))
    (oa : Option A) (s : TM.σ × (T1.σ × T2.σ)) (B : W → List Bool)
    (Q : ∀ r, List (GD A TM T1 T2 r)) (X : List A)
    (hX : Q (Sum.inl src) = X) (hrv : Q (Sum.inl SA.rv) = []) :
    ∃ Q' : ∀ r, List (GD A TM T1 T2 r),
      Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        ⟨some (Sum.inl L1), ((none, none, false), oa, s), mk B Q⟩
        ⟨some Ln, ((none, none, false), none, s), mk B Q'⟩ (2 * X.length + 2) ∧
      Q' (Sum.inl src) = [] ∧ Q' (Sum.inl SA.rv) = [] ∧
      Q' (Sum.inr (Sum.inr (Sum.inl T1.k₀))) =
        X.map e1.symm ++ Q (Sum.inr (Sum.inr (Sum.inl T1.k₀))) ∧
      Q' (Sum.inr (Sum.inr (Sum.inr T2.k₀))) =
        X.map e2.symm ++ Q (Sum.inr (Sum.inr (Sum.inr T2.k₀))) ∧
      (∀ r, r ≠ Sum.inl src → r ≠ Sum.inl SA.rv → r ≠ Sum.inr (Sum.inr (Sum.inl T1.k₀)) →
        r ≠ Sum.inr (Sum.inr (Sum.inr T2.k₀)) → Q' r = Q r) := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  have r1 := transfer M (Sum.inl L1) (Sum.inr (Sum.inl src)) (Sum.inr (Sum.inl SA.rv))
    (by simpa using hsrc) (updAD A TM T1 T2) (fun v => v.2.1.isNone) (fun _ => Sum.inl L2)
    (fun v => v.2.1.getD default) id (fun _ => True) h1 (fun _ _ _ => rfl)
    (fun _ _ _ => ⟨rfl, rfl⟩) [] X (mk B Q) ((none, none, false), oa, s) (by simp) (by simp [hX])
    rfl
  obtain ⟨S1, hS1, r1'⟩ := reach_gen r1
  have h1rv : S1 (Sum.inr (Sum.inl SA.rv)) = X.reverse := by
    rw [hS1]; simp [hrv]
  obtain ⟨S2, r2, ka, kb, kc, kr⟩ := copy2 M (Sum.inl L2) (Sum.inr (Sum.inl SA.rv))
    (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₀)))) (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₀))))
    (by simp) (by simp) (by simp)
    (updAD A TM T1 T2) (fun v => v.2.1.isNone) (fun _ => Ln)
    (fun v => e1.symm (v.2.1.getD default)) (fun v => e2.symm (v.2.1.getD default)) e1.symm e2.symm
    h2 (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) X.reverse S1
    ((none, none, false), none, s) h1rv
  have hfin : S2 = mk B (fun r => S2 (Sum.inr r)) := by
    refine mk_ext _ (fun a => ?_) (fun _ => rfl)
    rw [kr (Sum.inl a) (by simp) (by simp) (by simp), hS1]
    simp
  refine ⟨fun r => S2 (Sum.inr r), ((r1'.trans r2).of_eq (by rw [hfin]; rfl)).mono ?_,
    ?_, ka, ?_, ?_, ?_⟩
  · simp
    omega
  · show S2 _ = _
    rw [kr _ (by simpa using hsrc) (by simp) (by simp), hS1]; simp [Function.update_apply, hsrc]
  · show S2 _ = _
    rw [kb, hS1]; simp
  · show S2 _ = _
    rw [kc, hS1]; simp
  · intro q q1 q2 q3 q4
    show S2 _ = _
    rw [kr _ (by simpa using q2) (by simpa using q3) (by simpa using q4), hS1]
    simp [q1, q2]

/-- strip a number, push it MSB-last (so LSB on top) onto an oracle input as `bitA` symbols -/
lemma nblock (src : W) (hs1 : src ≠ W.t) (hs2 : src ≠ W.x2) (hs3 : src ≠ W.x1)
    (La Lb Lc Ld Ln : OLd) (k : RD TM T1 T2) (f : Bool → GD A TM T1 T2 k)
    (ha : progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 (Sum.inl La) =
      mvStmt src W.t (Sum.inl La) (Sum.inl Lb))
    (hb : progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 (Sum.inl Lb) =
      stripStmt W.t W.x2 (Sum.inl Lb) (Sum.inl Lc))
    (hc : progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 (Sum.inl Lc) =
      mvStmt W.x2 W.x1 (Sum.inl Lc) (Sum.inl Ld))
    (hd : progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 (Sum.inl Ld) =
      TM2.Stmt.pop (Sum.inl W.x1) (updBD A TM T1 T2)
      (TM2.Stmt.branch (fun v => v.1.1.isNone) (TM2.Stmt.goto fun _ => Sum.inl Ln)
        (TM2.Stmt.push (Sum.inr k) (fun v => f (v.1.1.getD false))
          (TM2.Stmt.goto fun _ => Sum.inl Ld))))
    (r : ρD A TM T1 T2) (B : W → List Bool) (Q : ∀ r, List (GD A TM T1 T2 r))
    (hx1 : B W.x1 = []) (hx2 : B W.x2 = []) (ht : B W.t = []) :
    ∃ Q' : ∀ r, List (GD A TM T1 T2 r),
      Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        ⟨some (Sum.inl La), ((none, none, false), r), mk B Q⟩
        ⟨some (Sum.inl Ln), ((none, none, false), r), mk (Function.update B src []) Q'⟩
        (4 * (B src).length + 4) ∧
      Q' k = (strip (B src)).map f ++ Q k ∧ (∀ k', k' ≠ k → Q' k' = Q k') := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  have r1 := mv_run M src W.t hs1 (Sum.inl La) (Sum.inl Lb) ha r false Q (B src) B rfl
  have r2 := r1.trans (strip_mk M W.t W.x2 (by decide) (Sum.inl Lb) (Sum.inl Lc) hb r false _ Q)
  have r3 := r2.trans (mv_run M W.x2 W.x1 (by decide) (Sum.inl Lc) (Sum.inl Ld) hc r false Q _ _ rfl)
  obtain ⟨B3, hB3, r3'⟩ := reach_genB r3
  have hB3x1 : B3 W.x1 = (strip (B src)).reverse := by
    rw [hB3, strip_rev]
    simp [Function.update_apply, hs1, hs2, hs3, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3, hx1, hx2,
      ht, stripPush]
  have r4 := r3'.trans (transfer M (Sum.inl Ld) (Sum.inl W.x1) (Sum.inr k) (by simp)
    (updBD A TM T1 T2) (fun v => v.1.1.isNone) (fun _ => Sum.inl Ln)
    (fun v => f (v.1.1.getD false)) f (fun _ => True) hd (fun _ _ _ => rfl)
    (fun _ _ _ => ⟨rfl, rfl⟩) [] (strip (B src)).reverse (mk B3 Q) ((none, none, false), r)
    (by simp) (by simp [hB3x1]) rfl)
  refine ⟨Function.update Q k (((strip (B src)).reverse.map f).reverse ++ Q k),
    (r4.of_eq ?_).mono ?_, ?_, ?_⟩
  · have hBfin : Function.update B3 W.x1 [] = Function.update B src [] := by
      funext a
      rw [hB3]
      by_cases e1' : a = W.x1
      · subst e1'; simp [hs1, hs2, hs3, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3, hx1, hx2, ht]
      by_cases e2' : a = W.x2
      · subst e2'; simp [hs1, hs2, hs3, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3, hx1, hx2, ht, e1']
      by_cases e3' : a = W.t
      · subst e3'; simp [hs1, hs2, hs3, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3, hx1, hx2, ht, e1', e2']
      by_cases e4' : a = src
      · subst e4'; simp [hs1, hs2, hs3, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3, hx1, hx2, ht, e1', e2', e3']
      · simp [Function.update_apply, e1', e2', e3', e4']
    simp only [List.tail_nil, update_mk, mk_inr, update_mk_inr, hBfin]
    rfl
  · have hl := length_strip (B src)
    have hl2 : ((B src).reverse.dropWhile (fun b => !b)).length ≤ (B src).length :=
      (List.dropWhile_suffix _).length_le.trans (by simp)
    simp [Function.update_apply, hs1, hs2, hs3, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3, hx1, hx2,
      ht, stripPush]
    omega
  · simp [List.map_reverse]
  · intro k' hk'
    simp [Function.update_of_ne hk']

end TMDq

end OCRS19TM


/-! L17: `TMD` oracle runs (outputs to `v` and `t`), the AND step and the halt step. -/

namespace OCRS19TM

open Turing

section TMDo

variable (A : Type) [Inhabited A] [DecidableEq A] (TM T1 T2 : FinTM2)
variable (sep : A) (bitA : Bool → A) (decA : A → Bool)
  (eM : TM.Γ TM.k₀ ≃ A) (oM : TM.Γ TM.k₁ ≃ Bool)
  (e1 : T1.Γ T1.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (e2 : T2.Γ T2.k₀ ≃ A) (o2 : T2.Γ T2.k₁ ≃ Bool)

/-- run the first oracle, its output goes (reversed) to `v` -/
lemma phaseT1 (oa : Option A) (sM : TM.σ) (s2 : T2.σ) (B : W → List Bool)
    (Q : ∀ r, List (GD A TM T1 T2 r))
    (inp : List (T1.Γ T1.k₀)) (out : List Bool) (t : ℕ)
    (hrun : TM2OutputsInTime T1 inp (some (out.map o1.symm)) t)
    (hQ : ∀ k, Q (Sum.inr (Sum.inr (Sum.inl k))) = (initList T1 inp).stk k)
    (hv : B W.v = []) :
    ∃ Q' : ∀ r, List (GD A TM T1 T2 r),
      Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        ⟨some (Sum.inr (Sum.inr (Sum.inl T1.main))),
          ((none, none, false), oa, sM, T1.initialState, s2), mk B Q⟩
        ⟨some (Sum.inr (Sum.inr (Sum.inr T2.main))),
          ((none, none, false), oa, sM, T1.initialState, s2),
          mk (Function.update B W.v out.reverse) Q'⟩ (t + out.length + 1) ∧
      (∀ k, Q' (Sum.inr (Sum.inr (Sum.inl k))) = []) ∧
      (∀ r, (∀ k, r ≠ Sum.inr (Sum.inr (Sum.inl k))) → Q' r = Q r) := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  obtain ⟨S1, hR, r1⟩ := (slotT1 A TM T1 T2).sub_run M (fun _ => rfl)
    ((none, none, false), oa, sM, T1.initialState, s2) (mk B Q) (mk B Q) hrun
    ⟨fun k => by simp [slotT1, hQ k], fun _ _ => rfl⟩
  have hk1 : S1 (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₁)))) = out.map o1.symm ++ [] := by
    have := hR.1 T1.k₁
    simp only [slotT1] at this
    rw [this, haltList_stk_k1]
    simp
  have r2 := r1.trans (transfer M (Sum.inl OLd.o1)
    (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₁)))) (Sum.inl W.v) (by simp) (updOD A TM T1 T2 o1)
    (fun v => v.1.1.isNone) (fun _ => Sum.inr (Sum.inr (Sum.inr T2.main)))
    (fun v => v.1.1.getD false) o1
    (fun _ => True) rfl (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) [] (out.map o1.symm) S1
    ((none, none, false), oa, sM, T1.initialState, s2) (by simp) hk1 rfl)
  have hfr : ∀ k', (∀ k, Sum.inr (Sum.inr (Sum.inr (Sum.inl k))) ≠ k') → S1 k' = mk B Q k' :=
    hR.2
  set S2 := Function.update (Function.update S1 (Sum.inr (Sum.inr (Sum.inr (Sum.inl T1.k₁))))
    [].tail) (Sum.inl W.v) (((out.map o1.symm).map o1).reverse ++ S1 (Sum.inl W.v)) with hS2
  have hB2 : ∀ a, S2 (Sum.inl a) = Function.update B W.v out.reverse a := by
    intro a
    rw [hS2]
    by_cases ha : a = W.v
    · subst ha
      rw [Function.update_self, hfr (Sum.inl W.v) (by simp)]
      simp [hv, Function.comp_def]
    · rw [Function.update_of_ne (fun e => ha (Sum.inl_injective e)), Function.update_of_ne (by simp),
        hfr (Sum.inl a) (by simp), Function.update_of_ne ha]
      rfl
  have hS2m : S2 = mk (Function.update B W.v out.reverse) (fun r => S2 (Sum.inr r)) :=
    mk_ext _ hB2 (fun _ => rfl)
  refine ⟨fun r => S2 (Sum.inr r), (r2.of_eq ?_).mono ?_, ?_, ?_⟩
  · rw [← hS2m]; rfl
  · simp
    omega
  · intro k
    show S2 _ = []
    rw [hS2, Function.update_of_ne (by simp)]
    by_cases hk : k = T1.k₁
    · subst hk; simp
    · rw [Function.update_of_ne (by simpa using hk)]
      have := hR.1 k
      simp only [slotT1] at this
      rw [this, haltList_stk_ne _ _ _ hk]
      simp
  · intro q hq
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simpa using hq _),
      hfr (Sum.inr q) (by intro k e; exact hq k (Sum.inr_injective e).symm)]
    rfl

/-- run the second oracle, its output goes (reversed) to `t` -/
lemma phaseT2 (oa : Option A) (sM : TM.σ) (s1 : T1.σ) (B : W → List Bool)
    (Q : ∀ r, List (GD A TM T1 T2 r))
    (inp : List (T2.Γ T2.k₀)) (out : List Bool) (t : ℕ)
    (hrun : TM2OutputsInTime T2 inp (some (out.map o2.symm)) t)
    (hQ : ∀ k, Q (Sum.inr (Sum.inr (Sum.inr k))) = (initList T2 inp).stk k)
    (ht : B W.t = []) :
    ∃ Q' : ∀ r, List (GD A TM T1 T2 r),
      Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        ⟨some (Sum.inr (Sum.inr (Sum.inr T2.main))),
          ((none, none, false), oa, sM, s1, T2.initialState), mk B Q⟩
        ⟨some (Sum.inl OLd.band),
          ((none, none, false), oa, sM, s1, T2.initialState),
          mk (Function.update B W.t out.reverse) Q'⟩ (t + out.length + 1) ∧
      (∀ k, Q' (Sum.inr (Sum.inr (Sum.inr k))) = []) ∧
      (∀ r, (∀ k, r ≠ Sum.inr (Sum.inr (Sum.inr k))) → Q' r = Q r) := by
  set M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 with hMdef
  obtain ⟨S1, hR, r1⟩ := (slotT2 A TM T1 T2).sub_run M (fun _ => rfl)
    ((none, none, false), oa, sM, s1, T2.initialState) (mk B Q) (mk B Q) hrun
    ⟨fun k => by simp [slotT2, hQ k], fun _ _ => rfl⟩
  have hk1 : S1 (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₁)))) = out.map o2.symm ++ [] := by
    have := hR.1 T2.k₁
    simp only [slotT2] at this
    rw [this, haltList_stk_k1]
    simp
  have r2 := r1.trans (transfer M (Sum.inl OLd.o2)
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₁)))) (Sum.inl W.t) (by simp) (updOD A TM T1 T2 o2)
    (fun v => v.1.1.isNone) (fun _ => Sum.inl OLd.band)
    (fun v => v.1.1.getD false) o2
    (fun _ => True) rfl (fun _ _ _ => rfl) (fun _ _ _ => ⟨rfl, rfl⟩) [] (out.map o2.symm) S1
    ((none, none, false), oa, sM, s1, T2.initialState) (by simp) hk1 rfl)
  have hfr : ∀ k', (∀ k, Sum.inr (Sum.inr (Sum.inr (Sum.inr k))) ≠ k') → S1 k' = mk B Q k' :=
    hR.2
  set S2 := Function.update (Function.update S1 (Sum.inr (Sum.inr (Sum.inr (Sum.inr T2.k₁))))
    [].tail) (Sum.inl W.t) (((out.map o2.symm).map o2).reverse ++ S1 (Sum.inl W.t)) with hS2
  have hB2 : ∀ a, S2 (Sum.inl a) = Function.update B W.t out.reverse a := by
    intro a
    rw [hS2]
    by_cases ha : a = W.t
    · subst ha
      rw [Function.update_self, hfr (Sum.inl W.t) (by simp)]
      simp [ht, Function.comp_def]
    · rw [Function.update_of_ne (fun e => ha (Sum.inl_injective e)), Function.update_of_ne (by simp),
        hfr (Sum.inl a) (by simp), Function.update_of_ne ha]
      rfl
  have hS2m : S2 = mk (Function.update B W.t out.reverse) (fun r => S2 (Sum.inr r)) :=
    mk_ext _ hB2 (fun _ => rfl)
  refine ⟨fun r => S2 (Sum.inr r), (r2.of_eq ?_).mono ?_, ?_, ?_⟩
  · rw [← hS2m]; rfl
  · simp
    omega
  · intro k
    show S2 _ = []
    rw [hS2, Function.update_of_ne (by simp)]
    by_cases hk : k = T2.k₁
    · subst hk; simp
    · rw [Function.update_of_ne (by simpa using hk)]
      have := hR.1 k
      simp only [slotT2] at this
      rw [this, haltList_stk_ne _ _ _ hk]
      simp
  · intro q hq
    show S2 _ = _
    rw [hS2, Function.update_of_ne (by simp), Function.update_of_ne (by simpa using hq _),
      hfr (Sum.inr q) (by intro k e; exact hq k (Sum.inr_injective e).symm)]
    rfl

/-- the AND step and the halt step -/
lemma phaseB (r : ρD A TM T1 T2) (B : W → List Bool) (Q : ∀ r, List (GD A TM T1 T2 r))
    (b1 b2 : Bool) (hv : B W.v = [b1]) (ht : B W.t = [b2]) :
    Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
      ⟨some (Sum.inl OLd.band), ((none, none, false), r), mk B Q⟩
      ⟨none, ((none, none, false), r), mk (Function.update (Function.update (Function.update B
        W.v []) W.t []) W.out ((b1 && b2) :: B W.out)) Q⟩ 2 := by
  have r1 := Reach.single (M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
    (c := ⟨some (Sum.inl OLd.band), ((none, none, false), r), mk B Q⟩)
    (c' := ⟨some (Sum.inl OLd.hlt), _, _⟩) rfl
  have r2 := r1.trans (Reach.single (c' := ⟨none, _, _⟩) rfl)
  refine r2.of_eq ?_
  simp [hv, ht, updBD]

end TMDo

end OCRS19TM


/-! L18: the whole `TMD` run. -/

namespace OCRS19TM

open Turing

lemma polyMono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

section TMDrun

variable (A : Type) [Inhabited A] [DecidableEq A] (TM T1 T2 : FinTM2)
variable (sep : A) (bitA : Bool → A) (decA : A → Bool)
  (eM : TM.Γ TM.k₀ ≃ A) (oM : TM.Γ TM.k₁ ≃ Bool)
  (e1 : T1.Γ T1.k₀ ≃ A) (o1 : T1.Γ T1.k₁ ≃ Bool)
  (e2 : T2.Γ T2.k₀ ≃ A) (o2 : T2.Γ T2.k₁ ≃ Bool)

lemma sp_step (v : Reg × ρD A TM T1 T2) (B : W → List Bool) (Q : ∀ r, List (GD A TM T1 T2 r)) :
    ∃ Q' : ∀ r, List (GD A TM T1 T2 r),
      Reach (progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        ⟨some (Sum.inl OLd.sp), v, mk B Q⟩ ⟨some (Sum.inl OLd.n1a), v, mk B Q'⟩ 1 ∧
      Q' (Sum.inr (Sum.inr (Sum.inl T1.k₀))) = e1.symm sep :: Q (Sum.inr (Sum.inr (Sum.inl T1.k₀))) ∧
      Q' (Sum.inr (Sum.inr (Sum.inr T2.k₀))) = e2.symm sep :: Q (Sum.inr (Sum.inr (Sum.inr T2.k₀))) ∧
      (∀ r, r ≠ Sum.inr (Sum.inr (Sum.inl T1.k₀)) → r ≠ Sum.inr (Sum.inr (Sum.inr T2.k₀)) →
        Q' r = Q r) := by
  obtain ⟨S, hS, r⟩ := reach_gen (Reach.single
    (M := progD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
    (c := ⟨some (Sum.inl OLd.sp), v, mk B Q⟩) (c' := ⟨some (Sum.inl OLd.n1a), _, _⟩) rfl)
  have hm : S = mk B (fun r => S (Sum.inr r)) := mk_ext _ (fun a => by rw [hS]; simp) (fun _ => rfl)
  refine ⟨fun r => S (Sum.inr r), r.of_eq (by rw [← hm]), ?_, ?_, ?_⟩
  · show S _ = _
    rw [hS]; simp
  · show S _ = _
    rw [hS]; simp
  · intro q h1 h2
    show S _ = _
    rw [hS]; simp [h1, h2]

lemma tmd_halt [Fintype A] (out : List Bool) (B : W → List Bool) (Q : ∀ r, List (GD A TM T1 T2 r))
    (hB : B W.out = out) (hB' : ∀ a, a ≠ W.out → B a = []) (hQ : ∀ r, Q r = []) :
    (⟨none, ((none, none, false), none, TM.initialState, T1.initialState, T2.initialState),
      mk B Q⟩ : TM2.Cfg (BΓ W (GD A TM T1 T2)) (LD TM T1 T2) (Reg × ρD A TM T1 T2)) =
      haltList (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        (List.map (Equiv.refl Bool).invFun out) := by
  apply cfg_eq_haltList (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2) _ _ rfl rfl
  · exact hB.trans (List.map_id out).symm
  · intro k hk
    rcases k with a | r
    · exact hB' a (fun h => hk (by rw [h]; rfl))
    · exact hQ r

lemma tmd_arith (a r s e tM t1 t2 c m q W : ℕ) (hW : W = a + r + s + 2) (he : e ≤ a + 1 + c * tM)
    (hm : m ≤ max e 1 + 1 + r) (hq : q = r) :
    3 * (a + r + s + 2) + 6 + (tM + 2 * e + 2 + (2 * e + 6 + (divT (max e 1 + 1) r +
      (max e 1 + 1) + 1 + (2 * s + 2 + (1 + (4 * m + 4 + (4 * q + 4 + (2 * (a + 1) + 2 +
      (t1 + 1 + 1 + (t2 + 1 + 1 + 2)))))))))) ≤
      100 * (W + (c + 1) * (tM + t1 + t2) + 1) ^ 2 := by
  have hx : max e 1 ≤ e + 1 := max_le (by omega) (by omega)
  generalize max e 1 = x at *
  have h1 : c * tM ≤ (c + 1) * (tM + t1 + t2) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : tM + t1 + t2 ≤ (c + 1) * (tM + t1 + t2) := Nat.le_mul_of_pos_left _ (by omega)
  generalize hL : W + (c + 1) * (tM + t1 + t2) = L
  have heL : e ≤ L := by omega
  have hrL : a + r + s + 2 ≤ L := by omega
  have htL : tM + t1 + t2 ≤ L := by omega
  have hdiv : divT (x + 1) r ≤ (L + 1) * (20 * L + 60) := by
    unfold divT; exact Nat.mul_le_mul (by omega) (by omega)
  nlinarith

lemma tmd_run [Fintype A] (P' S : List A) (R : List Bool) (nM tM t1 t2 T : ℕ) (b1 b2 : Bool)
    (hS : ∀ x ∈ S, x ≠ sep) (hbit : ∀ b, bitA b ≠ sep) (hdec : ∀ b, decA (bitA b) = b)
    (hrM : TM2OutputsInTime TM ((P' ++ [sep]).map eM.symm)
      (some ((Computability.encodeNat nM).map oM.symm)) tM)
    (hr1 : TM2OutputsInTime T1 ((P' ++ [sep] ++
      (Computability.encodeNat (val R % (nM + 1))).map bitA ++ [sep] ++ S).map e1.symm)
      (some ([b1].map o1.symm)) t1)
    (hr2 : TM2OutputsInTime T2 ((P' ++ [sep] ++
      (Computability.encodeNat (val R / (nM + 1))).map bitA ++ [sep] ++ S).map e2.symm)
      (some ([b2].map o2.symm)) t2)
    (hT : 100 * ((P' ++ [sep] ++ R.map bitA ++ [sep] ++ S).length +
      (pushC TM + 1) * (tM + t1 + t2) + 1) ^ 2 ≤ T) :
    Nonempty (TM2OutputsInTime (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
      ((P' ++ [sep] ++ R.map bitA ++ [sep] ++ S).map (Equiv.refl A).invFun)
      (some ([b1 && b2].map (Equiv.refl Bool).invFun)) T) := by
  have hlM := out_len TM hrM
  simp only [List.length_map] at hlM
  set w := P' ++ [sep] ++ R.map bitA ++ [sep] ++ S with hw
  let Q0 : ∀ r, List (GD A TM T1 T2 r) := Function.update (fun _ => []) (Sum.inl SA.inp) w
  have hQ0 : ∀ r, r ≠ Sum.inl SA.inp → Q0 r = [] := fun r hr => by
    simp only [Q0]; rw [Function.update_of_ne hr]
  obtain ⟨Q1, R1, q1inp, q1rv, q1sS, q1sP, q1k0, q1TM, q1T⟩ := phaseP A TM T1 T2 sep bitA decA
    eM oM e1 o1 e2 o2 (TM.initialState, T1.initialState, T2.initialState) none (fun _ => []) Q0
    P' S R hS hbit hdec (by simp [Q0, hw]) (hQ0 _ (by simp)) (hQ0 _ (by simp)) (hQ0 _ (by simp))
    rfl rfl
  have hQM : ∀ k, Q1 (Sum.inr (Sum.inl k)) = (initList TM ((P' ++ [sep]).map eM.symm)).stk k := by
    intro k
    by_cases hk : k = TM.k₀
    · subst hk; rw [q1k0, initList_stk_k0, hQ0 _ (by simp)]; simp
    · rw [q1TM k hk, initList_stk_ne TM _ k hk, hQ0 _ (by simp)]
  obtain ⟨Q2, R2, q2TM, q2B, q2T⟩ := phaseM A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 none
    T1.initialState T2.initialState (Function.update (fun _ => []) W.y R.reverse) Q1
    ((P' ++ [sep]).map eM.symm) (Computability.encodeNat nM) tM hrM hQM (by simp) (by simp)
  have R3 := phaseI A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2
    (none, TM.initialState, T1.initialState, T2.initialState)
    (Function.update (Function.update (fun _ => []) W.y R.reverse) W.x
      (Computability.encodeNat nM)) Q2 (by simp) (by simp)
  obtain ⟨B3, hB3, R3'⟩ := reach_genB R3
  have R4 := phaseDv A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2
    (none, TM.initialState, T1.initialState, T2.initialState) B3 Q2
    (by rw [hB3]; simp) (by rw [hB3]; simp) (by rw [hB3]; simp) (by rw [hB3]; simp)
    (by rw [hB3]; simp) (by rw [hB3]; simp) (by rw [hB3]; simp)
  obtain ⟨B4, hB4, R4'⟩ := reach_genB R4
  obtain ⟨Q5, R5, q5sS, q5rv, q5T1, q5T2, q5o⟩ := rcblock A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2
    SA.sS (by decide) OLd.rS OLd.cS (Sum.inl OLd.sp) rfl rfl none
    (TM.initialState, T1.initialState, T2.initialState) B4 Q2 S
    (by rw [q2B]; exact q1sS) (by rw [q2B]; exact q1rv)
  obtain ⟨Q6, R6, q6T1, q6T2, q6o⟩ := sp_step A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2
    ((none, none, false), none, TM.initialState, T1.initialState, T2.initialState) B4 Q5
  obtain ⟨Q7, R7, q7k, q7o⟩ := nblock A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 W.acc
    (by decide) (by decide) (by decide) OLd.n1a OLd.n1b OLd.n1c OLd.n1d OLd.n2a
    (Sum.inr (Sum.inr (Sum.inl T1.k₀))) (fun b => e1.symm (bitA b)) rfl rfl rfl rfl
    (none, TM.initialState, T1.initialState, T2.initialState) B4 Q6
    (by rw [hB4, hB3]; simp) (by rw [hB4, hB3]; simp) (by rw [hB4, hB3]; simp)
  obtain ⟨Q8, R8, q8k, q8o⟩ := nblock A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 W.u
    (by decide) (by decide) (by decide) OLd.n2a OLd.n2b OLd.n2c OLd.n2d OLd.rP
    (Sum.inr (Sum.inr (Sum.inr T2.k₀))) (fun b => e2.symm (bitA b)) rfl rfl rfl rfl
    (none, TM.initialState, T1.initialState, T2.initialState)
    (Function.update B4 W.acc []) Q7 (by rw [hB4, hB3]; simp) (by rw [hB4, hB3]; simp) (by rw [hB4, hB3]; simp)
  have h8sP : Q8 (Sum.inl SA.sP) = P' ++ [sep] := by
    rw [q8o _ (by simp), q7o _ (by simp), q6o _ (by simp) (by simp),
      q5o _ (by simp) (by simp) (by simp) (by simp), q2B, q1sP, hQ0 _ (by simp)]
    simp
  have h8rv : Q8 (Sum.inl SA.rv) = [] := by
    rw [q8o _ (by simp), q7o _ (by simp), q6o _ (by simp) (by simp), q5rv]
  obtain ⟨Q9, R9, q9sP, q9rv, q9T1, q9T2, q9o⟩ := rcblock A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2
    SA.sP (by decide) OLd.rP OLd.cP (Sum.inr (Sum.inr (Sum.inl T1.main))) rfl rfl none
    (TM.initialState, T1.initialState, T2.initialState)
    (Function.update (Function.update B4 W.acc []) W.u []) Q8 (P' ++ [sep]) h8sP h8rv
  have hD : val (addL false (Computability.encodeNat nM) [true]) = nM + 1 := by
    simp [val_addL, val_encodeNat, val]
  have hrem : strip (B4 W.acc) = Computability.encodeNat (val R % (nM + 1)) := by
    rw [← encodeNat_val, hB4, hB3]
    simp only [Function.update_self, Function.update_of_ne (show W.acc ≠ W.x by decide),
      Function.update_of_ne (show W.acc ≠ W.u by decide), Function.update_of_ne
        (show W.x ≠ W.y by decide), Function.update_of_ne (show W.y ≠ W.x by decide)]
    rw [(divLoop_divmod _ _ (by rw [hD]; omega)).2, valM_reverse, hD]
  have hquo : strip (B4 W.u) = Computability.encodeNat (val R / (nM + 1)) := by
    rw [← encodeNat_val, hB4, hB3]
    simp only [Function.update_self, Function.update_of_ne (show W.u ≠ W.x by decide),
      Function.update_of_ne (show W.x ≠ W.y by decide), Function.update_of_ne
        (show W.y ≠ W.x by decide)]
    rw [(divLoop_divmod _ _ (by rw [hD]; omega)).1, valM_reverse, hD]
  have hQT1 : ∀ k, Q9 (Sum.inr (Sum.inr (Sum.inl k))) = (initList T1 ((P' ++ [sep] ++
      (Computability.encodeNat (val R % (nM + 1))).map bitA ++ [sep] ++ S).map e1.symm)).stk k := by
    intro k
    by_cases hk : k = T1.k₀
    · subst hk
      rw [q9T1, q8o _ (by simp), q7k, q6T1, q5T1, q2T, q1T, hQ0 _ (by simp), initList_stk_k0,
        hrem]
      simp
    · have hk' : (Sum.inr (Sum.inr (Sum.inl k)) : RD TM T1 T2) ≠ Sum.inr (Sum.inr (Sum.inl T1.k₀)) :=
        by simpa using hk
      rw [q9o _ (by simp) (by simp) hk' (by simp), q8o _ (by simp), q7o _ hk',
        q6o _ hk' (by simp), q5o _ (by simp) (by simp) hk' (by simp), q2T, q1T, hQ0 _ (by simp),
        initList_stk_ne T1 _ k hk]
  obtain ⟨Q10, R10, q10T1, q10o⟩ := phaseT1 A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 none
    TM.initialState T2.initialState (Function.update (Function.update B4 W.acc []) W.u []) Q9 _
    [b1] t1 hr1 hQT1 (by rw [hB4, hB3]; simp)
  have hQT2 : ∀ k, Q10 (Sum.inr (Sum.inr (Sum.inr k))) = (initList T2 ((P' ++ [sep] ++
      (Computability.encodeNat (val R / (nM + 1))).map bitA ++ [sep] ++ S).map e2.symm)).stk k := by
    intro k
    rw [q10o _ (fun k' => by simp)]
    by_cases hk : k = T2.k₀
    · subst hk
      rw [q9T2, q8k, q7o _ (by simp), q6T2, q5T2, q2T, q1T, hQ0 _ (by simp), initList_stk_k0,
        Function.update_of_ne (show W.u ≠ W.acc by decide), hquo]
      simp
    · have hk' : (Sum.inr (Sum.inr (Sum.inr k)) : RD TM T1 T2) ≠ Sum.inr (Sum.inr (Sum.inr T2.k₀)) :=
        by simpa using hk
      rw [q9o _ (by simp) (by simp) (by simp) hk', q8o _ hk', q7o _ (by simp),
        q6o _ (by simp) hk', q5o _ (by simp) (by simp) (by simp) hk', q2T, q1T, hQ0 _ (by simp),
        initList_stk_ne T2 _ k hk]
  obtain ⟨Q11, R11, q11T2, q11o⟩ := phaseT2 A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2 none
    TM.initialState T1.initialState
    (Function.update (Function.update (Function.update B4 W.acc []) W.u []) W.v [b1].reverse) Q10
    _ [b2] t2 hr2 hQT2 (by rw [hB4, hB3]; simp)
  have R12 := phaseB A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2
    (none, TM.initialState, T1.initialState, T2.initialState)
    (Function.update (Function.update (Function.update (Function.update B4 W.acc []) W.u [])
      W.v [b1].reverse) W.t [b2].reverse) Q11 b1 b2 (by simp) (by simp)
  have R := R1.trans (R2.trans (R3'.trans (R4'.trans (R5.trans (R6.trans (R7.trans (R8.trans
    (R9.trans (R10.trans (R11.trans R12))))))))))
  have h0 : initList (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
      (List.map (Equiv.refl A).invFun w) = ⟨some (Sum.inl OLd.rev),
      ((none, none, false), none, TM.initialState, T1.initialState, T2.initialState),
      mk (fun _ => []) Q0⟩ := by
    have e : (initList (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2)
        (List.map (Equiv.refl A).invFun w)).stk = mk (fun _ => []) Q0 := by
      funext k
      rcases k with a | r
      · exact initList_stk_ne (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2) _ (Sum.inl a)
          (fun h => Sum.inl_ne_inr h)
      · by_cases hr : r = Sum.inl SA.inp
        · subst hr
          refine (initList_stk_k0 (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2) _).trans ?_
          exact List.map_id w
        · refine (initList_stk_ne (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2) _ (Sum.inr r)
            (fun h => hr (Sum.inr_injective h))).trans ?_
          exact (hQ0 r hr).symm
    rw [← e]; rfl
  obtain ⟨k, hk, e⟩ := R
  refine ⟨⟨⟨k, ?_⟩, hk.trans ?_⟩⟩
  · rw [h0]
    change _ = some (haltList (tmD A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2) _)
    refine e.trans (congrArg some ?_)
    apply tmd_halt A TM T1 T2 sep bitA decA eM oM e1 o1 e2 o2
    · simp only [Function.update_self]
      rw [hB4, hB3]
      simp
    · intro a ha
      rw [Function.update_of_ne ha, hB4, hB3]
      cases a <;> simp at ha ⊢
    · intro r
      · show Q11 r = []
        rcases r with sa | k | k | k
        · rw [q11o _ (fun k => by simp), q10o _ (fun k => by simp)]
          cases sa
          · rw [q9o _ (by simp) (by simp) (by simp) (by simp), q8o _ (by simp), q7o _ (by simp),
              q6o _ (by simp) (by simp), q5o _ (by simp) (by simp) (by simp) (by simp), q2B,
              q1inp]
          · exact q9rv
          · rw [q9o _ (by simp) (by simp) (by simp) (by simp), q8o _ (by simp), q7o _ (by simp),
              q6o _ (by simp) (by simp), q5sS]
          · exact q9sP
        · rw [q11o _ (fun k => by simp), q10o _ (fun k => by simp),
            q9o _ (by simp) (by simp) (by simp) (by simp), q8o _ (by simp), q7o _ (by simp),
            q6o _ (by simp) (by simp), q5o _ (by simp) (by simp) (by simp) (by simp), q2TM]
        · rw [q11o _ (fun k => by simp), q10T1]
        · exact q11T2 k
  · have hl1 := (divLoop_len (addL false (Computability.encodeNat nM) [true]) R.reverse [] []).1
    have hl2 := (divLoop_len (addL false (Computability.encodeNat nM) [true]) R.reverse [] []).2
    refine le_trans ?_ hT
    rw [hB4, hB3]
    simp [Function.update_apply, length_addL] at hl1 hl2 ⊢
    exact tmd_arith _ _ _ _ _ _ _ _ _ _ _ (by simp [hw]; omega) (by simpa using hlM) hl1 hl2

end TMDrun

end OCRS19TM

/-! L19 (needs Definitions encQuery/encSampler): `TMD` for the `Sym` encodings. -/

namespace OCRS19TM

open Turing OnlineCRS.Combine

lemma exists_list_val : ∀ (k n : ℕ), n < 2 ^ k → ∃ l : List Bool, l.length = k ∧ val l = n := by
  intro k
  induction k with
  | zero => intro n hn; exact ⟨[], rfl, by simp at hn; simp [hn]⟩
  | succ k ih =>
    intro n hn
    obtain ⟨l, hl, hv⟩ := ih (n / 2) (by rw [pow_succ] at hn; omega)
    refine ⟨decide (n % 2 = 1) :: l, by simp [hl], ?_⟩
    rw [val_cons, hv]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

lemma len_encodeNat_mono {a b : ℕ} (h : a ≤ b) :
    (Computability.encodeNat a).length ≤ (Computability.encodeNat b).length := by
  have hb := val_lt (Computability.encodeNat b)
  rw [val_encodeNat] at hb
  obtain ⟨l, hl, hv⟩ := exists_list_val _ a (lt_of_le_of_lt h hb)
  rw [← hv, encodeNat_val, ← hl]
  exact length_strip l

lemma bit_ne_three (b : Bool) : bit b ≠ 3 := by cases b <;> decide

lemma bit_dec (b : Bool) : decide (bit b = 1) = b := by cases b <;> decide

lemma encSet_ne_three {k : ℕ} (S : Finset (Fin k)) : ∀ y ∈ encSet S, y ≠ 3 := by
  intro y hy
  simp only [encSet, List.mem_map] at hy
  obtain ⟨j, -, rfl⟩ := hy
  exact bit_ne_three _

lemma encSampler_split {ι : Type} (n : ι → ℕ) (code : ι → List Bool) (p : Σ i, Fin (n i) → ℚ) :
    ∃ P', encSampler n code p = P' ++ [3] := by
  rcases List.eq_nil_or_concat (List.finRange (n p.1)) with h | ⟨L, a, h⟩
  · exact ⟨(code p.1).map bit, by simp [encSampler, encVec, h]⟩
  · exact ⟨(code p.1).map bit ++ [3] ++ (L.flatMap fun j => encRat (p.2 j) ++ [3]) ++
      encRat (p.2 a), by simp [encSampler, encVec, h, List.flatMap_append]⟩

lemma encQuery_mk {ι : Type} (n : ι → ℕ) (code : ι → List Bool) (i : ι) (x : Fin (n i) → ℚ)
    (r : ℕ) (S : Finset (Fin (n i))) :
    encQuery n code ⟨i, x, r, S⟩ =
      encSampler n code ⟨i, x⟩ ++ (Computability.encodeNat r).map bit ++ [3] ++ encSet S := by
  simp [encQuery, encSampler, encNat]

theorem tmd_spec {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    (m₁ : (Σ i, Fin (n i) → ℚ) → ℕ)
    (D₁ D₂ : (Σ i, (Fin (n i) → ℚ) × ℕ × Finset (Fin (n i))) → Bool)
    (hM : TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat m₁)
    (h1 : TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₁)
    (h2 : TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₂)
    (q : Σ i, (Fin (n i) → ℚ) × ℕ × Finset (Fin (n i))) :
    Nonempty (TM2OutputsInTime
      (tmD Sym hM.tm h1.tm h2.tm 3 bit (fun s => decide (s = 1)) hM.inputAlphabet
        hM.outputAlphabet h1.inputAlphabet h1.outputAlphabet h2.inputAlphabet h2.outputAlphabet)
      (List.map (Equiv.refl Sym).invFun (encQuery n code q))
      (some ((Computability.encodeBool (D₁ ⟨q.1, q.2.1, q.2.2.1 % (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩ &&
        D₂ ⟨q.1, q.2.1, q.2.2.1 / (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩)).map (Equiv.refl Bool).invFun))
      ((Polynomial.C 100 * (Polynomial.X + Polynomial.C (pushC hM.tm + 1) *
        (hM.time + h1.time + h2.time) + 1) ^ 2).eval (encQuery n code q).length)) := by
  obtain ⟨i, x, r, S⟩ := q
  obtain ⟨P', hP'⟩ := encSampler_split n code ⟨i, x⟩
  have hw : ∀ r', encQuery n code ⟨i, x, r', S⟩ =
      P' ++ [3] ++ (Computability.encodeNat r').map bit ++ [3] ++ encSet S := by
    intro r'; rw [encQuery_mk, hP']
  have hrM := hM.outputsFun ⟨i, x⟩
  rw [hP'] at hrM
  have hr1 := h1.outputsFun ⟨i, x, r % (m₁ ⟨i, x⟩ + 1), S⟩
  rw [hw] at hr1
  have hr2 := h2.outputsFun ⟨i, x, r / (m₁ ⟨i, x⟩ + 1), S⟩
  rw [hw] at hr2
  have hlen : ∀ r', r' ≤ r → (encQuery n code ⟨i, x, r', S⟩).length ≤
      (encQuery n code ⟨i, x, r, S⟩).length := by
    intro r' hr'
    rw [hw, hw]
    have := len_encodeNat_mono hr'
    simp only [List.length_append, List.length_map]
    omega
  have hsl : (P' ++ [3]).length ≤ (encQuery n code ⟨i, x, r, S⟩).length := by
    rw [hw]; simp only [List.length_append]; omega
  have hl1 := hlen _ (Nat.mod_le r (m₁ ⟨i, x⟩ + 1))
  have hl2 := hlen _ (Nat.div_le_self r (m₁ ⟨i, x⟩ + 1))
  simp only [hw] at hl1 hl2 hsl
  rw [hw]
  have key := tmd_run Sym hM.tm h1.tm h2.tm 3 bit (fun s => decide (s = 1)) hM.inputAlphabet
    hM.outputAlphabet h1.inputAlphabet h1.outputAlphabet h2.inputAlphabet h2.outputAlphabet
    P' (encSet S) (Computability.encodeNat r) (m₁ ⟨i, x⟩)
    (hM.time.eval (P' ++ [3]).length)
    (h1.time.eval (P' ++ [3] ++ (Computability.encodeNat (r % (m₁ ⟨i, x⟩ + 1))).map bit ++ [3] ++
      encSet S).length)
    (h2.time.eval (P' ++ [3] ++ (Computability.encodeNat (r / (m₁ ⟨i, x⟩ + 1))).map bit ++ [3] ++
      encSet S).length)
    ((Polynomial.C 100 * (Polynomial.X + Polynomial.C (pushC hM.tm + 1) *
        (hM.time + h1.time + h2.time) + 1) ^ 2).eval
      (P' ++ [3] ++ (Computability.encodeNat r).map bit ++ [3] ++ encSet S).length)
    (D₁ ⟨i, x, r % (m₁ ⟨i, x⟩ + 1), S⟩) (D₂ ⟨i, x, r / (m₁ ⟨i, x⟩ + 1), S⟩)
    (encSet_ne_three S) bit_ne_three bit_dec (by exact hrM)
    (by rw [val_encodeNat]; exact hr1) (by rw [val_encodeNat]; exact hr2) ?_
  · exact key
  · simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    have a1 := polyMono hM.time hsl
    have a2 := polyMono h1.time hl1
    have a3 := polyMono h2.time hl2
    gcongr
    all_goals first | exact a1 | exact a2 | exact a3

end OCRS19TM

namespace OCRS19TM

open Turing OnlineCRS.Combine

/-- the polytime combined oracle -/
noncomputable def tmdPoly {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    (m₁ : (Σ i, Fin (n i) → ℚ) → ℕ)
    (D₁ D₂ : (Σ i, (Fin (n i) → ℚ) × ℕ × Finset (Fin (n i))) → Bool)
    (hM : TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat m₁)
    (h1 : TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₁)
    (h2 : TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₂) :
    TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool
      (fun q => D₁ ⟨q.1, q.2.1, q.2.2.1 % (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩ &&
        D₂ ⟨q.1, q.2.1, q.2.2.1 / (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩) where
  tm := tmD Sym hM.tm h1.tm h2.tm 3 bit (fun s => decide (s = 1)) hM.inputAlphabet
    hM.outputAlphabet h1.inputAlphabet h1.outputAlphabet h2.inputAlphabet h2.outputAlphabet
  inputAlphabet := Equiv.refl Sym
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 100 * (Polynomial.X + Polynomial.C (pushC hM.tm + 1) *
    (hM.time + h1.time + h2.time) + 1) ^ 2
  outputsFun q := (tmd_spec n code m₁ D₁ D₂ hM h1 h2 q).some

theorem tmd_prop {ι : Type} (n : ι → ℕ) (code : ι → List Bool) :
    ∀ (m₁ : (Σ i, Fin (n i) → ℚ) → ℕ)
      (D₁ D₂ : (Σ i, (Fin (n i) → ℚ) × ℕ × Finset (Fin (n i))) → Bool),
      Nonempty (TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat m₁) →
      Nonempty (TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₁) →
      Nonempty (TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₂) →
      Nonempty (TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool
        (fun q => D₁ ⟨q.1, q.2.1, q.2.2.1 % (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩ &&
          D₂ ⟨q.1, q.2.1, q.2.2.1 / (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩)) :=
  fun m₁ D₁ D₂ hM h1 h2 => ⟨tmdPoly n code m₁ D₁ D₂ hM.some h1.some h2.some⟩

end OCRS19TM

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace OCRS19

open OnlineCRS.Combine

section Generic

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- product form of `activeProb` -/
def ap (x : N → ℝ) (A : Finset N) : ℝ := ∏ e, if e ∈ A then x e else 1 - x e

lemma activeProb_eq_ap (x : N → ℝ) (A : Finset N) : activeProb x A = ap x A := by
  unfold activeProb ap
  rw [← Finset.prod_mul_prod_compl A]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    rw [if_pos he]
  · apply Finset.prod_congr rfl
    intro e he
    rw [if_neg (Finset.mem_compl.mp he)]

lemma ap_nonneg (x : N → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (A : Finset N) : 0 ≤ ap x A := by
  unfold ap
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact (hx e).1
  · linarith [(hx e).2]

lemma ap_mul (x : N → ℝ) (A B : Finset N) :
    ap x A * ap x B = ap x (A ∩ B) * ap x (A ∪ B) := by
  unfold ap
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;>
    simp [ha, hb, Finset.mem_inter, Finset.mem_union]; ring

lemma ap_sum (x : N → ℝ) : ∑ A : Finset N, ap x A = 1 := by
  have h := Fintype.prod_add (fun e => x e) (fun e => 1 - x e)
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro A _
  rw [← activeProb_eq_ap]
  rfl

lemma harris_general (μ : Finset N → ℝ) (hμ0 : 0 ≤ μ)
    (hμ : ∀ A B, μ A * μ B ≤ μ (A ∩ B) * μ (A ∪ B))
    (f g : Finset N → ℝ) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hf : Antitone f) (hg : Antitone g) :
    (∑ A, μ A * f A) * ∑ A, μ A * g A ≤ (∑ A, μ A) * ∑ A, μ A * (f A * g A) := by
  have key := fkg (α := (Finset N)ᵒᵈ) (μ := μ ∘ OrderDual.ofDual) (f := f ∘ OrderDual.ofDual)
    (g := g ∘ OrderDual.ofDual) (fun a => hμ0 _) (fun a => hf0 _) (fun a => hg0 _)
    hf.dual_left hg.dual_left
    (fun a b => (hμ (OrderDual.ofDual a) (OrderDual.ofDual b)).trans (le_of_eq (mul_comm _ _)))
  exact key

lemma chi_inter {G₁ G₂ : Finset (Finset N)} {A : Finset N} {e : N}
    (h₁ : chi e A G₁ G₁) (h₂ : chi e A G₂ G₂) : chi e A (G₁ ∩ G₂) (G₁ ∩ G₂) := by
  intro I hI hG
  rw [Finset.mem_inter] at hG ⊢
  exact ⟨h₁ I hI hG.1, h₂ I hI hG.2⟩

lemma chi_anti {G : Finset (Finset N)} {A B : Finset N} {e : N} (hAB : A ⊆ B)
    (h : chi e B G G) : chi e A G G :=
  fun I hI hG => h I (hI.trans hAB) hG

open Classical in
/-- selectability probability for a fixed family -/
noncomputable def selP (x : N → ℝ) (G : Finset (Finset N)) (e : N) : ℝ :=
  ∑ A : Finset N, activeProb x A * (if chi e A G G then 1 else 0)

open Classical in
lemma selP_eq (x : N → ℝ) (G : Finset (Finset N)) (e : N) :
    selP x G e = ∑ A : Finset N, ap x A * (if chi e A G G then 1 else 0) := by
  unfold selP
  simp_rw [activeProb_eq_ap]

open Classical in
lemma harris_sel (x : N → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (G₁ G₂ : Finset (Finset N)) (e : N) :
    selP x G₁ e * selP x G₂ e ≤ selP x (G₁ ∩ G₂) e := by
  have key := harris_general (ap x) (fun A => ap_nonneg x hx A)
    (fun A B => (ap_mul x A B).le)
    (fun A => if chi e A G₁ G₁ then (1 : ℝ) else 0)
    (fun A => if chi e A G₂ G₂ then (1 : ℝ) else 0)
    (fun A => by dsimp only; split_ifs <;> norm_num)
    (fun A => by dsimp only; split_ifs <;> norm_num)
    (fun A B hAB => by
      dsimp only
      by_cases hB : chi e B G₁ G₁
      · rw [if_pos hB, if_pos (chi_anti hAB hB)]
      · rw [if_neg hB]; split_ifs <;> norm_num)
    (fun A B hAB => by
      dsimp only
      by_cases hB : chi e B G₂ G₂
      · rw [if_pos hB, if_pos (chi_anti hAB hB)]
      · rw [if_neg hB]; split_ifs <;> norm_num)
  rw [ap_sum, one_mul] at key
  rw [selP_eq, selP_eq, selP_eq]
  refine key.trans ?_
  apply Finset.sum_le_sum
  intro A _
  have hA := ap_nonneg x hx A
  by_cases h1 : chi e A G₁ G₁
  · by_cases h2 : chi e A G₂ G₂
    · rw [if_pos h1, if_pos h2, if_pos (chi_inter h1 h2)]; simp
    · rw [if_pos h1, if_neg h2]; split_ifs <;> simp [hA]
  · rw [if_neg h1]; split_ifs <;> simp [hA]

/-- Definition 2.10: the law of `F_{π¹,x} ∩ F_{π²,x}` with independent draws. -/
noncomputable def combLaw {F₁ F₂ : Finset (Finset N)} (π₁ : GreedyOCRS F₁) (π₂ : GreedyOCRS F₂)
    (x : N → ℝ) : PMF (Finset (Finset N)) :=
  (π₁.law x).bind fun G₁ => (π₂.law x).map fun G₂ => G₁ ∩ G₂

/-- The combined greedy OCRS. -/
noncomputable def comb {F₁ F₂ : Finset (Finset N)} (π₁ : GreedyOCRS F₁) (π₂ : GreedyOCRS F₂) :
    GreedyOCRS (F₁ ∩ F₂) where
  law := combLaw π₁ π₂
  law_support := by
    intro x G hG
    rw [combLaw, PMF.mem_support_bind_iff] at hG
    obtain ⟨G₁, h1, hG⟩ := hG
    rw [PMF.support_map] at hG
    obtain ⟨G₂, h2, rfl⟩ := hG
    obtain ⟨d1, e1, s1⟩ := π₁.law_support x G₁ h1
    obtain ⟨d2, e2, s2⟩ := π₂.law_support x G₂ h2
    refine ⟨?_, Finset.mem_inter.mpr ⟨e1, e2⟩, Finset.inter_subset_inter s1 s2⟩
    intro I hI J hJ
    rw [Finset.mem_inter] at hI ⊢
    exact ⟨d1 I hI.1 J hJ, d2 I hI.2 J hJ⟩

lemma combLaw_toReal {F₁ F₂ : Finset (Finset N)} (π₁ : GreedyOCRS F₁) (π₂ : GreedyOCRS F₂)
    (x : N → ℝ) (G : Finset (Finset N)) :
    (combLaw π₁ π₂ x G).toReal = ∑ G₁, ∑ G₂, (π₁.law x G₁).toReal * (π₂.law x G₂).toReal *
      (if G₁ ∩ G₂ = G then 1 else 0) := by
  rw [combLaw, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun G₁ _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro G₁ _
  rw [ENNReal.toReal_mul, PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum (fun G₂ _ => by split_ifs <;> simp [PMF.apply_ne_top]),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G₂ _
  by_cases h : G₁ ∩ G₂ = G
  · rw [if_pos h.symm, if_pos h]; ring
  · rw [if_neg (Ne.symm h), if_neg h]; simp

lemma comb_sum (w₁ w₂ : Finset (Finset N) → ℝ) (φ : Finset (Finset N) → ℝ) :
    ∑ G, (∑ G₁, ∑ G₂, w₁ G₁ * w₂ G₂ * (if G₁ ∩ G₂ = G then (1 : ℝ) else 0)) * φ G =
      ∑ G₁, ∑ G₂, w₁ G₁ * w₂ G₂ * φ (G₁ ∩ G₂) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G₂ _
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma selectProb_eq {F : Finset (Finset N)} (π : GreedyOCRS F) (x : N → ℝ) (e : N) :
    selectProb π x e = ∑ G, (π.law x G).toReal * selP x G e := rfl

lemma comb_selectable {F₁ F₂ : Finset (Finset N)} (P₁ P₂ : Set (N → ℝ))
    (hP₁ : P₁ ⊆ Set.Icc 0 1) (b c₁ c₂ : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc₁ : c₁ ∈ Set.Icc (0 : ℝ) 1) (hc₂ : c₂ ∈ Set.Icc (0 : ℝ) 1)
    (π₁ : GreedyOCRS F₁) (π₂ : GreedyOCRS F₂)
    (h₁ : IsSelectable P₁ π₁ b c₁) (h₂ : IsSelectable P₂ π₂ b c₂) :
    IsSelectable (P₁ ∩ P₂) (comb π₁ π₂) b (c₁ * c₂) := by
  intro x hx e
  obtain ⟨y, ⟨hy1, hy2⟩, rfl⟩ := hx
  have hx1 : b • y ∈ b • P₁ := Set.smul_mem_smul_set hy1
  have hx2 : b • y ∈ b • P₂ := Set.smul_mem_smul_set hy2
  have hbd : ∀ e, 0 ≤ (b • y) e ∧ (b • y) e ≤ 1 := by
    intro e'
    have h := hP₁ hy1
    have h0 : 0 ≤ y e' := h.1 e'
    have h1 : y e' ≤ 1 := h.2 e'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨mul_nonneg hb.1 h0, mul_le_one₀ hb.2 h0 h1⟩
  have s1 := h₁ (b • y) hx1 e
  have s2 := h₂ (b • y) hx2 e
  rw [selectProb_eq] at s1 s2
  rw [selectProb_eq]
  change c₁ * c₂ ≤ ∑ G, (combLaw π₁ π₂ (b • y) G).toReal * selP (b • y) G e
  simp_rw [combLaw_toReal]
  rw [comb_sum]
  calc c₁ * c₂
      ≤ (∑ G₁, (π₁.law (b • y) G₁).toReal * selP (b • y) G₁ e) *
          ∑ G₂, (π₂.law (b • y) G₂).toReal * selP (b • y) G₂ e :=
        mul_le_mul s1 s2 hc₂.1 (le_trans hc₁.1 s1)
    _ = ∑ G₁, ∑ G₂, ((π₁.law (b • y) G₁).toReal * selP (b • y) G₁ e) *
          ((π₂.law (b • y) G₂).toReal * selP (b • y) G₂ e) := Finset.sum_mul_sum _ _ _ _
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro G₁ _
        apply Finset.sum_le_sum
        intro G₂ _
        have hh := harris_sel (b • y) hbd G₁ G₂ e
        have hw : 0 ≤ (π₁.law (b • y) G₁).toReal * (π₂.law (b • y) G₂).toReal :=
          mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        calc ((π₁.law (b • y) G₁).toReal * selP (b • y) G₁ e) *
              ((π₂.law (b • y) G₂).toReal * selP (b • y) G₂ e)
            = ((π₁.law (b • y) G₁).toReal * (π₂.law (b • y) G₂).toReal) *
                (selP (b • y) G₁ e * selP (b • y) G₂ e) := by ring
          _ ≤ ((π₁.law (b • y) G₁).toReal * (π₂.law (b • y) G₂).toReal) *
                selP (b • y) (G₁ ∩ G₂) e := mul_le_mul_of_nonneg_left hh hw

/-- binary points -/
def Bin (N : Type*) : Set (N → ℝ) := {y | ∀ e, y e = 0 ∨ y e = 1}

lemma indicatorVec_injective : Function.Injective (indicatorVec (N := N)) := by
  intro I J h
  ext e
  have := congrFun h e
  unfold indicatorVec at this
  by_cases hI : e ∈ I <;> by_cases hJ : e ∈ J <;> simp_all

lemma indicatorVec_mem_Icc (I : Finset N) : indicatorVec I ∈ Set.Icc (0 : N → ℝ) 1 := by
  refine ⟨fun e => ?_, fun e => ?_⟩ <;> unfold indicatorVec <;> split_ifs <;> norm_num

lemma convexHull_inter_bin (F : Finset (Finset N)) :
    convexHull ℝ (indicatorVec '' (F : Set (Finset N))) ∩ {y | ∀ e, y e = 0 ∨ y e = 1} =
      indicatorVec '' (F : Set (Finset N)) := by
  apply Set.Subset.antisymm
  · rintro y ⟨hy, hbin⟩
    apply extremePoints_convexHull_subset (𝕜 := ℝ)
    have hcube : convexHull ℝ (indicatorVec '' (F : Set (Finset N))) ⊆ Set.Icc (0 : N → ℝ) 1 :=
      convexHull_min (by rintro _ ⟨I, _, rfl⟩; exact indicatorVec_mem_Icc I) (convex_Icc _ _)
    refine ⟨hy, ?_⟩
    intro x₁ hx₁ x₂ hx₂ hseg
    obtain ⟨a, c, ha, hc, hac, hxy⟩ := hseg
    have c1 := hcube hx₁
    have c2 := hcube hx₂
    have pt : ∀ e, x₁ e = y e ∧ x₂ e = y e := by
      intro e
      have he := congrFun hxy e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he
      have l1 : 0 ≤ x₁ e := c1.1 e
      have u1 : x₁ e ≤ 1 := c1.2 e
      have l2 : 0 ≤ x₂ e := c2.1 e
      have u2 : x₂ e ≤ 1 := c2.2 e
      rcases hbin e with h0 | h1
      · rw [h0] at he ⊢
        have p1 : 0 ≤ a * x₁ e := mul_nonneg ha.le l1
        have p2 : 0 ≤ c * x₂ e := mul_nonneg hc.le l2
        have q1 : a * x₁ e = 0 := by linarith
        have q2 : c * x₂ e = 0 := by linarith
        exact ⟨(mul_eq_zero.mp q1).resolve_left ha.ne', (mul_eq_zero.mp q2).resolve_left hc.ne'⟩
      · rw [h1] at he ⊢
        have p1 : 0 ≤ a * (1 - x₁ e) := mul_nonneg ha.le (by linarith)
        have p2 : 0 ≤ c * (1 - x₂ e) := mul_nonneg hc.le (by linarith)
        have q1 : a * (1 - x₁ e) = 0 := by nlinarith
        have q2 : c * (1 - x₂ e) = 0 := by nlinarith
        have r1 := (mul_eq_zero.mp q1).resolve_left ha.ne'
        have r2 := (mul_eq_zero.mp q2).resolve_left hc.ne'
        exact ⟨by linarith, by linarith⟩
    exact funext fun e => (pt e).1
  · rintro _ ⟨I, hI, rfl⟩
    refine ⟨subset_convexHull ℝ _ ⟨I, hI, rfl⟩, fun e => ?_⟩
    unfold indicatorVec
    split_ifs <;> simp

lemma relax_inter {F₁ F₂ : Finset (Finset N)} {P₁ P₂ : Set (N → ℝ)}
    (h₁ : IsRelaxation F₁ P₁) (h₂ : IsRelaxation F₂ P₂) :
    IsRelaxation (F₁ ∩ F₂) (P₁ ∩ P₂) := by
  refine ⟨fun y hy => h₁.1 hy.1, ?_⟩
  have k1 := h₁.2
  have k2 := h₂.2
  rw [convexHull_inter_bin] at k1 k2 ⊢
  rw [Finset.coe_inter, Set.image_inter indicatorVec_injective, ← k1, ← k2]
  ext y
  simp only [Set.mem_inter_iff]
  tauto

lemma downClosed_inter {F₁ F₂ : Finset (Finset N)} (h₁ : DownClosed F₁) (h₂ : DownClosed F₂) :
    DownClosed (F₁ ∩ F₂) := by
  intro I hI J hJ
  rw [Finset.mem_inter] at hI ⊢
  exact ⟨h₁ I hI.1 J hJ, h₂ I hI.2 J hJ⟩

end Generic

/-- product of two uniform draws = one uniform draw decoded by divmod -/
lemma unif_bind_map {β : Type} (m₁ m₂ M : ℕ) (hM : M + 1 = (m₁ + 1) * (m₂ + 1))
    (g : ℕ → ℕ → β) :
    (PMF.uniformOfFintype (Fin (m₁ + 1))).bind (fun r₁ : Fin (m₁ + 1) =>
        (PMF.uniformOfFintype (Fin (m₂ + 1))).map (fun r₂ : Fin (m₂ + 1) => g (r₁ : ℕ) (r₂ : ℕ))) =
      (PMF.uniformOfFintype (Fin (M + 1))).map
        (fun r : Fin (M + 1) => g ((r : ℕ) % (m₁ + 1)) ((r : ℕ) / (m₁ + 1))) := by
  have ha : 0 < m₁ + 1 := Nat.succ_pos _
  ext G
  simp only [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype,
    Fintype.card_fin]
  -- reindex the right sum by Fin b × Fin a
  let e : Fin (m₂ + 1) × Fin (m₁ + 1) ≃ Fin (M + 1) :=
    finProdFinEquiv.trans (finCongr (by rw [hM, Nat.mul_comm]))
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_congr rfl fun r₂ _ => ?_
  have h1 : ((e (r₂, r₁) : Fin (M + 1)) : ℕ) % (m₁ + 1) = r₁ := by
    simp only [e, Equiv.trans_apply, finProdFinEquiv_apply_val, finCongr_apply, Fin.val_cast]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r₁.isLt]
  have h2 : ((e (r₂, r₁) : Fin (M + 1)) : ℕ) / (m₁ + 1) = r₂ := by
    simp only [e, Equiv.trans_apply, finProdFinEquiv_apply_val, finCongr_apply, Fin.val_cast]
    rw [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt r₁.isLt, zero_add]
  rw [h1, h2]
  split_ifs
  · rw [hM, Nat.cast_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast ha.ne'))
      (Or.inl (ENNReal.natCast_ne_top _))]
  · simp


/-- the `IsEfficient` law is written with a coerced uniform draw -/
lemma map_coe {β : Type} (k : ℕ) (f : ℕ → β) :
    PMF.map f (do let a ← PMF.uniformOfFintype (Fin (k + 1)); pure (a : ℕ)) =
      (PMF.uniformOfFintype (Fin (k + 1))).map (fun r : Fin (k + 1) => f r) := by
  show PMF.map f (PMF.bind _ (PMF.pure ∘ (fun a : Fin (k + 1) => (a : ℕ)))) = _
  rw [PMF.bind_pure_comp, PMF.map_comp]
  rfl

/-- Remaining TM obligation 1: arithmetic on two polytime sampler-range machines. -/
def TMm {ι : Type} (n : ι → ℕ) (code : ι → List Bool) : Prop :=
  ∀ m₁ m₂ : (Σ i, Fin (n i) → ℚ) → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat m₁) →
    Nonempty (Turing.TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat m₂) →
    Nonempty (Turing.TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat
      (fun p => (m₁ p + 1) * (m₂ p + 1) - 1))

/-- Remaining TM obligation 2: the combined oracle. -/
def TMD {ι : Type} (n : ι → ℕ) (code : ι → List Bool) : Prop :=
  ∀ (m₁ : (Σ i, Fin (n i) → ℚ) → ℕ)
    (D₁ D₂ : (Σ i, (Fin (n i) → ℚ) × ℕ × Finset (Fin (n i))) → Bool),
    Nonempty (Turing.TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat m₁) →
    Nonempty (Turing.TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₁) →
    Nonempty (Turing.TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D₂) →
    Nonempty (Turing.TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool
      (fun q => D₁ ⟨q.1, q.2.1, q.2.2.1 % (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩ &&
        D₂ ⟨q.1, q.2.1, q.2.2.1 / (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩))

theorem eff_comb {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    {F₁ F₂ : ∀ i, Finset (Finset (Fin (n i)))} (P₁ P₂ : ∀ i, Set (Fin (n i) → ℝ))
    (π₁ : ∀ i, GreedyOCRS (F₁ i)) (π₂ : ∀ i, GreedyOCRS (F₂ i))
    (hm : TMm n code) (hD : TMD n code) :
    IsEfficient n code P₁ π₁ → IsEfficient n code P₂ π₂ →
      IsEfficient n code (fun i => P₁ i ∩ P₂ i) (fun i => comb (π₁ i) (π₂ i)) := by
  rintro ⟨m₁, D₁, hm₁, hD₁, hl₁⟩ ⟨m₂, D₂, hm₂, hD₂, hl₂⟩
  refine ⟨fun p => (m₁ p + 1) * (m₂ p + 1) - 1,
    fun q => D₁ ⟨q.1, q.2.1, q.2.2.1 % (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩ &&
        D₂ ⟨q.1, q.2.1, q.2.2.1 / (m₁ ⟨q.1, q.2.1⟩ + 1), q.2.2.2⟩,
    hm m₁ m₂ hm₁ hm₂, hD m₁ D₁ D₂ hm₁ hD₁ hD₂, ?_⟩
  intro i x hx
  show combLaw (π₁ i) (π₂ i) _ = _
  rw [combLaw, hl₁ i x hx.1, hl₂ i x hx.2, map_coe, map_coe, map_coe, PMF.bind_map]
  have hM : (m₁ ⟨i, x⟩ + 1) * (m₂ ⟨i, x⟩ + 1) - 1 + 1 = (m₁ ⟨i, x⟩ + 1) * (m₂ ⟨i, x⟩ + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _)
      (Nat.succ_ne_zero _)))
  have key := unif_bind_map (m₁ ⟨i, x⟩) (m₂ ⟨i, x⟩) _ hM
    (fun a b => (Finset.univ.filter fun S => D₁ ⟨i, x, a, S⟩ = true) ∩
      (Finset.univ.filter fun S => D₂ ⟨i, x, b, S⟩ = true))
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    funext r₁
    rw [Function.comp_apply, PMF.map_comp]
    rfl
  · congr 1
    funext r
    ext S
    simp [Bool.and_eq_true]


/-- Assembly: everything except efficiency of the combined sampler. -/
theorem assembly {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    (F₁ F₂ : ∀ i, Finset (Finset (Fin (n i)))) (P₁ P₂ : ∀ i, Set (Fin (n i) → ℝ))
    (hF₁ : ∀ i, DownClosed (F₁ i)) (hF₂ : ∀ i, DownClosed (F₂ i))
    (hP₁ : ∀ i, IsRelaxation (F₁ i) (P₁ i)) (hP₂ : ∀ i, IsRelaxation (F₂ i) (P₂ i))
    (b c₁ c₂ : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc₁ : c₁ ∈ Set.Icc (0 : ℝ) 1) (hc₂ : c₂ ∈ Set.Icc (0 : ℝ) 1)
    (π₁ : ∀ i, GreedyOCRS (F₁ i)) (π₂ : ∀ i, GreedyOCRS (F₂ i))
    (h₁ : ∀ i, IsSelectable (P₁ i) (π₁ i) b c₁) (h₂ : ∀ i, IsSelectable (P₂ i) (π₂ i) b c₂)
    (hm : TMm n code) (hD : TMD n code) :
    (∀ i, DownClosed (F₁ i ∩ F₂ i) ∧ IsRelaxation (F₁ i ∩ F₂ i) (P₁ i ∩ P₂ i)) ∧
      ∃ π : ∀ i, GreedyOCRS (F₁ i ∩ F₂ i),
        (∀ i, IsSelectable (P₁ i ∩ P₂ i) (π i) b (c₁ * c₂)) ∧
        (IsEfficient n code P₁ π₁ → IsEfficient n code P₂ π₂ →
          IsEfficient n code (fun i => P₁ i ∩ P₂ i) π) := by
  refine ⟨fun i => ⟨downClosed_inter (hF₁ i) (hF₂ i), relax_inter (hP₁ i) (hP₂ i)⟩,
    fun i => comb (π₁ i) (π₂ i), fun i => ?_, eff_comb n code P₁ P₂ π₁ π₂ hm hD⟩
  exact comb_selectable (P₁ i) (P₂ i) (hP₁ i).1 b c₁ c₂ hb hc₁ hc₂ (π₁ i) (π₂ i) (h₁ i) (h₂ i)

end OCRS19


open OnlineCRS.Combine in
theorem solution {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    (F₁ F₂ : ∀ i, Finset (Finset (Fin (n i)))) (P₁ P₂ : ∀ i, Set (Fin (n i) → ℝ))
    (hF₁ : ∀ i, DownClosed (F₁ i)) (hF₂ : ∀ i, DownClosed (F₂ i))
    (hP₁ : ∀ i, IsRelaxation (F₁ i) (P₁ i)) (hP₂ : ∀ i, IsRelaxation (F₂ i) (P₂ i))
    (b c₁ c₂ : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc₁ : c₁ ∈ Set.Icc (0 : ℝ) 1) (hc₂ : c₂ ∈ Set.Icc (0 : ℝ) 1)
    (π₁ : ∀ i, GreedyOCRS (F₁ i)) (π₂ : ∀ i, GreedyOCRS (F₂ i))
    (h₁ : ∀ i, IsSelectable (P₁ i) (π₁ i) b c₁) (h₂ : ∀ i, IsSelectable (P₂ i) (π₂ i) b c₂) :
    (∀ i, DownClosed (F₁ i ∩ F₂ i) ∧ IsRelaxation (F₁ i ∩ F₂ i) (P₁ i ∩ P₂ i)) ∧
      ∃ π : ∀ i, GreedyOCRS (F₁ i ∩ F₂ i),
        (∀ i, IsSelectable (P₁ i ∩ P₂ i) (π i) b (c₁ * c₂)) ∧
        (IsEfficient n code P₁ π₁ → IsEfficient n code P₂ π₂ →
          IsEfficient n code (fun i => P₁ i ∩ P₂ i) π) := by
  exact OCRS19.assembly n code F₁ F₂ P₁ P₂ hF₁ hF₂ hP₁ hP₂ b c₁ c₂ hb hc₁ hc₂ π₁ π₂ h₁ h₂
    (fun m₁ m₂ h1 h2 => OCRS19TM.tmm_poly (encSampler n code) m₁ m₂ h1 h2)
    (OCRS19TM.tmd_prop n code)
