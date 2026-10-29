-- Prove2me | solution 1 for RuralPostman.NPC.urp_mem_NP
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T05:12:29.604093+00:00
-- url     : https://prove2.me/submissions/514c28fc-1fca-4343-8b83-051cc39e7b59

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_RuralPostman_NPC_Instances
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false

section Sec_Stk0

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk

section Core
variable {K A : Type} [Fintype K] [DecidableEq K]

def S (s : K → List A) : ℕ := ∑ k, (s k).length

lemma apply_len (a : StackAct A) (l : List A) : (a.apply l).length ≤ l.length + 1 := by
  cases a <;> simp [StackAct.apply] <;> omega

lemma Exec_size {p : StackProg K A} {s t : K → List A} {n : ℕ} (h : p.Exec s t n) :
    S t ≤ S s + Fintype.card K * n := by
  induction h with
  | act f s =>
    unfold S
    calc ∑ k, ((StackProg.applyAct f s) k).length ≤ ∑ k, ((s k).length + 1) :=
          Finset.sum_le_sum (fun k _ => by simpa [StackProg.applyAct] using apply_len _ _)
      _ = ∑ k, (s k).length + Fintype.card K := by simp [Finset.sum_add_distrib]
      _ ≤ ∑ k, (s k).length + Fintype.card K * 1 := by omega
  | seq _ _ ih1 ih2 => nlinarith
  | branchTrue _ _ ih => nlinarith
  | branchFalse _ _ ih => nlinarith
  | loopFalse _ => nlinarith [Nat.zero_le (Fintype.card K)]
  | loopTrue _ _ _ ih1 ih2 => nlinarith

/-- polynomial-time specification of a program computing the store transformer `g` -/
def PolySpec (p : StackProg K A) (g : (K → List A) → (K → List A)) : Prop :=
  ∃ d : ℕ, ∀ s, ∃ n, n ≤ (S s + 2) ^ d ∧ p.Exec s (g s) n

lemma pw_const {X : ℕ} (hX : 2 ≤ X) (c : ℕ) : c ≤ X ^ c :=
  le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hX c)

lemma pw_mono {X : ℕ} (hX : 2 ≤ X) {a b : ℕ} (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right (by omega) h

lemma pw_add {X x y a b : ℕ} (hX : 2 ≤ X) (hx : x ≤ X ^ a) (hy : y ≤ X ^ b) :
    x + y ≤ X ^ (a + b + 1) := by
  have h1 : X ^ a ≤ X ^ (a + b) := pw_mono hX (by omega)
  have h2 : X ^ b ≤ X ^ (a + b) := pw_mono hX (by omega)
  have h3 : X ^ (a + b + 1) = X ^ (a + b) * X := pow_succ _ _
  have : 0 < X ^ (a + b) := by positivity
  nlinarith

lemma pw_mul {X x y a b : ℕ} (hx : x ≤ X ^ a) (hy : y ≤ X ^ b) : x * y ≤ X ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

lemma pw_pow {X x a b : ℕ} (hx : x ≤ X ^ a) : x ^ b ≤ X ^ (a * b) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left hx b

lemma pw_one {X : ℕ} (hX : 2 ≤ X) : 1 ≤ X ^ 1 := by simp; omega

lemma S_pos_ge (s : K → List A) : 2 ≤ S s + 2 := by omega

lemma ps_act (f : (K → Option A) → K → StackAct A) : PolySpec (.act f) (StackProg.applyAct f) := by
  refine ⟨1, fun s => ⟨1, ?_, StackProg.Exec.act f s⟩⟩
  simp


def PS (p : StackProg K A) (g : (K → List A) → (K → List A)) (d : ℕ) : Prop :=
  ∀ s, ∃ n, n ≤ (S s + 2) ^ d ∧ p.Exec s (g s) n

lemma PS.poly {p : StackProg K A} {g : (K → List A) → (K → List A)} {d : ℕ} (h : PS p g d) :
    PolySpec p g := ⟨d, h⟩

lemma PS.mono {p : StackProg K A} {g : (K → List A) → (K → List A)} {d e : ℕ} (h : PS p g d)
    (he : d ≤ e) : PS p g e := by
  intro s
  obtain ⟨n, hn, ex⟩ := h s
  exact ⟨n, le_trans hn (pw_mono (S_pos_ge s) he), ex⟩

lemma ps_seq' {p q : StackProg K A} {g h : (K → List A) → (K → List A)} {d1 d2 : ℕ}
    (hp : PS p g d1) (hq : PS q h d2) :
    PS (.seq p q) (h ∘ g) (d1 + 3 + (Fintype.card K + d1 + 2) * d2) := by
  intro s
  obtain ⟨n1, hn1, e1⟩ := hp s
  obtain ⟨n2, hn2, e2⟩ := hq (g s)
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  set X := S s + 2 with hXd
  have hX : 2 ≤ X := by omega
  have hsz := Exec_size e1
  have hY : S (g s) + 2 ≤ X ^ (Fintype.card K + d1 + 2) := by
    have a1 : X ≤ X ^ 1 := by simp
    have a2 : Fintype.card K * n1 ≤ X ^ (Fintype.card K + d1) :=
      pw_mul (pw_const hX (Fintype.card K)) hn1
    have := pw_add hX a1 a2
    calc S (g s) + 2 ≤ X + Fintype.card K * n1 := by omega
      _ ≤ X ^ (1 + (Fintype.card K + d1) + 1) := this
      _ = _ := by ring_nf
  have b1 : n2 ≤ X ^ ((Fintype.card K + d1 + 2) * d2) :=
    le_trans hn2 (pw_pow hY)
  have b2 : n1 + 1 ≤ X ^ (d1 + 0 + 1) := pw_add hX hn1 (show 1 ≤ X ^ 0 by simp)
  have := pw_add hX b2 b1
  exact le_trans this (pw_mono hX (by omega))

def hd (s : K → List A) : K → Option A := fun k => (s k).head?

lemma PolySpec.seq {p q : StackProg K A} {g h : (K → List A) → (K → List A)}
    (hp : PolySpec p g) (hq : PolySpec q h) : PolySpec (.seq p q) (fun s => h (g s)) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  exact ⟨_, ps_seq' (p := p) (q := q) (g := g) (h := h) hp hq⟩

lemma PolySpec.branch {p q : StackProg K A} {g h : (K → List A) → (K → List A)}
    (t : (K → Option A) → Bool)
    (hp : PolySpec p g) (hq : PolySpec q h) :
    PolySpec (.branch t p q) (fun s => if t (hd s) = true then g s else h s) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨2 * max d1 d2 + 3, fun s => ?_⟩
  have hX : 2 ≤ S s + 2 := by omega
  have key : ∀ n, n ≤ (S s + 2) ^ (max d1 d2) → 1 + n ≤ (S s + 2) ^ (2 * max d1 d2 + 3) := by
    intro n hn
    have h2 : 1 ≤ (S s + 2) ^ (max d1 d2) := Nat.one_le_pow _ _ (by omega)
    have := pw_add hX h2 hn
    exact le_trans this (pw_mono hX (by omega))
  by_cases ht : t (hd s) = true
  · obtain ⟨n, hn, e⟩ := hp s
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_pos ht]; exact StackProg.Exec.branchTrue ht e
  · have ht' : t (hd s) = false := by simpa using ht
    obtain ⟨n, hn, e⟩ := hq s
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_neg ht]; exact StackProg.Exec.branchFalse ht' e

/-- a loop whose body is a single action; cost `3m+1` for `m` iterations. -/
lemma loop1_exec (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (StackProg.applyAct f s) < μ s ∧
        G s = G (StackProg.applyAct f s)) :
    ∀ s, ∃ n, n ≤ 3 * μ s + 1 ∧ (StackProg.loop t (.act f)).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s ht
    obtain ⟨n, hn, e⟩ := ih (μ (StackProg.applyAct f s)) (by omega) _ rfl
    refine ⟨1 + 1 + 1 + n, by omega, ?_⟩
    rw [hG]
    exact StackProg.Exec.loopTrue ht (StackProg.Exec.act f s) e
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, by omega, ?_⟩
    rw [hstop s ht']
    exact StackProg.Exec.loopFalse ht'

lemma PolySpec.loop1 (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hμ : ∀ s, μ s ≤ S s)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (StackProg.applyAct f s) < μ s ∧
        G s = G (StackProg.applyAct f s)) :
    PolySpec (.loop t (.act f)) G := by
  refine ⟨2, fun s => ?_⟩
  obtain ⟨n, hn, e⟩ := loop1_exec t f G μ hstop hstep s
  refine ⟨n, ?_, e⟩
  have := hμ s
  nlinarith

end Core
end Stk

end Sec_Stk0

section Sec_Stk1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Prims
variable {K A : Type} [Fintype K] [DecidableEq K]

def upd (s : K → List A) (k : K) (l : List A) : K → List A := Function.update s k l

@[simp] lemma upd_same (s : K → List A) (k : K) (l : List A) : upd s k l k = l := by
  simp [upd]
lemma upd_ne (s : K → List A) {k j : K} (l : List A) (h : j ≠ k) : upd s k l j = s j := by
  simp [upd, h]

def mvw (pred : A → Bool) : List A → List A → List A × List A
  | [], b => ([], b)
  | x :: a, b => if pred x then mvw pred a (x :: b) else (x :: a, b)

def mvwT (a : K) (pred : A → Bool) : (K → Option A) → Bool :=
  fun h => match h a with | some x => pred x | none => false

def mvwF (a b : K) : (K → Option A) → K → StackAct A :=
  fun h k => if k = a then .pop else if k = b then (match h a with | some x => .push x | none => .keep) else .keep

def mvwG (a b : K) (pred : A → Bool) (s : K → List A) : K → List A :=
  upd (upd s a (mvw pred (s a) (s b)).1) b (mvw pred (s a) (s b)).2

lemma mvw_len (pred : A → Bool) : ∀ (a b : List A), (mvw pred a b).1.length ≤ a.length
  | [], b => by simp [mvw]
  | x :: a, b => by
    unfold mvw
    split_ifs
    · have := mvw_len pred a (x :: b); simp; omega
    · simp

@[simp] lemma upd_apply (s : K → List A) (k j : K) (l : List A) :
    upd s k l j = if j = k then l else s j := by
  by_cases h : j = k <;> simp [upd, h]

lemma upd_self (s : K → List A) (k : K) : upd s k (s k) = s := by
  funext j; by_cases h : j = k <;> simp [upd, h]

lemma upd_comm_ext (s : K → List A) {a b : K} (hab : a ≠ b) (la lb : List A) :
    ∀ k, upd (upd s a la) b lb k = if k = b then lb else if k = a then la else s k := by
  intro k
  by_cases h1 : k = b
  · subst h1; simp
  · by_cases h2 : k = a
    · subst h2; simp [upd_ne _ _ h1, h1]
    · simp [upd_ne _ _ h1, upd_ne _ _ h2, h1, h2]

lemma ps_mvw (a b : K) (hab : a ≠ b) (pred : A → Bool) :
    PolySpec (.loop (mvwT a pred) (.act (mvwF a b))) (mvwG a b pred) := by
  apply PolySpec.loop1 _ _ _ (fun s => (s a).length)
  · intro s
    unfold S
    exact Finset.single_le_sum (f := fun k => (s k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  · intro s h
    unfold mvwT hd at h
    unfold mvwG
    funext k
    cases hs : s a with
    | nil => simp [mvw]; split_ifs <;> simp_all
    | cons x l =>
      simp [hs] at h
      simp [mvw, h]; split_ifs <;> simp_all
  · intro s h
    unfold mvwT hd at h
    cases hs : s a with
    | nil => simp [hs] at h
    | cons x l =>
      simp [hs] at h
      have hstep : StackProg.applyAct (mvwF a b) s = upd (upd s a l) b (x :: s b) := by
        funext k
        by_cases h1 : k = b
        · subst h1; simp [StackProg.applyAct, mvwF, hab.symm, hs, StackAct.apply, hd]
        · by_cases h2 : k = a
          · subst h2; simp [StackProg.applyAct, mvwF, hs, StackAct.apply, h1]
          · simp [StackProg.applyAct, mvwF, h1, h2, StackAct.apply]
      rw [hstep]
      refine ⟨by simp [hs, hab], ?_⟩
      unfold mvwG
      funext k
      simp [hs, mvw, h, hab, hab.symm]
      split_ifs <;> simp_all
end Prims
end Stk

end Sec_Stk1

section Sec_Stk2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Loop
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma S_upd (s : K → List A) (k : K) (l : List A) :
    S (upd s k l) + (s k).length = S s + l.length := by
  unfold S upd
  have h1 := Finset.sum_update_of_mem (f := fun j => (s j).length) (Finset.mem_univ k) (l.length)
  have h2 : ∑ j, (Function.update s k l j).length = ∑ j, Function.update (fun j => (s j).length) k l.length j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = k <;> simp [Function.update, h]
  rw [h2, h1]
  have h3 : ∑ j ∈ (Finset.univ \ {k}), (s j).length + (s k).length = ∑ j, (s j).length := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    simp [Finset.sdiff_singleton_eq_erase]
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

lemma S_le_S_upd (s : K → List A) (k : K) (l : List A) :
    S (upd s k l) ≤ S s + l.length := by
  have := S_upd s k l; omega

/-- general loop lemma: body is a program with a polynomial spec and bounded size growth -/
lemma loop_exec {p : StackProg K A} {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PS p g d)
    (hgrow : ∀ s, t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, ∃ n, n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s ht
    obtain ⟨n1, hn1, e1⟩ := hp s
    obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl
    refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
    · rw [← hm]
      have hg := hgrow s ht
      have hY : S (g s) + c * μ (g s) + 2 ≤ S s + c * μ s + 2 := by
        have : c * μ (g s) + c ≤ c * μ s := by
          have : μ (g s) + 1 ≤ μ s := hlt
          nlinarith
        omega
      have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
        le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
      have h2 : n2 ≤ (μ (g s) + 1) * ((S s + c * μ s + 2) ^ d + 3) :=
        le_trans hn2 (Nat.mul_le_mul_left _ (by
          have := Nat.pow_le_pow_left hY d; omega))
      have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
      have h4 : (μ (g s) + 1 + 1) * ((S s + c * μ s + 2) ^ d + 3) ≤
          (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
      nlinarith
    · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + c * m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s ht']; exact StackProg.Exec.loopFalse ht'

lemma PolySpec.loop {p : StackProg K A} {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PS p g d) (hμ : ∀ s, μ s ≤ S s)
    (hgrow : ∀ s, t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PolySpec (.loop t p) G := by
  refine ⟨(c + 1) * d + 3, fun s => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_exec t G μ hp hgrow hstop hstep s
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + c * μ s + 2 ≤ X ^ (c + 1) := by
    have : S s + c * μ s + 2 ≤ (c + 1) * X := by nlinarith
    have hc : c + 1 ≤ X ^ c := le_trans (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left hX2 c)
    calc _ ≤ (c + 1) * X := this
      _ ≤ X ^ c * X := Nat.mul_le_mul_right _ hc
      _ = X ^ (c + 1) := by rw [pow_succ]
  have a2 : (S s + c * μ s + 2) ^ d ≤ X ^ ((c + 1) * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ ((c + 1) * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + c * μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ ((c + 1) * d + 3) := by rw [hZ]; ring

end Loop
end Stk

end Sec_Stk2

section Sec_Stk3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section PSI
variable {K A : Type} [Fintype K] [DecidableEq K]

/-- polynomial-time spec relative to an invariant `Inv` -/
def PSI (Inv : (K → List A) → Prop) (p : StackProg K A) (g : (K → List A) → (K → List A))
    (d : ℕ) : Prop :=
  ∀ s, Inv s → ∃ n, n ≤ (S s + 2) ^ d ∧ p.Exec s (g s) n

def PSp (Inv : (K → List A) → Prop) (p : StackProg K A) (g : (K → List A) → (K → List A)) : Prop :=
  ∃ d, PSI Inv p g d

lemma PSI.mono {Inv : (K → List A) → Prop} {p : StackProg K A} {g : (K → List A) → (K → List A)}
    {d e : ℕ} (h : PSI Inv p g d) (he : d ≤ e) : PSI Inv p g e := by
  intro s hs
  obtain ⟨n, hn, ex⟩ := h s hs
  exact ⟨n, le_trans hn (pw_mono (S_pos_ge s) he), ex⟩

lemma PSp.weaken {Inv Inv' : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} (h : PSp Inv p g) (hi : ∀ s, Inv' s → Inv s) :
    PSp Inv' p g := by
  obtain ⟨d, h⟩ := h
  exact ⟨d, fun s hs => h s (hi s hs)⟩

lemma PSp.congr {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g g' : (K → List A) → (K → List A)} (h : PSp Inv p g) (hg : ∀ s, Inv s → g s = g' s) :
    PSp Inv p g' := by
  obtain ⟨d, h⟩ := h
  refine ⟨d, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := h s hs
  exact ⟨n, hn, by rw [← hg s hs]; exact e⟩

lemma PSp.of_exec {Inv : (K → List A) → Prop} (p : StackProg K A)
    (g : (K → List A) → (K → List A)) (cost : (K → List A) → ℕ) (d : ℕ)
    (hex : ∀ s, Inv s → p.Exec s (g s) (cost s))
    (hc : ∀ s, Inv s → cost s ≤ (S s + 2) ^ d) : PSp Inv p g :=
  ⟨d, fun s hs => ⟨cost s, hc s hs, hex s hs⟩⟩

lemma PSp.act {Inv : (K → List A) → Prop} (f : (K → Option A) → K → StackAct A) :
    PSp Inv (.act f) (StackProg.applyAct f) :=
  ⟨1, fun s _ => ⟨1, by simp, StackProg.Exec.act f s⟩⟩

lemma PSp.seq {Inv : (K → List A) → Prop} {p q : StackProg K A}
    {g h : (K → List A) → (K → List A)}
    (hp : PSp Inv p g) (hq : PSp Inv q h) (hi : ∀ s, Inv s → Inv (g s)) :
    PSp Inv (.seq p q) (fun s => h (g s)) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨d1 + 3 + (Fintype.card K + d1 + 2) * d2, fun s hs => ?_⟩
  obtain ⟨n1, hn1, e1⟩ := hp s hs
  obtain ⟨n2, hn2, e2⟩ := hq (g s) (hi s hs)
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  set X := S s + 2 with hXd
  have hX : 2 ≤ X := by omega
  have hsz := Exec_size e1
  have hY : S (g s) + 2 ≤ X ^ (Fintype.card K + d1 + 2) := by
    have a1 : X ≤ X ^ 1 := by simp
    have a2 : Fintype.card K * n1 ≤ X ^ (Fintype.card K + d1) :=
      pw_mul (pw_const hX (Fintype.card K)) hn1
    have := pw_add hX a1 a2
    calc S (g s) + 2 ≤ X + Fintype.card K * n1 := by omega
      _ ≤ X ^ (1 + (Fintype.card K + d1) + 1) := this
      _ = _ := by ring_nf
  have b1 : n2 ≤ X ^ ((Fintype.card K + d1 + 2) * d2) :=
    le_trans hn2 (pw_pow hY)
  have b2 : n1 + 1 ≤ X ^ (d1 + 0 + 1) := pw_add hX hn1 (show 1 ≤ X ^ 0 by simp)
  have := pw_add hX b2 b1
  exact le_trans this (pw_mono hX (by omega))

lemma PSp.branch {Inv : (K → List A) → Prop} {p q : StackProg K A}
    {g h : (K → List A) → (K → List A)} (t : (K → Option A) → Bool)
    (hp : PSp Inv p g) (hq : PSp Inv q h) :
    PSp Inv (.branch t p q) (fun s => if t (hd s) = true then g s else h s) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨2 * max d1 d2 + 3, fun s hs => ?_⟩
  have hX : 2 ≤ S s + 2 := by omega
  have key : ∀ n, n ≤ (S s + 2) ^ (max d1 d2) → 1 + n ≤ (S s + 2) ^ (2 * max d1 d2 + 3) := by
    intro n hn
    have h2 : 1 ≤ (S s + 2) ^ (max d1 d2) := Nat.one_le_pow _ _ (by omega)
    have := pw_add hX h2 hn
    exact le_trans this (pw_mono hX (by omega))
  by_cases ht : t (hd s) = true
  · obtain ⟨n, hn, e⟩ := hp s hs
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_pos ht]; exact StackProg.Exec.branchTrue ht e
  · have ht' : t (hd s) = false := by simpa using ht
    obtain ⟨n, hn, e⟩ := hq s hs
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_neg ht]; exact StackProg.Exec.branchFalse ht' e

lemma loop_execI {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSI Inv p g d)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, Inv s → ∃ n, n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s hs ht
    obtain ⟨n1, hn1, e1⟩ := hp s hs
    obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl (hinv s hs ht)
    refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
    · rw [← hm]
      have hg := hgrow s hs ht
      have hY : S (g s) + c * μ (g s) + 2 ≤ S s + c * μ s + 2 := by
        have : c * μ (g s) + c ≤ c * μ s := by
          have : μ (g s) + 1 ≤ μ s := hlt
          nlinarith
        omega
      have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
        le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
      have h2 : n2 ≤ (μ (g s) + 1) * ((S s + c * μ s + 2) ^ d + 3) :=
        le_trans hn2 (Nat.mul_le_mul_left _ (by
          have := Nat.pow_le_pow_left hY d; omega))
      have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
      have h4 : (μ (g s) + 1 + 1) * ((S s + c * μ s + 2) ^ d + 3) ≤
          (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
      nlinarith
    · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + c * m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s hs ht']; exact StackProg.Exec.loopFalse ht'

lemma PSp.loop {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨(c + 1) * d + 3, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execI t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + c * μ s + 2 ≤ X ^ (c + 1) := by
    have : S s + c * μ s + 2 ≤ (c + 1) * X := by nlinarith
    have hc : c + 1 ≤ X ^ c := le_trans (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left hX2 c)
    calc _ ≤ (c + 1) * X := this
      _ ≤ X ^ c * X := Nat.mul_le_mul_right _ hc
      _ = X ^ (c + 1) := by rw [pow_succ]
  have a2 : (S s + c * μ s + 2) ^ d ≤ X ^ ((c + 1) * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ ((c + 1) * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + c * μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ ((c + 1) * d + 3) := by rw [hZ]; ring

/-- single-action loop: growth is at most `card K` per iteration -/
lemma PSp.loop1 {Inv : (K → List A) → Prop}
    (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (StackProg.applyAct f s))
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (StackProg.applyAct f s) < μ s ∧
        G s = G (StackProg.applyAct f s)) :
    PSp Inv (.loop t (.act f)) G := by
  refine PSp.loop (c := Fintype.card K) t G μ (PSp.act f) hμ hinv ?_ hstop hstep
  intro s _ _
  have := Exec_size (StackProg.Exec.act f s)
  omega

end PSI
end Stk

end Sec_Stk3

section Sec_Stk4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Run
variable {K A : Type} [Fintype K] [DecidableEq K]

/-- fuel-bounded iteration of a guarded step -/
def iter (t : (K → List A) → Bool) (g : (K → List A) → (K → List A)) :
    ℕ → (K → List A) → (K → List A)
  | 0, s => s
  | n + 1, s => if t s = true then iter t g n (g s) else s

lemma iter_false (t : (K → List A) → Bool) (g : (K → List A) → (K → List A))
    (s : K → List A) (h : t s = false) (n : ℕ) : iter t g n s = s := by
  cases n <;> simp [iter, h]

lemma iter_succ_true (t : (K → List A) → Bool) (g : (K → List A) → (K → List A))
    (s : K → List A) (h : t s = true) (n : ℕ) : iter t g (n + 1) s = iter t g n (g s) := by
  simp [iter, h]

lemma iter_stable (Inv : (K → List A) → Prop) (t : (K → List A) → Bool)
    (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (hinv : ∀ s, Inv s → t s = true → Inv (g s))
    (hdec : ∀ s, Inv s → t s = true → μ (g s) < μ s) :
    ∀ n s, Inv s → μ s ≤ n → iter t g n s = iter t g (μ s) s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hI h
    by_cases ht : t s = true
    · have hm := hdec s hI ht
      obtain ⟨j, hj⟩ : ∃ j, μ s = j + 1 := ⟨μ s - 1, by omega⟩
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      subst hn'
      rw [hj, iter_succ_true t g s ht, iter_succ_true t g s ht]
      rw [ih n' (by omega) (g s) (hinv s hI ht) (by omega),
        ih j (by omega) (g s) (hinv s hI ht) (by omega)]
    · have ht' : t s = false := by simpa using ht
      rw [iter_false t g s ht', iter_false t g s ht']

/-- the closed-form store map of a loop: iterate the body while the test holds -/
def lrun (t : (K → Option A) → Bool) (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (s : K → List A) : K → List A :=
  iter (fun s => t (hd s)) g (μ s) s

lemma lrun_false (t : (K → Option A) → Bool) (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (s : K → List A) (h : t (hd s) = false) : lrun t g μ s = s :=
  iter_false _ _ s h _

lemma lrun_true (Inv : (K → List A) → Prop) (t : (K → Option A) → Bool)
    (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s)
    (s : K → List A) (hI : Inv s) (h : t (hd s) = true) : lrun t g μ s = lrun t g μ (g s) := by
  have hm := hdec s hI h
  obtain ⟨j, hj⟩ : ∃ j, μ s = j + 1 := ⟨μ s - 1, by omega⟩
  unfold lrun
  rw [hj, iter_succ_true _ _ s h]
  exact iter_stable Inv (fun s => t (hd s)) g μ hinv hdec j (g s) (hinv s hI h) (by omega)

lemma PSp.loopI {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {c : ℕ}
    (t : (K → Option A) → Bool) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → S (g s) ≤ S s + c)
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s) :
    PSp Inv (.loop t p) (lrun t g μ) := by
  refine PSp.loop (c := c) t (lrun t g μ) μ hp hμ hinv hgrow
    (fun s _ h => lrun_false t g μ s h)
    (fun s hs h => ⟨hdec s hs h, lrun_true Inv t g μ hinv hdec s hs h⟩)

lemma lrun_rel (Inv : (K → List A) → Prop) (t : (K → Option A) → Bool)
    (g : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s)
    (Q : (K → List A) → (K → List A) → Prop)
    (hstop : ∀ s, Inv s → t (hd s) = false → Q s s)
    (hstep : ∀ s, Inv s → t (hd s) = true → Q (g s) (lrun t g μ (g s)) → Q s (lrun t g μ (g s))) :
    ∀ s, Inv s → Q s (lrun t g μ s) := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hI
  by_cases h : t (hd s) = true
  · rw [lrun_true Inv t g μ hinv hdec s hI h]
    exact hstep s hI h (ih (μ (g s)) (by have := hdec s hI h; omega) (g s) rfl (hinv s hI h))
  · have h' : t (hd s) = false := by simpa using h
    rw [lrun_false t g μ s h']
    exact hstop s hI h'

lemma PSp.loop1I {Inv : (K → List A) → Prop}
    (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (μ : (K → List A) → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (StackProg.applyAct f s))
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (StackProg.applyAct f s) < μ s) :
    PSp Inv (.loop t (.act f)) (lrun t (StackProg.applyAct f) μ) := by
  refine PSp.loopI (c := Fintype.card K) t μ (PSp.act f) hμ hinv ?_ hdec
  intro s _ _
  have := Exec_size (StackProg.Exec.act f s)
  omega

lemma S_frame (R : Finset K) (s s' : K → List A) (h : ∀ k, k ∉ R → s' k = s k) :
    S s' + ∑ k ∈ R, (s k).length = S s + ∑ k ∈ R, (s' k).length := by
  unfold S
  have e : ∀ u : K → List A, ∑ k, (u k).length = ∑ k ∈ R, (u k).length + ∑ k ∈ Rᶜ, (u k).length := by
    intro u; rw [Finset.sum_add_sum_compl]
  rw [e s', e s]
  have : ∑ k ∈ Rᶜ, (s' k).length = ∑ k ∈ Rᶜ, (s k).length :=
    Finset.sum_congr rfl (fun k hk => by rw [h k (by simpa using hk)])
  omega

lemma len_le_S (s : K → List A) (k : K) : (s k).length ≤ S s :=
  Finset.single_le_sum (f := fun k => (s k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end Run
end Stk

end Sec_Stk4

section Sec_Stk5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Macros
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma sq_aux (x S' : ℕ) (h : x ≤ S') : 6 * x + 3 ≤ (S' + 2) ^ 2 := by
  have h2 : 2 * S' ≤ S' * S' + 1 := by
    zify; nlinarith [sq_nonneg ((S' : ℤ) - 1)]
  nlinarith

lemma PSp.push (Inv : (K → List A) → Prop) (r : K) (a : A) :
    PSp Inv (pushProg r a) (fun s => upd s r (a :: s r)) :=
  PSp.of_exec _ _ (fun _ => 1) 1 (fun s _ => (stack_basic_macros r s).1 a)
    (fun s _ => by simp)

lemma PSp.pop (Inv : (K → List A) → Prop) (r : K) :
    PSp Inv (popProg r) (fun s => upd s r (s r).tail) :=
  PSp.of_exec _ _ (fun _ => 1) 1 (fun s _ => (stack_basic_macros r s).2.1)
    (fun s _ => by simp)

lemma PSp.clear (Inv : (K → List A) → Prop) (r : K) :
    PSp Inv (clearProg r) (fun s => upd s r []) := by
  refine PSp.of_exec _ _ (fun s => 3 * (s r).length + 1) 2
    (fun s _ => (stack_basic_macros r s).2.2) (fun s _ => ?_)
  have := sq_aux _ _ (len_le_S s r)
  omega

lemma PSp.mvAll (Inv : (K → List A) → Prop) (a b : K) (hab : a ≠ b) :
    PSp Inv (transferProg a (fun k => decide (k = b)))
      (fun s => upd (upd s a []) b ((s a).reverse ++ s b)) := by
  refine PSp.of_exec _ _ (fun s => 3 * (s a).length + 1) 2 (fun s _ => ?_) (fun s _ => ?_)
  · have := stack_transfer a (fun k => decide (k = b)) s
    convert this using 1
    funext k
    by_cases h1 : k = a
    · subst h1; simp [transferStore, upd, Function.update_apply, hab]
    · by_cases h2 : k = b
      · subst h2; simp [transferStore, upd, h1]
      · simp [transferStore, upd, h1, h2]
  · have := sq_aux _ _ (len_le_S s a)
    omega

lemma PSp.copy (Inv : (K → List A) → Prop) (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    PSp (fun s => Inv s ∧ s c = []) (copyProg a b c) (fun s => upd s b (s a ++ s b)) := by
  refine PSp.of_exec _ _ (fun s => 6 * (s a).length + 3) 2 (fun s hs => ?_) (fun s _ => ?_)
  · exact stack_copy a b c hab hac hbc s hs.2
  · have := sq_aux _ _ (len_le_S s a)
    omega

def emb4 (a b c d : K) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : Fin 4 ↪ K :=
  ⟨![a, b, c, d], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

lemma PSp.repcopy (Inv : (K → List A) → Prop) (a b c d : K) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    PSp (fun s => Inv s ∧ s d = []) (repeatCopyProg (emb4 a b c d hab hac had hbc hbd hcd))
      (fun s => upd (upd s c []) b ((List.replicate (s c).length (s a)).flatten ++ s b)) := by
  refine PSp.of_exec _ _ (fun s => (6 * (s a).length + 7) * (s c).length + 1) 3
    (fun s hs => ?_) (fun s _ => ?_)
  · exact stack_repeat_copy (emb4 a b c d hab hac had hbc hbd hcd) s hs.2
  · have h1 := len_le_S s a
    have h2 := len_le_S s c
    have h3 : (6 * (s a).length + 7) * (s c).length + 1 ≤ (6 * S s + 7) * S s + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul (by omega) h2) 1
    have h4 : (6 * S s + 7) * S s + 1 ≤ (S s + 2) ^ 3 := by
      zify; nlinarith [sq_nonneg ((S s : ℤ)), sq_nonneg ((S s : ℤ) - 1), Nat.zero_le (S s)]
    omega

lemma PSp.syncpop (Inv : (K → List A) → Prop) (i j : K) (hij : i ≠ j) :
    PSp Inv (syncPopProg i j)
      (fun s => upd (upd s i ((s i).drop (min (s i).length (s j).length)))
        j ((s j).drop (min (s i).length (s j).length))) := by
  refine PSp.of_exec _ _ (fun s => 3 * min (s i).length (s j).length + 1) 2
    (fun s _ => stack_sync_pop i j hij s) (fun s _ => ?_)
  have := sq_aux _ _ (le_trans (min_le_left (s i).length (s j).length) (len_le_S s i))
  omega

end Macros
end Stk

end Sec_Stk5

section Sec_TmNe
open CookPvsNP
set_option autoImplicit false

namespace Stk

inductive NQ | q0 | acc | rej
  deriving DecidableEq

instance : Fintype NQ where
  elems := {NQ.q0, NQ.acc, NQ.rej}
  complete := by intro x; cases x <;> simp

def neTM (Γ : Type) : TM Γ where
  Q := NQ
  q₀ := NQ.q0
  qaccept := NQ.acc
  qreject := NQ.rej
  accept_ne_reject := by decide
  δ := fun q s => match q with
    | NQ.q0 => ((if s.isSome then NQ.acc else NQ.rej), s, Move.right)
    | q => (q, s, Move.right)

lemma neTM_run (Γ : Type) (w : List Γ) (n : ℕ) :
    ((neTM Γ).run (n + 1) ((neTM Γ).init w)).state = if w = [] then NQ.rej else NQ.acc := by
  have h1 : ((neTM Γ).step ((neTM Γ).init w)).state = if w = [] then NQ.rej else NQ.acc := by
    cases w <;> simp [TM.step, TM.init, TM.IsHalting, neTM]
  have hfix : ∀ c : Cfg Γ (neTM Γ).Q, (c.state = NQ.acc ∨ c.state = NQ.rej) → (neTM Γ).step c = c := by
    intro c hc
    have : (neTM Γ).IsHalting c := hc
    unfold TM.step; rw [if_pos this]
  have hst : ∀ m, ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state =
      if w = [] then NQ.rej else NQ.acc := by
    intro m
    induction m with
    | zero => simpa [TM.run] using h1
    | succ m ih =>
      have h2 : (neTM Γ).run (m + 1 + 1) ((neTM Γ).init w) =
          (neTM Γ).step ((neTM Γ).run (m + 1) ((neTM Γ).init w)) := by
        simp only [TM.run]; rw [Function.iterate_succ_apply']
      rw [h2]
      have hh : ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state = NQ.acc ∨
          ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state = NQ.rej := by
        rw [ih]; split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
      exact (congrArg Cfg.state (hfix _ hh)).trans ih
  exact hst n

theorem neLang_mem_P (Γ : Type) [Fintype Γ] : {w : List Γ | w ≠ []} ∈ P Γ := by
  have e : ∀ w : List Γ, w.map (⇑(Function.Embedding.refl Γ)) = w := fun w => List.map_id w
  refine ⟨Γ, inferInstance, Function.Embedding.refl Γ, neTM Γ, 1, ?_, ?_⟩
  · intro w
    obtain ⟨m, hm⟩ : ∃ m, w.length ^ 1 + 1 = m + 1 := ⟨w.length, by simp⟩
    have := neTM_run Γ w m
    rw [e]
    unfold TM.HaltsWithin TM.IsHalting
    rw [hm]
    show _ = NQ.acc ∨ _ = NQ.rej
    rw [this]
    split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
  · intro w
    rw [e]
    constructor
    · intro hw
      refine ⟨1, ?_⟩
      have := neTM_run Γ w 0
      rw [if_neg hw] at this
      exact this
    · rintro ⟨n, hn⟩ rfl
      cases n with
      | zero => exact absurd hn (by simp [TM.run, TM.init, neTM])
      | succ n =>
        have := neTM_run Γ ([] : List Γ) n
        rw [if_pos rfl] at this
        have h2 : NQ.rej = NQ.acc := this.symm.trans hn
        exact absurd h2 (by decide)

end Stk

end Sec_TmNe

section Sec_RB
section Sec_Ver1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

inductive Reg
  | 
IN  | WR  | W  | N  | K  | TR  | T  | TMP  | MB  | NB  | KB  | U  | F  | HU  | C  | RC  | BAD  | OUT  | KP  | NC  | PP  | TC  | T2  | K2  | TM  | NC2  | TT  | FP  | H  | MR  | KR  | LT
  deriving DecidableEq

instance : Fintype Reg where
  elems := {Reg.IN, Reg.WR, Reg.W, Reg.N, Reg.K, Reg.TR, Reg.T, Reg.TMP, Reg.MB, Reg.NB, Reg.KB, Reg.U, Reg.F, Reg.HU, Reg.C, Reg.RC, Reg.BAD, Reg.OUT, Reg.KP, Reg.NC, Reg.PP, Reg.TC, Reg.T2, Reg.K2, Reg.TM, Reg.NC2, Reg.TT, Reg.FP, Reg.H, Reg.MR, Reg.KR, Reg.LT}
  complete := by intro x; cases x <;> decide

abbrev Al : Type := Option (BSym ⊕ BSym)
abbrev St : Type := Reg → List Al
abbrev Prog : Type := StackProg Reg Al

def tk (b : BSym) : Al := some (Sum.inl b)
def ty (b : BSym) : Al := some (Sum.inr b)
def mk : Al := none

/-- test: top of `r` satisfies `p` -/
def topP (r : Reg) (p : Al → Bool) (h : Reg → Option Al) : Bool :=
  match h r with | some x => p x | none => false
def topS (r : Reg) (h : Reg → Option Al) : Bool := (h r).isSome
def topN (r : Reg) (h : Reg → Option Al) : Bool := (h r).isNone

/-- skip -/
def skipP : Prog := .act (fun _ _ => .keep)

lemma applyAct_keep (s : St) : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
  funext k; simp [StackProg.applyAct, StackAct.apply]

def Gi (s : St) : Prop := s Reg.C = [] ∧ s Reg.RC = []

def wb (s : St) (c : ℕ) : St := upd s Reg.BAD (List.replicate c mk ++ s Reg.BAD)

lemma wb_apply (s : St) (c : ℕ) (r : Reg) :
    wb s c r = if r = Reg.BAD then List.replicate c mk ++ s Reg.BAD else s r := by
  simp [wb]

def badIf (t : (Reg → Option Al) → Bool) : Prog := .branch t (pushProg Reg.BAD mk) skipP

lemma PSp.skip (Inv : St → Prop) : PSp Inv skipP id := by
  have := PSp.act (Inv := Inv) (fun _ _ => (StackAct.keep : StackAct Al))
  refine PSp.congr this ?_
  intro s _
  exact applyAct_keep s

lemma PSp.badIf (Inv : St → Prop) (t : (Reg → Option Al) → Bool) :
    PSp Inv (badIf t) (fun s => if t (hd s) = true then wb s 1 else s) := by
  have h := PSp.branch (Inv := Inv) t (PSp.push Inv Reg.BAD mk) (PSp.skip Inv)
  refine PSp.congr h ?_
  intro s _
  simp [wb, mk]

end Stk

end Sec_Ver1

section Sec_Ver2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma mvw_eq (p : Al → Bool) : ∀ (a b : List Al),
    mvw p a b = (a.dropWhile p, (a.takeWhile p).reverse ++ b)
  | [], b => by simp [mvw]
  | x :: a, b => by
    unfold mvw
    by_cases h : p x = true
    · simp [h, mvw_eq p a (x :: b), List.takeWhile_cons_of_pos, List.dropWhile_cons_of_pos]
    · have h' : p x = false := by simpa using h
      simp [h']

def safe (r : Reg) : Prop := r ≠ Reg.C ∧ r ≠ Reg.RC

instance (r : Reg) : Decidable (safe r) := by unfold safe; infer_instance

def Gad (p : Prog) (g : St → St) : Prop := PSp Gi p g ∧ ∀ s, Gi s → Gi (g s)

lemma Gi_upd (s : St) (r : Reg) (l : List Al) (hr : safe r) (h : Gi s) : Gi (upd s r l) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨r1, r2⟩ := hr
  simp [Gi, upd_apply, r1, r2, r1.symm, r2.symm, h1, h2]

lemma Gad.seq {p q : Prog} {g h : St → St} (hp : Gad p g) (hq : Gad q h) :
    Gad (.seq p q) (fun s => h (g s)) :=
  ⟨PSp.seq hp.1 hq.1 hp.2, fun s hs => hq.2 _ (hp.2 s hs)⟩

lemma Gad.branch {p q : Prog} {g h : St → St} (t : (Reg → Option Al) → Bool)
    (hp : Gad p g) (hq : Gad q h) :
    Gad (.branch t p q) (fun s => if t (hd s) = true then g s else h s) :=
  ⟨PSp.branch t hp.1 hq.1, fun s hs => by
    by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact hp.2 s hs
    · simp only [ht, if_false]; exact hq.2 s hs⟩

lemma Gad.congr {p : Prog} {g g' : St → St} (h : Gad p g) (hg : ∀ s, Gi s → g s = g' s) :
    Gad p g' :=
  ⟨PSp.congr h.1 hg, fun s hs => by rw [← hg s hs]; exact h.2 s hs⟩

lemma Gad.skip : Gad skipP id := ⟨PSp.skip Gi, fun _ h => h⟩

lemma Gi_wb (s : St) (c : ℕ) (h : Gi s) : Gi (wb s c) := by
  unfold wb; exact Gi_upd s _ _ (by decide) h

lemma Gad.badIf (t : (Reg → Option Al) → Bool) :
    Gad (badIf t) (fun s => if t (hd s) = true then wb s 1 else s) :=
  ⟨PSp.badIf Gi t, fun s hs => by
    by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact Gi_wb s 1 hs
    · simp only [ht, if_false]; exact hs⟩

lemma Gad.push (r : Reg) (a : Al) (hr : safe r) :
    Gad (pushProg r a) (fun s => upd s r (a :: s r)) :=
  ⟨PSp.push Gi r a, fun s hs => Gi_upd s r _ hr hs⟩

lemma Gad.pop (r : Reg) (hr : safe r) :
    Gad (popProg r) (fun s => upd s r (s r).tail) :=
  ⟨PSp.pop Gi r, fun s hs => Gi_upd s r _ hr hs⟩

lemma Gad.clear (r : Reg) (hr : safe r) :
    Gad (clearProg r) (fun s => upd s r []) :=
  ⟨PSp.clear Gi r, fun s hs => Gi_upd s r _ hr hs⟩

lemma Gad.mvA (a b : Reg) (hab : a ≠ b) (ha : safe a) (hb : safe b) :
    Gad (transferProg a (fun k => decide (k = b)))
      (fun s => upd (upd s a []) b ((s a).reverse ++ s b)) :=
  ⟨PSp.mvAll Gi a b hab, fun s hs => Gi_upd _ _ _ hb (Gi_upd _ _ _ ha hs)⟩

lemma Gad.copy (a b : Reg) (hab : a ≠ b) (ha : safe a) (hb : safe b) :
    Gad (copyProg a b Reg.C) (fun s => upd s b (s a ++ s b)) := by
  refine ⟨?_, fun s hs => Gi_upd _ _ _ hb hs⟩
  have := PSp.copy Gi a b Reg.C hab ha.1 hb.1
  exact PSp.weaken this (fun s hs => ⟨hs, hs.1⟩)

lemma Gad.syncpop (i j : Reg) (hij : i ≠ j) (hi : safe i) (hj : safe j) :
    Gad (syncPopProg i j)
      (fun s => upd (upd s i ((s i).drop (min (s i).length (s j).length)))
        j ((s j).drop (min (s i).length (s j).length))) :=
  ⟨PSp.syncpop Gi i j hij, fun s hs => Gi_upd _ _ _ hj (Gi_upd _ _ _ hi hs)⟩

lemma Gad.mvP (a b : Reg) (hab : a ≠ b) (ha : safe a) (hb : safe b) (p : Al → Bool) :
    Gad (StackProg.loop (mvwT a p) (.act (mvwF a b)))
      (fun s => upd (upd s a ((s a).dropWhile p)) b (((s a).takeWhile p).reverse ++ s b)) := by
  obtain ⟨d, hd⟩ := ps_mvw a b hab p
  have h : Gad (StackProg.loop (mvwT a p) (.act (mvwF a b))) (mvwG a b p) :=
    ⟨⟨d, fun s _ => hd s⟩, fun s hs => by
      unfold mvwG; exact Gi_upd _ _ _ hb (Gi_upd _ _ _ ha hs)⟩
  refine Gad.congr h (fun s _ => ?_)
  simp [mvwG, mvw_eq]

end Stk

end Sec_Ver2

section Sec_Ver3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def isInl : Al → Bool | some (Sum.inl _) => true | _ => false
def isA (c : Al) : Al → Bool := fun a => decide (a = c)
def isBitY : Al → Bool := fun a => decide (a = ty BSym.zero ∨ a = ty BSym.one)
def isBitW : Al → Bool := fun a => decide (a = tk BSym.zero ∨ a = tk BSym.one)

def sq (p q : Prog) : Prog := .seq p q
def mvP (a b : Reg) (p : Al → Bool) : Prog := StackProg.loop (mvwT a p) (.act (mvwF a b))
def mvA (a b : Reg) : Prog := transferProg a (fun k => decide (k = b))
def popIf (r : Reg) (p : Al → Bool) : Prog := .branch (topP r p) (popProg r) (pushProg Reg.BAD mk)

def gMvP (a b : Reg) (p : Al → Bool) (s : St) : St :=
  upd (upd s a ((s a).dropWhile p)) b (((s a).takeWhile p).reverse ++ s b)
def gMvA (a b : Reg) (s : St) : St := upd (upd s a []) b ((s a).reverse ++ s b)
def gPopIf (r : Reg) (p : Al → Bool) (s : St) : St :=
  if topP r p (hd s) = true then upd s r (s r).tail else wb s 1
def gBadIf (t : (Reg → Option Al) → Bool) (s : St) : St := if t (hd s) = true then wb s 1 else s
def gPush (r : Reg) (a : Al) (s : St) : St := upd s r (a :: s r)
def gPop (r : Reg) (s : St) : St := upd s r (s r).tail
def gClear (r : Reg) (s : St) : St := upd s r []
def gCopy (a b : Reg) (s : St) : St := upd s b (s a ++ s b)

lemma gad_mvP (a b : Reg) (p : Al → Bool) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) : Gad (mvP a b p) (gMvP a b p) := Gad.mvP a b hab ha hb p
lemma gad_mvA (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) : Gad (mvA a b) (gMvA a b) := Gad.mvA a b hab ha hb
lemma gad_popIf (r : Reg) (p : Al → Bool) (hr : safe r := by decide) :
    Gad (popIf r p) (gPopIf r p) := by
  have h := Gad.branch (topP r p) (Gad.pop r hr) (Gad.push Reg.BAD mk (by decide))
  refine Gad.congr h (fun s _ => ?_)
  simp [gPopIf, wb, mk]
lemma gad_badIf (t : (Reg → Option Al) → Bool) : Gad (badIf t) (gBadIf t) := Gad.badIf t
lemma gad_push (r : Reg) (a : Al) (hr : safe r := by decide) :
    Gad (pushProg r a) (gPush r a) := Gad.push r a hr
lemma gad_pop (r : Reg) (hr : safe r := by decide) : Gad (popProg r) (gPop r) := Gad.pop r hr
lemma gad_clear (r : Reg) (hr : safe r := by decide) : Gad (clearProg r) (gClear r) :=
  Gad.clear r hr
lemma gad_copy (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) : Gad (copyProg a b Reg.C) (gCopy a b) := Gad.copy a b hab ha hb


def Sticky (g : St → St) : Prop := ∀ s, s Reg.BAD ≠ [] → g s Reg.BAD ≠ []

def Gs (p : Prog) (g T : St → St) (ok : St → Prop) : Prop :=
  Gad p g ∧ Sticky g ∧ (∀ s, T s Reg.BAD = s Reg.BAD) ∧
    ∀ s, Gi s → s Reg.BAD = [] → ((g s Reg.BAD = [] ↔ ok s) ∧ (ok s → g s = T s))

lemma Gs.seq {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 : St → Prop}
    (h1 : Gs p g1 T1 ok1) (h2 : Gs q g2 T2 ok2) :
    Gs (.seq p q) (fun s => g2 (g1 s)) (fun s => T2 (T1 s)) (fun s => ok1 s ∧ ok2 (T1 s)) := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.seq a1 a2, fun s hs => st2 _ (st1 s hs), fun s => by show T2 (T1 s) _ = _; rw [c2, c1], ?_⟩
  intro s hi hb
  obtain ⟨e1, f1⟩ := s1 s hi hb
  by_cases ho : ok1 s
  · have hg := f1 ho
    have hb' : T1 s Reg.BAD = [] := by rw [c1]; exact hb
    have hi' : Gi (T1 s) := by rw [← hg]; exact a1.2 s hi
    obtain ⟨e2, f2⟩ := s2 _ hi' hb'
    simp only [hg]
    exact ⟨by rw [e2]; simp [ho], fun h => f2 h.2⟩
  · have : g1 s Reg.BAD ≠ [] := fun h => ho (e1.1 h)
    refine ⟨?_, fun h => absurd h.1 ho⟩
    simp only
    constructor
    · intro h; exact absurd h (st2 _ this)
    · intro h; exact absurd h.1 ho

lemma Gs.branch {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 : St → Prop}
    (t : (Reg → Option Al) → Bool)
    (h1 : Gs p g1 T1 ok1) (h2 : Gs q g2 T2 ok2) :
    Gs (.branch t p q) (fun s => if t (hd s) = true then g1 s else g2 s)
      (fun s => if t (hd s) = true then T1 s else T2 s)
      (fun s => if t (hd s) = true then ok1 s else ok2 s) := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.branch t a1 a2, fun s hs => ?_, fun s => ?_, fun s hi hb => ?_⟩
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact st1 s hs
    · simp only [ht, if_false]; exact st2 s hs
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact c1 s
    · simp only [ht, if_false]; exact c2 s
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact s1 s hi hb
    · simp only [ht, if_false]; exact s2 s hi hb

lemma Gs.congr {p : Prog} {g T T' : St → St} {ok ok' : St → Prop} (h : Gs p g T ok)
    (hT : ∀ s, Gi s → T s = T' s) (hok : ∀ s, Gi s → (ok s ↔ ok' s))
    (hT' : ∀ s, T' s Reg.BAD = s Reg.BAD) : Gs p g T' ok' := by
  obtain ⟨a, st, c, s⟩ := h
  refine ⟨a, st, hT', fun s' hi hb => ?_⟩
  obtain ⟨e, f⟩ := s s' hi hb
  exact ⟨by rw [e, hok s' hi], fun h => by rw [← hT s' hi]; exact f ((hok s' hi).2 h)⟩

lemma Gs.total {p : Prog} {g : St → St} (h : Gad p g) (hb : ∀ s, g s Reg.BAD = s Reg.BAD) :
    Gs p g g (fun _ => True) :=
  ⟨h, fun s hs => by rw [hb]; exact hs, hb, fun s _ h0 => ⟨by simp [hb, h0], fun _ => rfl⟩⟩

lemma gMvP_BAD (a b : Reg) (p : Al → Bool) (ha : a ≠ Reg.BAD) (hb : b ≠ Reg.BAD) (s : St) :
    gMvP a b p s Reg.BAD = s Reg.BAD := by simp [gMvP, upd_apply, ha, hb, ha.symm, hb.symm]
lemma gMvA_BAD (a b : Reg) (ha : a ≠ Reg.BAD) (hb : b ≠ Reg.BAD) (s : St) :
    gMvA a b s Reg.BAD = s Reg.BAD := by simp [gMvA, upd_apply, ha, hb, ha.symm, hb.symm]
lemma gPush_BAD (r : Reg) (a : Al) (hr : r ≠ Reg.BAD) (s : St) :
    gPush r a s Reg.BAD = s Reg.BAD := by simp [gPush, upd_apply, hr, hr.symm]
lemma gPop_BAD (r : Reg) (hr : r ≠ Reg.BAD) (s : St) :
    gPop r s Reg.BAD = s Reg.BAD := by simp [gPop, upd_apply, hr, hr.symm]
lemma gClear_BAD (r : Reg) (hr : r ≠ Reg.BAD) (s : St) :
    gClear r s Reg.BAD = s Reg.BAD := by simp [gClear, upd_apply, hr, hr.symm]
lemma gCopy_BAD (a b : Reg) (hb : b ≠ Reg.BAD) (s : St) :
    gCopy a b s Reg.BAD = s Reg.BAD := by simp [gCopy, upd_apply, hb, hb.symm]

lemma gs_mvP (a b : Reg) (p : Al → Bool) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (ha' : a ≠ Reg.BAD := by decide) (hb' : b ≠ Reg.BAD := by decide) :
    Gs (mvP a b p) (gMvP a b p) (gMvP a b p) (fun _ => True) :=
  Gs.total (gad_mvP a b p hab ha hb) (gMvP_BAD a b p ha' hb')
lemma gs_mvA (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (ha' : a ≠ Reg.BAD := by decide) (hb' : b ≠ Reg.BAD := by decide) :
    Gs (mvA a b) (gMvA a b) (gMvA a b) (fun _ => True) :=
  Gs.total (gad_mvA a b hab ha hb) (gMvA_BAD a b ha' hb')
lemma gs_push (r : Reg) (a : Al) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (pushProg r a) (gPush r a) (gPush r a) (fun _ => True) :=
  Gs.total (gad_push r a hr) (gPush_BAD r a hr')
lemma gs_pop (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (popProg r) (gPop r) (gPop r) (fun _ => True) :=
  Gs.total (gad_pop r hr) (gPop_BAD r hr')
lemma gs_clear (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (clearProg r) (gClear r) (gClear r) (fun _ => True) :=
  Gs.total (gad_clear r hr) (gClear_BAD r hr')
lemma gs_copy (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (hb' : b ≠ Reg.BAD := by decide) :
    Gs (copyProg a b Reg.C) (gCopy a b) (gCopy a b) (fun _ => True) :=
  Gs.total (gad_copy a b hab ha hb) (gCopy_BAD a b hb')

lemma gs_badIf (t : (Reg → Option Al) → Bool) :
    Gs (badIf t) (gBadIf t) id (fun s => t (hd s) = false) := by
  refine ⟨gad_badIf t, fun s hs => ?_, fun _ => rfl, fun s _ hb => ?_⟩
  · unfold gBadIf; split_ifs <;> simp [wb, hs]
  · unfold gBadIf
    by_cases ht : t (hd s) = true
    · simp [ht, wb, hb]
    · have : t (hd s) = false := by simpa using ht
      simp [this, hb]

lemma gs_popIf (r : Reg) (p : Al → Bool) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (popIf r p) (gPopIf r p) (gPop r) (fun s => topP r p (hd s) = true) := by
  refine ⟨gad_popIf r p hr, fun s hs => ?_, gPop_BAD r hr', fun s _ hb => ?_⟩
  · unfold gPopIf; split_ifs <;> simp [wb, upd_apply, hs, hr', hr'.symm]
  · unfold gPopIf
    by_cases ht : topP r p (hd s) = true
    · simp [ht, gPop, hb, upd_apply, hr', hr'.symm]
    · simp [ht, wb, hb, mk]

end Stk

end Sec_Ver3

section Sec_Ver4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def init (x : List Al) : St := fun r => if r = Reg.IN then x else []
lemma Gi_init (x : List Al) : Gi (init x) := by simp [Gi, init]

def tyb (b : Bool) : Al := ty (if b then BSym.one else BSym.zero)
def tkb (b : Bool) : Al := tk (if b then BSym.one else BSym.zero)

lemma pre_split {p : Al → Bool} {A rest : List Al} (hA : ∀ a ∈ A, p a = true)
    (hr : ∀ a, rest.head? = some a → p a = false) :
    (A ++ rest).takeWhile p = A ∧ (A ++ rest).dropWhile p = rest := by
  refine ⟨?_, List.dropWhile_append_of_pos hA |>.trans ?_⟩
  · rw [List.takeWhile_append_of_pos hA]
    cases rest with
    | nil => simp
    | cons a r => simp [hr a rfl]
  · cases rest with
    | nil => simp
    | cons a r => simp [hr a rfl]

lemma tw_split (p : Al → Bool) (l : List Al) :
    l = l.takeWhile p ++ l.dropWhile p ∧ (∀ a ∈ l.takeWhile p, p a = true) :=
  ⟨List.takeWhile_append_dropWhile.symm, fun _ h => List.mem_takeWhile_imp h⟩

lemma isA_iff {c a : Al} : isA c a = true ↔ a = c := by simp [isA]

lemma rep_of_all {c : Al} {l : List Al} (h : ∀ a ∈ l, isA c a = true) :
    l = List.replicate l.length c :=
  List.eq_replicate_iff.2 ⟨rfl, fun b hb => isA_iff.1 (h b hb)⟩

lemma bits_of_all {l : List Al} (h : ∀ a ∈ l, isBitY a = true) : ∃ t : List Bool, l = t.map tyb := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a r ih =>
    obtain ⟨t, ht⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    simp only [isBitY, decide_eq_true_eq] at ha
    rcases ha with ha | ha
    · exact ⟨false :: t, by simp [tyb, ha, ht]⟩
    · exact ⟨true :: t, by simp [tyb, ha, ht]⟩

lemma inl_of_all {l : List Al} (h : ∀ a ∈ l, isInl a = true) : ∃ w : List BSym, l = w.map tk := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a r ih =>
    obtain ⟨t, ht⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    cases a with
    | none => simp [isInl] at ha
    | some v =>
      cases v with
      | inl b => exact ⟨b :: t, by simp [tk, ht]⟩
      | inr b => simp [isInl] at ha


def Fm (w : List BSym) (a b : ℕ) (t : List Bool) : List Al :=
  w.map tk ++ mk :: (List.replicate a (ty BSym.sep) ++ List.replicate b (ty BSym.minus) ++ t.map tyb)

def stA : Prog :=
  sq (mvP Reg.IN Reg.WR isInl) <| sq (popIf Reg.IN (isA mk)) <| sq (mvA Reg.WR Reg.W) <|
  sq (mvP Reg.IN Reg.N (isA (ty BSym.sep))) <| sq (mvP Reg.IN Reg.K (isA (ty BSym.minus))) <|
  sq (mvP Reg.IN Reg.TR isBitY) <| sq (mvA Reg.TR Reg.T) <| badIf (topS Reg.IN)

def A1 (s : St) : St := gMvP Reg.IN Reg.WR isInl s
def A2 (s : St) : St := gPop Reg.IN (A1 s)
def A3 (s : St) : St := gMvA Reg.WR Reg.W (A2 s)
def A4 (s : St) : St := gMvP Reg.IN Reg.N (isA (ty BSym.sep)) (A3 s)
def A5 (s : St) : St := gMvP Reg.IN Reg.K (isA (ty BSym.minus)) (A4 s)
def A6 (s : St) : St := gMvP Reg.IN Reg.TR isBitY (A5 s)
def A7 (s : St) : St := gMvA Reg.TR Reg.T (A6 s)
def okA (s : St) : Prop := topP Reg.IN (isA mk) (hd (A1 s)) = true ∧ topS Reg.IN (hd (A7 s)) = false

def gA : St → St := fun s =>
  gBadIf (topS Reg.IN) (gMvA Reg.TR Reg.T (gMvP Reg.IN Reg.TR isBitY (
  gMvP Reg.IN Reg.K (isA (ty BSym.minus)) (gMvP Reg.IN Reg.N (isA (ty BSym.sep)) (
  gMvA Reg.WR Reg.W (gPopIf Reg.IN (isA mk) (gMvP Reg.IN Reg.WR isInl s)))))))

lemma gs_stA : Gs stA gA A7 okA := by
  have h := Gs.seq (gs_mvP Reg.IN Reg.WR isInl) <|
    Gs.seq (gs_popIf Reg.IN (isA mk)) <|
    Gs.seq (gs_mvA Reg.WR Reg.W) <|
    Gs.seq (gs_mvP Reg.IN Reg.N (isA (ty BSym.sep))) <|
    Gs.seq (gs_mvP Reg.IN Reg.K (isA (ty BSym.minus))) <|
    Gs.seq (gs_mvP Reg.IN Reg.TR isBitY) <|
    Gs.seq (gs_mvA Reg.TR Reg.T) <|
    gs_badIf (topS Reg.IN)
  refine Gs.congr (p := stA) h (fun s _ => rfl) (fun s _ => ?_) (fun s => ?_)
  · simp only [okA, A1, A2, A3, A4, A5, A6, A7, id]; tauto
  · simp [A7, A6, A5, A4, A3, A2, A1, gMvA, gMvP, gPop, upd_apply]


def stateA (w : List BSym) (a b : ℕ) (t : List Bool) : St := fun r =>
  match r with
  | Reg.W => w.map tk
  | Reg.N => List.replicate a (ty BSym.sep)
  | Reg.K => List.replicate b (ty BSym.minus)
  | Reg.T => t.map tyb
  | _ => []

lemma isInl_tk (b : BSym) : isInl (tk b) = true := by simp [tk, isInl]
lemma isA_self (c : Al) : isA c c = true := by simp [isA]
lemma isBitY_tyb (b : Bool) : isBitY (tyb b) = true := by cases b <;> simp [isBitY, tyb]

lemma stA_dec (x : List Al) :
    (okA (init x) → ∃ w a b t, x = Fm w a b t) := by
  intro ⟨h1, h2⟩
  simp only [A1, A2, A3, A4, A5, A6, A7, gMvP, gMvA, gPop, topP, topS, hd, init, upd_apply] at h1 h2
  simp at h1 h2
  obtain ⟨hx0, hw0⟩ := tw_split isInl x
  obtain ⟨w, hw⟩ := inl_of_all hw0
  generalize List.dropWhile isInl x = r1 at h1 h2 hx0
  cases r1 with
  | nil => simp at h1
  | cons c r2 =>
    simp only [List.head?_cons, isA_iff] at h1
    have hc : c = mk := h1
    subst hc
    obtain ⟨hx1, hs1⟩ := tw_split (isA (ty BSym.sep)) r2
    obtain ⟨hx2, hs2⟩ := tw_split (isA (ty BSym.minus)) (r2.dropWhile (isA (ty BSym.sep)))
    obtain ⟨tt, htt⟩ := bits_of_all h2
    simp only [List.tail_cons] at h2
    refine ⟨w, (r2.takeWhile (isA (ty BSym.sep))).length, ((r2.dropWhile (isA (ty BSym.sep))).takeWhile (isA (ty BSym.minus))).length, tt, ?_⟩
    rw [rep_of_all hs1] at hx1
    rw [rep_of_all hs2] at hx2
    unfold Fm
    rw [← htt, ← hw]
    rw [hx0]
    congr 2
    conv_lhs => rw [hx1, hx2]
    simp


lemma tyb_ne_sep (b : Bool) : isA (ty BSym.sep) (tyb b) = false := by cases b <;> simp [isA, tyb, ty]
lemma tyb_ne_minus (b : Bool) : isA (ty BSym.minus) (tyb b) = false := by cases b <;> simp [isA, tyb, ty]
lemma minus_ne_sep : isA (ty BSym.sep) (ty BSym.minus) = false := by simp [isA, ty]
lemma isInl_mk : isInl mk = false := by simp [mk, isInl]
lemma sep_isBitY : isBitY (ty BSym.sep) = false := by simp [isBitY, ty]
lemma minus_isBitY : isBitY (ty BSym.minus) = false := by simp [isBitY, ty]

lemma stA_eval (w : List BSym) (a b : ℕ) (t : List Bool) :
    okA (init (Fm w a b t)) ∧ A7 (init (Fm w a b t)) = stateA w a b t := by
  have e1 : (Fm w a b t).takeWhile isInl = w.map tk ∧ (Fm w a b t).dropWhile isInl =
      mk :: (List.replicate a (ty BSym.sep) ++ List.replicate b (ty BSym.minus) ++ t.map tyb) := by
    unfold Fm
    exact pre_split (fun x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact isInl_tk y) (fun x hx => by
      simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; exact isInl_mk)
  have e2 : (List.replicate a (ty BSym.sep) ++ (List.replicate b (ty BSym.minus) ++ t.map tyb)).takeWhile
      (isA (ty BSym.sep)) = List.replicate a (ty BSym.sep) ∧
      (List.replicate a (ty BSym.sep) ++ (List.replicate b (ty BSym.minus) ++ t.map tyb)).dropWhile
      (isA (ty BSym.sep)) = List.replicate b (ty BSym.minus) ++ t.map tyb := by
    refine pre_split (fun x hx => (isA_iff).2 (List.eq_of_mem_replicate hx)) (fun x hx => ?_)
    cases b with
    | zero =>
      cases t with
      | nil => simp at hx
      | cons c r => simp at hx; subst hx; exact tyb_ne_sep c
    | succ b => simp [List.replicate_succ] at hx; subst hx; exact minus_ne_sep
  have e3 : (List.replicate b (ty BSym.minus) ++ t.map tyb).takeWhile (isA (ty BSym.minus))
      = List.replicate b (ty BSym.minus) ∧
      (List.replicate b (ty BSym.minus) ++ t.map tyb).dropWhile (isA (ty BSym.minus)) = t.map tyb := by
    refine pre_split (fun x hx => (isA_iff).2 (List.eq_of_mem_replicate hx)) (fun x hx => ?_)
    cases t with
    | nil => simp at hx
    | cons c r => simp at hx; subst hx; exact tyb_ne_minus c
  have e4 : (t.map tyb).takeWhile isBitY = t.map tyb ∧ (t.map tyb).dropWhile isBitY = [] := by
    constructor
    · exact List.takeWhile_eq_self_iff.2 (fun x hx => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact isBitY_tyb y)
    · exact List.dropWhile_eq_nil_iff.2 (fun x hx => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact isBitY_tyb y)
  have hA7 : A7 (init (Fm w a b t)) = stateA w a b t := by
    funext r
    cases r <;> simp [A7, A6, A5, A4, A3, A2, A1, gMvA, gMvP, gPop, init, upd_apply, stateA,
      e1.1, e1.2, e2.1, e3.1, e3.2, e4.1, e4.2, List.append_assoc, e2.2, List.reverse_replicate]
  refine ⟨⟨?_, ?_⟩, hA7⟩
  · simp [A1, gMvP, topP, hd, init, upd_apply, e1.2, isA_self]
  · rw [hA7]; simp [stateA, topS, hd]

end Stk

end Sec_Ver4

section Sec_Ver5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def bsb (b : Bool) : BSym := if b then BSym.one else BSym.zero
def encB (bl : List Bool) : List BSym := bl.map bsb ++ [BSym.sep]

lemma tkb_eq (b : Bool) : tkb b = tk (bsb b) := by simp [tkb, bsb]

def stNum (X : Reg) : Prog :=
  sq (mvP Reg.W Reg.TMP isBitW) <| sq (popIf Reg.W (isA (tk BSym.sep))) <| mvA Reg.TMP X

def B1 (s : St) : St := gMvP Reg.W Reg.TMP isBitW s
def B2 (s : St) : St := gPop Reg.W (B1 s)
def B3 (X : Reg) (s : St) : St := gMvA Reg.TMP X (B2 s)
def okNum (s : St) : Prop := topP Reg.W (isA (tk BSym.sep)) (hd (B1 s)) = true

lemma gs_stNum (X : Reg) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : Gs (stNum X) (fun s => gMvA Reg.TMP X (gPopIf Reg.W
      (isA (tk BSym.sep)) (gMvP Reg.W Reg.TMP isBitW s))) (B3 X) okNum := by
  have h := Gs.seq (gs_mvP Reg.W Reg.TMP isBitW) <|
    Gs.seq (gs_popIf Reg.W (isA (tk BSym.sep))) <|
      gs_mvA Reg.TMP X hX2 (by decide) hX (by decide) hX'
  refine Gs.congr (p := stNum X) h (fun s _ => rfl) (fun s _ => ?_) (fun s => ?_)
  · simp [okNum, B1]
  · simp [B3, B2, B1, gMvA, gMvP, gPop, upd_apply, hX'.symm]

end Stk

end Sec_Ver5

section Sec_Ver6
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma Gad.loopG {p : Prog} {g : St → St} {c : ℕ} (hp : Gad p g)
    (t : (Reg → Option Al) → Bool) (μ : St → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hgrow : ∀ s, Gi s → t (hd s) = true → S (g s) ≤ S s + c)
    (hdec : ∀ s, Gi s → t (hd s) = true → μ (g s) < μ s) :
    Gad (.loop t p) (lrun t g μ) := by
  refine ⟨PSp.loopI (c := c) t μ hp.1 hμ (fun s hs _ => hp.2 s hs) hgrow hdec, ?_⟩
  have := lrun_rel Gi t g μ (fun s hs _ => hp.2 s hs) hdec (fun s s' => Gi s')
    (fun s hs _ => hs) (fun s hs _ h => h)
  exact this

lemma Gad.loop1 (t : (Reg → Option Al) → Bool) (f : (Reg → Option Al) → Reg → StackAct Al)
    (μ : St → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hC : ∀ h, f h Reg.C = StackAct.keep) (hRC : ∀ h, f h Reg.RC = StackAct.keep)
    (hdec : ∀ s, Gi s → t (hd s) = true → μ (StackProg.applyAct f s) < μ s) :
    Gad (.loop t (.act f)) (lrun t (StackProg.applyAct f) μ) := by
  have hg : Gad (.act f) (StackProg.applyAct f) := by
    refine ⟨PSp.act f, fun s hs => ?_⟩
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, ?_⟩
    · simp [StackProg.applyAct, hC, StackAct.apply, h1]
    · simp [StackProg.applyAct, hRC, StackAct.apply, h2]
  refine Gad.loopG (c := Fintype.card Reg) hg t μ hμ ?_ hdec
  intro s _ _
  have := Exec_size (StackProg.Exec.act f s)
  omega

/-! halving -/
def hfAct : (Reg → Option Al) → Reg → StackAct Al := fun h k =>
  match k with
  | Reg.U => .pop
  | Reg.F => match h Reg.F with | none => .push mk | some _ => .pop
  | Reg.HU => match h Reg.F with | none => .keep | some _ => .push mk
  | _ => .keep

def halve : Prog := .loop (topS Reg.U) (.act hfAct)
def hfStep : St → St := StackProg.applyAct hfAct
def hfRun : St → St := lrun (topS Reg.U) hfStep (fun s => (s Reg.U).length)

lemma gad_halve : Gad halve hfRun := by
  refine Gad.loop1 (topS Reg.U) hfAct (fun s => (s Reg.U).length) (fun s => len_le_S s Reg.U)
    (fun h => rfl) (fun h => rfl) ?_
  intro s _ ht
  simp only [topS, hd, Option.isSome_iff_exists] at ht
  obtain ⟨a, ha⟩ := ht
  obtain ⟨l, hl⟩ : ∃ l, s Reg.U = a :: l := by
    cases h : s Reg.U with
    | nil => simp [h] at ha
    | cons b l => simp [h] at ha; exact ⟨l, by simp [ha]⟩
  simp [StackProg.applyAct, hfAct, StackAct.apply, hl]


def HI (s : St) : Prop := ∃ f, f ≤ 1 ∧ s Reg.F = List.replicate f mk

def hfRes (s : St) : St :=
  upd (upd (upd s Reg.U []) Reg.F (List.replicate (((s Reg.U).length + (s Reg.F).length) % 2) mk))
    Reg.HU (List.replicate (((s Reg.U).length + (s Reg.F).length) / 2) mk ++ s Reg.HU)

lemma hf_step0 (s : St) (a : Al) (l : List Al) (hl : s Reg.U = a :: l) (hF : s Reg.F = []) :
    hfStep s = upd (upd s Reg.U l) Reg.F [mk] := by
  funext k
  cases k <;> simp [hfStep, StackProg.applyAct, hfAct, StackAct.apply, hl, hF, hd]

lemma hf_step1 (s : St) (a : Al) (l : List Al) (hl : s Reg.U = a :: l) (b : Al) (r : List Al)
    (hF : s Reg.F = b :: r) :
    hfStep s = upd (upd (upd s Reg.U l) Reg.F r) Reg.HU (mk :: s Reg.HU) := by
  funext k
  cases k <;> simp [hfStep, StackProg.applyAct, hfAct, StackAct.apply, hl, hF, hd]

lemma hfRun_sem : ∀ s, HI s → hfRun s = hfRes s := by
  have key : ∀ s, HI s → (topS Reg.U) (hd s) = true → HI (hfStep s) ∧
      (s Reg.U).length ≥ 1 ∧ ((hfStep s) Reg.U).length < (s Reg.U).length ∧ hfRes (hfStep s) = hfRes s := by
    intro s ⟨f, hf, hF⟩ ht
    simp only [topS, hd, Option.isSome_iff_exists] at ht
    obtain ⟨a, ha⟩ := ht
    obtain ⟨l, hl⟩ : ∃ l, s Reg.U = a :: l := by
      cases h : s Reg.U with
      | nil => simp [h] at ha
      | cons b l => simp [h] at ha; exact ⟨l, by simp [ha]⟩
    have hfl : f = 0 ∨ f = 1 := by omega
    rcases hfl with rfl | rfl
    · rw [hf_step0 s a l hl (by simpa using hF)]
      refine ⟨⟨1, le_rfl, by simp⟩, by simp [hl], by simp [hl], ?_⟩
      funext k
      simp only [hfRes, upd_apply, hl, hF]
      split_ifs <;> simp_all <;> omega
    · rw [hf_step1 s a l hl mk [] (by simpa using hF)]
      refine ⟨⟨0, by omega, by simp⟩, by simp [hl], by simp [hl], ?_⟩
      funext k
      simp only [hfRes, upd_apply, hl, hF]
      split_ifs <;> simp_all
      · have : (l.length + 1 + 1) / 2 = l.length / 2 + 1 := by omega
        rw [this, List.replicate_succ']; simp
      · omega
  have := lrun_rel HI (topS Reg.U) hfStep (fun s => (s Reg.U).length)
    (fun s hs ht => (key s hs ht).1) (fun s hs ht => (key s hs ht).2.2.1)
    (fun s s' => HI s → s' = hfRes s) ?_ ?_
  · exact fun s hs => this s hs hs
  · intro s hs ht hs'
    obtain ⟨f, hf, hF⟩ := hs
    simp only [topS, hd] at ht
    have hU : s Reg.U = [] := by
      cases h : s Reg.U with
      | nil => rfl
      | cons b l => simp [h] at ht
    funext k
    simp only [hfRes, upd_apply, hU, hF]
    have hfl : f = 0 ∨ f = 1 := by omega
    rcases hfl with rfl | rfl <;> (split_ifs <;> simp_all)
  · intro s hs ht ih hs'
    obtain ⟨h1, h2, h3, h4⟩ := key s hs ht
    rw [ih h1, h4]

end Stk

end Sec_Ver6

section Sec_Ver7
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def GsP (p : Prog) (g T : St → St) (ok pre : St → Prop) : Prop :=
  Gad p g ∧ Sticky g ∧ (∀ s, T s Reg.BAD = s Reg.BAD) ∧
    ∀ s, Gi s → pre s → s Reg.BAD = [] → ((g s Reg.BAD = [] ↔ ok s) ∧ (ok s → g s = T s))

lemma Gs.toP {p : Prog} {g T : St → St} {ok : St → Prop} (h : Gs p g T ok) (pre : St → Prop) :
    GsP p g T ok pre :=
  ⟨h.1, h.2.1, h.2.2.1, fun s hi _ hb => h.2.2.2 s hi hb⟩

lemma GsP.ofTrue {p : Prog} {g T : St → St} {ok : St → Prop} (h : GsP p g T ok (fun _ => True)) :
    Gs p g T ok :=
  ⟨h.1, h.2.1, h.2.2.1, fun s hi hb => h.2.2.2 s hi trivial hb⟩

lemma GsP.seq {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 pre1 pre2 : St → Prop}
    (h1 : GsP p g1 T1 ok1 pre1) (h2 : GsP q g2 T2 ok2 pre2)
    (hpre : ∀ s, Gi s → pre1 s → s Reg.BAD = [] → ok1 s → pre2 (T1 s)) :
    GsP (.seq p q) (fun s => g2 (g1 s)) (fun s => T2 (T1 s)) (fun s => ok1 s ∧ ok2 (T1 s)) pre1 := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.seq a1 a2, fun s hs => st2 _ (st1 s hs), fun s => by show T2 (T1 s) _ = _; rw [c2, c1], ?_⟩
  intro s hi hp hb
  obtain ⟨e1, f1⟩ := s1 s hi hp hb
  by_cases ho : ok1 s
  · have hg := f1 ho
    have hb' : T1 s Reg.BAD = [] := by rw [c1]; exact hb
    have hi' : Gi (T1 s) := by rw [← hg]; exact a1.2 s hi
    obtain ⟨e2, f2⟩ := s2 _ hi' (hpre s hi hp hb ho) hb'
    simp only [hg]
    exact ⟨by rw [e2]; simp [ho], fun h => f2 h.2⟩
  · have : g1 s Reg.BAD ≠ [] := fun h => ho (e1.1 h)
    refine ⟨?_, fun h => absurd h.1 ho⟩
    simp only
    constructor
    · intro h; exact absurd h (st2 _ this)
    · intro h; exact absurd h.1 ho

lemma GsP.congr {p : Prog} {g T T' : St → St} {ok ok' pre pre' : St → Prop} (h : GsP p g T ok pre)
    (hT : ∀ s, Gi s → pre s → T s = T' s) (hok : ∀ s, Gi s → pre s → (ok s ↔ ok' s))
    (hpre : ∀ s, Gi s → pre' s → pre s)
    (hT' : ∀ s, T' s Reg.BAD = s Reg.BAD) : GsP p g T' ok' pre' := by
  obtain ⟨a, st, c, s⟩ := h
  refine ⟨a, st, hT', fun s' hi hp hb => ?_⟩
  have hp' := hpre s' hi hp
  obtain ⟨e, f⟩ := s s' hi hp' hb
  exact ⟨by rw [e, hok s' hi hp'], fun h => by rw [← hT s' hi hp']; exact f ((hok s' hi hp').2 h)⟩

end Stk

end Sec_Ver7

section Sec_Ver8
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def mmT (X : Reg) (h : Reg → Option Al) : Bool :=
  match h X with
  | some x => decide (x ≠ (if (h Reg.F).isSome then tkb true else tkb false))
  | none => false

def eqBody (X : Reg) : Prog :=
  sq (badIf (topN Reg.U)) <| sq halve <| sq (mvA Reg.HU Reg.U) <| sq (badIf (mmT X)) <|
  sq (popProg X) (popProg Reg.F)

def gEqB (X : Reg) (s : St) : St :=
  gPop Reg.F (gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))))

lemma gad_eqBody (X : Reg) (hX : safe X := by decide) : Gad (eqBody X) (gEqB X) := by
  have h := Gad.seq (gad_badIf (topN Reg.U)) <| Gad.seq gad_halve <|
    Gad.seq (gad_mvA Reg.HU Reg.U) <| Gad.seq (gad_badIf (mmT X)) <|
    Gad.seq (gad_pop X hX) (gad_pop Reg.F)
  exact h

def eqc (X : Reg) (s : St) (x : Al) : ℕ :=
  (if s Reg.U = [] then 1 else 0) +
  (if x ≠ tkb (decide ((s Reg.U).length % 2 = 1)) then 1 else 0)

lemma gEqB_formula (X : Reg) (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide)
    (s : St) (hF : s Reg.F = []) (hH : s Reg.HU = []) (x : Al) (X' : List Al)
    (hx : s X = x :: X') :
    gEqB X s = upd (upd (upd s Reg.BAD (List.replicate (eqc X s x) mk ++ s Reg.BAD)) Reg.U
      (List.replicate ((s Reg.U).length / 2) mk)) X X' := by
  have e1 : ∀ r, gBadIf (topN Reg.U) s r = if r = Reg.BAD then List.replicate (if s Reg.U = [] then 1 else 0) mk ++ s Reg.BAD else s r := by
    intro r
    unfold gBadIf
    by_cases hU : s Reg.U = []
    · simp [topN, hd, hU, wb_apply]
    · simp [topN, hd, hU]; rintro rfl; rfl
  have hI : HI (gBadIf (topN Reg.U) s) := ⟨0, by omega, by simp [e1, hF]⟩
  have e2 := hfRun_sem _ hI
  set u := (s Reg.U).length with hu
  have e3 : ∀ r, gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)) r =
      if r = Reg.BAD then List.replicate (if s Reg.U = [] then 1 else 0) mk ++ s Reg.BAD
      else if r = Reg.U then List.replicate (u / 2) mk
      else if r = Reg.F then List.replicate (u % 2) mk
      else if r = Reg.HU then [] else s r := by
    intro r
    rw [e2]
    cases r <;> simp [gMvA, hfRes, upd_apply, e1, hF, hH, hu]
  show gPop Reg.F (gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s))))) = _
  generalize gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)) = E at e3 ⊢
  have eX : E X = x :: X' := by
    rw [e3 X]; simp [hXU, hXF, hXH, hXB, hx]
  have hm : mmT X (hd E) = decide (x ≠ tkb (decide (u % 2 = 1))) := by
    simp only [mmT, hd, eX, e3]
    simp [hXU, hXF, hXH, hXB]
    rcases Nat.mod_two_eq_zero_or_one u with h0 | h1
    · simp [h0]
    · simp [h1]
  have hcl : eqc X s x = (if s Reg.U = [] then 1 else 0) + (if x ≠ tkb (decide (u % 2 = 1)) then 1 else 0) := rfl
  have hF' : E Reg.F = List.replicate (u % 2) mk := by rw [e3]; simp
  have hF'' : (E Reg.F).tail = [] := by
    rw [hF']; rcases Nat.mod_two_eq_zero_or_one u with h0 | h1
    · simp [h0]
    · simp [h1]
  unfold gBadIf
  rw [hm]
  funext r
  by_cases hrX : r = X
  · subst hrX
    by_cases hxe : x = tkb (decide (u % 2 = 1)) <;>
      simp [gPop, hxe, eX, upd_apply, hXU, hXF, hXH, hXB, hXU.symm, hXF.symm, hXH.symm, hXB.symm, wb_apply, hF, hH]
  · by_cases hrF : r = Reg.F
    · subst hrF
      by_cases hxe : x = tkb (decide (u % 2 = 1)) <;>
        simp [gPop, hxe, upd_apply, hrX, hXF.symm, wb_apply, hF'', hF, hH]
    · have hrX' : ¬ X = r := fun h => hrX h.symm
      by_cases hxe : x = tkb (decide (u % 2 = 1)) <;>
      by_cases hrU : r = Reg.U <;> by_cases hrB : r = Reg.BAD <;> by_cases hrH : r = Reg.HU <;>
      simp_all [gPop, upd_apply, wb_apply, e3, eqc, mk, hF, hH, List.replicate_succ]
end Stk

end Sec_Ver8

section Sec_Ver9
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma hfStep_cases (s : St) (h : (topS Reg.U) (hd s) = true) :
    ∃ a l, s Reg.U = a :: l ∧
      ((s Reg.F = [] ∧ hfStep s = upd (upd s Reg.U l) Reg.F [mk]) ∨
       (∃ b r, s Reg.F = b :: r ∧
         hfStep s = upd (upd (upd s Reg.U l) Reg.F r) Reg.HU (mk :: s Reg.HU))) := by
  simp only [topS, hd, Option.isSome_iff_exists] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨l, hl⟩ : ∃ l, s Reg.U = a :: l := by
    cases h : s Reg.U with
    | nil => simp [h] at ha
    | cons b l => simp [h] at ha; exact ⟨l, by simp [ha]⟩
  refine ⟨a, l, hl, ?_⟩
  cases hF : s Reg.F with
  | nil => exact Or.inl ⟨rfl, hf_step0 s a l hl hF⟩
  | cons b r => exact Or.inr ⟨b, r, rfl, hf_step1 s a l hl b r hF⟩

lemma hfRun_frame (r : Reg) (h1 : r ≠ Reg.U) (h2 : r ≠ Reg.F) (h3 : r ≠ Reg.HU) :
    ∀ s : St, hfRun s r = s r := by
  have := lrun_rel (fun _ : St => True) (topS Reg.U) hfStep (fun s => (s Reg.U).length)
    (fun _ _ _ => trivial)
    (fun s _ ht => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      rcases h with ⟨_, e⟩ | ⟨b, r', _, e⟩ <;> simp [e, hl])
    (fun s s' => s' r = s r) (fun _ _ _ => rfl)
    (fun s _ ht ih => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      rcases h with ⟨_, e⟩ | ⟨b, r', _, e⟩ <;> simp [e, h1, h2, h3] at ih ⊢ <;> exact ih)
  exact fun s => this s trivial

lemma S_hfRun_le : ∀ s : St, S (hfRun s) ≤ S s := by
  have := lrun_rel (fun _ : St => True) (topS Reg.U) hfStep (fun s => (s Reg.U).length)
    (fun _ _ _ => trivial)
    (fun s _ ht => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      rcases h with ⟨_, e⟩ | ⟨b, r', _, e⟩ <;> simp [e, hl])
    (fun s s' => S s' ≤ S s) (fun _ _ _ => le_rfl)
    (fun s _ ht ih => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      have : S (hfStep s) ≤ S s := by
        rcases h with ⟨hF, e⟩ | ⟨b, r', hF, e⟩
        · rw [e]
          have := S_upd (upd s Reg.U l) Reg.F [mk]
          have := S_upd s Reg.U l
          simp [hl, hF] at *; omega
        · rw [e]
          have h1 := S_upd (upd (upd s Reg.U l) Reg.F r') Reg.HU (mk :: s Reg.HU)
          have h2 := S_upd (upd s Reg.U l) Reg.F r'
          have h3 := S_upd s Reg.U l
          simp [hl, hF] at *; omega
      omega)
  exact fun s => this s trivial

lemma S_gBadIf (t : (Reg → Option Al) → Bool) (s : St) : S (gBadIf t s) ≤ S s + 1 := by
  unfold gBadIf
  split_ifs
  · have := S_upd s Reg.BAD (List.replicate 1 mk ++ s Reg.BAD)
    simp [wb] at *; omega
  · omega

lemma S_gMvA (a b : Reg) (hab : a ≠ b) (s : St) : S (gMvA a b s) ≤ S s := by
  unfold gMvA
  have h1 := S_upd (upd s a []) b ((s a).reverse ++ s b)
  have h2 := S_upd s a []
  simp [hab.symm] at *; omega

lemma S_gPop (r : Reg) (s : St) : S (gPop r s) ≤ S s := by
  unfold gPop
  have := S_upd s r (s r).tail
  have := List.length_tail (l := s r)
  omega

lemma S_gEqB (X : Reg) (hXU : X ≠ Reg.U := by decide) (s : St) : S (gEqB X s) ≤ S s + 2 := by
  unfold gEqB
  have a1 := S_gBadIf (topN Reg.U) s
  have a2 := S_hfRun_le (gBadIf (topN Reg.U) s)
  have a3 := S_gMvA Reg.HU Reg.U (by decide) (hfRun (gBadIf (topN Reg.U) s))
  have a4 := S_gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))
  have a5 := S_gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s))))
  have a6 := S_gPop Reg.F (gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))))
  omega

end Stk

end Sec_Ver9

section Sec_Ver10
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma bits_step (u : ℕ) (hu : u ≠ 0) : Nat.bits u = decide (u % 2 = 1) :: Nat.bits (u / 2) := by
  have h : Nat.bit (decide (u % 2 = 1)) (u / 2) = u := by
    rw [Nat.bit_val]; rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h] <;> omega
  have h2 : u / 2 = 0 → decide (u % 2 = 1) = true := by
    intro h0; have : u % 2 = 1 := by omega
    simp [this]
  rw [← Nat.bits_append_bit (u/2) (decide (u % 2 = 1)) h2, h]

def chk : List Al → ℕ → Option ℕ
  | [], u => some u
  | x :: l, u => if u ≠ 0 ∧ x = tkb (decide (u % 2 = 1)) then chk l (u / 2) else none

lemma chk_eq : ∀ (l : List Al) (u : ℕ), chk l u = some 0 ↔ l = (Nat.bits u).map tkb := by
  intro l
  induction l with
  | nil =>
    intro u
    by_cases hu : u = 0
    · subst hu; simp [chk]
    · rw [bits_step u hu]; simp [chk, hu]
  | cons x l ih =>
    intro u
    by_cases hu : u = 0
    · subst hu; simp [chk]
    · rw [bits_step u hu]
      simp only [chk, List.map_cons, List.cons.injEq]
      by_cases hc : x = tkb (decide (u % 2 = 1))
      · simp [hu, hc, ih]
      · simp [hu, hc]

def EqInv (s : St) : Prop :=
  s Reg.F = [] ∧ s Reg.HU = [] ∧ ∃ c, s Reg.U = List.replicate (s Reg.U).length c

lemma top_cons (X : Reg) (s : St) (h : topS X (hd s) = true) : ∃ x X', s X = x :: X' := by
  simp only [topS, hd] at h
  cases hs : s X with
  | nil => simp [hs] at h
  | cons x l => exact ⟨x, l, rfl⟩

lemma gBadIf_ne (t : (Reg → Option Al) → Bool) (s : St) (r : Reg) (h : r ≠ Reg.BAD) :
    gBadIf t s r = s r := by
  unfold gBadIf; split_ifs <;> simp [wb_apply, h]

lemma gMvA_ne (a b : Reg) (s : St) (r : Reg) (h1 : r ≠ a) (h2 : r ≠ b) : gMvA a b s r = s r := by
  simp [gMvA, h1, h2]

lemma gBadIf_BAD (t : (Reg → Option Al) → Bool) (s : St) :
    ∃ c, gBadIf t s Reg.BAD = List.replicate c mk ++ s Reg.BAD := by
  unfold gBadIf; split_ifs
  · exact ⟨1, by simp [wb_apply]⟩
  · exact ⟨0, by simp⟩

lemma gEqB_X (X : Reg) (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide) (s : St) :
    gEqB X s X = (s X).tail := by
  unfold gEqB
  simp only [gPop, upd_apply, hXF, if_false, if_true]
  rw [gBadIf_ne _ _ _ hXB, gMvA_ne _ _ _ _ hXH hXU, hfRun_frame X hXU hXF hXH,
    gBadIf_ne _ _ _ hXB]

lemma gEqB_BAD (X : Reg) (hXB : X ≠ Reg.BAD := by decide) (s : St) :
    ∃ c, gEqB X s Reg.BAD = List.replicate c mk ++ s Reg.BAD := by
  unfold gEqB
  obtain ⟨c1, h1⟩ := gBadIf_BAD (topN Reg.U) s
  obtain ⟨c2, h2⟩ := gBadIf_BAD (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))
  refine ⟨c2 + c1, ?_⟩
  simp only [gPop, upd_apply, if_neg (show Reg.BAD ≠ Reg.F by decide), if_neg (Ne.symm hXB)]
  rw [h2, gMvA_ne _ _ _ _ (by decide) (by decide),
    hfRun_frame Reg.BAD (by decide) (by decide) (by decide), h1, List.replicate_add, List.append_assoc]

end Stk

end Sec_Ver10

section Sec_Ver11
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def eqRun (X : Reg) : St → St := lrun (topS X) (gEqB X) (fun s => (s X).length)

lemma gad_eqLoop (X : Reg) (hX : safe X := by decide) (hXU : X ≠ Reg.U := by decide)
    (hXF : X ≠ Reg.F := by decide) (hXH : X ≠ Reg.HU := by decide)
    (hXB : X ≠ Reg.BAD := by decide) :
    Gad (.loop (topS X) (eqBody X)) (eqRun X) := by
  refine Gad.loopG (c := 2) (gad_eqBody X hX) (topS X) _ (fun s => len_le_S s X) ?_ ?_
  · intro s _ _; exact S_gEqB X hXU s
  · intro s _ ht
    obtain ⟨x, X', hx⟩ := top_cons X s ht
    rw [gEqB_X X hXU hXF hXH hXB, hx]; simp

lemma eqInv_step (X : Reg) (hXU : X ≠ Reg.U) (hXF : X ≠ Reg.F)
    (hXH : X ≠ Reg.HU) (hXB : X ≠ Reg.BAD) (s : St) (hI : EqInv s) (x : Al) (X' : List Al)
    (hx : s X = x :: X') :
    gEqB X s = upd (upd (upd s Reg.BAD (List.replicate (eqc X s x) mk ++ s Reg.BAD)) Reg.U
      (List.replicate ((s Reg.U).length / 2) mk)) X X' :=
  gEqB_formula X hXU hXF hXH hXB s hI.1 hI.2.1 x X' hx

lemma eqloop_sem (X : Reg) (hXU : X ≠ Reg.U) (hXF : X ≠ Reg.F)
    (hXH : X ≠ Reg.HU) (hXB : X ≠ Reg.BAD) :
    ∀ s : St, EqInv s →
      (∃ l, eqRun X s Reg.BAD = l ++ s Reg.BAD) ∧
      (chk (s X) (s Reg.U).length = none → eqRun X s Reg.BAD ≠ []) ∧
      (∀ u', chk (s X) (s Reg.U).length = some u' →
        (eqRun X s X = [] ∧ eqRun X s Reg.U = (if s X = [] then s Reg.U else List.replicate u' mk) ∧
         ∀ r, r ≠ Reg.U → r ≠ X → eqRun X s r = s r)) := by
  have key := lrun_rel EqInv (topS X) (gEqB X) (fun s => (s X).length)
    (fun s hI ht => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      rw [eqInv_step X hXU hXF hXH hXB s hI x X' hx]
      refine ⟨?_, ?_, ⟨mk, ?_⟩⟩ <;> simp [upd_apply, hXU, hXF, hXH, hXB, hXU.symm, hXF.symm, hXH.symm, hXB.symm, hI.1, hI.2.1, Ne.symm hXB] )
    (fun s hI ht => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      rw [gEqB_X X hXU hXF hXH hXB, hx]; simp)
    (fun s s' => EqInv s → (∃ l, s' Reg.BAD = l ++ s Reg.BAD) ∧
      (chk (s X) (s Reg.U).length = none → s' Reg.BAD ≠ []) ∧
      (∀ u', chk (s X) (s Reg.U).length = some u' →
        (s' X = [] ∧ s' Reg.U = (if s X = [] then s Reg.U else List.replicate u' mk) ∧ ∀ r, r ≠ Reg.U → r ≠ X → s' r = s r)))
    (fun s hI ht => by
      have hX : s X = [] := by
        simp only [topS, hd] at ht
        cases hs : s X with
        | nil => rfl
        | cons a l => simp [hs] at ht
      refine fun _ => ⟨⟨[], by simp⟩, ?_, ?_⟩
      · simp [hX, chk]
      · intro u' hu'
        simp [hX, chk] at hu'
        exact ⟨hX, by simp [hX], fun _ _ _ => rfl⟩)
    (fun s hI ht ih => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      have hf := eqInv_step X hXU hXF hXH hXB s hI x X' hx
      have hI1 : EqInv (gEqB X s) := by
        rw [hf]
        refine ⟨?_, ?_, ⟨mk, ?_⟩⟩ <;> simp [upd_apply, hXU, hXF, hXH, hXB, hXU.symm, hXF.symm, hXH.symm, hXB.symm, hI.1, hI.2.1, Ne.symm hXB]
      obtain ⟨ih1, ih2, ih3⟩ := ih hI1
      intro _
      have hBAD1 : gEqB X s Reg.BAD = List.replicate (eqc X s x) mk ++ s Reg.BAD := by
        rw [hf]; simp [upd_apply, hXB.symm, Ne.symm hXB]
      have hX1 : gEqB X s X = X' := by rw [gEqB_X X hXU hXF hXH hXB, hx]; rfl
      have hU1 : (gEqB X s Reg.U).length = (s Reg.U).length / 2 := by
        rw [hf]; simp [upd_apply, hXU.symm]
      have hfr : ∀ r, r ≠ Reg.U → r ≠ X → r ≠ Reg.BAD → gEqB X s r = s r := by
        intro r h1 h2 h3; rw [hf]; simp [upd_apply, h1, h2, h3]
      simp only [hX1, hU1] at ih2 ih3
      rw [hx]
      simp only [chk]
      by_cases hc : (s Reg.U).length ≠ 0 ∧ x = tkb (decide ((s Reg.U).length % 2 = 1))
      · have he : eqc X s x = 0 := by
          obtain ⟨h1, h2⟩ := hc
          have : s Reg.U ≠ [] := fun h => h1 (by simp [h])
          simp [eqc, this, h2]
        rw [he] at hBAD1
        simp only [List.replicate_zero, List.nil_append] at hBAD1
        rw [if_pos hc]
        refine ⟨?_, ?_, ?_⟩
        · obtain ⟨l, hl⟩ := ih1; exact ⟨l, by rw [hl, hBAD1]⟩
        · intro h; exact ih2 h
        · intro u' h
          obtain ⟨a, b, c⟩ := ih3 u' h
          have b' : lrun (topS X) (gEqB X) (fun s => (s X).length) (gEqB X s) Reg.U = List.replicate u' mk := by
            by_cases hX' : X' = []
            · subst hX'
              simp only [chk, Option.some.injEq] at h
              have : lrun (topS X) (gEqB X) (fun s => (s X).length) (gEqB X s) Reg.U = gEqB X s Reg.U := by simpa using b
              rw [this, hf]; simp [upd_apply, hXU.symm, hU1, h]
            · simpa [hX'] using b
          refine ⟨a, by simpa using b', fun r h1 h2 => ?_⟩
          by_cases h3 : r = Reg.BAD
          · subst h3; rw [c _ h1 h2, hBAD1]
          · rw [c r h1 h2, hfr r h1 h2 h3]
      · rw [if_neg hc]
        have he : eqc X s x ≠ 0 := by
          intro h0
          apply hc
          simp only [eqc, Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h0
          obtain ⟨h1, h2⟩ := h0
          exact ⟨fun h => h1 (List.length_eq_zero_iff.mp h), h2⟩
        refine ⟨?_, ?_, ?_⟩
        · obtain ⟨l, hl⟩ := ih1; exact ⟨l ++ List.replicate (eqc X s x) mk, by simp [hl, hBAD1]⟩
        · intro _
          obtain ⟨l, hl⟩ := ih1
          rw [hl, hBAD1]
          have : eqc X s x ≠ 0 := he
          intro h
          have := congrArg List.length h
          simp at this; omega
        · intro u' h; simp at h)
  exact fun s h => key s h h

end Stk

end Sec_Ver11

section Sec_Ver12
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma eqRun_BAD (X : Reg) (hXU : X ≠ Reg.U) (hXF : X ≠ Reg.F)
    (hXH : X ≠ Reg.HU) (hXB : X ≠ Reg.BAD) :
    ∀ s : St, ∃ l, eqRun X s Reg.BAD = l ++ s Reg.BAD := by
  have key := lrun_rel (fun _ : St => True) (topS X) (gEqB X) (fun s => (s X).length)
    (fun _ _ _ => trivial)
    (fun s _ ht => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      rw [gEqB_X X hXU hXF hXH hXB, hx]; simp)
    (fun s s' => ∃ l, s' Reg.BAD = l ++ s Reg.BAD) (fun s _ _ => ⟨[], by simp⟩)
    (fun s _ ht ih => by
      obtain ⟨l, hl⟩ := ih
      obtain ⟨c, hc⟩ := gEqB_BAD X hXB s
      exact ⟨l ++ List.replicate c mk, by rw [hl, hc]; simp⟩)
  exact fun s => key s trivial

def okL (X : Reg) (s : St) : Prop := chk (s X) (s Reg.U).length ≠ none
def TL (X : Reg) (s : St) : St :=
  upd (upd s X []) Reg.U (if s X = [] then s Reg.U else List.replicate ((chk (s X) (s Reg.U).length).getD 0) mk)

lemma gsP_eqLoop (X : Reg) (hX : safe X := by decide) (hXU : X ≠ Reg.U := by decide)
    (hXF : X ≠ Reg.F := by decide) (hXH : X ≠ Reg.HU := by decide)
    (hXB : X ≠ Reg.BAD := by decide) :
    GsP (.loop (topS X) (eqBody X)) (eqRun X) (TL X) (okL X) EqInv := by
  refine ⟨gad_eqLoop X hX hXU hXF hXH hXB, ?_, ?_, ?_⟩
  · intro s hs h
    obtain ⟨l, hl⟩ := eqRun_BAD X hXU hXF hXH hXB s
    rw [hl] at h; exact hs (List.append_eq_nil_iff.mp h).2
  · intro s; simp [TL, upd_apply, hXB, Ne.symm hXB]
  · intro s hi hp hb
    obtain ⟨a1, a2, a3⟩ := eqloop_sem X hXU hXF hXH hXB s hp
    cases hc : chk (s X) (s Reg.U).length with
    | none =>
      have := a2 hc
      refine ⟨⟨fun h => absurd h this, fun h => absurd h (by simp [okL, hc])⟩, fun h => absurd h (by simp [okL, hc])⟩
    | some u' =>
      obtain ⟨b1, b2, b3⟩ := a3 u' hc
      have hr : eqRun X s = TL X s := by
        funext r
        by_cases h1 : r = X
        · subst h1; simp [TL, hXU, b1]
        · by_cases h2 : r = Reg.U
          · subst h2; simp [TL, hc, b2, Ne.symm hXU]
          · simp [TL, h1, h2, b3 r h2 h1]
      refine ⟨⟨fun _ => by simp [okL, hc], fun _ => ?_⟩, fun _ => hr⟩
      have := b3 Reg.BAD (Ne.symm (by decide)) (Ne.symm hXB)
      rw [this, hb]

end Stk

end Sec_Ver12

section Sec_Ver13
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def eqProg (X D : Reg) : Prog :=
  sq (sq (sq (sq (clearProg Reg.U) (sq (clearProg Reg.F) (sq (clearProg Reg.HU)
    (copyProg D Reg.U Reg.C)))) (.loop (topS X) (eqBody X))) (badIf (topS Reg.U))) (clearProg Reg.U)

def g0 (D : Reg) (s : St) : St := gCopy D Reg.U (gClear Reg.HU (gClear Reg.F (gClear Reg.U s)))
def eqG (X D : Reg) (s : St) : St := gClear Reg.U (gBadIf (topS Reg.U) (eqRun X (g0 D s)))
def eqT (X : Reg) (s : St) : St := upd (upd (upd (upd s X []) Reg.U []) Reg.F []) Reg.HU []

lemma g0_apply (D : Reg) (hDU : D ≠ Reg.U) (hDF : D ≠ Reg.F) (hDH : D ≠ Reg.HU) (s : St) (r : Reg) :
    g0 D s r = if r = Reg.U then s D else if r = Reg.F then [] else if r = Reg.HU then [] else s r := by
  unfold g0 gCopy gClear
  by_cases h1 : r = Reg.U
  · subst h1; simp [upd_apply, hDF, hDH, hDU]
  · by_cases h2 : r = Reg.F
    · subst h2; simp [upd_apply]
    · by_cases h3 : r = Reg.HU
      · subst h3; simp [upd_apply]
      · simp [upd_apply, h1, h2, h3]


lemma gsP_eq (X D : Reg) (hX : safe X := by decide) (hD : safe D := by decide)
    (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide)
    (hDU : D ≠ Reg.U := by decide) (hDF : D ≠ Reg.F := by decide)
    (hDH : D ≠ Reg.HU := by decide) :
    GsP (eqProg X D) (eqG X D) (eqT X) (fun s => s X = (Nat.bits (s D).length).map tkb)
      (fun s => ∃ c, s D = List.replicate (s D).length c) := by
  have c := Gs.seq (gs_clear Reg.U) (Gs.seq (gs_clear Reg.F) (Gs.seq (gs_clear Reg.HU)
    (gs_copy D Reg.U hDU.symm.symm hD)))
  have P1 := c.toP (fun s => ∃ c, s D = List.replicate (s D).length c)
  have P2 := gsP_eqLoop X hX hXU hXF hXH hXB
  have P12 := GsP.seq P1 P2 (fun s _ hp _ _ => by
    show EqInv (g0 D s)
    have e := g0_apply D hDU hDF hDH s
    have hU0 : g0 D s Reg.U = s D := by rw [e]; simp
    refine ⟨by rw [e]; simp, by rw [e]; simp, ?_⟩
    rw [hU0]; exact hp)
  have P3 := GsP.seq P12 ((gs_badIf (topS Reg.U)).toP (fun _ => True)) (fun _ _ _ _ _ => trivial)
  have P4 := GsP.seq P3 ((gs_clear Reg.U).toP (fun _ => True)) (fun _ _ _ _ _ => trivial)
  refine GsP.congr P4 ?_ ?_ (fun _ _ h => h) ?_
  · intro s _ _
    funext r
    show gClear Reg.U (id (TL X (g0 D s))) r = eqT X s r
    have e := g0_apply D hDU hDF hDH s
    simp only [gClear, id, TL, eqT, upd_apply, e]
    split_ifs <;> rfl
  · intro s hi hp
    have e := g0_apply D hDU hDF hDH s
    have hX0 : g0 D s X = s X := by rw [e]; simp [hXU, hXF, hXH]
    have hU0 : g0 D s Reg.U = s D := by rw [e]; simp
    change ((((True ∧ True ∧ True ∧ True) ∧ okL X (g0 D s)) ∧
          topS Reg.U (hd (TL X (g0 D s))) = false) ∧ True) ↔ _
    simp only [okL, TL, hX0, hU0, true_and, and_true, hd, topS, upd_apply, if_true]
    have hq := chk_eq (s X) (s D).length
    cases hc : chk (s X) (s D).length with
    | none =>
      rw [hc] at hq
      simp only [ne_eq, not_true_eq_false, false_and, false_iff]
      intro h; have := hq.2 h; simp at this
    | some u =>
      rw [hc] at hq
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and, Option.getD_some]
      rw [← hq]
      by_cases hxe : s X = []
      · rw [hxe] at hc; simp [chk] at hc; subst hc
        simp [hxe]
      · simp [hxe]
  · intro s; simp [eqT, upd_apply, hXB, Ne.symm hXB]

end Stk

end Sec_Ver13

section Sec_Ver14
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma GsP.loop1x (t : (Reg → Option Al) → Bool) (f : (Reg → Option Al) → Reg → StackAct Al)
    (μ : St → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hC : ∀ h, f h Reg.C = StackAct.keep) (hRC : ∀ h, f h Reg.RC = StackAct.keep)
    (hBADf : ∀ h, f h Reg.BAD = StackAct.keep ∨ ∃ a, f h Reg.BAD = StackAct.push a)
    (hdec : ∀ s, t (hd s) = true → μ (StackProg.applyAct f s) < μ s)
    (Inv : St → Prop)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (StackProg.applyAct f s))
    (F : St → St) (e : St → List Al) (ok : St → Prop)
    (hstop : ∀ s, Inv s → t (hd s) = false → F s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → F (StackProg.applyAct f s) = F s)
    (hBAD : ∀ s, Inv s → F s Reg.BAD = e s ++ s Reg.BAD)
    (hok : ∀ s, Inv s → (e s = [] ↔ ok s)) :
    GsP (.loop t (.act f)) (lrun t (StackProg.applyAct f) μ)
      (fun s => upd (F s) Reg.BAD (s Reg.BAD)) ok Inv := by
  have hg := Gad.loop1 t f μ hμ hC hRC (fun s _ => hdec s)
  have hex : ∀ s, Inv s → lrun t (StackProg.applyAct f) μ s = F s := by
    have := lrun_rel Inv t (StackProg.applyAct f) μ hinv (fun s _ => hdec s)
      (fun s s' => s' = F s) (fun s hs ht => (hstop s hs ht).symm)
      (fun s hs ht h => by rw [h]; exact hstep s hs ht)
    exact this
  refine ⟨hg, ?_, fun s => by simp [upd_apply], ?_⟩
  · have := lrun_rel (fun _ : St => True) t (StackProg.applyAct f) μ (fun _ _ _ => trivial)
      (fun s _ => hdec s) (fun s s' => s Reg.BAD ≠ [] → s' Reg.BAD ≠ [])
      (fun s _ _ h => h)
      (fun s _ ht h hb => by
        apply h
        have e0 : (StackProg.applyAct f s) Reg.BAD = (f (hd s) Reg.BAD).apply (s Reg.BAD) := rfl
        rw [e0]
        rcases hBADf (hd s) with h1 | ⟨a, h1⟩
        · rw [h1]; simpa [StackAct.apply] using hb
        · rw [h1]; simp [StackAct.apply])
    exact fun s hs => this s trivial hs
  · intro s hi hp hb
    rw [hex s hp]
    have h1 := hBAD s hp
    rw [hb, List.append_nil] at h1
    refine ⟨by rw [h1]; exact hok s hp, fun ho => ?_⟩
    have he := (hok s hp).2 ho
    rw [he] at h1
    funext r
    by_cases hr : r = Reg.BAD
    · subst hr; simp [upd_apply, h1, hb]
    · simp [upd_apply, hr]

end Stk

end Sec_Ver14

section Sec_Ver15
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def dcAct (A B : Reg) (c : Al → Bool) : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = A then StackAct.pop
  else if r = B then (if (match h A with | some x => c x | none => false) = true then StackAct.pop else StackAct.keep)
  else if r = Reg.BAD then (if (match h A with | some x => c x | none => false) = true ∧ (h B).isNone = true
      then StackAct.push mk else StackAct.keep)
  else StackAct.keep

def drainProg (A B : Reg) (c : Al → Bool) : Prog := .loop (topS A) (.act (dcAct A B c))

def dcF (A B : Reg) (c : Al → Bool) (s : St) : St :=
  upd (upd (upd s A []) B ((s B).drop ((s A).countP c))) Reg.BAD
    (List.replicate ((s A).countP c - (s B).length) mk ++ s Reg.BAD)

lemma dc_step (A B : Reg) (c : Al → Bool) (hAB : A ≠ B) (hA : A ≠ Reg.BAD) (hB : B ≠ Reg.BAD)
    (s : St) (x : Al) (l : List Al) (hx : s A = x :: l) :
    StackProg.applyAct (dcAct A B c) s =
      upd (upd (upd s A l) B (if c x = true then (s B).tail else s B)) Reg.BAD
        (if c x = true ∧ s B = [] then mk :: s Reg.BAD else s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct (dcAct A B c) s r = (dcAct A B c (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdA : hd s A = some x := by simp [hd, hx]
  by_cases h1 : r = A
  · subst h1; simp [dcAct, upd_apply, hx, StackAct.apply, hAB, hA]
  · by_cases h2 : r = B
    · subst h2
      simp only [dcAct, h1, if_false, if_true, hdA, upd_apply, hA.symm, h1, hAB.symm]
      split_ifs <;> simp [StackAct.apply]
    · by_cases h3 : r = Reg.BAD
      · subst h3
        simp only [dcAct, h1, h2, if_false, if_true, hdA, upd_apply, h1, h2]
        by_cases hcx : c x = true
        · by_cases hb : s B = []
          · have : (hd s B).isNone = true := by simp [hd, hb]
            simp [hcx, hb, this, StackAct.apply]
          · have : (hd s B).isNone = false := by
              cases hh : s B with
              | nil => exact absurd hh hb
              | cons b bl => simp [hd, hh]
            simp [hcx, hb, this, StackAct.apply]
        · simp [hcx, StackAct.apply]
      · simp [dcAct, h1, h2, h3, upd_apply, StackAct.apply]

lemma gsP_drain (A B : Reg) (c : Al → Bool) (hA : safe A) (hB : safe B) (hAB : A ≠ B)
    (hA' : A ≠ Reg.BAD) (hB' : B ≠ Reg.BAD) :
    GsP (drainProg A B c) (lrun (topS A) (StackProg.applyAct (dcAct A B c)) (fun s => (s A).length))
      (fun s => upd (dcF A B c s) Reg.BAD (s Reg.BAD)) (fun s => (s A).countP c ≤ (s B).length)
      (fun _ => True) := by
  have hAC := hA.1; have hAR := hA.2; have hBC := hB.1; have hBR := hB.2
  refine GsP.loop1x (topS A) (dcAct A B c) (fun s => (s A).length) (fun s => len_le_S s A)
    (fun h => by simp [dcAct, hAC.symm, hBC.symm])
    (fun h => by simp [dcAct, hAR.symm, hBR.symm])
    (fun h => by unfold dcAct; rw [if_neg hA'.symm, if_neg hB'.symm, if_pos rfl]; split_ifs <;> simp)
    ?_ (fun _ => True) (fun _ _ _ => trivial) (dcF A B c)
    (fun s => List.replicate ((s A).countP c - (s B).length) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨x, l, hx⟩ := top_cons A s ht
    rw [dc_step A B c hAB hA' hB' s x l hx]
    simp [upd_apply, hA', hAB, hx]
  · intro s _ ht
    have hAe : s A = [] := by
      simp only [topS, hd] at ht
      cases hs : s A with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    by_cases h1 : r = A
    · subst h1; simp [dcF, upd_apply, hAe, hA', hAB]
    · by_cases h2 : r = B
      · subst h2; simp [dcF, upd_apply, hAe, h1, hB']
      · by_cases h3 : r = Reg.BAD
        · subst h3; simp [dcF, upd_apply, hAe, h1, h2]
        · simp [dcF, upd_apply, h1, h2, h3]
  · intro s _ ht
    obtain ⟨x, l, hx⟩ := top_cons A s ht
    rw [dc_step A B c hAB hA' hB' s x l hx]
    funext r
    by_cases h1 : r = A
    · subst h1; simp [dcF, upd_apply, hx, hAB, hA']
    · by_cases h2 : r = B
      · subst h2
        by_cases hcx : c x = true
        · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, List.countP_cons, hAB.symm]
        · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, List.countP_cons, hAB.symm]
      · by_cases h3 : r = Reg.BAD
        · subst h3
          by_cases hcx : c x = true
          · by_cases hb : s B = []
            · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, hb, List.countP_cons, hAB.symm, List.replicate_succ']
            · have : 1 ≤ (s B).length := List.length_pos_iff.2 hb
              simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, hb, List.countP_cons, hAB.symm]
              have : (l.countP c + 1 - (s B).length) = l.countP c - ((s B).length - 1) := by omega
              rw [this]
          · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, List.countP_cons, hAB.symm]
        · simp [dcF, upd_apply, h1, h2, h3]
  · intro s _
    simp [dcF, upd_apply, hA'.symm, hB'.symm]
  · intro s _
    simp
    omega

end Stk

end Sec_Ver15

section Sec_Ver16
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def flAct (A B : Reg) (x : Al) : (Reg → Option Al) → Reg → StackAct Al := fun _ r =>
  if r = A then StackAct.pop else if r = B then StackAct.push x else StackAct.keep

def fillProg (A B : Reg) (x : Al) : Prog := .loop (topS A) (.act (flAct A B x))

def flF (A B : Reg) (x : Al) (s : St) : St :=
  upd (upd s A []) B (List.replicate (s A).length x ++ s B)

lemma rep_append_cons (n : ℕ) (x : Al) (t : List Al) :
    List.replicate n x ++ x :: t = x :: (List.replicate n x ++ t) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

lemma fl_step (A B : Reg) (x : Al) (hAB : A ≠ B) (s : St) (y : Al) (l : List Al) (hy : s A = y :: l) :
    StackProg.applyAct (flAct A B x) s = upd (upd s A l) B (x :: s B) := by
  funext r
  have e0 : StackProg.applyAct (flAct A B x) s r = (flAct A B x (hd s) r).apply (s r) := rfl
  rw [e0]
  by_cases h1 : r = A
  · subst h1; simp [flAct, upd_apply, hy, StackAct.apply, hAB]
  · by_cases h2 : r = B
    · subst h2; simp [flAct, upd_apply, StackAct.apply, h1]
    · simp [flAct, upd_apply, StackAct.apply, h1, h2]

lemma gsP_fill (A B : Reg) (x : Al) (hA : safe A) (hB : safe B) (hAB : A ≠ B)
    (hA' : A ≠ Reg.BAD) (hB' : B ≠ Reg.BAD) :
    GsP (fillProg A B x) (lrun (topS A) (StackProg.applyAct (flAct A B x)) (fun s => (s A).length))
      (fun s => upd (flF A B x s) Reg.BAD (s Reg.BAD)) (fun _ => True) (fun _ => True) := by
  have hAC := hA.1; have hAR := hA.2; have hBC := hB.1; have hBR := hB.2
  refine GsP.loop1x (topS A) (flAct A B x) (fun s => (s A).length) (fun s => len_le_S s A)
    (fun h => by simp [flAct, hAC.symm, hBC.symm])
    (fun h => by simp [flAct, hAR.symm, hBR.symm])
    (fun h => by unfold flAct; rw [if_neg hA'.symm, if_neg hB'.symm]; simp)
    ?_ (fun _ => True) (fun _ _ _ => trivial) (flF A B x) (fun _ => []) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨y, l, hy⟩ := top_cons A s ht
    rw [fl_step A B x hAB s y l hy]
    simp [upd_apply, hA', hAB, hy]
  · intro s _ ht
    have hAe : s A = [] := by
      simp only [topS, hd] at ht
      cases hs : s A with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    by_cases h1 : r = A
    · subst h1; simp [flF, upd_apply, hAe, hAB]
    · by_cases h2 : r = B
      · subst h2; simp [flF, upd_apply, hAe, h1]
      · simp [flF, upd_apply, h1, h2]
  · intro s _ ht
    obtain ⟨y, l, hy⟩ := top_cons A s ht
    rw [fl_step A B x hAB s y l hy]
    funext r
    by_cases h1 : r = A
    · subst h1; simp [flF, upd_apply, hy, hAB]
    · by_cases h2 : r = B
      · subst h2; simp [flF, upd_apply, hy, hAB, h1, hAB.symm, List.replicate_succ, rep_append_cons]
      · simp [flF, upd_apply, h1, h2]
  · intro s _
    simp [flF, upd_apply, hA'.symm, hB'.symm]
  · intro s _; simp

end Stk

end Sec_Ver16

section Sec_Ver17
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def paAct : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = Reg.W then StackAct.pop
  else if r = Reg.MR then (if h Reg.W = some (tk BSym.sep) then
      StackAct.push (if (h Reg.FP).isSome then ty BSym.one else ty BSym.zero) else StackAct.keep)
  else if r = Reg.FP then (if h Reg.W = some (tk BSym.one) then
      (if (h Reg.FP).isNone then StackAct.push mk else StackAct.keep)
    else if h Reg.W = some (tk BSym.sep) then StackAct.pop else StackAct.keep)
  else if r = Reg.BAD then (if h Reg.W = some (tk BSym.one) then
      (if (h Reg.FP).isSome then StackAct.push mk else StackAct.keep)
    else if h Reg.W = some (tk BSym.sep) then StackAct.keep else StackAct.push mk)
  else StackAct.keep

def parseLoop : Prog := .loop (topS Reg.W) (.act paAct)

/-- state: (pending-one flag, matrix bits so far (reversed), bad count) -/
def ps (st : Bool × List Al × ℕ) (a : Al) : Bool × List Al × ℕ :=
  if a = tk BSym.one then (true, st.2.1, if st.1 then st.2.2 + 1 else st.2.2)
  else if a = tk BSym.sep then (false, (if st.1 then ty BSym.one else ty BSym.zero) :: st.2.1, st.2.2)
  else (st.1, st.2.1, st.2.2 + 1)

def PInv (s : St) : Prop := s Reg.FP = [] ∨ s Reg.FP = [mk]

def paF (s : St) : St :=
  let r := (s Reg.W).foldl ps (decide (s Reg.FP ≠ []), s Reg.MR, 0)
  upd (upd (upd (upd s Reg.W []) Reg.FP (if r.1 then [mk] else [])) Reg.MR r.2.1) Reg.BAD
    (List.replicate r.2.2 mk ++ s Reg.BAD)

lemma pa_step (s : St) (x : Al) (l : List Al) (hx : s Reg.W = x :: l) (hI : PInv s) :
    StackProg.applyAct paAct s =
      upd (upd (upd (upd s Reg.W l) Reg.FP
        (if (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).1 then [mk] else [])) Reg.MR
        (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.1) Reg.BAD
        (List.replicate (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.2 mk ++ s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct paAct s r = (paAct (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdW : hd s Reg.W = some x := by simp [hd, hx]
  have hdF : (hd s Reg.FP) = if s Reg.FP = [] then none else some mk := by
    rcases hI with h | h <;> simp [hd, h]
  by_cases hx1 : x = tk BSym.one
  · subst hx1
    rcases hI with h | h
    · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx]
    · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx]
  · by_cases hx2 : x = tk BSym.sep
    · subst hx2
      rcases hI with h | h
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx, ty]
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx, ty]
    · rcases hI with h | h
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, hx, hx1, hx2, List.replicate_succ']
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, hx, hx1, hx2, List.replicate_succ']


lemma ps_add (l : List Al) : ∀ (r : Bool) (M : List Al) (n : ℕ),
    l.foldl ps (r, M, n) = ((l.foldl ps (r, M, 0)).1, (l.foldl ps (r, M, 0)).2.1,
      (l.foldl ps (r, M, 0)).2.2 + n) := by
  induction l with
  | nil => intro r M n; simp
  | cons a l ih =>
    intro r M n
    simp only [List.foldl_cons]
    rw [ih (ps (r, M, n) a).1 (ps (r, M, n) a).2.1 (ps (r, M, n) a).2.2,
      ih (ps (r, M, 0) a).1 (ps (r, M, 0) a).2.1 (ps (r, M, 0) a).2.2]
    unfold ps
    by_cases h1 : a = tk BSym.one <;> by_cases h2 : a = tk BSym.sep <;> simp [h1, h2] <;> (try split_ifs) <;> (try simp) <;> (try omega)

def paNB (s : St) : ℕ := ((s Reg.W).foldl ps (decide (s Reg.FP ≠ []), s Reg.MR, 0)).2.2

lemma paF_step (s : St) (x : Al) (l : List Al) (hx : s Reg.W = x :: l) (hI : PInv s) :
    paF (StackProg.applyAct paAct s) = paF s := by
  rw [pa_step s x l hx hI]
  have hk := ps_add l (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).1
    (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.1 (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.2
  have e : paF s = upd (upd (upd (upd s Reg.W []) Reg.FP
        (if (l.foldl ps (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x)).1 then [mk] else [])) Reg.MR
        (l.foldl ps (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x)).2.1) Reg.BAD
        (List.replicate (l.foldl ps (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x)).2.2 mk ++ s Reg.BAD) := by
    unfold paF
    rw [hx]
    rfl
  rw [e]
  generalize (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x) = q at hk ⊢
  obtain ⟨b, M, n1⟩ := q
  simp only at hk
  rw [hk]
  funext r
  unfold paF
  simp only [upd_apply, reduceCtorEq, ↓reduceIte]
  have hb : decide ((if b = true then [mk] else []) ≠ []) = b := by cases b <;> simp
  rw [hb]
  by_cases h1 : r = Reg.BAD
  · subst h1; simp only [ite_true]; rw [List.replicate_add, List.append_assoc]
  · by_cases h2 : r = Reg.MR
    · subst h2; simp
    · by_cases h3 : r = Reg.FP
      · subst h3; simp
      · by_cases h4 : r = Reg.W
        · subst h4; simp
        · simp [h1, h2, h3, h4]

lemma gsP_parse : GsP parseLoop (lrun (topS Reg.W) (StackProg.applyAct paAct) (fun s => (s Reg.W).length))
    (fun s => upd (paF s) Reg.BAD (s Reg.BAD)) (fun s => paNB s = 0) PInv := by
  refine GsP.loop1x (topS Reg.W) paAct (fun s => (s Reg.W).length) (fun s => len_le_S s Reg.W)
    (fun h => by simp [paAct]) (fun h => by simp [paAct]) 
    (fun h => by simp only [paAct]; simp; split_ifs <;> simp)
    ?_ PInv ?_ paF (fun s => List.replicate (paNB s) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.W s ht
    have e0 : StackProg.applyAct paAct s Reg.W = (paAct (hd s) Reg.W).apply (s Reg.W) := rfl
    have e1 : paAct (hd s) Reg.W = StackAct.pop := by simp [paAct]
    show (StackProg.applyAct paAct s Reg.W).length < (s Reg.W).length
    rw [e0, e1, hx]
    simp [StackAct.apply]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.W s ht
    rw [pa_step s x l hx hI]
    unfold PInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte]
    by_cases hb : (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).1 = true <;> simp [hb]
  · intro s hI ht
    have hWe : s Reg.W = [] := by
      simp only [topS, hd] at ht
      cases hs : s Reg.W with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    unfold paF
    simp only [hWe, List.foldl_nil, upd_apply]
    have hb : (if decide (s Reg.FP ≠ []) = true then [mk] else []) = s Reg.FP := by
      rcases hI with h | h <;> simp [h]
    by_cases h1 : r = Reg.BAD
    · subst h1; simp
    · by_cases h2 : r = Reg.MR
      · subst h2; simp
      · by_cases h3 : r = Reg.FP
        · subst h3; simpa using hb
        · by_cases h4 : r = Reg.W
          · subst h4; simp [hWe]
          · simp [h1, h2, h3, h4]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.W s ht
    exact paF_step s x l hx hI
  · intro s _
    simp [paF, upd_apply, paNB]
  · intro s _
    simp [paNB]

end Stk

end Sec_Ver17

section Sec_Ver18
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def scAct : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = Reg.TT then StackAct.pop
  else if r = Reg.KR then (if h Reg.TT = some (ty BSym.one) ∨ h Reg.TT = some (ty BSym.zero) then
      StackAct.pop else StackAct.keep)
  else if r = Reg.H then (if h Reg.TT = some mk then StackAct.pop
      else if h Reg.TT = some (ty BSym.one) ∧ h Reg.KR = some (ty BSym.one) ∧ (h Reg.H).isNone then
        StackAct.push mk else StackAct.keep)
  else if r = Reg.BAD then (if h Reg.TT = some mk then
      (if (h Reg.H).isNone then StackAct.push mk else StackAct.keep)
    else if h Reg.TT = some (ty BSym.one) ∨ h Reg.TT = some (ty BSym.zero) then
      (if (h Reg.KR).isNone then StackAct.push mk else StackAct.keep)
    else StackAct.push mk)
  else StackAct.keep

def scanLoop : Prog := .loop (topS Reg.TT) (.act scAct)

def ss (st : Bool × List Al × ℕ) (a : Al) : Bool × List Al × ℕ :=
  if a = mk then (false, st.2.1, if st.1 then st.2.2 else st.2.2 + 1)
  else if a = ty BSym.one then (st.1 || decide (st.2.1.head? = some (ty BSym.one)), st.2.1.tail,
      if st.2.1 = [] then st.2.2 + 1 else st.2.2)
  else if a = ty BSym.zero then (st.1, st.2.1.tail, if st.2.1 = [] then st.2.2 + 1 else st.2.2)
  else (st.1, st.2.1, st.2.2 + 1)

def SInv (s : St) : Prop := s Reg.H = [] ∨ s Reg.H = [mk]

def scF (s : St) : St :=
  let r := (s Reg.TT).foldl ss (decide (s Reg.H ≠ []), s Reg.KR, 0)
  upd (upd (upd (upd s Reg.TT []) Reg.H (if r.1 then [mk] else [])) Reg.KR r.2.1) Reg.BAD
    (List.replicate r.2.2 mk ++ s Reg.BAD)

lemma sc_step (s : St) (x : Al) (l : List Al) (hx : s Reg.TT = x :: l) (hI : SInv s) :
    StackProg.applyAct scAct s =
      upd (upd (upd (upd s Reg.TT l) Reg.H
        (if (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).1 then [mk] else [])) Reg.KR
        (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.1) Reg.BAD
        (List.replicate (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.2 mk ++ s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct scAct s r = (scAct (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdT : hd s Reg.TT = some x := by simp [hd, hx]
  have hdH : (hd s Reg.H) = if s Reg.H = [] then none else some mk := by
    rcases hI with h | h <;> simp [hd, h]
  have hdK : hd s Reg.KR = (s Reg.KR).head? := rfl
  cases hK : s Reg.KR with
  | nil =>
    have hdK' : hd s Reg.KR = none := by rw [hdK, hK]; rfl
    by_cases hx1 : x = mk
    · subst hx1
      rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
    · by_cases hx2 : x = ty BSym.one
      · subst hx2
        rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK] <;> (try split_ifs) <;> rfl
      · by_cases hx3 : x = ty BSym.zero
        · subst hx3
          rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
        · rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, hx, hK, hx1, hx2, hx3, List.replicate_succ']
  | cons y ky =>
    have hdK' : hd s Reg.KR = some y := by rw [hdK, hK]; rfl
    by_cases hx1 : x = mk
    · subst hx1
      rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
    · by_cases hx2 : x = ty BSym.one
      · subst hx2
        rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK] <;> (try split_ifs) <;> rfl
      · by_cases hx3 : x = ty BSym.zero
        · subst hx3
          rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
        · rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, hx, hK, hx1, hx2, hx3, List.replicate_succ']

lemma ss_add (l : List Al) : ∀ (r : Bool) (M : List Al) (n : ℕ),
    l.foldl ss (r, M, n) = ((l.foldl ss (r, M, 0)).1, (l.foldl ss (r, M, 0)).2.1,
      (l.foldl ss (r, M, 0)).2.2 + n) := by
  induction l with
  | nil => intro r M n; simp
  | cons a l ih =>
    intro r M n
    simp only [List.foldl_cons]
    rw [ih (ss (r, M, n) a).1 (ss (r, M, n) a).2.1 (ss (r, M, n) a).2.2,
      ih (ss (r, M, 0) a).1 (ss (r, M, 0) a).2.1 (ss (r, M, 0) a).2.2]
    unfold ss
    by_cases h1 : a = mk <;> by_cases h2 : a = ty BSym.one <;> by_cases h3 : a = ty BSym.zero <;> simp [h1, h2, h3] <;> (try split_ifs) <;> (try simp) <;> (try omega)

def scNB (s : St) : ℕ := ((s Reg.TT).foldl ss (decide (s Reg.H ≠ []), s Reg.KR, 0)).2.2

lemma scF_step (s : St) (x : Al) (l : List Al) (hx : s Reg.TT = x :: l) (hI : SInv s) :
    scF (StackProg.applyAct scAct s) = scF s := by
  rw [sc_step s x l hx hI]
  have hk := ss_add l (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).1
    (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.1 (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.2
  have e : scF s = upd (upd (upd (upd s Reg.TT []) Reg.H
        (if (l.foldl ss (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x)).1 then [mk] else [])) Reg.KR
        (l.foldl ss (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x)).2.1) Reg.BAD
        (List.replicate (l.foldl ss (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x)).2.2 mk ++ s Reg.BAD) := by
    unfold scF
    rw [hx]
    rfl
  rw [e]
  generalize (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x) = q at hk ⊢
  obtain ⟨b, M, n1⟩ := q
  simp only at hk
  rw [hk]
  funext r
  unfold scF
  simp only [upd_apply, reduceCtorEq, ↓reduceIte]
  have hb : decide ((if b = true then [mk] else []) ≠ []) = b := by cases b <;> simp
  rw [hb]
  by_cases h1 : r = Reg.BAD
  · subst h1; simp only [ite_true]; rw [List.replicate_add, List.append_assoc]
  · by_cases h2 : r = Reg.KR
    · subst h2; simp
    · by_cases h3 : r = Reg.H
      · subst h3; simp
      · by_cases h4 : r = Reg.TT
        · subst h4; simp
        · simp [h1, h2, h3, h4]

lemma gsP_scan : GsP scanLoop (lrun (topS Reg.TT) (StackProg.applyAct scAct) (fun s => (s Reg.TT).length))
    (fun s => upd (scF s) Reg.BAD (s Reg.BAD)) (fun s => scNB s = 0) SInv := by
  refine GsP.loop1x (topS Reg.TT) scAct (fun s => (s Reg.TT).length) (fun s => len_le_S s Reg.TT)
    (fun h => by simp [scAct]) (fun h => by simp [scAct]) 
    (fun h => by simp only [scAct]; simp; split_ifs <;> simp)
    ?_ SInv ?_ scF (fun s => List.replicate (scNB s) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.TT s ht
    have e0 : StackProg.applyAct scAct s Reg.TT = (scAct (hd s) Reg.TT).apply (s Reg.TT) := rfl
    have e1 : scAct (hd s) Reg.TT = StackAct.pop := by simp [scAct]
    show (StackProg.applyAct scAct s Reg.TT).length < (s Reg.TT).length
    rw [e0, e1, hx]
    simp [StackAct.apply]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.TT s ht
    rw [sc_step s x l hx hI]
    unfold SInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte]
    by_cases hb : (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).1 = true <;> simp [hb]
  · intro s hI ht
    have hWe : s Reg.TT = [] := by
      simp only [topS, hd] at ht
      cases hs : s Reg.TT with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    unfold scF
    simp only [hWe, List.foldl_nil, upd_apply]
    have hb : (if decide (s Reg.H ≠ []) = true then [mk] else []) = s Reg.H := by
      rcases hI with h | h <;> simp [h]
    by_cases h1 : r = Reg.BAD
    · subst h1; simp
    · by_cases h2 : r = Reg.KR
      · subst h2; simp
      · by_cases h3 : r = Reg.H
        · subst h3; simpa using hb
        · by_cases h4 : r = Reg.TT
          · subst h4; simp [hWe]
          · simp [h1, h2, h3, h4]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.TT s ht
    exact scF_step s x l hx hI
  · intro s _
    simp [scF, upd_apply, scNB]
  · intro s _
    simp [scNB]

end Stk

end Sec_Ver18

section Sec_Ver19
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def rcProg (a b c : Reg) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : safe a) (hb : safe b)
    (hc : safe c) : Prog :=
  repeatCopyProg (emb4 a b c Reg.RC hab hac ha.2 hbc hb.2 hc.2)

def gRc (a b c : Reg) (s : St) : St := upd (upd s c []) b ((List.replicate (s c).length (s a)).flatten ++ s b)

lemma gRc_BAD (a b c : Reg) (hb : b ≠ Reg.BAD) (hc : c ≠ Reg.BAD) (s : St) :
    gRc a b c s Reg.BAD = s Reg.BAD := by simp [gRc, upd_apply, hb, hc, hb.symm, hc.symm]

lemma gs_repcopy (a b c : Reg) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : safe a) (hb : safe b)
    (hc : safe c) (hb' : b ≠ Reg.BAD) (hc' : c ≠ Reg.BAD) :
    Gs (rcProg a b c hab hac hbc ha hb hc) (gRc a b c) (gRc a b c) (fun _ => True) := by
  refine Gs.total ⟨?_, fun s hs => ?_⟩ (gRc_BAD a b c hb' hc')
  · have := PSp.repcopy Gi a b c Reg.RC hab hac ha.2 hbc hb.2 hc.2
    exact PSp.weaken this (fun s hs => ⟨hs, hs.2⟩)
  · unfold gRc
    exact Gi_upd _ _ _ hb (Gi_upd _ _ _ hc hs)

end Stk

end Sec_Ver19

section Sec_Ver20
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def cmpAct : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = Reg.MB then StackAct.pop
  else if r = Reg.KB then StackAct.pop
  else if r = Reg.H then
    (if h Reg.MB = some (tk BSym.one) ∧ h Reg.KB ≠ some (tk BSym.one) then
        (if (h Reg.H).isNone then StackAct.push mk else StackAct.keep)
      else if h Reg.MB ≠ some (tk BSym.one) ∧ h Reg.KB = some (tk BSym.one) then StackAct.pop
      else StackAct.keep)
  else StackAct.keep

def cmpT : (Reg → Option Al) → Bool := fun h => (h Reg.MB).isSome || (h Reg.KB).isSome
def cmpLoop : Prog := .loop cmpT (.act cmpAct)

def cs (g : Bool) (x y : Option Al) : Bool :=
  if decide (x = some (tk BSym.one)) = decide (y = some (tk BSym.one)) then g
  else decide (x = some (tk BSym.one))

def cf (xs ys : List Al) (g : Bool) : Bool :=
  (List.zipWithAll (fun x y => (x, y)) xs ys).foldl (fun g p => cs g p.1 p.2) g

def CInv (s : St) : Prop := s Reg.H = [] ∨ s Reg.H = [mk]

def cmpF (s : St) : St :=
  upd (upd (upd s Reg.MB []) Reg.KB []) Reg.H
    (if cf (s Reg.MB) (s Reg.KB) (decide (s Reg.H ≠ [])) then [mk] else [])

lemma cmp_step (s : St) (hI : CInv s) (ht : cmpT (hd s) = true) :
    StackProg.applyAct cmpAct s =
      upd (upd (upd s Reg.MB (s Reg.MB).tail) Reg.KB (s Reg.KB).tail) Reg.H
        (if cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head? then [mk] else []) := by
  funext r
  have e0 : StackProg.applyAct cmpAct s r = (cmpAct (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdH : (hd s Reg.H) = if s Reg.H = [] then none else some mk := by
    rcases hI with h | h <;> simp [hd, h]
  have h1 : hd s Reg.MB = (s Reg.MB).head? := rfl
  have h2 : hd s Reg.KB = (s Reg.KB).head? := rfl
  by_cases hr1 : r = Reg.MB
  · subst hr1; simp [cmpAct, StackAct.apply, upd_apply]
  by_cases hr2 : r = Reg.KB
  · subst hr2; simp [cmpAct, StackAct.apply, upd_apply]
  by_cases hr3 : r = Reg.H
  · subst hr3
    simp only [cmpAct, upd_apply, reduceCtorEq, ↓reduceIte, hdH, h1, h2, cs]
    rcases hI with h | h <;> simp [h, StackAct.apply] <;> split_ifs <;> simp_all [StackAct.apply]
  · simp [cmpAct, StackAct.apply, upd_apply, hr1, hr2, hr3]

lemma cf_step (xs ys : List Al) (g : Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    cf xs ys g = cf xs.tail ys.tail (cs g xs.head? ys.head?) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp [cf, List.zipWithAll]
  | cons x xs =>
    cases ys with
    | nil => simp [cf, List.zipWithAll]
    | cons y ys => simp [cf, List.zipWithAll]

lemma cmpF_step (s : St) (hI : CInv s) (ht : cmpT (hd s) = true) :
    cmpF (StackProg.applyAct cmpAct s) = cmpF s := by
  rw [cmp_step s hI ht]
  have hne : s Reg.MB ≠ [] ∨ s Reg.KB ≠ [] := by
    simp only [cmpT, hd, Bool.or_eq_true] at ht
    rcases ht with h | h
    · left; intro h'; simp [h'] at h
    · right; intro h'; simp [h'] at h
  have e : cmpF s = upd (upd (upd s Reg.MB []) Reg.KB []) Reg.H
      (if cf (s Reg.MB).tail (s Reg.KB).tail
        (cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head?) then [mk] else []) := by
    unfold cmpF
    rw [cf_step _ _ _ hne]
  rw [e]
  generalize (cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head?) = g
  unfold cmpF
  funext r
  simp only [upd_apply, reduceCtorEq, ↓reduceIte]
  have hb : decide ((if g = true then [mk] else []) ≠ []) = g := by cases g <;> simp
  rw [hb]
  by_cases h1 : r = Reg.MB
  · subst h1; simp
  · by_cases h2 : r = Reg.KB
    · subst h2; simp
    · by_cases h3 : r = Reg.H
      · subst h3; simp
      · simp [h1, h2, h3]

lemma gsP_cmp : GsP cmpLoop (lrun cmpT (StackProg.applyAct cmpAct)
      (fun s => max (s Reg.MB).length (s Reg.KB).length))
    (fun s => upd (cmpF s) Reg.BAD (s Reg.BAD)) (fun _ => True) CInv := by
  refine GsP.loop1x cmpT cmpAct (fun s => max (s Reg.MB).length (s Reg.KB).length)
    (fun s => max_le (len_le_S s Reg.MB) (len_le_S s Reg.KB))
    (fun h => by simp [cmpAct]) (fun h => by simp [cmpAct])
    (fun h => by left; simp [cmpAct]) ?_ CInv ?_ cmpF (fun _ => []) _ ?_ ?_ ?_ ?_
  · intro s ht
    have e1 : StackProg.applyAct cmpAct s Reg.MB = (s Reg.MB).tail := by
      show (cmpAct (hd s) Reg.MB).apply (s Reg.MB) = _
      simp [cmpAct, StackAct.apply]
    have e2 : StackProg.applyAct cmpAct s Reg.KB = (s Reg.KB).tail := by
      show (cmpAct (hd s) Reg.KB).apply (s Reg.KB) = _
      simp [cmpAct, StackAct.apply]
    have hne : s Reg.MB ≠ [] ∨ s Reg.KB ≠ [] := by
      simp only [cmpT, hd, Bool.or_eq_true] at ht
      rcases ht with h | h
      · left; intro h'; simp [h'] at h
      · right; intro h'; simp [h'] at h
    show max (StackProg.applyAct cmpAct s Reg.MB).length (StackProg.applyAct cmpAct s Reg.KB).length < _
    rw [e1, e2]
    simp only [List.length_tail]
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; omega
    · have := List.length_pos_iff.2 h; omega
  · intro s hI ht
    rw [cmp_step s hI ht]
    unfold CInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte]
    by_cases hb : cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head? = true <;> simp [hb]
  · intro s hI ht
    have hMe : s Reg.MB = [] ∧ s Reg.KB = [] := by
      simp only [cmpT, hd, Bool.or_eq_false_iff] at ht
      constructor
      · cases hs : s Reg.MB with
        | nil => rfl
        | cons x l => simp [hs] at ht
      · cases hs : s Reg.KB with
        | nil => rfl
        | cons x l => simp [hs] at ht
    funext r
    unfold cmpF
    simp only [upd_apply, hMe.1, hMe.2]
    have hb : (if cf [] [] (decide (s Reg.H ≠ [])) = true then [mk] else []) = s Reg.H := by
      rcases hI with h | h <;> simp [cf, h]
    by_cases h1 : r = Reg.MB
    · subst h1; simp [hMe.1]
    · by_cases h2 : r = Reg.KB
      · subst h2; simp [hMe.2]
      · by_cases h3 : r = Reg.H
        · subst h3; simpa using hb
        · simp [h1, h2, h3]
  · intro s hI ht
    exact cmpF_step s hI ht
  · intro s _
    simp [cmpF, upd_apply]
  · intro s _
    simp

end Stk

end Sec_Ver20

section Sec_Ver21
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma GsP.branch {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 pre1 pre2 : St → Prop}
    (t : (Reg → Option Al) → Bool)
    (h1 : GsP p g1 T1 ok1 pre1) (h2 : GsP q g2 T2 ok2 pre2) :
    GsP (.branch t p q) (fun s => if t (hd s) = true then g1 s else g2 s)
      (fun s => if t (hd s) = true then T1 s else T2 s)
      (fun s => if t (hd s) = true then ok1 s else ok2 s)
      (fun s => if t (hd s) = true then pre1 s else pre2 s) := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.branch t a1 a2, fun s hs => ?_, fun s => ?_, fun s hi hp hb => ?_⟩
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact st1 s hs
    · simp only [ht, if_false]; exact st2 s hs
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact c1 s
    · simp only [ht, if_false]; exact c2 s
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true] at hp ⊢; exact s1 s hi hp hb
    · simp only [ht, if_false] at hp ⊢; exact s2 s hi hp hb

structure GB where
  p : Prog
  g : St → St
  T : St → St
  ok : St → Prop
  pre : St → Prop
  h : GsP p g T ok pre

def GB.weak (a : GB) (pre' : St → Prop) (hp : ∀ s, pre' s → a.pre s) : GsP a.p a.g a.T a.ok pre' :=
  GsP.congr a.h (fun _ _ _ => rfl) (fun _ _ _ => Iff.rfl) (fun s _ h => hp s h) a.h.2.2.1

def GB.seq (a b : GB) : GB where
  p := .seq a.p b.p
  g := fun s => b.g (a.g s)
  T := fun s => b.T (a.T s)
  ok := fun s => a.ok s ∧ b.ok (a.T s)
  pre := fun s => a.pre s ∧ (Gi s → s Reg.BAD = [] → a.ok s → b.pre (a.T s))
  h := GsP.seq (a.weak (fun s => a.pre s ∧ (Gi s → s Reg.BAD = [] → a.ok s → b.pre (a.T s)))
      (fun s h => h.1)) b.h (fun s hi hp hb ho => hp.2 hi hb ho)

def GB.branch (t : (Reg → Option Al) → Bool) (a b : GB) : GB where
  p := .branch t a.p b.p
  g := fun s => if t (hd s) = true then a.g s else b.g s
  T := fun s => if t (hd s) = true then a.T s else b.T s
  ok := fun s => if t (hd s) = true then a.ok s else b.ok s
  pre := fun s => if t (hd s) = true then a.pre s else b.pre s
  h := GsP.branch t a.h b.h

def GB.ofGs {p : Prog} {g T : St → St} {ok : St → Prop} (h : Gs p g T ok) : GB where
  p := p
  g := g
  T := T
  ok := ok
  pre := fun _ => True
  h := h.toP _

end Stk

end Sec_Ver21

section Sec_Ver22
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def bStNum (X : Reg) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : GB := GB.ofGs (gs_stNum X hX hX' hX2)
def bCopy (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (hb' : b ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_copy a b hab ha hb hb')
def bPush (r : Reg) (a : Al) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_push r a hr hr')
def bPop (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_pop r hr hr')
def bClear (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_clear r hr hr')
def bMvA (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (ha' : a ≠ Reg.BAD := by decide) (hb' : b ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_mvA a b hab ha hb ha' hb')
def bBad (t : (Reg → Option Al) → Bool) : GB := GB.ofGs (gs_badIf t)
def bEq (X D : Reg) (hX : safe X := by decide) (hD : safe D := by decide)
    (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide)
    (hDU : D ≠ Reg.U := by decide) (hDF : D ≠ Reg.F := by decide)
    (hDH : D ≠ Reg.HU := by decide) : GB :=
  ⟨_, _, _, _, _, gsP_eq X D hX hD hXU hXF hXH hXB hDU hDF hDH⟩
def bFill (A B : Reg) (x : Al) (hA : safe A := by decide) (hB : safe B := by decide)
    (hAB : A ≠ B := by decide) (hA' : A ≠ Reg.BAD := by decide) (hB' : B ≠ Reg.BAD := by decide) : GB :=
  ⟨_, _, _, _, _, gsP_fill A B x hA hB hAB hA' hB'⟩
def bDrain (A B : Reg) (c : Al → Bool) (hA : safe A := by decide) (hB : safe B := by decide)
    (hAB : A ≠ B := by decide) (hA' : A ≠ Reg.BAD := by decide) (hB' : B ≠ Reg.BAD := by decide) : GB :=
  ⟨_, _, _, _, _, gsP_drain A B c hA hB hAB hA' hB'⟩
def bRc (a b c : Reg) (hab : a ≠ b := by decide) (hac : a ≠ c := by decide)
    (hbc : b ≠ c := by decide) (ha : safe a := by decide) (hb : safe b := by decide)
    (hc : safe c := by decide) (hb' : b ≠ Reg.BAD := by decide) (hc' : c ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_repcopy a b c hab hac hbc ha hb hc hb' hc')
def bParse : GB := ⟨_, _, _, _, _, gsP_parse⟩
def bScan : GB := ⟨_, _, _, _, _, gsP_scan⟩
def bCmp : GB := ⟨_, _, _, _, _, gsP_cmp⟩

def isNoneT (r : Reg) (h : Reg → Option Al) : Bool := (h r).isNone
def notOneT (r : Reg) (h : Reg → Option Al) : Bool := decide (h r ≠ some (tk BSym.one))

def posB : GB :=
  (bEq Reg.KB Reg.K).seq <| (bBad (isNoneT Reg.K)).seq <|
  (bCopy Reg.T Reg.TC).seq <| (bFill Reg.TC Reg.T2 mk).seq <| (bEq Reg.MB Reg.T2).seq <|
  (bCopy Reg.K Reg.NC).seq <| (bPush Reg.NC mk).seq <| (bRc Reg.N Reg.PP Reg.NC).seq <|
  (bPush Reg.PP mk).seq <| (bCopy Reg.K Reg.PP).seq <|
  (bCopy Reg.T Reg.TC).seq <| (bDrain Reg.PP Reg.TC (fun _ => true)).seq <| (bClear Reg.TC).seq <|
  (bCopy Reg.K Reg.K2).seq <| (bCopy Reg.T Reg.TC).seq <|
    (bDrain Reg.TC Reg.K2 (isA (ty BSym.one))).seq <|
  bParse.seq <| (bMvA Reg.MR Reg.KR).seq <| (bBad (topS Reg.FP)).seq <|
  (bPush Reg.TM mk).seq <| (bCopy Reg.T Reg.TM).seq <| (bCopy Reg.N Reg.NC2).seq <|
    (bRc Reg.TM Reg.TT Reg.NC2).seq <|
  bScan.seq <| bBad (topS Reg.KR)

def negB : GB :=
  (bBad (topS Reg.W)).seq <|
  (bCopy Reg.MB Reg.LT).seq <| (bMvA Reg.LT Reg.MR).seq <| (bBad (notOneT Reg.MR)).seq <|
    (bClear Reg.MR).seq <|
  (bCopy Reg.KB Reg.LT).seq <| (bMvA Reg.LT Reg.MR).seq <| (bBad (notOneT Reg.MR)).seq <|
    (bClear Reg.MR).seq <|
  bCmp.seq <| bBad (isNoneT Reg.H)

end Stk

end Sec_Ver22

section Sec_Ver25
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def val : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * val l + b.toNat

lemma val_cons (b : Bool) (l : List Bool) : val (b :: l) = 2 * val l + b.toNat := rfl

lemma bits_val_of_canon : ∀ (l : List Bool), l.getLast? = some true ∨ l = [] → Nat.bits (val l) = l
  | [] , _ => by simp [val]
  | b :: l, h => by
    have hl : l.getLast? = some true ∨ l = [] := by
      rcases h with h | h
      · cases l with
        | nil => right; rfl
        | cons x r => left; simpa [List.getLast?_cons_cons] using h
      · simp at h
    have ih := bits_val_of_canon l hl
    have e : val (b :: l) = Nat.bit b (val l) := by
      rw [val_cons, Nat.bit_val]
    rw [e, Nat.bits_append_bit _ _ ?_, ih]
    intro h0
    cases l with
    | nil =>
      rcases h with h | h
      · simpa using h
      · simp at h
    | cons x r =>
      have : Nat.bits (val (x :: r)) = x :: r := ih
      rw [h0] at this
      simp at this

lemma val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : Nat.bit b n = 0
    · rw [h]; simp [val]
    · have hn : n = 0 → b = true := by
        intro h0; subst h0
        cases b with
        | false => simp at h
        | true => rfl
      rw [Nat.bits_append_bit _ _ hn, val_cons, ih, Nat.bit_val]

lemma getLast_bits (n : ℕ) (h : n ≠ 0) : (Nat.bits n).getLast? = some true := by
  induction n using Nat.binaryRec with
  | zero => exact absurd rfl h
  | bit b n ih =>
    have hn : n = 0 → b = true := by
      intro h0; subst h0
      cases b with
      | false => simp at h
      | true => rfl
    rw [Nat.bits_append_bit _ _ hn]
    by_cases h0 : n = 0
    · subst h0; simp [hn rfl]
    · have := ih h0
      have hne : Nat.bits n ≠ [] := by
        intro he; rw [he] at this; simp at this
      obtain ⟨x, r, hr⟩ := List.exists_cons_of_ne_nil hne
      rw [hr] at this ⊢
      simpa [List.getLast?_cons_cons] using this

end Stk

end Sec_Ver25

section Sec_Ver26
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma cf_nil (g : Bool) : cf [] [] g = g := by simp [cf]

lemma tkb_one_iff (b : Bool) : (some (tkb b) = some (tk BSym.one)) ↔ b = true := by
  cases b <;> simp [tkb, tk]

lemma cf_val : ∀ (xs ys : List Bool) (g : Bool),
    cf (xs.map tkb) (ys.map tkb) g = decide (val ys < val xs ∨ (val xs = val ys ∧ g = true))
  | [], [], g => by simp [cf_nil, val]
  | x :: xs, [], g => by
    rw [List.map_cons, List.map_nil, cf_step _ _ _ (Or.inl (by simp))]
    have ih := cf_val xs [] (cs g (some (tkb x)) none)
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil] at ih ⊢
    rw [ih]
    cases x <;> cases g <;> simp [cs, tkb, tk, val] <;> omega
  | [], y :: ys, g => by
    rw [List.map_cons, List.map_nil, cf_step _ _ _ (Or.inr (by simp))]
    have ih := cf_val [] ys (cs g none (some (tkb y)))
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil] at ih ⊢
    rw [ih]
    cases y <;> cases g <;> simp [cs, tkb, tk, val] <;> omega
  | x :: xs, y :: ys, g => by
    rw [List.map_cons, List.map_cons, cf_step _ _ _ (Or.inl (by simp))]
    have ih := cf_val xs ys (cs g (some (tkb x)) (some (tkb y)))
    simp only [List.map_cons, List.tail_cons, List.head?_cons] at ih ⊢
    rw [ih]
    cases x <;> cases y <;> cases g <;> simp [cs, tkb, tk, val]
    all_goals first | omega | (apply decide_eq_decide.2; omega) | (simp only [← Bool.decide_or]; apply decide_eq_decide.2; omega)

end Stk

end Sec_Ver26

section Sec_Ver30
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma isBitW_tkb (b : Bool) : isBitW (tkb b) = true := by cases b <;> simp [isBitW, tkb, tk]
lemma isBitW_sep : isBitW (tk BSym.sep) = false := by simp [isBitW, tk]

lemma tw_calc : ∀ (bl : List Bool) (rest : List Al),
    (bl.map tkb ++ tk BSym.sep :: rest).takeWhile isBitW = bl.map tkb ∧
    (bl.map tkb ++ tk BSym.sep :: rest).dropWhile isBitW = tk BSym.sep :: rest
  | [], rest => by simp [isBitW_sep]
  | b :: bl, rest => by
    have := tw_calc bl rest
    simp [List.takeWhile_cons, List.dropWhile_cons, isBitW_tkb, this]

lemma bits_dec : ∀ (l : List Al), (∀ a ∈ l, isBitW a = true) → ∃ bl : List Bool, l = bl.map tkb
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨bl, hbl⟩ := bits_dec l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self)
    simp only [isBitW, decide_eq_true_eq] at ha
    rcases ha with ha | ha
    · exact ⟨false :: bl, by simp [hbl, ha, tkb, tk]⟩
    · exact ⟨true :: bl, by simp [hbl, ha, tkb, tk]⟩

lemma stNum_dec (s : St) : okNum s → ∃ (bl : List Bool) (rest : List Al),
    s Reg.W = bl.map tkb ++ tk BSym.sep :: rest := by
  intro h
  unfold okNum B1 gMvP at h
  simp only [topP, hd, upd_apply, reduceCtorEq, ↓reduceIte, if_true] at h
  cases hd' : (s Reg.W).dropWhile isBitW with
  | nil => simp [hd'] at h
  | cons x rest =>
    rw [hd'] at h
    simp only [List.head?_cons, isA, decide_eq_true_eq] at h
    subst h
    obtain ⟨bl, hbl⟩ := bits_dec ((s Reg.W).takeWhile isBitW) (fun a ha => List.mem_takeWhile_imp ha)
    refine ⟨bl, rest, ?_⟩
    rw [← hbl, ← hd']
    exact (List.takeWhile_append_dropWhile).symm

lemma stNum_calc (X : Reg) (s : St) (bl : List Bool) (rest : List Al)
    (hW : s Reg.W = bl.map tkb ++ tk BSym.sep :: rest) (hT : s Reg.TMP = [])
    (hXW : X ≠ Reg.W) (hXT : X ≠ Reg.TMP) :
    okNum s ∧ ∀ r, B3 X s r = if r = X then bl.map tkb ++ s X else if r = Reg.W then rest
      else if r = Reg.TMP then [] else s r := by
  have hc := tw_calc bl rest
  have hB1 : B1 s = upd (upd s Reg.W (tk BSym.sep :: rest)) Reg.TMP (bl.map tkb).reverse := by
    unfold B1 gMvP
    rw [hW, hc.1, hc.2]; simp [hT]
  constructor
  · unfold okNum; rw [hB1]; simp [topP, hd, upd_apply, isA]
  · intro r
    unfold B3 B2 gMvA gPop
    rw [hB1]
    by_cases h1 : r = X <;> by_cases h2 : r = Reg.W <;> by_cases h3 : r = Reg.TMP <;>
      simp [upd_apply, h1, h2, h3, hXW, hXT, hXW.symm, hXT.symm, hT] <;> subst_vars <;> simp_all

end Stk

end Sec_Ver30

section Sec_Ver44
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
section PSJ
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma loop_execJ {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSI Inv p g d)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, Inv s → ∃ n, n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s hs ht
    obtain ⟨n1, hn1, e1⟩ := hp s hs
    have hgs := hinv s hs ht
    by_cases ht2 : t (hd (g s)) = true
    · obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl hgs
      refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
      · rw [← hm]
        have hg := hgrow s hs ht ht2
        have hY : S (g s) + c * μ (g s) + 2 ≤ S s + c * μ s + 2 := by
          have : c * μ (g s) + c ≤ c * μ s := by
            have : μ (g s) + 1 ≤ μ s := hlt
            nlinarith
          omega
        have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h2 : n2 ≤ (μ (g s) + 1) * ((S s + c * μ s + 2) ^ d + 3) :=
          le_trans hn2 (Nat.mul_le_mul_left _ (by
            have := Nat.pow_le_pow_left hY d; omega))
        have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
        have h4 : (μ (g s) + 1 + 1) * ((S s + c * μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        nlinarith
      · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
    · have ht2' : t (hd (g s)) = false := by simpa using ht2
      refine ⟨1 + n1 + 1 + 1, ?_, ?_⟩
      · rw [← hm]
        have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h3 : 2 ≤ μ s + 1 := by omega
        have h4 : 2 * ((S s + c * μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        omega
      · have e3 : (StackProg.loop t p).Exec (g s) (G (g s)) 1 := by
          rw [hstop (g s) hgs ht2']; exact StackProg.Exec.loopFalse ht2'
        rw [hG]
        exact StackProg.Exec.loopTrue ht e1 e3
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + c * m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s hs ht']; exact StackProg.Exec.loopFalse ht'

lemma PSp.loopJ {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨(c + 1) * d + 3, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execJ t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + c * μ s + 2 ≤ X ^ (c + 1) := by
    have : S s + c * μ s + 2 ≤ (c + 1) * X := by nlinarith
    have hc : c + 1 ≤ X ^ c := le_trans (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left hX2 c)
    calc _ ≤ (c + 1) * X := this
      _ ≤ X ^ c * X := Nat.mul_le_mul_right _ hc
      _ = X ^ (c + 1) := by rw [pow_succ]
  have a2 : (S s + c * μ s + 2) ^ d ≤ X ^ ((c + 1) * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ ((c + 1) * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + c * μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ ((c + 1) * d + 3) := by rw [hZ]; ring

lemma PSp.seq2 {I1 I2 : (K → List A) → Prop} {p q : StackProg K A}
    {g h : (K → List A) → (K → List A)}
    (hp : PSp I1 p g) (hq : PSp I2 q h) (hi : ∀ s, I1 s → I2 (g s)) :
    PSp I1 (.seq p q) (fun s => h (g s)) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨d1 + 3 + (Fintype.card K + d1 + 2) * d2, fun s hs => ?_⟩
  obtain ⟨n1, hn1, e1⟩ := hp s hs
  obtain ⟨n2, hn2, e2⟩ := hq (g s) (hi s hs)
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  set X := S s + 2 with hXd
  have hX : 2 ≤ X := by omega
  have hsz := Exec_size e1
  have hY : S (g s) + 2 ≤ X ^ (Fintype.card K + d1 + 2) := by
    have a1 : X ≤ X ^ 1 := by simp
    have a2 : Fintype.card K * n1 ≤ X ^ (Fintype.card K + d1) :=
      pw_mul (pw_const hX (Fintype.card K)) hn1
    have := pw_add hX a1 a2
    calc S (g s) + 2 ≤ X + Fintype.card K * n1 := by omega
      _ ≤ X ^ (1 + (Fintype.card K + d1) + 1) := this
      _ = _ := by ring_nf
  have b1 : n2 ≤ X ^ ((Fintype.card K + d1 + 2) * d2) :=
    le_trans hn2 (pw_pow hY)
  have b2 : n1 + 1 ≤ X ^ (d1 + 0 + 1) := pw_add hX hn1 (show 1 ≤ X ^ 0 by simp)
  have := pw_add hX b2 b1
  exact le_trans this (pw_mono hX (by omega))

end PSJ
end Stk

end Sec_Ver44

section Sec_Ver45
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def isOne (x : Option Al) : Bool := decide (x = some (tk BSym.one))

def adSum (c : Bool) (p : Option Al × Option Al) : Bool := xor (xor (isOne p.1) (isOne p.2)) c
def adCar (c : Bool) (p : Option Al × Option Al) : Bool :=
  (isOne p.1 && isOne p.2) || (isOne p.1 && c) || (isOne p.2 && c)

def addAct (A X : Reg) : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = A then StackAct.pop
  else if r = X then StackAct.pop
  else if r = Reg.LT then StackAct.push (tkb (adSum (h Reg.FP).isSome (h A, h X)))
  else if r = Reg.FP then
    (if (h Reg.FP).isSome then
      (if adCar (h Reg.FP).isSome (h A, h X) then StackAct.keep else StackAct.pop)
     else (if adCar false (h A, h X) then StackAct.push mk else StackAct.keep))
  else StackAct.keep

def addT (A X : Reg) : (Reg → Option Al) → Bool := fun h => (h A).isSome || (h X).isSome

def adf (acc : List Al) (c : Bool) (xs ys : List Al) : List Al × Bool :=
  (List.zipWithAll (fun x y => (x, y)) xs ys).foldl
    (fun st p => (tkb (adSum st.2 p) :: st.1, adCar st.2 p)) (acc, c)

lemma adf_step (acc : List Al) (c : Bool) (xs ys : List Al) (h : xs ≠ [] ∨ ys ≠ []) :
    adf acc c xs ys = adf (tkb (adSum c (xs.head?, ys.head?)) :: acc)
      (adCar c (xs.head?, ys.head?)) xs.tail ys.tail := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp [adf, List.zipWithAll]
  | cons x xs =>
    cases ys with
    | nil => simp [adf, List.zipWithAll]
    | cons y ys => simp [adf, List.zipWithAll]

lemma adf_nil (acc : List Al) (c : Bool) : adf acc c [] [] = (acc, c) := by simp [adf]

def AInv (s : St) : Prop := s Reg.FP = [] ∨ s Reg.FP = [mk]

def addF (A X : Reg) (s : St) : St :=
  upd (upd (upd (upd s A []) X []) Reg.LT
    (adf (s Reg.LT) (decide (s Reg.FP ≠ [])) (s A) (s X)).1) Reg.FP
    (if (adf (s Reg.LT) (decide (s Reg.FP ≠ [])) (s A) (s X)).2 then [mk] else [])

lemma add_step (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT) (hAF : A ≠ Reg.FP)
    (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP) (s : St) (hI : AInv s) :
    StackProg.applyAct (addAct A X) s =
      upd (upd (upd (upd s A (s A).tail) X (s X).tail) Reg.LT
        (tkb (adSum (decide (s Reg.FP ≠ [])) ((s A).head?, (s X).head?)) :: s Reg.LT)) Reg.FP
        (if adCar (decide (s Reg.FP ≠ [])) ((s A).head?, (s X).head?) then [mk] else []) := by
  funext r
  have e0 : StackProg.applyAct (addAct A X) s r = (addAct A X (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdH : (hd s Reg.FP).isSome = decide (s Reg.FP ≠ []) := by
    rcases hI with h | h <;> simp [hd, h]
  have h1 : hd s A = (s A).head? := rfl
  have h2 : hd s X = (s X).head? := rfl
  by_cases hr1 : r = A
  · subst hr1; simp [addAct, StackAct.apply, upd_apply, hAX, hAL, hAF]
  by_cases hr2 : r = X
  · subst hr2; simp [addAct, StackAct.apply, upd_apply, hAX, hXL, hXF, hr1]
  by_cases hr3 : r = Reg.LT
  · subst hr3; simp [addAct, StackAct.apply, upd_apply, hr1, hr2, hdH, h1, h2, hAL.symm, hXL.symm]
  by_cases hr4 : r = Reg.FP
  · subst hr4
    simp only [addAct, upd_apply, reduceCtorEq, ↓reduceIte, hdH, h1, h2, hr1, hr2, hr3]
    rcases hI with h | h <;> simp [h, StackAct.apply] <;> split_ifs <;> simp_all [StackAct.apply]
  · simp [addAct, StackAct.apply, upd_apply, hr1, hr2, hr3, hr4]

lemma addF_step (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT) (hAF : A ≠ Reg.FP)
    (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP) (s : St) (hI : AInv s)
    (ht : addT A X (hd s) = true) :
    addF A X (StackProg.applyAct (addAct A X) s) = addF A X s := by
  rw [add_step A X hAX hAL hAF hXL hXF s hI]
  have hne : s A ≠ [] ∨ s X ≠ [] := by
    simp only [addT, hd, Bool.or_eq_true] at ht
    rcases ht with h | h
    · left; intro h'; simp [h'] at h
    · right; intro h'; simp [h'] at h
  have key := adf_step (s Reg.LT) (decide (s Reg.FP ≠ [])) (s A) (s X) hne
  unfold addF
  have hb : ∀ c : Bool, decide ((if c = true then [mk] else ([] : List Al)) ≠ []) = c := by
    intro c; cases c <;> simp
  simp only [upd_apply, reduceCtorEq, ↓reduceIte, hAL, hAF, hXL, hXF, hAL.symm, hXF.symm, hXL.symm,
    hAF.symm, hAX, hAX.symm, hb, if_true]
  rw [key]
  funext r
  simp only [upd_apply]
  split_ifs <;> simp_all

end Stk

end Sec_Ver45

section Sec_Ver46
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma gsP_addLoop (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT) (hAF : A ≠ Reg.FP)
    (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP) (hA : safe A) (hX : safe X)
    (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) :
    GsP (.loop (addT A X) (.act (addAct A X)))
      (lrun (addT A X) (StackProg.applyAct (addAct A X)) (fun s => max (s A).length (s X).length))
      (fun s => upd (addF A X s) Reg.BAD (s Reg.BAD)) (fun _ => True) AInv := by
  obtain ⟨hAC, hARC⟩ := hA
  obtain ⟨hXC, hXRC⟩ := hX
  refine GsP.loop1x (addT A X) (addAct A X) (fun s => max (s A).length (s X).length)
    (fun s => max_le (len_le_S s A) (len_le_S s X))
    (fun h => by simp [addAct, hAC, hXC, hAC.symm, hXC.symm])
    (fun h => by simp [addAct, hARC, hXRC, hARC.symm, hXRC.symm])
    (fun h => by left; simp [addAct, hAB, hXB, hAB.symm, hXB.symm]) ?_ AInv ?_ (addF A X) (fun _ => []) _ ?_ ?_ ?_ ?_
  · intro s ht
    have e1 : StackProg.applyAct (addAct A X) s A = (s A).tail := by
      show (addAct A X (hd s) A).apply (s A) = _
      simp [addAct, StackAct.apply]
    have e2 : StackProg.applyAct (addAct A X) s X = (s X).tail := by
      show (addAct A X (hd s) X).apply (s X) = _
      simp [addAct, StackAct.apply, hAX.symm]
    have hne : s A ≠ [] ∨ s X ≠ [] := by
      simp only [addT, hd, Bool.or_eq_true] at ht
      rcases ht with h | h
      · left; intro h'; simp [h'] at h
      · right; intro h'; simp [h'] at h
    show max (StackProg.applyAct (addAct A X) s A).length
      (StackProg.applyAct (addAct A X) s X).length < _
    rw [e1, e2]
    simp only [List.length_tail]
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; omega
    · have := List.length_pos_iff.2 h; omega
  · intro s hI ht
    rw [add_step A X hAX hAL hAF hXL hXF s hI]
    unfold AInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte, hAF, hXF, hAF.symm, hXF.symm, hAX, hAX.symm]
    by_cases hb : adCar (decide (s Reg.FP ≠ [])) ((s A).head?, (s X).head?) = true <;> simp [hb]
  · intro s hI ht
    have hMe : s A = [] ∧ s X = [] := by
      simp only [addT, hd, Bool.or_eq_false_iff] at ht
      constructor
      · cases hs : s A with
        | nil => rfl
        | cons x l => simp [hs] at ht
      · cases hs : s X with
        | nil => rfl
        | cons x l => simp [hs] at ht
    funext r
    unfold addF
    simp only [upd_apply, hMe.1, hMe.2, adf_nil]
    have hb : (if (decide (s Reg.FP ≠ [])) = true then [mk] else []) = s Reg.FP := by
      rcases hI with h | h <;> simp [h]
    by_cases h1 : r = A
    · simp [h1, hMe.1, hAX, hAL, hAF]
    · by_cases h2 : r = X
      · simp [h2, hMe.2, hAX.symm, hXL, hXF]
      · by_cases h3 : r = Reg.LT
        · simp [h3, hAL.symm, hXL.symm]
        · by_cases h4 : r = Reg.FP
          · simp [h4, hAF.symm, hXF.symm]; simpa using hb
          · simp [h1, h2, h3, h4]
  · intro s hI ht
    exact addF_step A X hAX hAL hAF hXL hXF s hI ht
  · intro s _
    simp [addF, upd_apply, hAB.symm, hXB.symm]
  · intro s _
    simp

end Stk

end Sec_Ver46

section Sec_Ver47
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def abits : Bool → List Bool → List Bool → List Bool × Bool
  | c, [], [] => ([], c)
  | c, x :: xs, [] =>
    let r := abits ((x && false) || (x && c) || (false && c)) xs []
    (xor (xor x false) c :: r.1, r.2)
  | c, [], y :: ys =>
    let r := abits ((false && y) || (false && c) || (y && c)) [] ys
    (xor (xor false y) c :: r.1, r.2)
  | c, x :: xs, y :: ys =>
    let r := abits ((x && y) || (x && c) || (y && c)) xs ys
    (xor (xor x y) c :: r.1, r.2)

lemma isOne_tkb (b : Bool) : isOne (some (tkb b)) = b := by
  cases b <;> simp [isOne, tkb, tk]

lemma isOne_none : isOne none = false := by simp [isOne, tk]

lemma adSum_xx (c x y : Bool) : adSum c (some (tkb x), some (tkb y)) = xor (xor x y) c := by
  simp [adSum, isOne_tkb]
lemma adSum_xn (c x : Bool) : adSum c (some (tkb x), none) = xor (xor x false) c := by
  simp [adSum, isOne_tkb, isOne_none]
lemma adSum_nx (c y : Bool) : adSum c (none, some (tkb y)) = xor (xor false y) c := by
  simp [adSum, isOne_tkb, isOne_none]
lemma adCar_xx (c x y : Bool) :
    adCar c (some (tkb x), some (tkb y)) = ((x && y) || (x && c) || (y && c)) := by
  simp [adCar, isOne_tkb]
lemma adCar_xn (c x : Bool) :
    adCar c (some (tkb x), none) = ((x && false) || (x && c) || (false && c)) := by
  simp [adCar, isOne_tkb, isOne_none]
lemma adCar_nx (c y : Bool) :
    adCar c (none, some (tkb y)) = ((false && y) || (false && c) || (y && c)) := by
  simp [adCar, isOne_tkb, isOne_none]

lemma adf_bits : ∀ (c : Bool) (xs ys : List Bool) (acc : List Al),
    adf acc c (xs.map tkb) (ys.map tkb) =
      (((abits c xs ys).1.map tkb).reverse ++ acc, (abits c xs ys).2)
  | c, [], [], acc => by simp [abits, adf_nil]
  | c, x :: xs, [], acc => by
    rw [List.map_cons, List.map_nil, adf_step _ _ _ _ (Or.inl (by simp))]
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons,
      List.head?_nil, adSum_xn, adCar_xn]
    have ih := adf_bits ((x && false) || (x && c) || (false && c)) xs []
      (tkb (xor (xor x false) c) :: acc)
    simp only [List.map_nil] at ih
    rw [ih]
    simp [abits]
  | c, [], y :: ys, acc => by
    rw [List.map_cons, List.map_nil, adf_step _ _ _ _ (Or.inr (by simp))]
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons,
      List.head?_nil, adSum_nx, adCar_nx]
    have ih := adf_bits ((false && y) || (false && c) || (y && c)) [] ys
      (tkb (xor (xor false y) c) :: acc)
    simp only [List.map_nil] at ih
    rw [ih]
    simp [abits]
  | c, x :: xs, y :: ys, acc => by
    rw [List.map_cons, List.map_cons, adf_step _ _ _ _ (Or.inl (by simp))]
    simp only [List.map_cons, List.tail_cons, List.head?_cons, adSum_xx, adCar_xx]
    have ih := adf_bits ((x && y) || (x && c) || (y && c)) xs ys (tkb (xor (xor x y) c) :: acc)
    rw [ih]
    simp [abits]

lemma abits_len : ∀ (c : Bool) (xs ys : List Bool),
    ((abits c xs ys).1).length = max xs.length ys.length
  | c, [], [] => by simp [abits]
  | c, x :: xs, [] => by simp [abits, abits_len _ xs []]
  | c, [], y :: ys => by simp [abits, abits_len _ [] ys]
  | c, x :: xs, y :: ys => by simp [abits, abits_len _ xs ys]

lemma pmul2 (P k : ℕ) : P * 2 * k = 2 * (P * k) := by ring

lemma abits_val : ∀ (c : Bool) (xs ys : List Bool),
    val (abits c xs ys).1 + 2 ^ ((abits c xs ys).1).length * (abits c xs ys).2.toNat =
      val xs + val ys + c.toNat
  | c, [], [] => by simp [abits, val]
  | c, x :: xs, [] => by
    have ih := abits_val ((x && false) || (x && c) || (false && c)) xs []
    simp only [abits, List.length_cons, val_cons, pow_succ, pmul2] at ih ⊢
    have : val [] = 0 := rfl
    rw [this] at ih ⊢
    cases x <;> cases c <;> simp_all [Bool.toNat] <;> omega
  | c, [], y :: ys => by
    have ih := abits_val ((false && y) || (false && c) || (y && c)) [] ys
    simp only [abits, List.length_cons, val_cons, pow_succ, pmul2] at ih ⊢
    have : val [] = 0 := rfl
    rw [this] at ih ⊢
    cases y <;> cases c <;> simp_all [Bool.toNat] <;> omega
  | c, x :: xs, y :: ys => by
    have ih := abits_val ((x && y) || (x && c) || (y && c)) xs ys
    simp only [abits, List.length_cons, val_cons, pow_succ, pmul2] at ih ⊢
    cases x <;> cases y <;> cases c <;> simp_all [Bool.toNat] <;> omega

end Stk

end Sec_Ver47

section Sec_Ver48
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma val_append : ∀ (l1 l2 : List Bool), val (l1 ++ l2) = val l1 + 2 ^ l1.length * val l2
  | [], l2 => by simp [val]
  | b :: l1, l2 => by
    simp only [List.cons_append, val_cons, val_append l1 l2, List.length_cons, pow_succ]
    ring

def addBits (xs ys : List Bool) : List Bool :=
  (abits false xs ys).1 ++ (if (abits false xs ys).2 then [true] else [])

lemma val_addBits (xs ys : List Bool) : val (addBits xs ys) = val xs + val ys := by
  have h := abits_val false xs ys
  unfold addBits
  rw [val_append]
  cases hc : (abits false xs ys).2 <;> simp [hc, val] at h ⊢ <;> omega

def skipB : GB := GB.ofGs (Gs.total Gad.skip (fun _ => rfl))

def bAdd (A X : Reg) (hAX : A ≠ X := by decide) (hAL : A ≠ Reg.LT := by decide)
    (hAF : A ≠ Reg.FP := by decide) (hXL : X ≠ Reg.LT := by decide) (hXF : X ≠ Reg.FP := by decide)
    (hA : safe A := by decide) (hX : safe X := by decide)
    (hAB : A ≠ Reg.BAD := by decide) (hXB : X ≠ Reg.BAD := by decide) : GB :=
  (bClear Reg.LT).seq <| (bClear Reg.FP).seq <|
  (⟨_, _, _, _, _, gsP_addLoop A X hAX hAL hAF hXL hXF hA hX hAB hXB⟩ : GB).seq <|
  (GB.branch (topS Reg.FP) ((bPush Reg.LT (tkb true)).seq (bPop Reg.FP)) skipB).seq <|
  bMvA Reg.LT A hAL.symm (by decide) hA (by decide) hAB

end Stk

end Sec_Ver48

section Sec_Ver49
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma bAdd_pre (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT)
    (hAF : A ≠ Reg.FP) (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP)
    (hA : safe A) (hX : safe X) (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) (s : St) :
    (bAdd A X hAX hAL hAF hXL hXF hA hX hAB hXB).pre s := by
  simp only [bAdd, GB.seq, GB.branch, bClear, bPush, bPop, bMvA, skipB, GB.ofGs, gClear, upd_apply]
  simp [AInv, hd, topS]

end Stk
namespace Stk

lemma bAdd_ok (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT)
    (hAF : A ≠ Reg.FP) (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP)
    (hA : safe A) (hX : safe X) (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) (s : St) :
    (bAdd A X hAX hAL hAF hXL hXF hA hX hAB hXB).ok s := by
  simp only [bAdd, GB.seq, GB.branch, bClear, bPush, bPop, bMvA, skipB, GB.ofGs, gClear, upd_apply]
  simp

lemma bAdd_T (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT)
    (hAF : A ≠ Reg.FP) (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP)
    (hA : safe A) (hX : safe X) (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) (s : St)
    (bl1 bl2 : List Bool) (h1 : s A = bl1.map tkb) (h2 : s X = bl2.map tkb) :
    (bAdd A X hAX hAL hAF hXL hXF hA hX hAB hXB).T s =
      upd (upd (upd (upd s A ((addBits bl1 bl2).map tkb)) X []) Reg.LT []) Reg.FP [] := by
  simp only [bAdd, GB.seq, GB.branch, bClear, bPush, bPop, bMvA, skipB, GB.ofGs, gClear, upd_apply,
    gMvA, gPush, gPop]
  have hA1 : ∀ l : List Al, upd (upd s Reg.LT []) Reg.FP [] A = s A := by
    intro l; simp [upd_apply, hAL, hAF]
  have hX1 : upd (upd s Reg.LT []) Reg.FP [] X = s X := by simp [upd_apply, hXL, hXF]
  have hf := adf_bits false bl1 bl2 []
  funext r
  unfold addF
  simp only [hA1 [], hX1, h1, h2, hf, upd_apply, topS, hd]
  cases hc : (abits false bl1 bl2).2 <;> simp [hc, hf, addBits, hAL, hAF, hXL, hXF, hAL.symm, hAF.symm, hXL.symm, hXF.symm, hAB, hXB, hAB.symm, hXB.symm] <;>
    (by_cases e1 : r = A <;> by_cases e2 : r = X <;> by_cases e3 : r = Reg.LT <;> by_cases e4 : r = Reg.FP <;> by_cases e5 : r = Reg.BAD <;> simp_all)

end Stk

end Sec_Ver49

section Sec_Ver50
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

abbrev AddH (A X : Reg) : Prop := A ≠ X ∧ A ≠ Reg.LT ∧ A ≠ Reg.FP ∧ X ≠ Reg.LT ∧ X ≠ Reg.FP ∧
  safe A ∧ safe X ∧ A ≠ Reg.BAD ∧ X ≠ Reg.BAD

def addG (A X : Reg) (h : AddH A X := by decide) : GB :=
  bAdd A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

lemma addG_pre (A X : Reg) (h : AddH A X) (s : St) : (addG A X h).pre s :=
  bAdd_pre A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 s

lemma seq_pre_all {a b : GB} (ha : ∀ s, a.pre s) (hb : ∀ s, b.pre s) : ∀ s, (a.seq b).pre s :=
  fun s => ⟨ha s, fun _ _ _ => hb _⟩

lemma branch_pre_all {a b : GB} (t : (Reg → Option Al) → Bool) (ha : ∀ s, a.pre s)
    (hb : ∀ s, b.pre s) : ∀ s, (GB.branch t a b).pre s := by
  intro s; simp only [GB.branch]; split_ifs
  · exact ha s
  · exact hb s

lemma ofGs_pre_all {p : Prog} {g T : St → St} {ok : St → Prop} (h : Gs p g T ok) :
    ∀ s, (GB.ofGs h).pre s := fun _ => trivial

lemma clear_pre (r : Reg) (hr : safe r) (hr' : r ≠ Reg.BAD) (s : St) : (bClear r hr hr').pre s := trivial
lemma bad_pre (t : (Reg → Option Al) → Bool) (s : St) : (bBad t).pre s := trivial

def cmpL (g : Bool) : GB :=
  (bClear Reg.H).seq <| (if g then bPush Reg.H mk else skipB).seq bCmp

lemma cmpL_pre (g : Bool) (s : St) : (cmpL g).pre s := by
  cases g <;> simp only [cmpL, GB.seq, bClear, bPush, skipB, GB.ofGs, bCmp, Bool.false_eq_true, if_false, if_true,
    gClear, gPush] <;> refine ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => ?_⟩⟩ <;>
    simp [CInv, upd_apply]

end Stk

end Sec_Ver50

section Sec_Ver55x
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
lemma addG_ok (A X : Reg) (h : AddH A X) (s : St) : (addG A X h).ok s :=
  bAdd_ok A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 s

lemma addG_T (A X : Reg) (h : AddH A X) (s : St) (bl1 bl2 : List Bool) (h1 : s A = bl1.map tkb)
    (h2 : s X = bl2.map tkb) :
    (addG A X h).T s = upd (upd (upd (upd s A ((addBits bl1 bl2).map tkb)) X []) Reg.LT []) Reg.FP [] :=
  bAdd_T A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 s bl1 bl2 h1 h2


end Stk

end Sec_Ver55x

section Sec_Ap1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def stBlk (R X : Reg) : Prog :=
  sq (mvP R Reg.TMP isBitW) <| sq (popIf R (isA (tk BSym.sep))) <| mvA Reg.TMP X

def PB1 (R : Reg) (s : St) : St := gMvP R Reg.TMP isBitW s
def PB2 (R : Reg) (s : St) : St := gPop R (PB1 R s)
def PB3 (R X : Reg) (s : St) : St := gMvA Reg.TMP X (PB2 R s)
def okBlk (R : Reg) (s : St) : Prop := topP R (isA (tk BSym.sep)) (hd (PB1 R s)) = true

lemma gs_stBlk (R X : Reg) (hR : safe R := by decide) (hRB : R ≠ Reg.BAD := by decide)
    (hRT : R ≠ Reg.TMP := by decide) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : Gs (stBlk R X) (fun s => gMvA Reg.TMP X (gPopIf R
      (isA (tk BSym.sep)) (gMvP R Reg.TMP isBitW s))) (PB3 R X) (okBlk R) := by
  have h := Gs.seq (gs_mvP R Reg.TMP isBitW hRT hR (by decide) hRB (by decide)) <|
    Gs.seq (gs_popIf R (isA (tk BSym.sep)) hR hRB) <|
      gs_mvA Reg.TMP X hX2 (by decide) hX (by decide) hX'
  refine Gs.congr (p := stBlk R X) h (fun s _ => rfl) (fun s _ => ?_) (fun s => ?_)
  · simp [okBlk, PB1]
  · simp [PB3, PB2, PB1, gMvA, gMvP, gPop, upd_apply, hX'.symm, hRB.symm]

def bPopBlk (R X : Reg) (hR : safe R := by decide) (hRB : R ≠ Reg.BAD := by decide)
    (hRT : R ≠ Reg.TMP := by decide) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : GB := GB.ofGs (gs_stBlk R X hR hRB hRT hX hX' hX2)

lemma popBlk_calc (R X : Reg) (s : St) (bl : List Bool) (rest : List Al)
    (hW : s R = bl.map tkb ++ tk BSym.sep :: rest) (hT : s Reg.TMP = [])
    (hXW : X ≠ R) (hXT : X ≠ Reg.TMP) (hRT : R ≠ Reg.TMP) :
    okBlk R s ∧ ∀ r, PB3 R X s r = if r = X then bl.map tkb ++ s X else if r = R then rest
      else if r = Reg.TMP then [] else s r := by
  have hc := tw_calc bl rest
  have hB1 : PB1 R s = upd (upd s R (tk BSym.sep :: rest)) Reg.TMP (bl.map tkb).reverse := by
    unfold PB1 gMvP
    rw [hW, hc.1, hc.2]; simp [hT]
  constructor
  · unfold okBlk; rw [hB1]; simp [topP, hd, upd_apply, isA, hRT]
  · intro r
    unfold PB3 PB2 gMvA gPop
    rw [hB1]
    by_cases h1 : r = X <;> by_cases h2 : r = R <;> by_cases h3 : r = Reg.TMP <;>
      simp [upd_apply, h1, h2, h3, hXW, hXT, hXW.symm, hXT.symm, hRT, hRT.symm]

end Stk

end Sec_Ap1

section Sec_Ver57
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
section PSJ
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma loop_execJ2 {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {d : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSI Inv p g d)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) + μ (g s) ≤ S s + μ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, Inv s → ∃ n, n ≤ (μ s + 1) * ((S s + μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s hs ht
    obtain ⟨n1, hn1, e1⟩ := hp s hs
    have hgs := hinv s hs ht
    by_cases ht2 : t (hd (g s)) = true
    · obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl hgs
      refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
      · rw [← hm]
        have hg := hgrow s hs ht ht2
        have hY : S (g s) + μ (g s) + 2 ≤ S s + μ s + 2 := by omega
        have h1 : n1 ≤ (S s + μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h2 : n2 ≤ (μ (g s) + 1) * ((S s + μ s + 2) ^ d + 3) :=
          le_trans hn2 (Nat.mul_le_mul_left _ (by
            have := Nat.pow_le_pow_left hY d; omega))
        have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
        have h4 : (μ (g s) + 1 + 1) * ((S s + μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        nlinarith
      · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
    · have ht2' : t (hd (g s)) = false := by simpa using ht2
      refine ⟨1 + n1 + 1 + 1, ?_, ?_⟩
      · rw [← hm]
        have h1 : n1 ≤ (S s + μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h3 : 2 ≤ μ s + 1 := by omega
        have h4 : 2 * ((S s + μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        omega
      · have e3 : (StackProg.loop t p).Exec (g s) (G (g s)) 1 := by
          rw [hstop (g s) hgs ht2']; exact StackProg.Exec.loopFalse ht2'
        rw [hG]
        exact StackProg.Exec.loopTrue ht e1 e3
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s hs ht']; exact StackProg.Exec.loopFalse ht'

lemma PSp.loopJ2 {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) + μ (g s) ≤ S s + μ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨2 * d + 3, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execJ2 t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + μ s + 2 ≤ X ^ 2 := by nlinarith
  have a2 : (S s + μ s + 2) ^ d ≤ X ^ (2 * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ (2 * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ (2 * d + 3) := by rw [hZ]; ring

end PSJ
end Stk

end Sec_Ver57
section Sec_Ap8x
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
section PSJ3
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma PSp.loopJ3 {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ 3 * S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) + μ (g s) ≤ S s + μ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨2 * d + 4, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execJ2 t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + μ s + 2 ≤ X ^ 2 := by nlinarith
  have a2 : (S s + μ s + 2) ^ d ≤ X ^ (2 * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ (2 * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X ^ 2 := by nlinarith
  calc n ≤ (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := hn
    _ ≤ X ^ 2 * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ (2 * d + 4) := by rw [hZ]; ring

end PSJ3
end Stk

end Sec_Ap8x



section Sec_flag
namespace Stk
def flag (b : Bool) : List Al := if b then [mk] else []

@[simp] lemma bCopy_ok (a b : Reg) (h1 : a ≠ b) (h2 : safe a) (h3 : safe b) (h4 : b ≠ Reg.BAD) (s : St) :
    (bCopy a b h1 h2 h3 h4).ok s = True := rfl
@[simp] lemma bCopy_T (a b : Reg) (h1 : a ≠ b) (h2 : safe a) (h3 : safe b) (h4 : b ≠ Reg.BAD) (s : St) :
    (bCopy a b h1 h2 h3 h4).T s = gCopy a b s := rfl
@[simp] lemma bClear_ok (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bClear a h1 h2).ok s = True := rfl
@[simp] lemma bClear_T (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bClear a h1 h2).T s = gClear a s := rfl
@[simp] lemma bPop_ok (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bPop a h1 h2).ok s = True := rfl
@[simp] lemma bPop_T (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bPop a h1 h2).T s = gPop a s := rfl
@[simp] lemma bBad_ok (t : (Reg → Option Al) → Bool) (s : St) :
    (bBad t).ok s = (t (hd s) = false) := rfl
@[simp] lemma bBad_T (t : (Reg → Option Al) → Bool) (s : St) : (bBad t).T s = s := rfl
@[simp] lemma seq_ok (a b : GB) (s : St) : (a.seq b).ok s = (a.ok s ∧ b.ok (a.T s)) := rfl
@[simp] lemma seq_T (a b : GB) (s : St) : (a.seq b).T s = b.T (a.T s) := rfl
@[simp] lemma cmpL_ok (g : Bool) (s : St) : (cmpL g).ok s = True := by
  cases g <;> simp [cmpL, bPush, skipB, GB.ofGs, bCmp]
end Stk
end Sec_flag
section Sec_Ap11
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma cmpL_gen (g : Bool) (s : St) (mb kb : List Bool) (hmb : s Reg.MB = mb.map tkb)
    (hkb : s Reg.KB = kb.map tkb) :
    (cmpL g).T s = upd (upd (upd s Reg.MB []) Reg.KB []) Reg.H
      (flag (decide (val kb < val mb ∨ (val mb = val kb ∧ g = true)))) := by
  have hg : ∀ s' : St, s' Reg.MB = mb.map tkb → s' Reg.KB = kb.map tkb →
      (upd (cmpF s') Reg.BAD (s' Reg.BAD)) = upd (upd (upd s' Reg.MB []) Reg.KB []) Reg.H
      (flag (decide (val kb < val mb ∨ (val mb = val kb ∧ (decide (s' Reg.H ≠ [])) = true)))) := by
    intro s' h1 h2
    unfold cmpF
    rw [h1, h2, cf_val]
    funext r
    by_cases hr : r = Reg.BAD
    · subst hr; simp [upd_apply]
    · simp [upd_apply, hr, flag]
  have hH : ∀ (s' : St) (x : List Al), upd (upd (upd (upd s' Reg.H []) Reg.MB []) Reg.KB []) Reg.H x = upd (upd (upd s' Reg.MB []) Reg.KB []) Reg.H x := by
    intro s' x; funext r; by_cases hr : r = Reg.H <;> simp [upd_apply, hr]
  cases g
  · have := hg (upd s Reg.H []) (by simp [upd_apply, hmb]) (by simp [upd_apply, hkb])
    simp only [cmpL, GB.seq, bClear, skipB, GB.ofGs, bCmp, gClear, Bool.false_eq_true, if_false, id] at this ⊢
    rw [this]
    simp [hH, upd_apply]
  · have := hg (upd (upd s Reg.H []) Reg.H (mk :: upd s Reg.H [] Reg.H)) (by simp [upd_apply, hmb]) (by simp [upd_apply, hkb])
    simp only [cmpL, GB.seq, bClear, bPush, GB.ofGs, bCmp, gClear, gPush, if_true, id] at this ⊢
    rw [this]
    funext r
    by_cases hr : r = Reg.H <;> by_cases hb : r = Reg.MB <;> by_cases hk : r = Reg.KB <;> simp [upd_apply, hr, hb, hk]

end Stk

end Sec_Ap11

section Sec_Ap13
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def LtH (X Y : Reg) : Prop := X ≠ Reg.KB ∧ X ≠ Reg.MB ∧ Y ≠ Reg.KB ∧ Y ≠ Reg.MB ∧ safe X ∧ safe Y

instance (X Y : Reg) : Decidable (LtH X Y) := by unfold LtH; infer_instance

def cmpLt (X Y : Reg) (h : LtH X Y := by decide) : GB :=
  ((bCopy X Reg.KB h.1 h.2.2.2.2.1 (by decide) (by decide)).seq
    (bCopy Y Reg.MB h.2.2.2.1 h.2.2.2.2.2 (by decide) (by decide))).seq (cmpL false)

lemma cmpLt_pre (X Y : Reg) (h : LtH X Y) (s : St) : (cmpLt X Y h).pre s := by
  refine seq_pre_all (seq_pre_all (fun _ => trivial) (fun _ => trivial)) (fun s' => cmpL_pre false s') s

lemma cmpLt_spec (X Y : Reg) (h : LtH X Y) (s : St) (xs ys : List Bool)
    (hX : s X = xs.map tkb) (hY : s Y = ys.map tkb) (hM : s Reg.MB = []) (hK : s Reg.KB = []) :
    (cmpLt X Y h).ok s ∧ (cmpLt X Y h).T s = upd s Reg.H (flag (decide (val xs < val ys))) := by
  refine ⟨by simp [cmpLt], ?_⟩
  have hXK : X ≠ Reg.KB := h.1
  have hYK : Y ≠ Reg.KB := h.2.2.1
  have hYM : Y ≠ Reg.MB := h.2.2.2.1
  have e0 : (cmpLt X Y h).T s = (cmpL false).T (gCopy Y Reg.MB (gCopy X Reg.KB s)) := rfl
  have e1 : (gCopy Y Reg.MB (gCopy X Reg.KB s)) Reg.KB = xs.map tkb := by
    simp [gCopy, upd_apply, hX, hK]
  have e2 : (gCopy Y Reg.MB (gCopy X Reg.KB s)) Reg.MB = ys.map tkb := by
    simp [gCopy, upd_apply, hY, hM, hYK]
  rw [e0, cmpL_gen false _ ys xs e2 e1]
  have e3 : decide (val xs < val ys ∨ val ys = val xs ∧ false = true) = decide (val xs < val ys) := by simp
  rw [e3]
  funext r
  by_cases hH : r = Reg.H
  · subst hH; simp [upd_apply]
  by_cases hm : r = Reg.MB
  · subst hm; simp [upd_apply, hM]
  by_cases hk : r = Reg.KB
  · subst hk; simp [upd_apply, hK]
  simp [upd_apply, gCopy, hH, hm, hk]

end Stk

end Sec_Ap13

end Sec_RB

section Sec_RPV1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
section PSC
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma loop_execC {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {d : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ Φ : (K → List A) → ℕ)
    (hp : PSI Inv p g d)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hΦ : ∀ s, Inv s → t (hd s) = true → S s + μ s ≤ Φ s)
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → Φ (g s) ≤ Φ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, Inv s → ∃ n, n ≤ (μ s + 1) * ((Φ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases ht : t (hd s) = true
  · have hΦs := hΦ s hs ht
    obtain ⟨hlt, hG⟩ := hstep s hs ht
    obtain ⟨n1, hn1, e1⟩ := hp s hs
    have hgs := hinv s hs ht
    have h1 : n1 ≤ (Φ s + 2) ^ d :=
      le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
    by_cases ht2 : t (hd (g s)) = true
    · obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl hgs
      refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
      · rw [← hm]
        have hg := hgrow s hs ht ht2
        have hY : Φ (g s) + 2 ≤ Φ s + 2 := by omega
        have h2 : n2 ≤ (μ (g s) + 1) * ((Φ s + 2) ^ d + 3) :=
          le_trans hn2 (Nat.mul_le_mul_left _ (by
            have := Nat.pow_le_pow_left hY d; omega))
        have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
        have h4 : (μ (g s) + 1 + 1) * ((Φ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((Φ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        nlinarith
      · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
    · have ht2' : t (hd (g s)) = false := by simpa using ht2
      refine ⟨1 + n1 + 1 + 1, ?_, ?_⟩
      · rw [← hm]
        have h3 : 2 ≤ μ s + 1 := by omega
        have h4 : 2 * ((Φ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((Φ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        omega
      · have e3 : (StackProg.loop t p).Exec (g s) (G (g s)) 1 := by
          rw [hstop (g s) hgs ht2']; exact StackProg.Exec.loopFalse ht2'
        rw [hG]
        exact StackProg.Exec.loopTrue ht e1 e3
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (Φ s + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s hs ht']; exact StackProg.Exec.loopFalse ht'

lemma PSp.loopC {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ Φ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ 3 * S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hΦ : ∀ s, Inv s → t (hd s) = true → S s + μ s ≤ Φ s)
    (hΦ0 : ∀ s, Inv s → t (hd s) = true → Φ s ≤ 4 * S s + 6)
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → Φ (g s) ≤ Φ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨3 * d + 4, fun s hs => ?_⟩
  by_cases hT : t (hd s) = true
  swap
  · have hT' : t (hd s) = false := by simpa using hT
    refine ⟨1, ?_, ?_⟩
    · have h2 : 2 ≤ S s + 2 := by omega
      calc 1 ≤ S s + 2 := by omega
        _ ≤ (S s + 2) ^ (3 * d + 4) := by
          calc S s + 2 = (S s + 2) ^ 1 := by simp
            _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    · rw [hstop s hs hT']; exact StackProg.Exec.loopFalse hT'
  obtain ⟨n, hn, e⟩ := loop_execC t G μ Φ hp hinv hΦ hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have hF := hΦ0 s hs hT
  have a1 : Φ s + 2 ≤ X ^ 3 := by
    have h4 : 4 ≤ X ^ 2 := by nlinarith
    have : X ^ 3 = X * X ^ 2 := by ring
    nlinarith
  have a2 : (Φ s + 2) ^ d ≤ X ^ (3 * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ (3 * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (Φ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X ^ 2 := by nlinarith
  calc n ≤ (μ s + 1) * ((Φ s + 2) ^ d + 3) := hn
    _ ≤ X ^ 2 * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ (3 * d + 4) := by rw [hZ]; ring

end PSC
end Stk

end Sec_RPV1

section Sec_RPV2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

section Fold
variable {Y ι : Type}

def EfR (LR : Reg) (E0 : Y → St) (y : Y) (yv : List Al) : St := upd (E0 y) LR yv

def ltR (LR : Reg) : (Reg → Option Al) → Bool := fun h => (h LR).isSome && (h Reg.BAD).isNone

def muR (LR : Reg) (s : St) : ℕ := if s Reg.BAD = [] then 3 * (s LR).length else 0

def PhiR (LR : Reg) (pot : St → ℕ) (s : St) : ℕ := pot (upd s LR []) + 4 * (s LR).length

def JR (LR : Reg) (Vv : List Al → Prop) (E0 : Y → St) (s : St) : Prop :=
  Gi s ∧ (s Reg.BAD ≠ [] ∨ ∃ y yv, Vv yv ∧ s = EfR LR E0 y yv)

def foldOK (okf : Y → ι → Prop) (f : Y → ι → Y) : Y → List ι → Prop
  | _, [] => True
  | y, p :: l => okf y p ∧ foldOK okf f (f y p) l

def encs (enc : ι → List Al) (l : List ι) : List Al := l.flatMap enc

structure FoldH (LR : Reg) (Vv : List Al → Prop) (enc : ι → List Al) (body : GB) (E0 : Y → St)
    (okf : Y → ι → Prop) (f : Y → ι → Y) (pot : St → ℕ) : Prop where
  lrB : LR ≠ Reg.BAD
  lrC : LR ≠ Reg.C
  lrR : LR ≠ Reg.RC
  gi : ∀ y, Gi (E0 y)
  bad : ∀ y, E0 y Reg.BAD = []
  lr0 : ∀ y, E0 y LR = []
  pre : ∀ s, body.pre s
  encne : ∀ p, enc p ≠ []
  vrest : ∀ p rest, Vv (enc p ++ rest) → Vv rest
  dec : ∀ y yv, Vv yv → yv ≠ [] → (∀ p rest, yv ≠ enc p ++ rest) → ¬ body.ok (EfR LR E0 y yv)
  stepO : ∀ y p rest, Vv (enc p ++ rest) → (body.ok (EfR LR E0 y (enc p ++ rest)) ↔ okf y p)
  stepT : ∀ y p rest, Vv (enc p ++ rest) → okf y p →
    body.T (EfR LR E0 y (enc p ++ rest)) = EfR LR E0 (f y p) rest
  potS : ∀ y, S (E0 y) ≤ pot (E0 y)
  potG : ∀ y p, okf y p → pot (E0 (f y p)) ≤ pot (E0 y) + 4 * (enc p).length
  potL : ∀ y, pot (E0 y) ≤ 4 * S (E0 y) + 6

variable {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB} {E0 : Y → St}
  {okf : Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ}

lemma ltR_iff (s : St) : ltR LR (hd s) = true ↔ s LR ≠ [] ∧ s Reg.BAD = [] := by
  unfold ltR hd
  cases h1 : s LR <;> cases h2 : s Reg.BAD <;> simp

lemma EfR_LR (y : Y) (yv : List Al) : EfR LR E0 y yv LR = yv := by simp [EfR, upd_apply]

lemma EfR_BAD (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (yv : List Al) :
    EfR LR E0 y yv Reg.BAD = [] := by
  simp [EfR, upd_apply, h.bad y, h.lrB.symm]

lemma EfR_Gi (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (yv : List Al) :
    Gi (EfR LR E0 y yv) := by
  have := h.gi y
  refine ⟨?_, ?_⟩ <;> simp [EfR, upd_apply, this.1, this.2, h.lrC.symm, h.lrR.symm]

lemma S_EfR (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (yv : List Al) :
    S (EfR LR E0 y yv) = S (E0 y) + yv.length := by
  have := S_upd (E0 y) LR yv
  rw [h.lr0 y] at this
  simp only [List.length_nil] at this
  unfold EfR; omega

lemma EfR_clear (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (yv : List Al) :
    upd (EfR LR E0 y yv) LR [] = E0 y := by
  funext r
  by_cases hr : r = LR
  · subst hr; simp [upd_apply, h.lr0 y]
  · simp [EfR, upd_apply, hr]

lemma PhiR_EfR (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (yv : List Al) :
    PhiR LR pot (EfR LR E0 y yv) = pot (E0 y) + 4 * yv.length := by
  simp [PhiR, EfR_clear h, EfR_LR]

lemma muR_EfR (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (yv : List Al) :
    muR LR (EfR LR E0 y yv) = 3 * yv.length := by
  simp [muR, EfR_BAD h, EfR_LR]

/-- one-step behaviour of the body on a state with non-empty register content -/
lemma fold_step (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (yv : List Al) (hv : Vv yv)
    (hne : yv ≠ []) :
    body.g (EfR LR E0 y yv) Reg.BAD ≠ [] ∨
      ∃ p rest, yv = enc p ++ rest ∧ Vv rest ∧ okf y p ∧
        body.g (EfR LR E0 y yv) = EfR LR E0 (f y p) rest := by
  have hh := body.h.2.2.2 (EfR LR E0 y yv) (EfR_Gi h _ _) (h.pre _) (EfR_BAD h _ _)
  by_cases hd : ∃ p rest, yv = enc p ++ rest
  · obtain ⟨p, rest, rfl⟩ := hd
    by_cases hk : okf y p
    · right
      have ho : body.ok (EfR LR E0 y (enc p ++ rest)) := (h.stepO y p rest hv).2 hk
      exact ⟨p, rest, rfl, h.vrest p rest hv, hk, by rw [hh.2 ho]; exact h.stepT y p rest hv hk⟩
    · left
      intro hb
      exact hk ((h.stepO y p rest hv).1 (hh.1.1 hb))
  · left
    intro hb
    push_neg at hd
    exact h.dec y yv hv hne hd (hh.1.1 hb)

lemma JR_true (h : FoldH LR Vv enc body E0 okf f pot) (s : St) (hs : JR LR Vv E0 s)
    (ht : ltR LR (hd s) = true) : ∃ y yv, Vv yv ∧ yv ≠ [] ∧ s = EfR LR E0 y yv := by
  rw [ltR_iff] at ht
  rcases hs.2 with h2 | ⟨y, yv, hv, rfl⟩
  · exact absurd ht.2 h2
  · exact ⟨y, yv, hv, by simpa [EfR_LR] using ht.1, rfl⟩

lemma fold_hinv (h : FoldH LR Vv enc body E0 okf f pot) (s : St) (hs : JR LR Vv E0 s)
    (ht : ltR LR (hd s) = true) : JR LR Vv E0 (body.g s) := by
  refine ⟨body.h.1.2 s hs.1, ?_⟩
  obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true h s hs ht
  rcases fold_step h y yv hv hne with hb | ⟨p, rest, _, hr, _, he⟩
  · exact Or.inl hb
  · rw [he]; exact Or.inr ⟨_, _, hr, rfl⟩

lemma fold_hdec (h : FoldH LR Vv enc body E0 okf f pot) (s : St) (hs : JR LR Vv E0 s)
    (ht : ltR LR (hd s) = true) : muR LR (body.g s) < muR LR s := by
  obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true h s hs ht
  rw [muR_EfR h]
  have hl : 0 < yv.length := List.length_pos_iff.2 hne
  rcases fold_step h y yv hv hne with hb | ⟨p, rest, he, hr, _, hg⟩
  · simp [muR, hb]; omega
  · rw [hg, muR_EfR h]
    have := h.encne p
    have h1 : 0 < (enc p).length := List.length_pos_iff.2 this
    rw [he]; simp only [List.length_append]; omega

lemma fold_PSp (h : FoldH LR Vv enc body E0 okf f pot) :
    PSp (JR LR Vv E0) (.loop (ltR LR) body.p) (lrun (ltR LR) body.g (muR LR)) := by
  refine PSp.loopC (ltR LR) (lrun (ltR LR) body.g (muR LR)) (muR LR) (PhiR LR pot)
    (PSp.weaken body.h.1.1 (fun s hs => hs.1)) ?_ (fold_hinv h) ?_ ?_ ?_
    (fun s _ ht => lrun_false _ _ _ s ht)
    (fun s hs ht => ⟨fold_hdec h s hs ht, lrun_true (JR LR Vv E0) _ _ _ (fold_hinv h) (fold_hdec h) s hs ht⟩)
  · intro s
    unfold muR; split_ifs
    · have := len_le_S s LR; omega
    · exact Nat.zero_le _
  · intro s hs ht
    obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true h s hs ht
    rw [PhiR_EfR h, muR_EfR h, S_EfR h]
    have := h.potS y; omega
  · intro s hs ht
    obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true h s hs ht
    rw [PhiR_EfR h, S_EfR h]
    have := h.potL y; omega
  · intro s hs ht ht2
    obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true h s hs ht
    rcases fold_step h y yv hv hne with hb | ⟨p, rest, he, hr, hk, hg⟩
    · rw [ltR_iff] at ht2; exact absurd ht2.2 hb
    · rw [hg, PhiR_EfR h, PhiR_EfR h, he]
      have := h.potG y p hk
      simp only [List.length_append]; omega

lemma lrun_keep (h : FoldH LR Vv enc body E0 okf f pot) (s : St) (hs : JR LR Vv E0 s) :
    Gi (lrun (ltR LR) body.g (muR LR) s) ∧
      (s Reg.BAD ≠ [] → lrun (ltR LR) body.g (muR LR) s Reg.BAD ≠ []) := by
  have := lrun_rel (JR LR Vv E0) (ltR LR) body.g (muR LR) (fold_hinv h) (fold_hdec h)
    (fun s s' => Gi s' ∧ (s Reg.BAD ≠ [] → s' Reg.BAD ≠ []))
    (fun s hs _ => ⟨hs.1, id⟩)
    (fun s hs ht ih => ⟨ih.1, fun hb => ih.2 (body.h.2.1 s hb)⟩) s hs
  exact this

lemma fold_gE (h : FoldH LR Vv enc body E0 okf f pot) (y : Y) (p : ι) (rest : List Al)
    (hv : Vv (enc p ++ rest)) (hk : okf y p) :
    body.g (EfR LR E0 y (enc p ++ rest)) = EfR LR E0 (f y p) rest := by
  have hh := body.h.2.2.2 (EfR LR E0 y (enc p ++ rest)) (EfR_Gi h _ _) (h.pre _) (EfR_BAD h _ _)
  rw [hh.2 ((h.stepO y p rest hv).2 hk)]; exact h.stepT y p rest hv hk

lemma fold_complete (h : FoldH LR Vv enc body E0 okf f pot) :
    ∀ (l : List ι) (y : Y), Vv (encs enc l) → foldOK okf f y l →
      lrun (ltR LR) body.g (muR LR) (EfR LR E0 y (encs enc l)) = EfR LR E0 (l.foldl f y) [] := by
  intro l
  induction l with
  | nil =>
    intro y _ _
    apply lrun_false
    rw [← Bool.not_eq_true, ltR_iff]; simp [EfR_LR, encs]
  | cons p l ih =>
    intro y hv hk
    have e : encs enc (p :: l) = enc p ++ encs enc l := by simp [encs]
    rw [e] at hv ⊢
    have hj : JR LR Vv E0 (EfR LR E0 y (enc p ++ encs enc l)) :=
      ⟨EfR_Gi h _ _, Or.inr ⟨y, _, hv, rfl⟩⟩
    have ht : ltR LR (hd (EfR LR E0 y (enc p ++ encs enc l))) = true := by
      rw [ltR_iff]
      exact ⟨by simp [EfR_LR, h.encne p], EfR_BAD h _ _⟩
    rw [lrun_true (JR LR Vv E0) _ _ _ (fold_hinv h) (fold_hdec h) _ hj ht,
      fold_gE h y p _ hv hk.1, ih (f y p) (h.vrest p _ hv) hk.2]
    rfl

lemma fold_sound (h : FoldH LR Vv enc body E0 okf f pot) :
    ∀ (n : ℕ) (yv : List Al) (y : Y), yv.length ≤ n → Vv yv →
      lrun (ltR LR) body.g (muR LR) (EfR LR E0 y yv) Reg.BAD = [] →
      ∃ l, yv = encs enc l ∧ foldOK okf f y l := by
  intro n
  induction n with
  | zero =>
    intro yv y hl _ _
    have : yv = [] := List.length_eq_zero_iff.1 (by omega)
    exact ⟨[], by simp [this, encs], trivial⟩
  | succ n ih =>
    intro yv y hl hv hb
    by_cases hne : yv = []
    · exact ⟨[], by simp [hne, encs], trivial⟩
    · have hj : JR LR Vv E0 (EfR LR E0 y yv) := ⟨EfR_Gi h _ _, Or.inr ⟨y, yv, hv, rfl⟩⟩
      have ht : ltR LR (hd (EfR LR E0 y yv)) = true := by
        rw [ltR_iff]; exact ⟨by simpa [EfR_LR] using hne, EfR_BAD h _ _⟩
      rw [lrun_true (JR LR Vv E0) _ _ _ (fold_hinv h) (fold_hdec h) _ hj ht] at hb
      rcases fold_step h y yv hv hne with hbad | ⟨p, rest, he, hr, hk, hg⟩
      · exact absurd hb (((lrun_keep h _ (fold_hinv h _ hj ht)).2) hbad)
      · rw [hg] at hb
        have hl2 : rest.length ≤ n := by
          have := h.encne p
          have h1 : 0 < (enc p).length := List.length_pos_iff.2 this
          rw [he] at hl; simp only [List.length_append] at hl; omega
        obtain ⟨l, hl', hk'⟩ := ih rest (f y p) hl2 hr hb
        exact ⟨p :: l, by simp [encs, he, hl'] , hk, hk'⟩

end Fold
end Stk

end Sec_RPV2

section Sec_RPV3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def canon (bl : List Bool) : Prop := bl.getLast? = some true ∨ bl = []
instance (bl : List Bool) : Decidable (canon bl) := by unfold canon; infer_instance

def bitsOf (ts : List Al) : List Bool := ts.map (fun a => decide (a = tkb true))

def popNum (l : List Al) : Option (List Bool × List Al) :=
  match l.dropWhile isBitW with
  | a :: rest => if a = tk BSym.sep ∧ canon (bitsOf (l.takeWhile isBitW)) then
      some (bitsOf (l.takeWhile isBitW), rest) else none
  | [] => none

lemma bitsOf_map (bl : List Bool) : bitsOf (bl.map tkb) = bl := by
  induction bl with
  | nil => rfl
  | cons b bl ih => cases b <;> simp [bitsOf, tkb, tk] at ih ⊢ <;> simp [ih]

lemma popNum_enc (bl : List Bool) (rest : List Al) (h : canon bl) :
    popNum (bl.map tkb ++ tk BSym.sep :: rest) = some (bl, rest) := by
  have hc := tw_calc bl rest
  unfold popNum
  rw [hc.2, hc.1, bitsOf_map]
  simp [h]

lemma map_of_isBit (ts : List Al) (h : ∀ a ∈ ts, isBitW a = true) : (bitsOf ts).map tkb = ts := by
  induction ts with
  | nil => rfl
  | cons a ts ih =>
    have ha := h a (by simp)
    have h2 : (bitsOf ts).map tkb = ts := ih (fun b hb => h b (by simp [hb]))
    have h3 : tkb (decide (a = tkb true)) = a := by
      simp only [isBitW, decide_eq_true_eq] at ha
      rcases ha with rfl | rfl <;> simp [tkb, tk]
    simp [bitsOf] at h2 ⊢
    exact ⟨h3, h2⟩

lemma popNum_some (l : List Al) (bl : List Bool) (rest : List Al)
    (h : popNum l = some (bl, rest)) : l = bl.map tkb ++ tk BSym.sep :: rest ∧ canon bl := by
  unfold popNum at h
  have hs := List.takeWhile_append_dropWhile (p := isBitW) (l := l)
  cases hd : l.dropWhile isBitW with
  | nil => simp [hd] at h
  | cons a r =>
    rw [hd] at h hs
    simp only at h
    by_cases hc : a = tk BSym.sep ∧ canon (bitsOf (l.takeWhile isBitW))
    · rw [if_pos hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hm := map_of_isBit (l.takeWhile isBitW) (fun x hx => by
        have := List.mem_takeWhile_imp hx; simpa using this)
      refine ⟨?_, hc.2⟩
      rw [hm, ← hc.1]; exact hs.symm
    · rw [if_neg hc] at h; simp at h


def bMvP (a b : Reg) (p : Al → Bool) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (ha' : a ≠ Reg.BAD := by decide) (hb' : b ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_mvP a b p hab ha hb ha' hb')
def bPopIf (r : Reg) (p : Al → Bool) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_popIf r p hr hr')

def stC (R X : Reg) (hR : safe R := by decide) (hRB : R ≠ Reg.BAD := by decide)
    (hRT : R ≠ Reg.TMP := by decide) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : GB :=
  (bMvP R Reg.TMP isBitW hRT hR (by decide) hRB (by decide)).seq <|
  (bPopIf R (isA (tk BSym.sep)) hR hRB).seq <|
  (bBad (topP Reg.TMP (isA (tkb false)))).seq <|
  (bMvA Reg.TMP X hX2 (by decide) hX (by decide) hX')

lemma stC_calc (R X : Reg) (hR : safe R) (hRB : R ≠ Reg.BAD) (hRT : R ≠ Reg.TMP)
    (hX : safe X) (hX' : X ≠ Reg.BAD) (hX2 : Reg.TMP ≠ X) (hXR : X ≠ R)
    (s : St) (bl : List Bool) (rest : List Al)
    (hW : s R = bl.map tkb ++ tk BSym.sep :: rest) (hT : s Reg.TMP = []) (hc : canon bl) :
    (stC R X hR hRB hRT hX hX' hX2).ok s ∧ ∀ r, (stC R X hR hRB hRT hX hX' hX2).T s r =
      if r = X then bl.map tkb ++ s X else if r = R then rest
      else if r = Reg.TMP then [] else s r := by
  have hcc := tw_calc bl rest
  have h1 : gMvP R Reg.TMP isBitW s = upd (upd s R (tk BSym.sep :: rest)) Reg.TMP (bl.map tkb).reverse := by
    unfold gMvP; rw [hW, hcc.1, hcc.2]; simp [hT]
  have h2 : gPop R (gMvP R Reg.TMP isBitW s) = upd (upd s R rest) Reg.TMP (bl.map tkb).reverse := by
    rw [h1]; unfold gPop; funext r; by_cases hr : r = R <;> by_cases ht : r = Reg.TMP <;>
      simp [upd_apply, hr, ht, hRT, hRT.symm]
  have hTop : topP Reg.TMP (isA (tkb false)) (hd (gPop R (gMvP R Reg.TMP isBitW s))) = false := by
    rw [h2]
    rcases hc with hc | hc
    · have hh : (bl.map tkb).reverse.head? = some (tkb true) := by
        rw [List.head?_reverse, List.getLast?_map]; simp [hc]
      cases hl : (bl.map tkb).reverse with
      | nil => rw [hl] at hh; simp at hh
      | cons a l =>
        rw [hl] at hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp [topP, hd, upd_apply, hRT.symm, hRT, isA, tkb, tk]
    · subst hc; simp [topP, hd, upd_apply, hRT.symm, hRT]
  have hpi : topP R (isA (tk BSym.sep)) (hd (gMvP R Reg.TMP isBitW s)) = true := by
    rw [h1]; simp [topP, hd, upd_apply, hRT, isA]
  have hbad : gBadIf (topP Reg.TMP (isA (tkb false))) (gPop R (gMvP R Reg.TMP isBitW s)) =
      gPop R (gMvP R Reg.TMP isBitW s) := by
    unfold gBadIf; rw [hTop]; simp
  have e1 : gPopIf R (isA (tk BSym.sep)) (gMvP R Reg.TMP isBitW s) = gPop R (gMvP R Reg.TMP isBitW s) := by
    unfold gPopIf; rw [if_pos hpi]; rw [h1]; unfold gPop; simp [upd_apply, hRT, hRT.symm, hRT]
  have hT3 : (stC R X hR hRB hRT hX hX' hX2).T s = gMvA Reg.TMP X (upd (upd s R rest) Reg.TMP (bl.map tkb).reverse) := by
    show gMvA Reg.TMP X (id (gPop R (gMvP R Reg.TMP isBitW s))) = _
    rw [h2]; rfl
  constructor
  · show True ∧ topP R (isA (tk BSym.sep)) (hd (gMvP R Reg.TMP isBitW s)) = true ∧ _
    refine ⟨trivial, hpi, ?_, trivial⟩
    exact hTop
  · intro r
    rw [hT3]
    unfold gMvA
    by_cases h1 : r = X <;> by_cases h2 : r = R <;> by_cases h3 : r = Reg.TMP <;>
      simp [upd_apply, h1, h2, h3, hXR, hX2, hRT, hRT.symm, hX2.symm, hXR.symm]

lemma stC_dec (R X : Reg) (hR : safe R) (hRB : R ≠ Reg.BAD) (hRT : R ≠ Reg.TMP)
    (hX : safe X) (hX' : X ≠ Reg.BAD) (hX2 : Reg.TMP ≠ X)
    (s : St) (hT : s Reg.TMP = []) (hok : (stC R X hR hRB hRT hX hX' hX2).ok s) :
    ∃ bl rest, popNum (s R) = some (bl, rest) := by
  obtain ⟨_, hpi, hbad, _⟩ := hok
  have hpi' : topP R (isA (tk BSym.sep)) (hd (gMvP R Reg.TMP isBitW s)) = true := hpi
  have hbad' : topP Reg.TMP (isA (tkb false)) (hd (gPop R (gMvP R Reg.TMP isBitW s))) = false := hbad
  have hR1 : (gMvP R Reg.TMP isBitW s) R = (s R).dropWhile isBitW := by
    simp [gMvP, upd_apply, hRT]
  have hT1 : (gPop R (gMvP R Reg.TMP isBitW s)) Reg.TMP = ((s R).takeWhile isBitW).reverse := by
    simp [gPop, gMvP, upd_apply, hRT, hRT.symm, hT]
  cases hd1 : (s R).dropWhile isBitW with
  | nil => simp [topP, hd, hR1, hd1] at hpi'
  | cons a rest =>
    have ha : a = tk BSym.sep := by simpa [topP, hd, hR1, hd1, isA] using hpi'
    have hcan : canon (bitsOf ((s R).takeWhile isBitW)) := by
      rcases hts : ((s R).takeWhile isBitW).reverse with _ | ⟨b, l⟩
      · right
        have : (s R).takeWhile isBitW = [] := by simpa using congrArg List.reverse hts
        simp [this, bitsOf]
      · left
        have hb : b ≠ tkb false := by simpa [topP, hd, isA, hT1, hts] using hbad'
        have hmem : b ∈ (s R).takeWhile isBitW := by
          have : b ∈ ((s R).takeWhile isBitW).reverse := by rw [hts]; simp
          simpa using this
        have hbit : isBitW b = true := by
          have := List.mem_takeWhile_imp hmem; simpa using this
        have hb1 : b = tkb true := by
          simp only [isBitW, decide_eq_true_eq] at hbit
          rcases hbit with h | h
          · exact absurd (by simpa [tkb, tk] using h) hb
          · simpa [tkb, tk] using h
        have hts' : (s R).takeWhile isBitW = l.reverse ++ [b] := by
          have := congrArg List.reverse hts
          simpa using this
        rw [hts']
        simp [bitsOf, hb1]
    refine ⟨bitsOf ((s R).takeWhile isBitW), rest, ?_⟩
    unfold popNum
    rw [hd1]
    simp [ha, hcan]

end Stk

end Sec_RPV3

section Sec_RPV4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

structure Z where
  w : List Al := []
  t : List Al := []
  nb : List Al := []
  kk : List Al := []
  wa : List Al := []
  vis : List Al := []
  acc : List Al := []
  prev : List Al := []
  first : List Al := []
  fst : List Al := []
  cn : List Al := []
  cn2 : List Al := []
  tx : List Al := []
  hx : List Al := []
  wx : List Al := []
  df : List Al := []
  rq : List Al := []
  tv : List Al := []
  h : List Al := []

def Zs (z : Z) : St := fun r =>
  match r with
  | Reg.W => z.w
  | Reg.T => z.t
  | Reg.N => z.nb
  | Reg.K => z.kk
  | Reg.KP => z.wa
  | Reg.NC => z.vis
  | Reg.PP => z.acc
  | Reg.TC => z.prev
  | Reg.T2 => z.first
  | Reg.K2 => z.fst
  | Reg.MR => z.cn
  | Reg.KR => z.cn2
  | Reg.TM => z.tx
  | Reg.TT => z.hx
  | Reg.TR => z.wx
  | Reg.WR => z.df
  | Reg.IN => z.rq
  | Reg.NC2 => z.tv
  | Reg.H => z.h
  | _ => []

@[simp] lemma Zs_w (z : Z) : Zs z Reg.W = z.w := rfl
@[simp] lemma Zs_t (z : Z) : Zs z Reg.T = z.t := rfl
@[simp] lemma Zs_nb (z : Z) : Zs z Reg.N = z.nb := rfl
@[simp] lemma Zs_kk (z : Z) : Zs z Reg.K = z.kk := rfl
@[simp] lemma Zs_wa (z : Z) : Zs z Reg.KP = z.wa := rfl
@[simp] lemma Zs_vis (z : Z) : Zs z Reg.NC = z.vis := rfl
@[simp] lemma Zs_acc (z : Z) : Zs z Reg.PP = z.acc := rfl
@[simp] lemma Zs_prev (z : Z) : Zs z Reg.TC = z.prev := rfl
@[simp] lemma Zs_first (z : Z) : Zs z Reg.T2 = z.first := rfl
@[simp] lemma Zs_fst (z : Z) : Zs z Reg.K2 = z.fst := rfl
@[simp] lemma Zs_cn (z : Z) : Zs z Reg.MR = z.cn := rfl
@[simp] lemma Zs_cn2 (z : Z) : Zs z Reg.KR = z.cn2 := rfl
@[simp] lemma Zs_tx (z : Z) : Zs z Reg.TM = z.tx := rfl
@[simp] lemma Zs_hx (z : Z) : Zs z Reg.TT = z.hx := rfl
@[simp] lemma Zs_wx (z : Z) : Zs z Reg.TR = z.wx := rfl
@[simp] lemma Zs_df (z : Z) : Zs z Reg.WR = z.df := rfl
@[simp] lemma Zs_rq (z : Z) : Zs z Reg.IN = z.rq := rfl
@[simp] lemma Zs_tv (z : Z) : Zs z Reg.NC2 = z.tv := rfl
@[simp] lemma Zs_h (z : Z) : Zs z Reg.H = z.h := rfl
@[simp] lemma Zs_TMP (z : Z) : Zs z Reg.TMP = [] := rfl
@[simp] lemma Zs_MB (z : Z) : Zs z Reg.MB = [] := rfl
@[simp] lemma Zs_NB (z : Z) : Zs z Reg.NB = [] := rfl
@[simp] lemma Zs_KB (z : Z) : Zs z Reg.KB = [] := rfl
@[simp] lemma Zs_U (z : Z) : Zs z Reg.U = [] := rfl
@[simp] lemma Zs_F (z : Z) : Zs z Reg.F = [] := rfl
@[simp] lemma Zs_HU (z : Z) : Zs z Reg.HU = [] := rfl
@[simp] lemma Zs_C (z : Z) : Zs z Reg.C = [] := rfl
@[simp] lemma Zs_RC (z : Z) : Zs z Reg.RC = [] := rfl
@[simp] lemma Zs_BAD (z : Z) : Zs z Reg.BAD = [] := rfl
@[simp] lemma Zs_OUT (z : Z) : Zs z Reg.OUT = [] := rfl
@[simp] lemma Zs_FP (z : Z) : Zs z Reg.FP = [] := rfl
@[simp] lemma Zs_LT (z : Z) : Zs z Reg.LT = [] := rfl
@[simp] lemma upd_Zs_w (z : Z) (l : List Al) : upd (Zs z) Reg.W l = Zs { z with w := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_t (z : Z) (l : List Al) : upd (Zs z) Reg.T l = Zs { z with t := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_nb (z : Z) (l : List Al) : upd (Zs z) Reg.N l = Zs { z with nb := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_kk (z : Z) (l : List Al) : upd (Zs z) Reg.K l = Zs { z with kk := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_wa (z : Z) (l : List Al) : upd (Zs z) Reg.KP l = Zs { z with wa := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_vis (z : Z) (l : List Al) : upd (Zs z) Reg.NC l = Zs { z with vis := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_acc (z : Z) (l : List Al) : upd (Zs z) Reg.PP l = Zs { z with acc := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_prev (z : Z) (l : List Al) : upd (Zs z) Reg.TC l = Zs { z with prev := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_first (z : Z) (l : List Al) : upd (Zs z) Reg.T2 l = Zs { z with first := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_fst (z : Z) (l : List Al) : upd (Zs z) Reg.K2 l = Zs { z with fst := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_cn (z : Z) (l : List Al) : upd (Zs z) Reg.MR l = Zs { z with cn := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_cn2 (z : Z) (l : List Al) : upd (Zs z) Reg.KR l = Zs { z with cn2 := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_tx (z : Z) (l : List Al) : upd (Zs z) Reg.TM l = Zs { z with tx := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_hx (z : Z) (l : List Al) : upd (Zs z) Reg.TT l = Zs { z with hx := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_wx (z : Z) (l : List Al) : upd (Zs z) Reg.TR l = Zs { z with wx := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_df (z : Z) (l : List Al) : upd (Zs z) Reg.WR l = Zs { z with df := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_rq (z : Z) (l : List Al) : upd (Zs z) Reg.IN l = Zs { z with rq := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_tv (z : Z) (l : List Al) : upd (Zs z) Reg.NC2 l = Zs { z with tv := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_h (z : Z) (l : List Al) : upd (Zs z) Reg.H l = Zs { z with h := l } := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]

@[simp] lemma upd_Zs_TMP_nil (z : Z) : upd (Zs z) Reg.TMP [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_MB_nil (z : Z) : upd (Zs z) Reg.MB [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_NB_nil (z : Z) : upd (Zs z) Reg.NB [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_KB_nil (z : Z) : upd (Zs z) Reg.KB [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_U_nil (z : Z) : upd (Zs z) Reg.U [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_F_nil (z : Z) : upd (Zs z) Reg.F [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_HU_nil (z : Z) : upd (Zs z) Reg.HU [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_C_nil (z : Z) : upd (Zs z) Reg.C [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_RC_nil (z : Z) : upd (Zs z) Reg.RC [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_BAD_nil (z : Z) : upd (Zs z) Reg.BAD [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_OUT_nil (z : Z) : upd (Zs z) Reg.OUT [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_FP_nil (z : Z) : upd (Zs z) Reg.FP [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]
@[simp] lemma upd_Zs_LT_nil (z : Z) : upd (Zs z) Reg.LT [] = Zs z := by
  funext r; cases r <;> first | rfl | simp [upd_apply, Zs]

lemma Zs_Gi (z : Z) : Gi (Zs z) := ⟨rfl, rfl⟩
lemma Zs_BAD_nil (z : Z) : (Zs z) Reg.BAD = [] := rfl

lemma S_Zs0 : S (Zs ({} : Z)) = 0 := by
  unfold S
  apply Finset.sum_eq_zero
  intro r _
  cases r <;> rfl

lemma S_Zs (z : Z) : S (Zs z) = z.w.length + z.t.length + z.nb.length + z.kk.length + z.wa.length +
    z.vis.length + z.acc.length + z.prev.length + z.first.length + z.fst.length + z.cn.length +
    z.cn2.length + z.tx.length + z.hx.length + z.wx.length + z.df.length + z.rq.length +
    z.tv.length + z.h.length := by
  have e0 : S (Zs ({ z with w := [] })) + (z).w.length = S (Zs (z)) := by
    have := S_upd (Zs (z)) Reg.W []
    rw [upd_Zs_w] at this
    simpa using this
  have e1 : S (Zs ({ { z with w := [] } with t := [] })) + ({ z with w := [] }).t.length = S (Zs ({ z with w := [] })) := by
    have := S_upd (Zs ({ z with w := [] })) Reg.T []
    rw [upd_Zs_t] at this
    simpa using this
  have e2 : S (Zs ({ { { z with w := [] } with t := [] } with nb := [] })) + ({ { z with w := [] } with t := [] }).nb.length = S (Zs ({ { z with w := [] } with t := [] })) := by
    have := S_upd (Zs ({ { z with w := [] } with t := [] })) Reg.N []
    rw [upd_Zs_nb] at this
    simpa using this
  have e3 : S (Zs ({ { { { z with w := [] } with t := [] } with nb := [] } with kk := [] })) + ({ { { z with w := [] } with t := [] } with nb := [] }).kk.length = S (Zs ({ { { z with w := [] } with t := [] } with nb := [] })) := by
    have := S_upd (Zs ({ { { z with w := [] } with t := [] } with nb := [] })) Reg.K []
    rw [upd_Zs_kk] at this
    simpa using this
  have e4 : S (Zs ({ { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] })) + ({ { { { z with w := [] } with t := [] } with nb := [] } with kk := [] }).wa.length = S (Zs ({ { { { z with w := [] } with t := [] } with nb := [] } with kk := [] })) := by
    have := S_upd (Zs ({ { { { z with w := [] } with t := [] } with nb := [] } with kk := [] })) Reg.KP []
    rw [upd_Zs_wa] at this
    simpa using this
  have e5 : S (Zs ({ { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] })) + ({ { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] }).vis.length = S (Zs ({ { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] })) := by
    have := S_upd (Zs ({ { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] })) Reg.NC []
    rw [upd_Zs_vis] at this
    simpa using this
  have e6 : S (Zs ({ { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] })) + ({ { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] }).acc.length = S (Zs ({ { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] })) := by
    have := S_upd (Zs ({ { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] })) Reg.PP []
    rw [upd_Zs_acc] at this
    simpa using this
  have e7 : S (Zs ({ { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] })) + ({ { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] }).prev.length = S (Zs ({ { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] })) := by
    have := S_upd (Zs ({ { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] })) Reg.TC []
    rw [upd_Zs_prev] at this
    simpa using this
  have e8 : S (Zs ({ { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] })) + ({ { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] }).first.length = S (Zs ({ { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] })) := by
    have := S_upd (Zs ({ { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] })) Reg.T2 []
    rw [upd_Zs_first] at this
    simpa using this
  have e9 : S (Zs ({ { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] })) + ({ { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] }).fst.length = S (Zs ({ { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] })) Reg.K2 []
    rw [upd_Zs_fst] at this
    simpa using this
  have e10 : S (Zs ({ { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] })) + ({ { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] }).cn.length = S (Zs ({ { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] })) Reg.MR []
    rw [upd_Zs_cn] at this
    simpa using this
  have e11 : S (Zs ({ { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] })) + ({ { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] }).cn2.length = S (Zs ({ { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] })) Reg.KR []
    rw [upd_Zs_cn2] at this
    simpa using this
  have e12 : S (Zs ({ { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] })) + ({ { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] }).tx.length = S (Zs ({ { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] })) Reg.TM []
    rw [upd_Zs_tx] at this
    simpa using this
  have e13 : S (Zs ({ { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] })) + ({ { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] }).hx.length = S (Zs ({ { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] })) Reg.TT []
    rw [upd_Zs_hx] at this
    simpa using this
  have e14 : S (Zs ({ { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] })) + ({ { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] }).wx.length = S (Zs ({ { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] })) Reg.TR []
    rw [upd_Zs_wx] at this
    simpa using this
  have e15 : S (Zs ({ { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] })) + ({ { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] }).df.length = S (Zs ({ { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] })) Reg.WR []
    rw [upd_Zs_df] at this
    simpa using this
  have e16 : S (Zs ({ { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] })) + ({ { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] }).rq.length = S (Zs ({ { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] })) Reg.IN []
    rw [upd_Zs_rq] at this
    simpa using this
  have e17 : S (Zs ({ { { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] } with tv := [] })) + ({ { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] }).tv.length = S (Zs ({ { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] })) Reg.NC2 []
    rw [upd_Zs_tv] at this
    simpa using this
  have e18 : S (Zs ({ { { { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] } with tv := [] } with h := [] })) + ({ { { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] } with tv := [] }).h.length = S (Zs ({ { { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] } with tv := [] })) := by
    have := S_upd (Zs ({ { { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] } with tv := [] })) Reg.H []
    rw [upd_Zs_h] at this
    simpa using this
  have e : Zs ({ { { { { { { { { { { { { { { { { { { z with w := [] } with t := [] } with nb := [] } with kk := [] } with wa := [] } with vis := [] } with acc := [] } with prev := [] } with first := [] } with fst := [] } with cn := [] } with cn2 := [] } with tx := [] } with hx := [] } with wx := [] } with df := [] } with rq := [] } with tv := [] } with h := [] }) = Zs ({} : Z) := rfl
  rw [e, S_Zs0] at e18
  simp at *
  omega



def isInr : Al → Bool | some (Sum.inr _) => true | _ => false

lemma inr_of_all {l : List Al} (h : ∀ a ∈ l, isInr a = true) : ∃ w : List BSym, l = w.map ty := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a r ih =>
    obtain ⟨t, ht⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    cases a with
    | none => simp [isInr] at ha
    | some v =>
      cases v with
      | inl b => simp [isInr] at ha
      | inr b => exact ⟨b :: t, by simp [ty, ht]⟩

-- block simp lemmas
@[simp] lemma bMvP_T (a b : Reg) (p : Al → Bool) (h1 h2 h3 h4 h5) (s : St) : (bMvP a b p h1 h2 h3 h4 h5).T s = gMvP a b p s := rfl
@[simp] lemma bMvP_ok (a b : Reg) (p : Al → Bool) (h1 h2 h3 h4 h5) (s : St) : (bMvP a b p h1 h2 h3 h4 h5).ok s = True := rfl
@[simp] lemma bMvA_T (a b : Reg) (h1 h2 h3 h4 h5) (s : St) : (bMvA a b h1 h2 h3 h4 h5).T s = gMvA a b s := rfl
@[simp] lemma bMvA_ok (a b : Reg) (h1 h2 h3 h4 h5) (s : St) : (bMvA a b h1 h2 h3 h4 h5).ok s = True := rfl
@[simp] lemma bPopIf_T (r : Reg) (p : Al → Bool) (h1 h2) (s : St) : (bPopIf r p h1 h2).T s = gPop r s := rfl
@[simp] lemma bPopIf_ok (r : Reg) (p : Al → Bool) (h1 h2) (s : St) : (bPopIf r p h1 h2).ok s = (topP r p (hd s) = true) := rfl
@[simp] lemma bPush_T (a : Reg) (x : Al) (h1 h2) (s : St) : (bPush a x h1 h2).T s = gPush a x s := rfl
@[simp] lemma bPush_ok (a : Reg) (x : Al) (h1 h2) (s : St) : (bPush a x h1 h2).ok s = True := rfl
@[simp] lemma bEq_T (X D : Reg) (h1 h2 h3 h4 h5 h6 h7 h8 h9) (s : St) : (bEq X D h1 h2 h3 h4 h5 h6 h7 h8 h9).T s = eqT X s := rfl
@[simp] lemma bEq_ok (X D : Reg) (h1 h2 h3 h4 h5 h6 h7 h8 h9) (s : St) :
    (bEq X D h1 h2 h3 h4 h5 h6 h7 h8 h9).ok s = (s X = (Nat.bits (s D).length).map tkb) := rfl

def stP0 : GB :=
  (bMvP Reg.IN Reg.WR isInl).seq <| (bPopIf Reg.IN (isA mk)).seq <| (bMvA Reg.WR Reg.W).seq <|
  (bMvP Reg.IN Reg.TR isInr).seq <| (bMvA Reg.TR Reg.T).seq <| bBad (topS Reg.IN)

lemma dw_map_tk (w : List BSym) : (w.map tk).dropWhile isInl = [] := by
  apply List.dropWhile_eq_nil_iff.mpr; intro x hx; simp at hx; obtain ⟨b, _, rfl⟩ := hx; rfl
lemma tw_map_tk (w : List BSym) : (w.map tk).takeWhile isInl = w.map tk := by
  apply List.takeWhile_eq_self_iff.mpr; intro x hx; simp at hx; obtain ⟨b, _, rfl⟩ := hx; rfl
lemma dw_map_ty (w : List BSym) : (w.map ty).dropWhile isInr = [] := by
  apply List.dropWhile_eq_nil_iff.mpr; intro x hx; simp at hx; obtain ⟨b, _, rfl⟩ := hx; rfl
lemma tw_map_ty (w : List BSym) : (w.map ty).takeWhile isInr = w.map ty := by
  apply List.takeWhile_eq_self_iff.mpr; intro x hx; simp at hx; obtain ⟨b, _, rfl⟩ := hx; rfl
lemma dw_mk (w : List BSym) (r : List Al) : (w.map tk ++ mk :: r).dropWhile isInl = mk :: r := by
  rw [List.dropWhile_append, dw_map_tk]; simp [isInl, mk]
lemma tw_mk (w : List BSym) (r : List Al) : (w.map tk ++ mk :: r).takeWhile isInl = w.map tk := by
  rw [List.takeWhile_append, tw_map_tk]; simp [isInl, mk, dw_map_tk]

lemma stP0_calc (w y : List BSym) :
    stP0.ok (Zs { rq := w.map tk ++ mk :: y.map ty }) ∧
    stP0.T (Zs { rq := w.map tk ++ mk :: y.map ty }) = Zs { w := w.map tk, t := y.map ty } := by
  simp [stP0, gMvP, gMvA, gPop, topP, topS, hd, dw_mk, tw_mk, dw_map_ty, tw_map_ty, isA]
  done

lemma stP0_dec (x : List Al) (h : stP0.ok (Zs { rq := x })) : ∃ w y : List BSym, x = w.map tk ++ mk :: y.map ty := by
  simp [stP0, gMvP, gMvA, gPop, topP, topS, hd, isA] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hx0, hw0⟩ := tw_split isInl x
  obtain ⟨w, hw⟩ := inl_of_all hw0
  generalize List.dropWhile isInl x = r1 at h1 h2 hx0
  cases r1 with
  | nil => simp at h1
  | cons c r2 =>
    simp only [List.head?_cons, decide_eq_true_eq] at h1
    have hc : c = mk := h1
    subst hc
    simp only [List.tail_cons] at h2
    obtain ⟨y, hy⟩ := inr_of_all h2
    exact ⟨w, y, by rw [hx0, hw, ← hy]⟩

-- STC_BEGIN

lemma stC_calc_w_nb (z : Z) (bl : List Bool) (rest : List Al)
    (hW : z.w = bl.map tkb ++ tk BSym.sep :: rest) (hc : canon bl) :
    (stC Reg.W Reg.N).ok (Zs z) ∧ (stC Reg.W Reg.N).T (Zs z) = Zs { z with w := rest, nb := bl.map tkb ++ z.nb } := by
  obtain ⟨h1, h2⟩ := stC_calc Reg.W Reg.N (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Zs z) bl rest hW rfl hc
  refine ⟨h1, ?_⟩
  funext r; rw [h2]; cases r <;> simp [Zs]

lemma stC_dec_w_nb (z : Z) (h : (stC Reg.W Reg.N).ok (Zs z)) :
    ∃ bl rest, popNum z.w = some (bl, rest) :=
  stC_dec Reg.W Reg.N (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Zs z) rfl h

lemma stC_calc_w_kk (z : Z) (bl : List Bool) (rest : List Al)
    (hW : z.w = bl.map tkb ++ tk BSym.sep :: rest) (hc : canon bl) :
    (stC Reg.W Reg.K).ok (Zs z) ∧ (stC Reg.W Reg.K).T (Zs z) = Zs { z with w := rest, kk := bl.map tkb ++ z.kk } := by
  obtain ⟨h1, h2⟩ := stC_calc Reg.W Reg.K (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Zs z) bl rest hW rfl hc
  refine ⟨h1, ?_⟩
  funext r; rw [h2]; cases r <;> simp [Zs]

lemma stC_dec_w_kk (z : Z) (h : (stC Reg.W Reg.K).ok (Zs z)) :
    ∃ bl rest, popNum z.w = some (bl, rest) :=
  stC_dec Reg.W Reg.K (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Zs z) rfl h

lemma stC_calc_w_tx (z : Z) (bl : List Bool) (rest : List Al)
    (hW : z.w = bl.map tkb ++ tk BSym.sep :: rest) (hc : canon bl) :
    (stC Reg.W Reg.TM).ok (Zs z) ∧ (stC Reg.W Reg.TM).T (Zs z) = Zs { z with w := rest, tx := bl.map tkb ++ z.tx } := by
  obtain ⟨h1, h2⟩ := stC_calc Reg.W Reg.TM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Zs z) bl rest hW rfl hc
  refine ⟨h1, ?_⟩
  funext r; rw [h2]; cases r <;> simp [Zs]

lemma stC_dec_w_tx (z : Z) (h : (stC Reg.W Reg.TM).ok (Zs z)) :
    ∃ bl rest, popNum z.w = some (bl, rest) :=
  stC_dec Reg.W Reg.TM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Zs z) rfl h

lemma stC_calc_w_hx (z : Z) (bl : List Bool) (rest : List Al)
    (hW : z.w = bl.map tkb ++ tk BSym.sep :: rest) (hc : canon bl) :
    (stC Reg.W Reg.TT).ok (Zs z) ∧ (stC Reg.W Reg.TT).T (Zs z) = Zs { z with w := rest, hx := bl.map tkb ++ z.hx } := by
  obtain ⟨h1, h2⟩ := stC_calc Reg.W Reg.TT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Zs z) bl rest hW rfl hc
  refine ⟨h1, ?_⟩
  funext r; rw [h2]; cases r <;> simp [Zs]

lemma stC_dec_w_hx (z : Z) (h : (stC Reg.W Reg.TT).ok (Zs z)) :
    ∃ bl rest, popNum z.w = some (bl, rest) :=
  stC_dec Reg.W Reg.TT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Zs z) rfl h

lemma stC_calc_w_wx (z : Z) (bl : List Bool) (rest : List Al)
    (hW : z.w = bl.map tkb ++ tk BSym.sep :: rest) (hc : canon bl) :
    (stC Reg.W Reg.TR).ok (Zs z) ∧ (stC Reg.W Reg.TR).T (Zs z) = Zs { z with w := rest, wx := bl.map tkb ++ z.wx } := by
  obtain ⟨h1, h2⟩ := stC_calc Reg.W Reg.TR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Zs z) bl rest hW rfl hc
  refine ⟨h1, ?_⟩
  funext r; rw [h2]; cases r <;> simp [Zs]

lemma stC_dec_w_wx (z : Z) (h : (stC Reg.W Reg.TR).ok (Zs z)) :
    ∃ bl rest, popNum z.w = some (bl, rest) :=
  stC_dec Reg.W Reg.TR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Zs z) rfl h

lemma stC_calc_w_df (z : Z) (bl : List Bool) (rest : List Al)
    (hW : z.w = bl.map tkb ++ tk BSym.sep :: rest) (hc : canon bl) :
    (stC Reg.W Reg.WR).ok (Zs z) ∧ (stC Reg.W Reg.WR).T (Zs z) = Zs { z with w := rest, df := bl.map tkb ++ z.df } := by
  obtain ⟨h1, h2⟩ := stC_calc Reg.W Reg.WR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Zs z) bl rest hW rfl hc
  refine ⟨h1, ?_⟩
  funext r; rw [h2]; cases r <;> simp [Zs]

lemma stC_dec_w_df (z : Z) (h : (stC Reg.W Reg.WR).ok (Zs z)) :
    ∃ bl rest, popNum z.w = some (bl, rest) :=
  stC_dec Reg.W Reg.WR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Zs z) rfl h
-- STC_END

lemma canon_bits (n : ℕ) : canon (Nat.bits n) := by
  by_cases h : n = 0
  · subst h; right; simp
  · left; exact getLast_bits n h

def stH : GB :=
  (stC Reg.W Reg.N).seq <| (stC Reg.W Reg.K).seq <|
  (bMvP Reg.T Reg.NC (isA (ty BSym.zero))).seq <| (bPopIf Reg.T (isA (ty BSym.sep))).seq <|
  (bEq Reg.K Reg.NC).seq <| (bCopy Reg.W Reg.KP).seq <| bClear Reg.W

lemma dw_rep (c d : Al) (hd : d ≠ c) (L : ℕ) (t : List Al) :
    (List.replicate L c ++ d :: t).dropWhile (isA c) = d :: t := by
  induction L with
  | zero => simp [isA, hd]
  | succ n ih => simpa [List.replicate_succ, isA] using ih
lemma tw_rep (c d : Al) (hd : d ≠ c) (L : ℕ) (t : List Al) :
    (List.replicate L c ++ d :: t).takeWhile (isA c) = List.replicate L c := by
  induction L with
  | zero => simp [isA, hd]
  | succ n ih => simp [List.replicate_succ, isA] at ih ⊢; exact ih

lemma stH_calc (n L : ℕ) (rest t' : List Al) :
    stH.ok (Zs { w := (Nat.bits n).map tkb ++ tk BSym.sep :: ((Nat.bits L).map tkb ++ tk BSym.sep :: rest),
                 t := List.replicate L (ty BSym.zero) ++ ty BSym.sep :: t' }) ∧
    stH.T (Zs { w := (Nat.bits n).map tkb ++ tk BSym.sep :: ((Nat.bits L).map tkb ++ tk BSym.sep :: rest),
                 t := List.replicate L (ty BSym.zero) ++ ty BSym.sep :: t' }) =
      Zs { nb := (Nat.bits n).map tkb, wa := rest, vis := List.replicate L (ty BSym.zero), t := t' } := by
  obtain ⟨a1, a2⟩ := stC_calc_w_nb ({ w := (Nat.bits n).map tkb ++ tk BSym.sep :: ((Nat.bits L).map tkb ++ tk BSym.sep :: rest), t := List.replicate L (ty BSym.zero) ++ ty BSym.sep :: t' } : Z) (Nat.bits n) _ rfl (canon_bits n)
  obtain ⟨b1, b2⟩ := stC_calc_w_kk ({ w := (Nat.bits L).map tkb ++ tk BSym.sep :: rest, t := List.replicate L (ty BSym.zero) ++ ty BSym.sep :: t', nb := (Nat.bits n).map tkb } : Z) (Nat.bits L) rest rfl (canon_bits L)
  have hz := dw_rep (ty BSym.zero) (ty BSym.sep) (by simp [ty]) L t'
  have hz' := tw_rep (ty BSym.zero) (ty BSym.sep) (by simp [ty]) L t'
  simp only [stH, seq_ok, seq_T, a2, List.append_nil, b2]
  simp [gMvP, gPop, gCopy, gClear, eqT, topP, hd, hz, hz', isA, a1, b1]

lemma tkb_inj : Function.Injective tkb := by
  intro a b hab; cases a <;> cases b <;> first | rfl | (exfalso; simp [tkb, tk] at hab)

lemma stH_dec (z : Z) (hk : z.kk = []) (hv : z.vis = []) (h : stH.ok (Zs z)) :
    ∃ n L : ℕ, ∃ rest t' : List Al,
      z.w = (Nat.bits n).map tkb ++ tk BSym.sep :: ((Nat.bits L).map tkb ++ tk BSym.sep :: rest) ∧
      z.t = List.replicate L (ty BSym.zero) ++ ty BSym.sep :: t' := by
  simp only [stH, seq_ok, seq_T] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨bl, rest1, hp⟩ := stC_dec_w_nb z h1
  obtain ⟨hw1, hc1⟩ := popNum_some _ _ _ hp
  obtain ⟨a1, a2⟩ := stC_calc_w_nb z bl rest1 hw1 hc1
  rw [a2] at h2
  obtain ⟨h2, h3⟩ := h2
  obtain ⟨bl2, rest2, hp2⟩ := stC_dec_w_kk _ h2
  obtain ⟨hw2, hc2⟩ := popNum_some _ _ _ hp2
  obtain ⟨b1, b2⟩ := stC_calc_w_kk _ bl2 rest2 hw2 hc2
  rw [b2] at h3
  simp [gMvP, gPop, gCopy, gClear, eqT, topP, hd, isA, hk, hv] at h3
  obtain ⟨h3a, h3b⟩ := h3
  obtain ⟨ht0, ht1⟩ := tw_split (isA (ty BSym.zero)) z.t
  have hr := rep_of_all ht1
  generalize List.takeWhile (isA (ty BSym.zero)) z.t = tw at *
  generalize List.dropWhile (isA (ty BSym.zero)) z.t = dw at *
  cases dw with
  | nil => simp at h3a
  | cons c t' =>
    simp only [List.head?_cons, decide_eq_true_eq] at h3a
    subst h3a
    have hb2 : bl2 = Nat.bits tw.length := List.map_injective_iff.mpr tkb_inj h3b
    have hw2' : rest1 = bl2.map tkb ++ tk BSym.sep :: rest2 := hw2
    refine ⟨val bl, val bl2, rest2, t', ?_, ?_⟩
    · rw [hw1, hw2', bits_val_of_canon _ hc1, bits_val_of_canon _ hc2]
    · rw [ht0, hr, hb2, val_bits]

end Stk

end Sec_RPV4

section Sec_RPV5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

/-- skip loop: pop `A`; whenever the popped token is `sep` (or `A` is empty) pop one counter `B`;
 push BAD when `A` is empty. -/
def skAct (A B : Reg) : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = A then StackAct.pop
  else if r = B then (if (match h A with | some x => decide (x = tk BSym.sep) | none => true) = true
      then StackAct.pop else StackAct.keep)
  else if r = Reg.BAD then (if (h A).isNone = true then StackAct.push mk else StackAct.keep)
  else StackAct.keep

def skProg (A B : Reg) : Prog := .loop (topS B) (.act (skAct A B))

/-- remaining list after skipping `k` separators -/
def skW : List Al → ℕ → List Al
  | W, 0 => W
  | [], _ => []
  | x :: W, k + 1 => if x = tk BSym.sep then skW W k else skW W (k + 1)

/-- shortfall -/
def skE : List Al → ℕ → ℕ
  | _, 0 => 0
  | [], k => k
  | x :: W, k + 1 => if x = tk BSym.sep then skE W k else skE W (k + 1)

def skF (A B : Reg) (s : St) : St :=
  upd (upd (upd s A (skW (s A) (s B).length)) B []) Reg.BAD
    (List.replicate (skE (s A) (s B).length) mk ++ s Reg.BAD)

lemma sk_step_cons (A B : Reg) (hAB : A ≠ B) (hA : A ≠ Reg.BAD) (hB : B ≠ Reg.BAD)
    (s : St) (x : Al) (l : List Al) (hx : s A = x :: l) :
    StackProg.applyAct (skAct A B) s =
      upd (upd s A l) B (if x = tk BSym.sep then (s B).tail else s B) := by
  funext r
  have e0 : StackProg.applyAct (skAct A B) s r = (skAct A B (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdA : hd s A = some x := by simp [hd, hx]
  by_cases h1 : r = A
  · subst h1; simp [skAct, upd_apply, hx, StackAct.apply, hAB, hA]
  · by_cases h2 : r = B
    · subst h2
      by_cases hx' : x = tk BSym.sep <;>
        simp [skAct, h1, hdA, upd_apply, hAB.symm, hx', StackAct.apply]
    · by_cases h3 : r = Reg.BAD
      · subst h3
        simp [skAct, h1, h2, hdA, upd_apply, StackAct.apply]
      · simp [skAct, h1, h2, h3, upd_apply, StackAct.apply]

lemma sk_step_nil (A B : Reg) (hAB : A ≠ B) (hA : A ≠ Reg.BAD) (hB : B ≠ Reg.BAD)
    (s : St) (hx : s A = []) :
    StackProg.applyAct (skAct A B) s =
      upd (upd s B (s B).tail) Reg.BAD (mk :: s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct (skAct A B) s r = (skAct A B (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdA : hd s A = none := by simp [hd, hx]
  by_cases h1 : r = A
  · subst h1; simp [skAct, upd_apply, hx, StackAct.apply, hAB, hA]
  · by_cases h2 : r = B
    · subst h2
      simp [skAct, h1, hdA, upd_apply, StackAct.apply, hAB.symm, hB]
    · by_cases h3 : r = Reg.BAD
      · subst h3
        simp [skAct, h1, h2, hdA, upd_apply, StackAct.apply]
      · simp [skAct, h1, h2, h3, upd_apply, StackAct.apply]


lemma len2_le_S (s : St) (A B : Reg) (hAB : A ≠ B) : (s A).length + (s B).length ≤ S s := by
  have : ∑ k ∈ ({A, B} : Finset Reg), (s k).length ≤ ∑ k, (s k).length :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hAB] at this
  exact this

lemma skW_nil (k : ℕ) : skW [] k = [] := by cases k <;> simp [skW]
lemma skE_nil (k : ℕ) : skE [] k = k := by cases k <;> simp [skE]

lemma gsP_skip (A B : Reg) (hA : safe A) (hB : safe B) (hAB : A ≠ B)
    (hA' : A ≠ Reg.BAD) (hB' : B ≠ Reg.BAD) :
    GsP (skProg A B) (lrun (topS B) (StackProg.applyAct (skAct A B)) (fun s => (s A).length + (s B).length))
      (fun s => upd (skF A B s) Reg.BAD (s Reg.BAD)) (fun s => skE (s A) (s B).length = 0)
      (fun _ => True) := by
  have hAC := hA.1; have hAR := hA.2; have hBC := hB.1; have hBR := hB.2
  refine GsP.loop1x (topS B) (skAct A B) (fun s => (s A).length + (s B).length)
    (fun s => len2_le_S s A B hAB)
    (fun h => by simp [skAct, hAC.symm, hBC.symm])
    (fun h => by simp [skAct, hAR.symm, hBR.symm])
    (fun h => by unfold skAct; rw [if_neg hA'.symm, if_neg hB'.symm, if_pos rfl]; split_ifs <;> simp)
    ?_ (fun _ => True) (fun _ _ _ => trivial) (skF A B)
    (fun s => List.replicate (skE (s A) (s B).length) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨y, l, hy⟩ := top_cons B s ht
    by_cases hx : s A = []
    · rw [sk_step_nil A B hAB hA' hB' s hx]
      simp [upd_apply, hA', hAB, hB', hx, hy]
    · obtain ⟨x, l', hx'⟩ := List.exists_cons_of_ne_nil hx
      rw [sk_step_cons A B hAB hA' hB' s x l' hx']
      by_cases hs : x = tk BSym.sep <;> simp [upd_apply, hA', hAB, hB', hx', hy, hs] <;> omega
  · intro s _ ht
    have hBe : s B = [] := by
      simp only [topS, hd] at ht
      cases hs : s B with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    by_cases h1 : r = A
    · subst h1; simp [skF, upd_apply, hBe, hA', hAB, skW]
    · by_cases h2 : r = B
      · subst h2; simp [skF, upd_apply, hBe, h1, hB']
      · by_cases h3 : r = Reg.BAD
        · subst h3; simp [skF, upd_apply, hBe, h1, h2, skE]
        · simp [skF, upd_apply, h1, h2, h3]
  · intro s _ ht
    obtain ⟨y, l, hy⟩ := top_cons B s ht
    by_cases hx : s A = []
    · rw [sk_step_nil A B hAB hA' hB' s hx]
      funext r
      by_cases h1 : r = A
      · subst h1; simp [skF, upd_apply, hx, hA', hAB, hy, hB', skW_nil]
      · by_cases h2 : r = B
        · subst h2; simp [skF, upd_apply, hB', hy]
        · by_cases h3 : r = Reg.BAD
          · subst h3
            simp [skF, upd_apply, hx, hy, h1, h2, hB', hA', hAB, skE_nil, skW_nil, List.replicate_succ']
          · simp [skF, upd_apply, h1, h2, h3]
    · obtain ⟨x, l', hx'⟩ := List.exists_cons_of_ne_nil hx
      rw [sk_step_cons A B hAB hA' hB' s x l' hx']
      funext r
      by_cases hs : x = tk BSym.sep
      · by_cases h1 : r = A
        · subst h1; simp [skF, upd_apply, hx', hy, hs, hA', hAB, skW]
        · by_cases h2 : r = B
          · subst h2; simp [skF, upd_apply, hx', hy, hs, hB', h1]
          · by_cases h3 : r = Reg.BAD
            · subst h3; simp [skF, upd_apply, hx', hy, hs, h1, h2, skE, hA', hB', hAB]
            · simp [skF, upd_apply, h1, h2, h3]
      · by_cases h1 : r = A
        · subst h1; simp [skF, upd_apply, hx', hy, hs, hA', hAB, skW]
        · by_cases h2 : r = B
          · subst h2; simp [skF, upd_apply, hx', hy, hs, hB', h1]
          · by_cases h3 : r = Reg.BAD
            · subst h3; simp [skF, upd_apply, hx', hy, hs, h1, h2, skE, hA', hB', hAB]
            · simp [skF, upd_apply, h1, h2, h3]
  · intro s _
    simp [skF, upd_apply, hA', hB']
  · intro s _
    simp [List.replicate_eq_nil_iff]


/-- mark loop: per counter token, pop `K`, pop `V`, push the popped element on `T`; BAD if `V` empty -/
def mkAct (K V T : Reg) : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = K then StackAct.pop
  else if r = V then StackAct.pop
  else if r = T then (match h V with | some x => StackAct.push x | none => StackAct.keep)
  else if r = Reg.BAD then (if (h V).isNone = true then StackAct.push mk else StackAct.keep)
  else StackAct.keep

def mkProg (K V T : Reg) : Prog := .loop (topS K) (.act (mkAct K V T))

def mkF (K V T : Reg) (s : St) : St :=
  upd (upd (upd (upd s K []) V ((s V).drop (s K).length)) T (((s V).take (s K).length).reverse ++ s T))
    Reg.BAD (List.replicate ((s K).length - (s V).length) mk ++ s Reg.BAD)

lemma mk_step_cons (K V T : Reg) (hKV : K ≠ V) (hKT : K ≠ T) (hVT : V ≠ T) (hK : K ≠ Reg.BAD)
    (hV : V ≠ Reg.BAD) (hT : T ≠ Reg.BAD)
    (s : St) (x : Al) (l : List Al) (hx : s V = x :: l) :
    StackProg.applyAct (mkAct K V T) s =
      upd (upd (upd s K (s K).tail) V l) T (x :: s T) := by
  funext r
  have e0 : StackProg.applyAct (mkAct K V T) s r = (mkAct K V T (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdV : hd s V = some x := by simp [hd, hx]
  by_cases h1 : r = K
  · subst h1; simp [mkAct, upd_apply, StackAct.apply, hKV, hKT]
  · by_cases h2 : r = V
    · subst h2; simp [mkAct, h1, upd_apply, hx, StackAct.apply, hVT, hKV.symm]
    · by_cases h3 : r = T
      · subst h3; simp [mkAct, h1, h2, hdV, upd_apply, StackAct.apply]
      · by_cases h4 : r = Reg.BAD
        · subst h4; simp [mkAct, h1, h2, h3, hdV, upd_apply, StackAct.apply]
        · simp [mkAct, h1, h2, h3, h4, upd_apply, StackAct.apply]

lemma mk_step_nil (K V T : Reg) (hKV : K ≠ V) (hKT : K ≠ T) (hVT : V ≠ T) (hK : K ≠ Reg.BAD)
    (hV : V ≠ Reg.BAD) (hT : T ≠ Reg.BAD)
    (s : St) (hx : s V = []) :
    StackProg.applyAct (mkAct K V T) s =
      upd (upd s K (s K).tail) Reg.BAD (mk :: s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct (mkAct K V T) s r = (mkAct K V T (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdV : hd s V = none := by simp [hd, hx]
  by_cases h1 : r = K
  · subst h1; simp [mkAct, upd_apply, StackAct.apply, hK]
  · by_cases h2 : r = V
    · subst h2; simp [mkAct, h1, upd_apply, hx, StackAct.apply, hV]
    · by_cases h3 : r = T
      · subst h3; simp [mkAct, h1, h2, hdV, upd_apply, StackAct.apply, hT]
      · by_cases h4 : r = Reg.BAD
        · subst h4; simp [mkAct, h1, h2, h3, hdV, upd_apply, StackAct.apply]
        · simp [mkAct, h1, h2, h3, h4, upd_apply, StackAct.apply]

lemma gsP_mark (K V T : Reg) (hK : safe K) (hV : safe V) (hT : safe T) (hKV : K ≠ V) (hKT : K ≠ T)
    (hVT : V ≠ T) (hK' : K ≠ Reg.BAD) (hV' : V ≠ Reg.BAD) (hT' : T ≠ Reg.BAD) :
    GsP (mkProg K V T) (lrun (topS K) (StackProg.applyAct (mkAct K V T)) (fun s => (s K).length))
      (fun s => upd (mkF K V T s) Reg.BAD (s Reg.BAD)) (fun s => (s K).length ≤ (s V).length)
      (fun _ => True) := by
  have hKC := hK.1; have hKR := hK.2; have hVC := hV.1; have hVR := hV.2
  have hTC := hT.1; have hTR := hT.2
  refine GsP.loop1x (topS K) (mkAct K V T) (fun s => (s K).length) (fun s => len_le_S s K)
    (fun h => by simp [mkAct, hKC.symm, hVC.symm, hTC.symm])
    (fun h => by simp [mkAct, hKR.symm, hVR.symm, hTR.symm])
    (fun h => by
      unfold mkAct
      rw [if_neg hK'.symm, if_neg hV'.symm, if_neg hT'.symm, if_pos rfl]; split_ifs <;> simp)
    ?_ (fun _ => True) (fun _ _ _ => trivial) (mkF K V T)
    (fun s => List.replicate ((s K).length - (s V).length) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨y, l, hy⟩ := top_cons K s ht
    by_cases hx : s V = []
    · rw [mk_step_nil K V T hKV hKT hVT hK' hV' hT' s hx]
      simp [upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hK', hy]
    · obtain ⟨x, l', hx'⟩ := List.exists_cons_of_ne_nil hx
      rw [mk_step_cons K V T hKV hKT hVT hK' hV' hT' s x l' hx']
      simp [upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hK', hy, hKV, hKT]
  · intro s _ ht
    have hKe : s K = [] := by
      simp only [topS, hd] at ht
      cases hs : s K with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    by_cases h1 : r = K
    · subst h1; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hKe, hK', hKV, hKT]
    · by_cases h2 : r = V
      · subst h2; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hKe, h1, hV', hVT]
      · by_cases h3 : r = T
        · subst h3; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hKe, h1, h2, hT']
        · by_cases h4 : r = Reg.BAD
          · subst h4; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hKe, h1, h2, h3]
          · simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, h1, h2, h3, h4]
  · intro s _ ht
    obtain ⟨y, l, hy⟩ := top_cons K s ht
    by_cases hx : s V = []
    · rw [mk_step_nil K V T hKV hKT hVT hK' hV' hT' s hx]
      funext r
      by_cases h1 : r = K
      · subst h1; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx, hK', hy, hKV, hKT]
      · by_cases h2 : r = V
        · subst h2; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx, hy, h1, hV', hVT]
        · by_cases h3 : r = T
          · subst h3; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx, hy, h1, h2, hT']
          · by_cases h4 : r = Reg.BAD
            · subst h4
              simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx, hy, h1, h2, h3, hKV, hKT, List.replicate_succ']
            · simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, h1, h2, h3, h4]
    · obtain ⟨x, l', hx'⟩ := List.exists_cons_of_ne_nil hx
      rw [mk_step_cons K V T hKV hKT hVT hK' hV' hT' s x l' hx']
      funext r
      by_cases h1 : r = K
      · subst h1; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx', hy, hK', hKV, hKT]
      · by_cases h2 : r = V
        · subst h2; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx', hy, h1, hV', hVT]
        · by_cases h3 : r = T
          · subst h3; simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx', hy, h1, h2, hT', hKT, hVT]
          · by_cases h4 : r = Reg.BAD
            · subst h4
              simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hx', hy, h1, h2, h3, hKV, hKT, hK', hV', hT']
            · simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, h1, h2, h3, h4]
  · intro s _
    simp [mkF, upd_apply, hK', hV', hT', hK'.symm, hV'.symm, hT'.symm, hKV, hKV.symm, hKT, hKT.symm, hVT, hVT.symm, hK', hV', hT']
  · intro s _
    simp [List.replicate_eq_nil_iff, Nat.sub_eq_zero_iff_le]

end Stk

end Sec_RPV5

section Sec_RPV6
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def skGB : GB :=
  ⟨skProg Reg.W Reg.NC2, _, _, _, _,
    gsP_skip Reg.W Reg.NC2 (by decide) (by decide) (by decide) (by decide) (by decide)⟩

def mkGB : GB :=
  ⟨mkProg Reg.KR Reg.NC Reg.NC2, _, _, _, _,
    gsP_mark Reg.KR Reg.NC Reg.NC2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)⟩

lemma skGB_pre (s : St) : skGB.pre s := trivial
lemma mkGB_pre (s : St) : mkGB.pre s := trivial

lemma skGB_Zs (z : Z) : skGB.ok (Zs z) ↔ skE z.w z.tv.length = 0 := Iff.rfl
lemma mkGB_Zs_ok (z : Z) : mkGB.ok (Zs z) ↔ z.cn2.length ≤ z.vis.length := Iff.rfl

lemma skGB_T_Zs (z : Z) (h : skE z.w z.tv.length = 0) :
    skGB.T (Zs z) = Zs { z with w := skW z.w z.tv.length, tv := [] } := by
  show upd (skF Reg.W Reg.NC2 (Zs z)) Reg.BAD (Zs z Reg.BAD) = _
  simp [skF, h]

lemma mkGB_T_Zs (z : Z) (h : z.cn2.length ≤ z.vis.length) :
    mkGB.T (Zs z) = Zs { z with cn2 := [], vis := z.vis.drop z.cn2.length, tv := (z.vis.take z.cn2.length).reverse ++ z.tv } := by
  show upd (mkF Reg.KR Reg.NC Reg.NC2 (Zs z)) Reg.BAD (Zs z Reg.BAD) = _
  simp [mkF, Nat.sub_eq_zero_of_le h]


def badTop : (Reg → Option Al) → Bool := fun h =>
  match h Reg.T with | some x => !(decide (x = ty BSym.one ∨ x = ty BSym.minus)) | none => true

def rA : GB :=
  (bMvP Reg.T Reg.MR (isA (ty BSym.zero))).seq <| (bBad badTop).seq <|
  (bCopy Reg.MR Reg.NC2).seq <| (bCopy Reg.MR Reg.NC2).seq <| (bCopy Reg.MR Reg.NC2).seq <|
  (bCopy Reg.MR Reg.NC2).seq <| (bCopy Reg.KP Reg.W).seq skGB

lemma rA_calc (z : Z) (i : ℕ) (x : Al) (rest : List Al) (hx : x = ty BSym.one ∨ x = ty BSym.minus)
    (hT : z.t = List.replicate i (ty BSym.zero) ++ x :: rest) (hcn : z.cn = []) (hw : z.w = [])
    (htv : z.tv = []) :
    rA.ok (Zs z) ↔ skE z.wa (4 * i) = 0 := by
  have hz := dw_rep (ty BSym.zero) x (by rcases hx with rfl | rfl <;> simp [ty]) i rest
  have hz' := tw_rep (ty BSym.zero) x (by rcases hx with rfl | rfl <;> simp [ty]) i rest
  simp [rA, skGB_Zs, gMvP, gCopy, hT, hz, hz', hcn, hw, htv, badTop, hd, hx]
  rw [show i + (i + (i + i)) = 4 * i by omega]


lemma rA_T (z : Z) (i : ℕ) (x : Al) (rest : List Al) (hx : x = ty BSym.one ∨ x = ty BSym.minus)
    (hT : z.t = List.replicate i (ty BSym.zero) ++ x :: rest) (hcn : z.cn = []) (hw : z.w = [])
    (htv : z.tv = []) (ho : skE z.wa (4 * i) = 0) :
    rA.T (Zs z) = Zs { z with t := x :: rest, cn := List.replicate i (ty BSym.zero), tv := [], w := skW z.wa (4 * i) } := by
  have hz := dw_rep (ty BSym.zero) x (by rcases hx with rfl | rfl <;> simp [ty]) i rest
  have hz' := tw_rep (ty BSym.zero) x (by rcases hx with rfl | rfl <;> simp [ty]) i rest
  have e4 : (List.replicate i (ty BSym.zero)).length + (List.replicate i (ty BSym.zero)).length +
      (List.replicate i (ty BSym.zero)).length + (List.replicate i (ty BSym.zero)).length = 4 * i := by
    simp; omega
  have e5 : i + (i + (i + i)) = 4 * i := by omega
  simp [rA, gMvP, gCopy, hT, hz, hz', hcn, hw, htv]
  rw [show i + (i + (i + i)) = 4 * i by omega]
  rw [skGB_T_Zs _ (by simpa [e5] using ho)]
  simp [e5]


def rB : GB :=
  (stC Reg.W Reg.TM).seq <| (stC Reg.W Reg.TT).seq <| (stC Reg.W Reg.TR).seq <| bClear Reg.W

lemma rB_calc (z : Z) (b1 b2 b3 : List Bool) (rest : List Al)
    (hW : z.w = b1.map tkb ++ tk BSym.sep :: (b2.map tkb ++ tk BSym.sep :: (b3.map tkb ++ tk BSym.sep :: rest)))
    (c1 : canon b1) (c2 : canon b2) (c3 : canon b3) (h1 : z.tx = []) (h2 : z.hx = []) (h3 : z.wx = []) :
    rB.ok (Zs z) ∧ rB.T (Zs z) = Zs { z with w := [], tx := b1.map tkb, hx := b2.map tkb, wx := b3.map tkb } := by
  obtain ⟨a1, a2⟩ := stC_calc_w_tx z b1 _ hW c1
  obtain ⟨b1', b2'⟩ := stC_calc_w_hx ({ z with w := b2.map tkb ++ tk BSym.sep :: (b3.map tkb ++ tk BSym.sep :: rest), tx := b1.map tkb } : Z) b2 _ rfl c2
  obtain ⟨c1', c2'⟩ := stC_calc_w_wx ({ z with w := b3.map tkb ++ tk BSym.sep :: rest, tx := b1.map tkb, hx := b2.map tkb } : Z) b3 rest rfl c3
  simp only [h1, h2, h3, List.append_nil] at a1 a2 b1' b2' c1' c2'
  simp only [rB, seq_ok, seq_T, a2, b2', c2']
  simp [gClear, a1, b1', c1']


def rC : GB :=
  (GB.branch (topN Reg.K2)
      ((bCopy Reg.TM Reg.T2).seq (bPush Reg.K2 mk))
      ((cmpLt Reg.TC Reg.TM).seq <| (bBad (topS Reg.H)).seq <| (cmpLt Reg.TM Reg.TC).seq <|
        bBad (topS Reg.H))).seq <|
  (bClear Reg.TC).seq <| (bCopy Reg.TT Reg.TC).seq <| (bClear Reg.TM).seq <| (bClear Reg.TT).seq <|
  bClear Reg.H

lemma rC_first (z : Z) (s dd : ℕ) (h1 : z.tx = (Nat.bits s).map tkb) (h2 : z.hx = (Nat.bits dd).map tkb)
    (hf : z.fst = []) (hfi : z.first = []) :
    rC.ok (Zs z) ∧ rC.T (Zs z) = Zs { z with first := (Nat.bits s).map tkb, fst := [mk], prev := (Nat.bits dd).map tkb, tx := [], hx := [], h := [] } := by
  simp [rC, GB.branch, topN, hd, hf, gCopy, gPush, gClear, h1, h2, hfi]
  done


@[simp] lemma br_ok (t : (Reg → Option Al) → Bool) (a b : GB) (s : St) :
    (GB.branch t a b).ok s = (if t (hd s) = true then a.ok s else b.ok s) := rfl
@[simp] lemma br_T (t : (Reg → Option Al) → Bool) (a b : GB) (s : St) :
    (GB.branch t a b).T s = (if t (hd s) = true then a.T s else b.T s) := rfl

lemma rC_next (z : Z) (m s dd : ℕ) (h1 : z.tx = (Nat.bits s).map tkb) (hp : z.prev = (Nat.bits m).map tkb)
    (hf : z.fst = [mk]) (h2 : z.hx = (Nat.bits dd).map tkb) :
    (rC.ok (Zs z) ↔ m = s) ∧ (m = s → rC.T (Zs z) = Zs { z with prev := (Nat.bits dd).map tkb, tx := [], hx := [], h := [] }) := by
  obtain ⟨a1, a2⟩ := cmpLt_spec Reg.TC Reg.TM (by decide) (Zs z) (Nat.bits m) (Nat.bits s) (by simp [Zs, hp]) (by simp [Zs, h1]) rfl rfl
  obtain ⟨b1, b2⟩ := cmpLt_spec Reg.TM Reg.TC (by decide) (Zs { z with h := flag (decide (m < s)) }) (Nat.bits s) (Nat.bits m) (by simp [Zs, h1]) (by simp [Zs, hp]) rfl rfl
  simp only [val_bits] at a2 b2
  rw [upd_Zs_h] at a2 b2
  have hc : topN Reg.K2 (hd (Zs z)) = false := by simp [topN, hd, hf, Zs]
  have e1 : (Zs z) Reg.K2 = [mk] := hf
  simp only [rC, seq_ok, seq_T, br_ok, br_T, hc, Bool.false_eq_true, if_false, a2, b2, bBad_ok, bBad_T, a1, b1, true_and]
  simp [topS, hd, flag, Zs, gClear, gCopy, h2]
  constructor
  · omega
  · intro hms; subst hms; simp
  done


def badMark : (Reg → Option Al) → Bool := fun h =>
  match h Reg.NC with | some x => !(decide (x = ty BSym.zero ∨ x = ty BSym.one)) | none => true

def rM : GB :=
  (bCopy Reg.MR Reg.KR).seq <| mkGB.seq <| (bBad badMark).seq <| (bPop Reg.NC).seq <|
  (bPush Reg.NC (ty BSym.one)).seq <| (bMvA Reg.NC2 Reg.NC).seq <| bClear Reg.MR

lemma rM_calc (z : Z) (vis : List Bool) (i : ℕ) (hv : z.vis = vis.map tyb)
    (hcn : z.cn = List.replicate i (ty BSym.zero)) (hcn2 : z.cn2 = []) (htv : z.tv = []) :
    (rM.ok (Zs z) ↔ i < vis.length) ∧
    (i < vis.length → rM.T (Zs z) = Zs { z with vis := (vis.set i true).map tyb, cn := [], cn2 := [], tv := [] }) := by
  by_cases hi : i < vis.length
  · obtain ⟨A, c, B, hs, hA⟩ : ∃ A c B, vis = A ++ c :: B ∧ A.length = i :=
      ⟨vis.take i, vis[i], vis.drop (i+1), by simp [List.getElem_cons_drop_succ_eq_drop] , by simp; omega⟩
    subst hs
    have hv' : z.vis = A.map tyb ++ tyb c :: B.map tyb := by simp [hv]
    have hz1 := mkGB_T_Zs { z with cn := List.replicate i (ty BSym.zero), cn2 := List.replicate i (ty BSym.zero) } (by simp [hv']; omega)
    have hset : (A ++ c :: B).set i true = A ++ true :: B := by
      subst hA; simp [List.set_append]
    have hz2 : (rM.T (Zs z)) = Zs { z with vis := (A ++ true :: B).map tyb, cn := [], cn2 := [], tv := [] } := by
      simp only [rM, seq_T, bCopy_T, bBad_T, bPop_T, bPush_T, bMvA_T, bClear_T]
      simp only [gCopy, Zs_cn, Zs_cn2, hcn, hcn2, List.append_nil, upd_Zs_cn2]
      rw [hz1]
      simp [gPop, gPush, gMvA, gClear, hv', hA, htv, tyb]
    have hok : rM.ok (Zs z) := by
      simp only [rM, seq_ok, seq_T, bCopy_T, bCopy_ok, bBad_ok, bBad_T, bPop_ok, bPop_T, bPush_ok, bPush_T, bMvA_ok, bClear_ok]
      simp only [gCopy, Zs_cn, Zs_cn2, hcn, hcn2, List.append_nil, upd_Zs_cn2]
      refine ⟨trivial, (mkGB_Zs_ok _).2 (by simp [hv']; omega), ?_, by simp⟩
      rw [hz1]
      cases c <;> simp [badMark, hd, hv', hA, tyb]
    refine ⟨⟨fun _ => hA ▸ hi, fun _ => hok⟩, fun _ => ?_⟩
    rw [hz2, hset]
  · refine ⟨⟨fun hok => ?_, fun h => absurd h hi⟩, fun h => absurd h hi⟩
    simp only [rM, seq_ok, bCopy_T, bCopy_ok, bBad_ok, bBad_T, bPop_ok, bPop_T, bPush_ok, bPush_T, bMvA_ok, bClear_ok] at hok
    simp only [gCopy, Zs_cn, Zs_cn2, hcn, hcn2, List.append_nil, upd_Zs_cn2] at hok
    obtain ⟨_, hmk, hbad, _⟩ := hok
    rw [mkGB_Zs_ok] at hmk
    simp [hv] at hmk
    have hl : i = vis.length := by omega
    rw [mkGB_T_Zs _ (by simp [hv]; omega)] at hbad
    simp [badMark, hd, hv, hl] at hbad



def swapG : GB :=
  (bCopy Reg.TM Reg.NC2).seq <| (bClear Reg.TM).seq <| (bCopy Reg.TT Reg.TM).seq <|
  (bClear Reg.TT).seq <| (bCopy Reg.NC2 Reg.TT).seq <| bClear Reg.NC2

lemma swapG_calc (z : Z) (htv : z.tv = []) :
    swapG.ok (Zs z) ∧ swapG.T (Zs z) = Zs { z with tx := z.hx, hx := z.tx } := by
  simp only [swapG, seq_ok, seq_T, bCopy_T, bCopy_ok, bClear_ok, bClear_T]
  refine ⟨by simp, ?_⟩
  simp [gCopy, gClear, htv]
  done


lemma addZ_T (z : Z) (a b : List Bool) (h1 : z.acc = a.map tkb) (h2 : z.wx = b.map tkb) :
    (addG Reg.PP Reg.TR).T (Zs z) = Zs { z with acc := (addBits a b).map tkb, wx := [] } := by
  rw [addG_T Reg.PP Reg.TR (by decide) _ a b h1 h2]
  simp

def dirBad (d : Bool) : (Reg → Option Al) → Bool := fun h => d && topP Reg.T (isA (ty BSym.minus)) h




def Z4 (z : Z) (i : ℕ) (x : Al) (rest : List Al) (b1 b2 b3 : List Bool) : Z :=
  { z with t := rest, cn := List.replicate i (ty BSym.zero), tv := [], w := [], tx := (if x = ty BSym.minus then b2 else b1).map tkb, hx := (if x = ty BSym.minus then b1 else b2).map tkb, wx := b3.map tkb }

def Z5 (z : Z) (i : ℕ) (rest : List Al) (b3 : List Bool) (f1 f2 f3 : List Al) : Z :=
  { z with t := rest, cn := List.replicate i (ty BSym.zero), tv := [], w := [], tx := [], hx := [], wx := b3.map tkb, first := f1, fst := f2, prev := f3, h := [] }

def Y2 (z : Z) (i : ℕ) (x : Al) (rest : List Al) (b1 b2 b3 : List Bool) : Z :=
  { z with t := x :: rest, cn := List.replicate i (ty BSym.zero), tv := [], w := [], tx := b1.map tkb, hx := b2.map tkb, wx := b3.map tkb }

@[simp] lemma Y2_t (z : Z) (i : ℕ) (x : Al) (rest : List Al) (b1 b2 b3 : List Bool) : (Y2 z i x rest b1 b2 b3).t = x :: rest := rfl
lemma Y2_tv (z : Z) (i : ℕ) (x : Al) (rest : List Al) (b1 b2 b3 : List Bool) : (Y2 z i x rest b1 b2 b3).tv = [] := rfl

def MID (d : Bool) : GB :=
  (bBad (dirBad d)).seq <| (GB.branch (topP Reg.T (isA (ty BSym.minus))) swapG (bClear Reg.TMP)).seq <| (bPop Reg.T)

lemma gPopT_Zs (z : Z) : gPop Reg.T (Zs z) = Zs { z with t := z.t.tail } := by
  simp [gPop, Zs]

lemma gClrTMP (z : Z) : gClear Reg.TMP (Zs z) = Zs z := upd_Zs_TMP_nil z

lemma mid_calc (d : Bool) (z : Z) (i : ℕ) (x : Al) (rest : List Al) (b1 b2 b3 : List Bool)
    (hx : x = ty BSym.one ∨ x = ty BSym.minus) :
    ((MID d).ok (Zs (Y2 z i x rest b1 b2 b3)) ↔ ¬ (d = true ∧ x = ty BSym.minus)) ∧
    ((MID d).T (Zs (Y2 z i x rest b1 b2 b3)) = Zs (Z4 z i x rest b1 b2 b3)) := by
  have hs := swapG_calc (Y2 z i x rest b1 b2 b3) rfl
  rcases hx with rfl | rfl
  · constructor
    · simp [MID, dirBad, topP, hd, isA, ty, Zs]
    · simp only [MID, seq_T, bBad_T, br_T, bPop_T, bClear_T]
      have : topP Reg.T (isA (ty BSym.minus)) (hd (Zs (Y2 z i (ty BSym.one) rest b1 b2 b3))) = false := by
        simp [topP, hd, isA, ty, Zs]
      rw [this]
      simp only [Bool.false_eq_true, if_false]
      rw [gClrTMP, gPopT_Zs]
      simp [Z4, Y2, ty]
  · constructor
    · simp [MID, dirBad, topP, hd, isA, ty, Zs]
      exact fun _ => hs.1
    · simp only [MID, seq_T, bBad_T, br_T, bPop_T, bClear_T]
      have : topP Reg.T (isA (ty BSym.minus)) (hd (Zs (Y2 z i (ty BSym.minus) rest b1 b2 b3))) = true := by
        simp [topP, hd, isA, ty, Zs]
      rw [this]
      simp only [if_true]
      rw [hs.2, gPopT_Zs]
      simp [Z4, Y2, ty]

def rR (d : Bool) : GB :=
  rA.seq <| rB.seq <| (MID d).seq <| rC.seq <| (addG Reg.PP Reg.TR).seq <| rM

lemma rR_calc (d : Bool) (z : Z) (i : ℕ) (x : Al) (rest : List Al) (b1 b2 b3 : List Bool) (wr : List Al)
    (vis : List Bool) (a : List Bool)
    (hx : x = ty BSym.one ∨ x = ty BSym.minus)
    (hT : z.t = List.replicate i (ty BSym.zero) ++ x :: rest) (hcn : z.cn = []) (hcn2 : z.cn2 = []) (hw : z.w = [])
    (htv : z.tv = []) (htx : z.tx = []) (hhx : z.hx = []) (hwx : z.wx = []) (hv : z.vis = vis.map tyb)
    (ha : z.acc = a.map tkb)
    (hske : skE z.wa (4 * i) = 0)
    (hW : skW z.wa (4 * i) = b1.map tkb ++ tk BSym.sep :: (b2.map tkb ++ tk BSym.sep :: (b3.map tkb ++ tk BSym.sep :: wr)))
    (c1 : canon b1) (c2 : canon b2) (c3 : canon b3)
    (P : Prop) (f1 f2 f3 : List Al)
    (hC : (rC.ok (Zs (Z4 z i x rest b1 b2 b3)) ↔ P) ∧ (P → rC.T (Zs (Z4 z i x rest b1 b2 b3)) = Zs (Z5 z i rest b3 f1 f2 f3))) :
    ((rR d).ok (Zs z) ↔ ((¬ (d = true ∧ x = ty BSym.minus)) ∧ P ∧ i < vis.length)) ∧
    ((rR d).ok (Zs z) → (rR d).T (Zs z) = Zs { Z5 z i rest [] f1 f2 f3 with acc := (addBits a b3).map tkb, wx := [], vis := (vis.set i true).map tyb, cn := [], cn2 := [], tv := [] }) := by
  have hA1 := (rA_calc z i x rest hx hT hcn hw htv).2 hske
  have hA2 := rA_T z i x rest hx hT hcn hw htv hske
  have hB := rB_calc { z with t := x :: rest, cn := List.replicate i (ty BSym.zero), tv := [], w := skW z.wa (4 * i) } b1 b2 b3 wr hW c1 c2 c3 htx hhx hwx
  have hY : rB.T (rA.T (Zs z)) = Zs (Y2 z i x rest b1 b2 b3) := by rw [hA2, hB.2]; rfl
  have hM := mid_calc d z i x rest b1 b2 b3 hx
  simp only [rR, seq_ok, seq_T]
  rw [hY, hM.2]
  by_cases hP : P
  · rw [hC.2 hP]
    have hadd := addZ_T (Z5 z i rest b3 f1 f2 f3) a b3 ha rfl
    have hm := rM_calc { Z5 z i rest b3 f1 f2 f3 with acc := (addBits a b3).map tkb, wx := [] } vis i hv (by simp [Z5]) hcn2 (by simp [Z5])
    rw [hadd]
    have hrb : rB.ok (rA.T (Zs z)) := by rw [hA2]; exact hB.1
    have hrb' := hrb
    simp only [hA1, hB.1, hM.1, hC.1, true_and, hP, addG_ok]
    refine ⟨?_, fun hok => ?_⟩
    · simp only [hrb, true_and]
      exact and_congr_right (fun _ => hm.1)
    · have hlt : i < vis.length := by
        have := hok
        simp only [hrb', true_and] at this
        exact hm.1.1 this.2
      rw [hm.2 hlt]
      simp [Z5]
  · have hn : ¬ rC.ok (Zs (Z4 z i x rest b1 b2 b3)) := fun h => hP (hC.1.1 h)
    refine ⟨⟨fun h => ?_, fun h => absurd h.2.1 hP⟩, fun h => ?_⟩
    · exact absurd h.2.2.2.1 hn
    · exact absurd h.2.2.2.1 hn


lemma tw_rep_ex (c : Al) (l : List Al) : ∃ n, l.takeWhile (isA c) = List.replicate n c := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
    by_cases h : isA c a = true
    · obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      have : a = c := by simpa [isA] using h
      subst this
      simp [List.takeWhile_cons, h, hn, List.replicate_succ]
    · exact ⟨0, by simp [List.takeWhile_cons, h]⟩

lemma rA_dec (z : Z) (hcn : z.cn = []) (hok : rA.ok (Zs z)) :
    ∃ i x rest, (x = ty BSym.one ∨ x = ty BSym.minus) ∧ z.t = List.replicate i (ty BSym.zero) ++ x :: rest := by
  obtain ⟨n, hn⟩ := tw_rep_ex (ty BSym.zero) z.t
  have h1 := List.takeWhile_append_dropWhile (p := isA (ty BSym.zero)) (l := z.t)
  obtain ⟨_, hb, _⟩ := hok
  simp only [bBad_ok, bMvP_T] at hb
  simp only [gMvP, badTop, hd] at hb
  simp [upd_apply] at hb
  rcases hdw : z.t.dropWhile (isA (ty BSym.zero)) with _ | ⟨x, rest⟩
  · simp [hdw] at hb
  · simp [hdw] at hb
    refine ⟨n, x, rest, (by by_cases h : x = ty BSym.one; exact Or.inl h; exact Or.inr (hb h)), ?_⟩
    rw [← h1, hn, hdw]


lemma rB_dec (z : Z) (h1 : z.tx = []) (h2 : z.hx = []) (h3 : z.wx = []) (hok : rB.ok (Zs z)) :
    ∃ b1 b2 b3 wr, z.w = b1.map tkb ++ tk BSym.sep :: (b2.map tkb ++ tk BSym.sep :: (b3.map tkb ++ tk BSym.sep :: wr)) ∧
      canon b1 ∧ canon b2 ∧ canon b3 := by
  obtain ⟨o1, o2, o3, _⟩ := hok
  obtain ⟨b1, r1, p1⟩ := stC_dec_w_tx z o1
  obtain ⟨e1, c1⟩ := popNum_some _ _ _ p1
  obtain ⟨a1, a2⟩ := stC_calc_w_tx z b1 r1 e1 c1
  rw [a2] at o2 o3
  obtain ⟨b2, r2, p2⟩ := stC_dec_w_hx _ o2
  obtain ⟨e2, c2⟩ := popNum_some _ _ _ p2
  simp only at e2
  obtain ⟨a1', a2'⟩ := stC_calc_w_hx { z with w := r1, tx := b1.map tkb ++ z.tx } b2 r2 e2 c2
  rw [a2'] at o3
  obtain ⟨b3, r3, p3⟩ := stC_dec_w_wx _ o3
  obtain ⟨e3, c3⟩ := popNum_some _ _ _ p3
  simp only at e3
  exact ⟨b1, b2, b3, r3, by rw [e1, e2, e3], c1, c2, c3⟩


lemma rR_dec (d : Bool) (z : Z) (hcn : z.cn = []) (hw : z.w = []) (htv : z.tv = [])
    (htx : z.tx = []) (hhx : z.hx = []) (hwx : z.wx = []) (hok : (rR d).ok (Zs z)) :
    ∃ i x rest b1 b2 b3 wr, (x = ty BSym.one ∨ x = ty BSym.minus) ∧
      z.t = List.replicate i (ty BSym.zero) ++ x :: rest ∧ skE z.wa (4 * i) = 0 ∧
      skW z.wa (4 * i) = b1.map tkb ++ tk BSym.sep :: (b2.map tkb ++ tk BSym.sep :: (b3.map tkb ++ tk BSym.sep :: wr)) ∧
      canon b1 ∧ canon b2 ∧ canon b3 := by
  have hA : rA.ok (Zs z) := by
    simp only [rR, seq_ok] at hok; exact hok.1
  obtain ⟨i, x, rest, hx, hT⟩ := rA_dec z hcn hA
  have hske := (rA_calc z i x rest hx hT hcn hw htv).1 hA
  have hA2 := rA_T z i x rest hx hT hcn hw htv hske
  have hB : rB.ok (rA.T (Zs z)) := by
    simp only [rR, seq_ok] at hok; exact hok.2.1
  rw [hA2] at hB
  obtain ⟨b1, b2, b3, wr, hW, c1, c2, c3⟩ := rB_dec { z with t := x :: rest, cn := List.replicate i (ty BSym.zero), tv := [], w := skW z.wa (4 * i) } htx hhx hwx hB
  exact ⟨i, x, rest, b1, b2, b3, wr, hx, hT, hske, hW, c1, c2, c3⟩

end Stk

end Sec_RPV6

section Sec_RPV7
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def encFlat : List ℕ → List Al
  | [] => []
  | n :: l => (Nat.bits n).map tkb ++ tk BSym.sep :: encFlat l

lemma tkb_ne_sep (b : Bool) : tkb b ≠ tk BSym.sep := by cases b <;> simp [tkb, tk]

lemma skW_bits (bl : List Bool) (W : List Al) (k : ℕ) :
    skW (bl.map tkb ++ tk BSym.sep :: W) (k + 1) = skW W k := by
  induction bl with
  | nil => simp [skW]
  | cons b bl ih => simp [skW, tkb_ne_sep, ih]

lemma skE_bits (bl : List Bool) (W : List Al) (k : ℕ) :
    skE (bl.map tkb ++ tk BSym.sep :: W) (k + 1) = skE W k := by
  induction bl with
  | nil => simp [skE]
  | cons b bl ih => simp [skE, tkb_ne_sep, ih]

lemma skW_enc : ∀ (fl : List ℕ) (j : ℕ), skW (encFlat fl) j = encFlat (fl.drop j)
  | [], j => by cases j <;> simp [encFlat, skW]
  | n :: l, 0 => by simp [skW]
  | n :: l, j + 1 => by
    simp only [encFlat]
    rw [skW_bits, skW_enc l j]; simp

lemma skE_enc : ∀ (fl : List ℕ) (j : ℕ), skE (encFlat fl) j = j - fl.length
  | [], j => by cases j <;> simp [encFlat, skE]
  | n :: l, 0 => by simp [skE]
  | n :: l, j + 1 => by
    simp only [encFlat]
    rw [skE_bits, skE_enc l j]; simp

lemma encFlat_cons_inj (n m : ℕ) (l l' : List ℕ) (h : encFlat (n :: l) = encFlat (m :: l')) :
    n = m ∧ encFlat l = encFlat l' := by
  have h1 := popNum_enc (Nat.bits n) (encFlat l) (canon_bits n)
  have h2 := popNum_enc (Nat.bits m) (encFlat l') (canon_bits m)
  simp only [encFlat] at h
  rw [h] at h1
  rw [h1] at h2
  simp at h2
  obtain ⟨a, b⟩ := h2
  refine ⟨?_, b⟩
  have := congrArg val a
  simpa [val_bits] using this

lemma encFlat_len_bits (n : ℕ) (fl : List ℕ) (h : n ∈ fl) : (Nat.bits n).length < (encFlat fl).length := by
  induction fl with
  | nil => simp at h
  | cons m l ih =>
    simp only [encFlat, List.length_append, List.length_map, List.length_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega


lemma enc_parse1 (fl : List ℕ) (b : List Bool) (R : List Al) (hc : canon b)
    (h : encFlat fl = b.map tkb ++ tk BSym.sep :: R) :
    ∃ n l, fl = n :: l ∧ b = Nat.bits n ∧ R = encFlat l := by
  cases fl with
  | nil => simp [encFlat] at h
  | cons n l =>
    have h1 := popNum_enc (Nat.bits n) (encFlat l) (canon_bits n)
    have h2 := popNum_enc b R hc
    simp only [encFlat] at h
    rw [h] at h1
    rw [h1] at h2
    simp at h2
    exact ⟨n, l, rfl, h2.1.symm, h2.2.symm⟩

lemma enc_parse3 (fl : List ℕ) (b1 b2 b3 : List Bool) (wr : List Al) (c1 : canon b1) (c2 : canon b2) (c3 : canon b3)
    (h : encFlat fl = b1.map tkb ++ tk BSym.sep :: (b2.map tkb ++ tk BSym.sep :: (b3.map tkb ++ tk BSym.sep :: wr))) :
    ∃ s d w r, fl = s :: d :: w :: r ∧ b1 = Nat.bits s ∧ b2 = Nat.bits d ∧ b3 = Nat.bits w ∧ wr = encFlat r := by
  obtain ⟨s, l1, e1, f1, g1⟩ := enc_parse1 fl b1 _ c1 h
  obtain ⟨d, l2, e2, f2, g2⟩ := enc_parse1 l1 b2 _ c2 g1.symm
  obtain ⟨w, l3, e3, f3, g3⟩ := enc_parse1 l2 b3 _ c3 g2.symm
  exact ⟨s, d, w, l3, by rw [e1, e2, e3], f1, f2, f3, g3⟩

def arcOf (fl : List ℕ) (i : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match fl.drop (4 * i) with
  | s :: d :: w :: _ => some (s, d, w)
  | _ => none

lemma arcOf_some (fl : List ℕ) (i s d w : ℕ) (h : arcOf fl i = some (s, d, w)) :
    ∃ r, fl.drop (4 * i) = s :: d :: w :: r := by
  unfold arcOf at h
  rcases hh : fl.drop (4 * i) with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> rw [hh] at h <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨r, rfl⟩

lemma arcOf_eq (fl : List ℕ) (i s d w : ℕ) (r : List ℕ) (h : fl.drop (4 * i) = s :: d :: w :: r) :
    arcOf fl i = some (s, d, w) := by
  unfold arcOf; rw [h]

lemma arcOf_none (fl : List ℕ) (i : ℕ) (h : arcOf fl i = none) : ∀ s d w r, fl.drop (4 * i) ≠ s :: d :: w :: r := by
  intro s d w r hh
  rw [arcOf_eq fl i s d w r hh] at h; simp at h

structure Ys where
  fl : List ℕ
  vis : List Bool
  a : List Bool
  ch : Option (ℕ × ℕ)
  nb : List Al

def toZ (y : Ys) : Z :=
  { nb := y.nb, wa := encFlat y.fl, vis := y.vis.map tyb, acc := y.a.map tkb,
    first := match y.ch with | none => [] | some (f, _) => (Nat.bits f).map tkb,
    fst := match y.ch with | none => [] | some _ => [mk],
    prev := match y.ch with | none => [] | some (_, m) => (Nat.bits m).map tkb }

def encI (p : ℕ × Bool) : List Al := List.replicate p.1 (ty BSym.zero) ++ [if p.2 then ty BSym.minus else ty BSym.one]

def st' (rev : Bool) (s dd : ℕ) : ℕ × ℕ := if rev then (dd, s) else (s, dd)

def okf (d : Bool) (y : Ys) (p : ℕ × Bool) : Prop :=
  match arcOf y.fl p.1 with
  | none => False
  | some (s, dd, _) => ¬ (d = true ∧ p.2 = true) ∧ p.1 < y.vis.length ∧
      (match y.ch with | none => True | some (_, m) => m = (st' p.2 s dd).1)

def nxt (y : Ys) (p : ℕ × Bool) : Ys :=
  match arcOf y.fl p.1 with
  | none => y
  | some (s, dd, w) =>
    { y with vis := y.vis.set p.1 true, a := addBits y.a (Nat.bits w),
             ch := some (match y.ch with | none => (st' p.2 s dd).1 | some (f, _) => f, (st' p.2 s dd).2) }


def zz (y : Ys) (p : ℕ × Bool) (rest : List Al) : Z := { toZ y with t := encI p ++ rest }

lemma ty_one_ne_minus : ty BSym.one ≠ ty BSym.minus := by simp [ty]

lemma rep_inj {α : Type} (z a b : α) (ha : a ≠ z) (hb : b ≠ z) : ∀ (i j : ℕ) (r r' : List α),
    List.replicate i z ++ a :: r = List.replicate j z ++ b :: r' → i = j ∧ a = b ∧ r = r'
  | 0, 0, r, r', h => by simp at h; exact ⟨rfl, h.1, h.2⟩
  | 0, j + 1, r, r', h => by simp [List.replicate_succ] at h; exact absurd h.1 ha
  | i + 1, 0, r, r', h => by simp [List.replicate_succ] at h; exact absurd h.1.symm hb
  | i + 1, j + 1, r, r', h => by
    simp [List.replicate_succ] at h
    have := rep_inj z a b ha hb i j r r' h
    exact ⟨by omega, this.2⟩

lemma core_none (d : Bool) (y : Ys) (i : ℕ) (rev : Bool) (rest : List Al) (harc : arcOf y.fl i = none) :
    ¬ (rR d).ok (Zs (zz y (i, rev) rest)) := by
  intro hok
  obtain ⟨i', x, rest', b1, b2, b3, wr, hx, hT, hske, hW, c1, c2, c3⟩ :=
    rR_dec d (zz y (i, rev) rest) rfl rfl rfl rfl rfl rfl hok
  have hW' : encFlat (y.fl.drop (4 * i')) = b1.map tkb ++ tk BSym.sep :: (b2.map tkb ++ tk BSym.sep :: (b3.map tkb ++ tk BSym.sep :: wr)) := by
    rw [← skW_enc]; exact hW
  obtain ⟨s, dd, w, r, e, _⟩ := enc_parse3 _ b1 b2 b3 wr c1 c2 c3 hW'
  have hT' : List.replicate i (ty BSym.zero) ++ (if rev then ty BSym.minus else ty BSym.one) :: rest = List.replicate i' (ty BSym.zero) ++ x :: rest' := by
    simpa [zz, encI] using hT
  have hi := (rep_inj (ty BSym.zero) _ x (by cases rev <;> simp [ty]) (by rcases hx with rfl | rfl <;> simp [ty]) i i' _ _ hT').1
  subst hi
  exact arcOf_none _ _ harc s dd w r e


def xr (rev : Bool) : Al := if rev then ty BSym.minus else ty BSym.one

lemma xr_minus (rev : Bool) : (xr rev = ty BSym.minus) ↔ rev = true := by
  cases rev <;> simp [xr, ty]

lemma Z4_tx (z : Z) (i : ℕ) (rev : Bool) (rest : List Al) (s dd w : ℕ) :
    (Z4 z i (xr rev) rest (Nat.bits s) (Nat.bits dd) (Nat.bits w)).tx = (Nat.bits (st' rev s dd).1).map tkb ∧
    (Z4 z i (xr rev) rest (Nat.bits s) (Nat.bits dd) (Nat.bits w)).hx = (Nat.bits (st' rev s dd).2).map tkb := by
  cases rev <;> simp [Z4, xr, st', ty]

lemma core_some (d : Bool) (y : Ys) (i : ℕ) (rev : Bool) (rest : List Al) (s dd w : ℕ)
    (harc : arcOf y.fl i = some (s, dd, w)) :
    ((rR d).ok (Zs (zz y (i, rev) rest)) ↔ okf d y (i, rev)) ∧
    (okf d y (i, rev) → (rR d).T (Zs (zz y (i, rev) rest)) = Zs { toZ (nxt y (i, rev)) with t := rest }) := by
  obtain ⟨r, hr⟩ := arcOf_some _ _ _ _ _ harc
  have hlen : 4 * i < y.fl.length := by
    by_contra hh
    rw [List.drop_eq_nil_of_le (by omega)] at hr
    simp at hr
  have hske : skE (zz y (i, rev) rest).wa (4 * i) = 0 := by
    simp [zz, toZ, skE_enc]; omega
  have hW : skW (zz y (i, rev) rest).wa (4 * i) = (Nat.bits s).map tkb ++ tk BSym.sep :: ((Nat.bits dd).map tkb ++ tk BSym.sep :: ((Nat.bits w).map tkb ++ tk BSym.sep :: encFlat r)) := by
    simp [zz, toZ, skW_enc, hr, encFlat]
  have hx : xr rev = ty BSym.one ∨ xr rev = ty BSym.minus := by cases rev <;> simp [xr]
  have hT : (zz y (i, rev) rest).t = List.replicate i (ty BSym.zero) ++ xr rev :: rest := by
    simp [zz, encI, xr]
  obtain ⟨h4x, h4h⟩ := Z4_tx (zz y (i, rev) rest) i rev rest s dd w
  cases hch : y.ch with
  | none =>
    obtain ⟨c1, c2⟩ := rC_first (Z4 (zz y (i, rev) rest) i (xr rev) rest (Nat.bits s) (Nat.bits dd) (Nat.bits w)) _ _ h4x h4h
      (by simp [Z4, zz, toZ, hch]) (by simp [Z4, zz, toZ, hch])
    have key := rR_calc d (zz y (i, rev) rest) i (xr rev) rest (Nat.bits s) (Nat.bits dd) (Nat.bits w) (encFlat r) y.vis y.a hx hT
      rfl rfl rfl rfl rfl rfl rfl rfl rfl hske hW (canon_bits _) (canon_bits _) (canon_bits _)
      True _ _ _ ⟨⟨fun _ => trivial, fun _ => c1⟩, fun _ => c2⟩
    have hok : okf d y (i, rev) ↔ (¬ (d = true ∧ xr rev = ty BSym.minus)) ∧ True ∧ i < y.vis.length := by
      simp [okf, harc, hch, xr_minus]
    rw [hok]
    refine ⟨key.1, fun h => ?_⟩
    rw [key.2 (key.1.2 h)]
    simp [toZ, nxt, harc, hch, Z5, st']
    rfl
  | some fm =>
    obtain ⟨fi, m⟩ := fm
    have hn := rC_next (Z4 (zz y (i, rev) rest) i (xr rev) rest (Nat.bits s) (Nat.bits dd) (Nat.bits w)) m _ _ h4x
      (by simp [Z4, zz, toZ, hch]) (by simp [Z4, zz, toZ, hch]) h4h
    have key := rR_calc d (zz y (i, rev) rest) i (xr rev) rest (Nat.bits s) (Nat.bits dd) (Nat.bits w) (encFlat r) y.vis y.a hx hT
      rfl rfl rfl rfl rfl rfl rfl rfl rfl hske hW (canon_bits _) (canon_bits _) (canon_bits _)
      (m = (st' rev s dd).1) (zz y (i, rev) rest).first (zz y (i, rev) rest).fst ((Nat.bits (st' rev s dd).2).map tkb)
      ⟨hn.1, fun h => by rw [hn.2 h]; rfl⟩
    have hok : okf d y (i, rev) ↔ (¬ (d = true ∧ xr rev = ty BSym.minus)) ∧ m = (st' rev s dd).1 ∧ i < y.vis.length := by
      simp only [okf, harc, hch, xr_minus]
      tauto
    rw [hok]
    refine ⟨key.1, fun h => ?_⟩
    rw [key.2 (key.1.2 h)]
    simp [toZ, nxt, harc, hch, Z5, zz]


lemma rR_pre (d : Bool) : ∀ s, (rR d).pre s := by
  unfold rR rA rB MID rC rM swapG
  repeat' first
    | (intro s; exact cmpLt_pre _ _ _ s)
    | (intro s; exact addG_pre _ _ _ s)
    | apply seq_pre_all
    | apply branch_pre_all
    | (intro s; trivial)


lemma core (d : Bool) (y : Ys) (p : ℕ × Bool) (rest : List Al) :
    ((rR d).ok (Zs (zz y p rest)) ↔ okf d y p) ∧
    (okf d y p → (rR d).T (Zs (zz y p rest)) = Zs { toZ (nxt y p) with t := rest }) := by
  obtain ⟨i, rev⟩ := p
  cases harc : arcOf y.fl i with
  | none =>
    refine ⟨⟨fun h => absurd h (core_none d y i rev rest harc), fun h => by simp [okf, harc] at h⟩, fun h => by simp [okf, harc] at h⟩
  | some t =>
    obtain ⟨s, dd, w⟩ := t
    exact core_some d y i rev rest s dd w harc

lemma len_addBits (a b : List Bool) : (addBits a b).length ≤ max a.length b.length + 1 := by
  unfold addBits
  rw [List.length_append, abits_len]
  split <;> simp

def VvR (yv : List Al) : Prop := ∀ a ∈ yv, ∃ b, a = ty b

def E0R (y : Ys) : St := Zs (toZ y)

def potR (s : St) : ℕ := S s + ((s Reg.KP).length - (s Reg.PP).length) +
  ((s Reg.KP).length - (s Reg.TC).length) + ((s Reg.KP).length - (s Reg.T2).length)

lemma E0R_T (y : Ys) (p : ℕ × Bool) (rest : List Al) : EfR Reg.T E0R y (encI p ++ rest) = Zs (zz y p rest) := by
  simp [EfR, E0R, zz]


lemma S_E0R (y : Ys) : S (E0R y) = y.nb.length + (encFlat y.fl).length + (y.vis.map tyb).length + (y.a.map tkb).length +
    (toZ y).prev.length + (toZ y).first.length + (toZ y).fst.length := by
  have h := S_Zs (toZ y)
  have e : S (E0R y) = S (Zs (toZ y)) := rfl
  rw [e, h]
  simp [toZ]

lemma E0R_KP (y : Ys) : E0R y Reg.KP = encFlat y.fl := rfl
lemma E0R_PP (y : Ys) : E0R y Reg.PP = y.a.map tkb := rfl
lemma E0R_TC (y : Ys) : E0R y Reg.TC = (toZ y).prev := rfl
lemma E0R_T2 (y : Ys) : E0R y Reg.T2 = (toZ y).first := rfl

lemma potL_R (y : Ys) : potR (E0R y) ≤ 4 * S (E0R y) + 6 := by
  have h := S_E0R y
  unfold potR
  rw [E0R_KP, E0R_PP, E0R_TC, E0R_T2]
  omega


lemma arc_mem (fl : List ℕ) (i s dd w : ℕ) (h : arcOf fl i = some (s, dd, w)) : s ∈ fl ∧ dd ∈ fl ∧ w ∈ fl := by
  obtain ⟨r, hr⟩ := arcOf_some _ _ _ _ _ h
  have : ∀ x, x ∈ fl.drop (4 * i) → x ∈ fl := fun x hx => List.mem_of_mem_drop hx
  rw [hr] at this
  exact ⟨this s (by simp), this dd (by simp), this w (by simp)⟩

lemma st'_mem (rev : Bool) (s dd : ℕ) : ((st' rev s dd).1 = s ∧ (st' rev s dd).2 = dd) ∨ ((st' rev s dd).1 = dd ∧ (st' rev s dd).2 = s) := by
  cases rev <;> simp [st']

lemma potG_R (d : Bool) (y : Ys) (p : ℕ × Bool) (h : okf d y p) :
    potR (E0R (nxt y p)) ≤ potR (E0R y) + 4 * (encI p).length := by
  obtain ⟨i, rev⟩ := p
  cases harc : arcOf y.fl i with
  | none => simp [okf, harc] at h
  | some t =>
    obtain ⟨s, dd, w⟩ := t
    obtain ⟨ms, md, mw⟩ := arc_mem _ _ _ _ _ harc
    have l1 := encFlat_len_bits s _ ms
    have l2 := encFlat_len_bits dd _ md
    have l3 := encFlat_len_bits w _ mw
    have l4 := len_addBits y.a (Nat.bits w)
    have ffl : (nxt y (i, rev)).fl = y.fl := by simp [nxt, harc]
    have fv : (nxt y (i, rev)).vis = y.vis.set i true := by simp [nxt, harc]
    have fa : (nxt y (i, rev)).a = addBits y.a (Nat.bits w) := by simp [nxt, harc]
    have fn : (nxt y (i, rev)).nb = y.nb := by simp [nxt, harc]
    have fc : (nxt y (i, rev)).ch = some (match y.ch with | none => (st' rev s dd).1 | some (f, _) => f, (st' rev s dd).2) := by simp [nxt, harc]
    have hS := S_E0R (nxt y (i, rev))
    have hS' := S_E0R y
    unfold potR
    rw [E0R_KP, E0R_PP, E0R_TC, E0R_T2, E0R_KP, E0R_PP, E0R_TC, E0R_T2]
    simp only [ffl, fv, fa, fn] at hS ⊢
    have hm := st'_mem rev s dd
    have hl : (encI (i, rev)).length = i + 1 := by simp [encI]
    rw [hl]
    cases hch : y.ch with
    | none =>
      rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [toZ, fc, fn, hch, e1, e2] at hS hS' ⊢ <;> omega
    | some fm =>
      obtain ⟨fi, m⟩ := fm
      rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [toZ, fc, fn, hch, e1, e2] at hS hS' ⊢ <;> omega


theorem foldH_rR (d : Bool) : FoldH Reg.T VvR encI (rR d) E0R (okf d) nxt potR where
  lrB := by decide
  lrC := by decide
  lrR := by decide
  gi := fun y => ⟨rfl, rfl⟩
  bad := fun y => rfl
  lr0 := fun y => rfl
  pre := rR_pre d
  encne := fun p => by simp [encI]
  vrest := fun p rest h a ha => h a (List.mem_append_right _ ha)
  dec := by
    intro y yv _ hne hno hok
    have e : EfR Reg.T E0R y yv = Zs { toZ y with t := yv } := by simp [EfR, E0R]
    rw [e] at hok
    obtain ⟨i, x, rest, b1, b2, b3, wr, hx, hT, _⟩ := rR_dec d { toZ y with t := yv } rfl rfl rfl rfl rfl rfl hok
    apply hno (i, decide (x = ty BSym.minus)) rest
    have hT' : yv = List.replicate i (ty BSym.zero) ++ x :: rest := hT
    rw [hT']
    rcases hx with rfl | rfl <;> simp [encI, ty]
  stepO := by
    intro y p rest _
    rw [E0R_T]
    exact (core d y p rest).1
  stepT := by
    intro y p rest _ hk
    rw [E0R_T, (core d y p rest).2 hk]
    simp [EfR, E0R]
  potS := fun y => by unfold potR; omega
  potG := fun y p h => potG_R d y p h
  potL := fun y => potL_R y

end Stk

end Sec_RPV7

section Sec_RPV8
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma stC_calc_w_rq (z : Z) (bl : List Bool) (rest : List Al)
    (hW : z.w = bl.map tkb ++ tk BSym.sep :: rest) (hc : canon bl) :
    (stC Reg.W Reg.IN).ok (Zs z) ∧ (stC Reg.W Reg.IN).T (Zs z) = Zs { z with w := rest, rq := bl.map tkb ++ z.rq } := by
  obtain ⟨h1, h2⟩ := stC_calc Reg.W Reg.IN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Zs z) bl rest hW rfl hc
  refine ⟨h1, ?_⟩
  funext r; rw [h2]; cases r <;> simp [Zs]

lemma stC_dec_w_rq (z : Z) (h : (stC Reg.W Reg.IN).ok (Zs z)) :
    ∃ bl rest, popNum z.w = some (bl, rest) :=
  stC_dec Reg.W Reg.IN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Zs z) rfl h

def markNotOne : (Reg → Option Al) → Bool := fun h =>
  match h Reg.NC with | some x => !(decide (x = ty BSym.one)) | none => true

def cZ4 (z : Z) (s d wt r : ℕ) (rest : List ℕ) : Z :=
  { z with w := encFlat rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb }

def cA : GB :=
  (stC Reg.W Reg.TM).seq <| (stC Reg.W Reg.TT).seq <| (stC Reg.W Reg.TR).seq <| (stC Reg.W Reg.IN).seq <|
  (cmpLt Reg.TM Reg.N).seq <| (bBad (topN Reg.H)).seq <| (cmpLt Reg.TT Reg.N).seq <| (bBad (topN Reg.H))

def cIn : GB :=
  (GB.branch (topN Reg.IN) (bClear Reg.IN) ((bPop Reg.IN).seq <| (bBad (topS Reg.IN)).seq <| bBad markNotOne)).seq <|
  (bPop Reg.NC)

def cEnd : GB := (bClear Reg.TM).seq <| (bClear Reg.TT).seq <| (bClear Reg.TR).seq <| bClear Reg.H

def cB : GB := cA.seq (cIn.seq cEnd)

lemma cEnd_calc (z : Z) : cEnd.ok (Zs z) ∧ cEnd.T (Zs z) = Zs { z with tx := [], hx := [], wx := [], h := [] } := by
  refine ⟨by simp [cEnd], ?_⟩
  simp only [cEnd, seq_T, bClear_T]
  funext r; cases r <;> first | rfl | simp [Zs, gClear, upd_apply]

lemma val_pos_last : ∀ l : List Bool, l.getLast? = some true → 1 ≤ val l
  | [], h => by simp at h
  | [b], h => by simp at h; subst h; simp [val]
  | b :: c :: l', h => by
    have h' : (c :: l').getLast? = some true := by simpa [List.getLast?_cons_cons] using h
    have := val_pos_last _ h'
    rw [val_cons]; omega

lemma cIn_calc (z : Z) (r : ℕ) (b : Bool) (vrest : List Al) (hrq : z.rq = (Nat.bits r).map tkb) (hv : z.vis = tyb b :: vrest) :
    (cIn.ok (Zs z) ↔ r ≤ 1 ∧ (r = 1 → b = true)) ∧ (cIn.ok (Zs z) → cIn.T (Zs z) = Zs { z with rq := [], vis := vrest }) := by
  have hcases : (r = 0 ∧ Nat.bits r = []) ∨ (r = 1 ∧ Nat.bits r = [true]) ∨ ∃ a c l, Nat.bits r = a :: c :: l := by
    have h1 := val_bits r
    have h2 := canon_bits r
    cases hb : Nat.bits r with
    | nil => left; rw [hb] at h1; simp [val] at h1; exact ⟨h1.symm, rfl⟩
    | cons a l =>
      cases l with
      | nil =>
        right; left
        rw [hb] at h1 h2
        simp [canon] at h2
        subst h2
        simp [val] at h1
        exact ⟨h1.symm, rfl⟩
      | cons c l' => right; right; exact ⟨a, c, l', rfl⟩
  have hv' : (Zs z) Reg.NC = tyb b :: vrest := hv
  rcases hcases with ⟨hr0, hb⟩ | ⟨hr1, hb⟩ | ⟨a, c, l, hb⟩
  · have hq : (Zs z) Reg.IN = [] := by rw [show (Zs z) Reg.IN = z.rq from rfl, hrq, hb]; rfl
    have hT : cIn.T (Zs z) = Zs { z with rq := [], vis := vrest } := by
      simp only [cIn, seq_T, br_T, bClear_T, bPop_T]
      simp [topN, hd, hq, gClear, gPop]
      funext r'; cases r' <;> simp [Zs, upd_apply, hv, hrq, hb]
    refine ⟨?_, fun _ => hT⟩
    simp only [cIn, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok]
    simp [topN, hd, hq, hr0]
  · have hq : (Zs z) Reg.IN = [tkb true] := by rw [show (Zs z) Reg.IN = z.rq from rfl, hrq, hb]; rfl
    have hT : cIn.T (Zs z) = Zs { z with rq := [], vis := vrest } := by
      simp only [cIn, seq_T, br_T, bClear_T, bPop_T, bBad_T]
      simp [topN, hd, hq, gClear, gPop]
      funext r'; cases r' <;> simp [Zs, upd_apply, hv, hrq, hb]
    refine ⟨?_, fun _ => hT⟩
    simp only [cIn, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok, bBad_ok, bBad_T]
    cases b <;> simp [topN, topS, hd, hq, hr1, gPop, markNotOne, hv', tyb, ty, upd_apply]
  · have hq : (Zs z) Reg.IN = tkb a :: tkb c :: l.map tkb := by rw [show (Zs z) Reg.IN = z.rq from rfl, hrq, hb]; rfl
    have hr2 : ¬ (r ≤ 1) := by
      intro hle
      have h1 := val_bits r
      rw [hb] at h1
      have h3 := canon_bits r
      rw [hb] at h3
      have : 2 ≤ val (a :: c :: l) := by
        have e : (c :: l).getLast? = some true := by
          rcases h3 with h3 | h3
          · simpa [List.getLast?_cons_cons] using h3
          · simp at h3
        have := val_pos_last _ e
        rw [val_cons]; omega
      omega
    refine ⟨⟨fun h => ?_, fun h => absurd h.1 hr2⟩, fun h => ?_⟩
    · exfalso
      simp only [cIn, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok, bBad_ok, bBad_T] at h
      simp [topN, topS, hd, hq, gPop] at h
    · exfalso
      simp only [cIn, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok, bBad_ok, bBad_T] at h
      simp [topN, topS, hd, hq, gPop] at h

lemma cA_calc (z : Z) (s d wt r n : ℕ) (rest : List ℕ)
    (hw : z.w = encFlat (s :: d :: wt :: r :: rest)) (hnb : z.nb = (Nat.bits n).map tkb)
    (htx : z.tx = []) (hhx : z.hx = []) (hwx : z.wx = []) (hrq : z.rq = []) (hh : z.h = []) :
    (cA.ok (Zs z) ↔ s < n ∧ d < n) ∧
    (cA.ok (Zs z) → cA.T (Zs z) = Zs { z with w := encFlat rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) }) := by
  obtain ⟨a1, a2⟩ := stC_calc_w_tx z (Nat.bits s) (encFlat (d :: wt :: r :: rest)) (by rw [hw]; simp [encFlat]) (canon_bits _)
  obtain ⟨b1, b2⟩ := stC_calc_w_hx { z with w := encFlat (d :: wt :: r :: rest), tx := (Nat.bits s).map tkb } (Nat.bits d) (encFlat (wt :: r :: rest)) (by simp [encFlat]) (canon_bits _)
  obtain ⟨c1, c2⟩ := stC_calc_w_wx { z with w := encFlat (wt :: r :: rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb } (Nat.bits wt) (encFlat (r :: rest)) (by simp [encFlat]) (canon_bits _)
  obtain ⟨d1, d2⟩ := stC_calc_w_rq { z with w := encFlat (r :: rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb } (Nat.bits r) (encFlat rest) (by simp [encFlat]) (canon_bits _)
  have a2' : (stC Reg.W Reg.TM).T (Zs z) = Zs { z with w := encFlat (d :: wt :: r :: rest), tx := (Nat.bits s).map tkb } := by rw [a2, htx]; simp
  have b2' : (stC Reg.W Reg.TT).T (Zs { z with w := encFlat (d :: wt :: r :: rest), tx := (Nat.bits s).map tkb }) = Zs { z with w := encFlat (wt :: r :: rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb } := by rw [b2, hhx]; simp
  have c2' : (stC Reg.W Reg.TR).T (Zs { z with w := encFlat (wt :: r :: rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb }) = Zs { z with w := encFlat (r :: rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb } := by rw [c2, hwx]; simp
  have d2' : (stC Reg.W Reg.IN).T (Zs { z with w := encFlat (r :: rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb }) = Zs (cZ4 z s d wt r rest) := by rw [d2, hrq]; simp [cZ4]
  obtain ⟨e1, e2⟩ := cmpLt_spec Reg.TM Reg.N (by decide) (Zs (cZ4 z s d wt r rest)) (Nat.bits s) (Nat.bits n) (by simp [Zs, cZ4]) (by simp [Zs, cZ4, hnb]) rfl rfl
  obtain ⟨f1, f2⟩ := cmpLt_spec Reg.TT Reg.N (by decide) (Zs { cZ4 z s d wt r rest with h := flag (decide (s < n)) }) (Nat.bits d) (Nat.bits n) (by simp [Zs, cZ4]) (by simp [Zs, cZ4, hnb]) rfl rfl
  simp only [val_bits] at e2 f2
  rw [upd_Zs_h] at e2 f2
  simp only [cA, seq_ok, seq_T, a2', b2', c2', d2', e2, f2, a1, b1, c1, d1, e1, f1, bBad_ok, bBad_T, true_and]
  simp only [topN, hd, flag, Zs, cZ4]
  by_cases hs : s < n <;> by_cases hd : d < n <;> simp [hs, hd]

lemma cB_calc (z : Z) (s d wt r n : ℕ) (rest : List ℕ) (b : Bool) (vrest : List Al)
    (hw : z.w = encFlat (s :: d :: wt :: r :: rest)) (hnb : z.nb = (Nat.bits n).map tkb)
    (hv : z.vis = tyb b :: vrest) (htx : z.tx = []) (hhx : z.hx = []) (hwx : z.wx = []) (hrq : z.rq = []) (hh : z.h = []) :
    (cB.ok (Zs z) ↔ s < n ∧ d < n ∧ r ≤ 1 ∧ (r = 1 → b = true)) ∧
    (cB.ok (Zs z) → cB.T (Zs z) = Zs { z with w := encFlat rest, vis := vrest, tx := [], hx := [], wx := [], rq := [], h := [] }) := by
  obtain ⟨a1, a2⟩ := cA_calc z s d wt r n rest hw hnb htx hhx hwx hrq hh
  obtain ⟨b1, b2⟩ := cIn_calc { z with w := encFlat rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) } r b vrest rfl hv
  obtain ⟨c1, c2⟩ := cEnd_calc { { z with w := encFlat rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) } with rq := [], vis := vrest }
  have hok : cB.ok (Zs z) ↔ s < n ∧ d < n ∧ r ≤ 1 ∧ (r = 1 → b = true) := by
    simp only [cB, seq_ok, seq_T]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨(a1.1 h1).1, (a1.1 h1).2, (b1.1 (by rw [a2 h1] at h2; exact h2)).1, (b1.1 (by rw [a2 h1] at h2; exact h2)).2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have hA : cA.ok (Zs z) := a1.2 ⟨h1, h2⟩
      refine ⟨hA, ?_, ?_⟩
      · rw [a2 hA]; exact b1.2 ⟨h3, h4⟩
      · rw [a2 hA, b2 (b1.2 ⟨h3, h4⟩)]
        exact c1
  refine ⟨hok, fun h => ?_⟩
  have hA : cA.ok (Zs z) := (hok.1 h) |> fun h' => a1.2 ⟨h'.1, h'.2.1⟩
  have hI := b1.2 ⟨(hok.1 h).2.2.1, (hok.1 h).2.2.2⟩
  simp only [cB, seq_T]
  rw [a2 hA, b2 hI, c2]

lemma cB_pre : ∀ s, cB.pre s := by
  unfold cB cA cIn cEnd
  repeat' first
    | (intro s; exact cmpLt_pre _ _ _ s)
    | apply seq_pre_all
    | apply branch_pre_all
    | (intro s; trivial)

def VvC (yv : List Al) : Prop := ∀ a ∈ yv, ∃ b, a = tyb b

def encC (b : Bool) : List Al := [tyb b]

def okC (n : ℕ) (y : List ℕ) (b : Bool) : Prop :=
  match y with
  | s :: d :: _ :: r :: _ => s < n ∧ d < n ∧ r ≤ 1 ∧ (r = 1 → b = true)
  | _ => False

def nxtC (y : List ℕ) (_ : Bool) : List ℕ := y.drop 4

def E0C (P : Z) (y : List ℕ) : St :=
  Zs { P with w := encFlat y, vis := [], tx := [], hx := [], wx := [], rq := [], h := [] }

lemma encFlat_drop_len (k : ℕ) : ∀ l : List ℕ, (encFlat (l.drop k)).length ≤ (encFlat l).length
  | [] => by simp
  | a :: l => by
    cases k with
    | zero => simp
    | succ k =>
      have := encFlat_drop_len k l
      simp [encFlat]; omega

lemma S_E0C (P : Z) (y : List ℕ) : S (E0C P y) = (encFlat y).length + S (E0C P []) := by
  unfold E0C
  rw [S_Zs, S_Zs]
  simp [encFlat]
  omega

lemma EfR_E0C (P : Z) (y : List ℕ) (yv : List Al) :
    EfR Reg.NC (E0C P) y yv = Zs { P with w := encFlat y, vis := yv, tx := [], hx := [], wx := [], rq := [], h := [] } := by
  simp [EfR, E0C]

lemma cA_dec (z : Z) (y : List ℕ) (hw : z.w = encFlat y) (hlen : y.length < 4) : ¬ cA.ok (Zs z) := by
  intro hok
  simp only [cA, seq_ok, seq_T] at hok
  obtain ⟨o1, o2, o3, o4, _⟩ := hok
  rcases y with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · obtain ⟨bl, r, hp⟩ := stC_dec_w_tx z o1
    simp [hw, encFlat, popNum] at hp
  · obtain ⟨c1, c2⟩ := stC_calc_w_tx z (Nat.bits a) (encFlat []) (by rw [hw]; simp [encFlat]) (canon_bits _)
    rw [c2] at o2
    obtain ⟨bl, r, hp⟩ := stC_dec_w_hx _ o2
    simp [encFlat, popNum] at hp
  · obtain ⟨c1, c2⟩ := stC_calc_w_tx z (Nat.bits a) (encFlat [b]) (by rw [hw]; simp [encFlat]) (canon_bits _)
    obtain ⟨d1, d2⟩ := stC_calc_w_hx { z with w := encFlat [b], tx := (Nat.bits a).map tkb ++ z.tx } (Nat.bits b) (encFlat []) (by simp [encFlat]) (canon_bits _)
    rw [c2] at o2
    rw [c2, d2] at o3
    obtain ⟨bl, r, hp⟩ := stC_dec_w_wx _ o3
    simp [encFlat, popNum] at hp
  · obtain ⟨c1, c2⟩ := stC_calc_w_tx z (Nat.bits a) (encFlat [b, c]) (by rw [hw]; simp [encFlat]) (canon_bits _)
    obtain ⟨d1, d2⟩ := stC_calc_w_hx { z with w := encFlat [b, c], tx := (Nat.bits a).map tkb ++ z.tx } (Nat.bits b) (encFlat [c]) (by simp [encFlat]) (canon_bits _)
    obtain ⟨e1, e2⟩ := stC_calc_w_wx { z with w := encFlat [c], tx := (Nat.bits a).map tkb ++ z.tx, hx := (Nat.bits b).map tkb ++ z.hx } (Nat.bits c) (encFlat []) (by simp [encFlat]) (canon_bits _)
    rw [c2] at o2
    rw [c2, d2] at o3
    rw [c2, d2, e2] at o4
    obtain ⟨bl, r, hp⟩ := stC_dec_w_rq _ o4
    simp [encFlat, popNum] at hp
  · exact absurd hlen (by simp)

lemma coreC (P : Z) (n : ℕ) (hnb : P.nb = (Nat.bits n).map tkb) (y : List ℕ) (b : Bool) (rest : List Al) :
    (cB.ok (EfR Reg.NC (E0C P) y (encC b ++ rest)) ↔ okC n y b) ∧
    (okC n y b → cB.T (EfR Reg.NC (E0C P) y (encC b ++ rest)) = EfR Reg.NC (E0C P) (nxtC y b) rest) := by
  rw [EfR_E0C]
  match y with
  | s :: d :: wt :: r :: rest' =>
    have := cB_calc { P with w := encFlat (s :: d :: wt :: r :: rest'), vis := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] } s d wt r n rest' b rest rfl hnb rfl rfl rfl rfl rfl rfl
    refine ⟨this.1, fun h => ?_⟩
    rw [this.2 (this.1.2 h), EfR_E0C]
    simp [nxtC]
  | [] =>
    have := cA_dec { P with w := encFlat [], vis := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] } [] rfl (by simp)
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · exact (this (by simp only [cB, seq_ok] at h; exact h.1)).elim
    · exact absurd h (by simp [okC])
    · exact absurd h (by simp [okC])
  | [a] =>
    have := cA_dec { P with w := encFlat [a], vis := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] } [a] rfl (by simp)
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · exact (this (by simp only [cB, seq_ok] at h; exact h.1)).elim
    · exact absurd h (by simp [okC])
    · exact absurd h (by simp [okC])
  | [a, c] =>
    have := cA_dec { P with w := encFlat [a, c], vis := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] } [a, c] rfl (by simp)
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · exact (this (by simp only [cB, seq_ok] at h; exact h.1)).elim
    · exact absurd h (by simp [okC])
    · exact absurd h (by simp [okC])
  | [a, c, e] =>
    have := cA_dec { P with w := encFlat [a, c, e], vis := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] } [a, c, e] rfl (by simp)
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · exact (this (by simp only [cB, seq_ok] at h; exact h.1)).elim
    · exact absurd h (by simp [okC])
    · exact absurd h (by simp [okC])

theorem foldH_cB (P : Z) (n : ℕ) (hnb : P.nb = (Nat.bits n).map tkb) :
    FoldH Reg.NC VvC encC cB (E0C P) (okC n) nxtC S where
  lrB := by decide
  lrC := by decide
  lrR := by decide
  gi := fun y => ⟨rfl, rfl⟩
  bad := fun y => rfl
  lr0 := fun y => rfl
  pre := cB_pre
  encne := fun p => by simp [encC]
  vrest := fun p rest h a ha => h a (List.mem_append_right _ ha)
  dec := by
    intro y yv hv hne hno hok
    cases yv with
    | nil => exact hne rfl
    | cons a rest =>
      obtain ⟨b, hb⟩ := hv a (by simp)
      exact hno b rest (by simp [encC, hb])
  stepO := fun y p rest _ => (coreC P n hnb y p rest).1
  stepT := fun y p rest _ hk => (coreC P n hnb y p rest).2 hk
  potS := fun y => le_refl _
  potG := by
    intro y p _
    have h1 := S_E0C P y
    have h2 := S_E0C P (nxtC y p)
    have h3 := encFlat_drop_len 4 y
    simp only [nxtC] at h2 ⊢
    simp [encC]
    omega
  potL := fun y => by omega

end Stk

end Sec_RPV8

section Sec_RPV9
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def cCl : GB :=
  (cmpLt Reg.TC Reg.T2).seq <| (bBad (topS Reg.H)).seq <| (cmpLt Reg.T2 Reg.TC).seq <| (bBad (topS Reg.H))

def cFin : GB :=
  (stC Reg.W Reg.K).seq <| (bBad (topS Reg.W)).seq <| (cmpLt Reg.K Reg.PP).seq <| (bBad (topS Reg.H)).seq <|
  GB.branch (topN Reg.K2) (bClear Reg.H) cCl

lemma cFin_pre : ∀ s, cFin.pre s := by
  intro s
  unfold cFin cCl
  repeat' first | (intro s; exact cmpLt_pre _ _ _ s) | apply seq_pre_all | apply branch_pre_all | (intro s; trivial)

lemma cCl_ok (z : Z) (m f : ℕ) (hprev : z.prev = (Nat.bits m).map tkb) (hfirst : z.first = (Nat.bits f).map tkb) :
    cCl.ok (Zs z) ↔ m = f := by
  obtain ⟨a1, a2⟩ := cmpLt_spec Reg.TC Reg.T2 (by decide) (Zs z) (Nat.bits m) (Nat.bits f) (by simp [Zs, hprev]) (by simp [Zs, hfirst]) rfl rfl
  obtain ⟨b1, b2⟩ := cmpLt_spec Reg.T2 Reg.TC (by decide) (Zs { z with h := flag (decide (m < f)) }) (Nat.bits f) (Nat.bits m) (by simp [Zs, hfirst]) (by simp [Zs, hprev]) rfl rfl
  simp only [val_bits] at a2 b2
  rw [upd_Zs_h] at a2 b2
  simp only [cCl, seq_ok, seq_T, a2, b2, a1, b1, bBad_ok, bBad_T, true_and]
  simp only [topS, hd, Zs, flag]
  by_cases h1 : m < f <;> by_cases h2 : f < m <;> simp [h1, h2] <;> omega

lemma cFin_ok (z : Z) (k : ℕ) (a : List Bool) (ch : Option (ℕ × ℕ))
    (hw : z.w = encFlat [k]) (hkk : z.kk = []) (hacc : z.acc = a.map tkb)
    (hfst : z.fst = match ch with | none => [] | some _ => [mk])
    (hfirst : z.first = match ch with | none => [] | some (f, _) => (Nat.bits f).map tkb)
    (hprev : z.prev = match ch with | none => [] | some (_, m) => (Nat.bits m).map tkb) :
    cFin.ok (Zs z) ↔ ¬ (k < val a) ∧ (match ch with | none => True | some (f, m) => m = f) := by
  obtain ⟨a1, a2⟩ := stC_calc_w_kk z (Nat.bits k) [] (by rw [hw]; simp [encFlat]) (canon_bits _)
  have a2' : (stC Reg.W Reg.K).T (Zs z) = Zs { z with w := [], kk := (Nat.bits k).map tkb } := by rw [a2, hkk]; simp
  obtain ⟨b1, b2⟩ := cmpLt_spec Reg.K Reg.PP (by decide) (Zs { z with w := [], kk := (Nat.bits k).map tkb }) (Nat.bits k) a (by simp [Zs]) (by simp [Zs, hacc]) rfl rfl
  simp only [val_bits] at b2
  rw [upd_Zs_h] at b2
  have hf : ∀ c : Option (ℕ × ℕ), z.fst = (match c with | none => [] | some _ => [mk]) → True := fun _ _ => trivial
  simp only [cFin, seq_ok, seq_T, a2', a1, b1, b2, bBad_ok, bBad_T, true_and, br_ok, br_T]
  simp only [topS, topN, hd, Zs, flag]
  cases ch with
  | none =>
    simp [hfst]
  | some fm =>
    obtain ⟨f, m⟩ := fm
    have key := cCl_ok { z with w := [], kk := (Nat.bits k).map tkb, fst := [mk], h := if k < val a then [mk] else [] } m f (by simpa using hprev) (by simpa using hfirst)
    simp [hfst]
    rw [key]
    omega

end Stk

end Sec_RPV9

section Sec_RPV10
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma S_init (x : List Al) : S (init x) = x.length := by
  unfold S init
  rw [Finset.sum_eq_single Reg.IN]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

def Inv0 (s : St) : Prop := ∃ x, s = init x

def outProg : Prog := .seq (clearProg Reg.OUT) (.branch (topS Reg.BAD) skipP (pushProg Reg.OUT mk))
def outG (s : St) : St := if topS Reg.BAD (hd s) = true then gClear Reg.OUT s else gPush Reg.OUT mk (gClear Reg.OUT s)

lemma gs_out : Gs outProg outG outG (fun _ => True) := by
  have h := Gs.seq (gs_clear Reg.OUT) (Gs.branch (topS Reg.BAD) (Gs.total Gad.skip (fun _ => rfl))
    (gs_push Reg.OUT mk))
  refine Gs.total ?_ (fun s => ?_)
  · exact h.1
  · unfold outG gClear gPush; split_ifs <;> simp [upd_apply, hd]

def bOut : GB := GB.ofGs gs_out

lemma outG_OUT (s : St) : outG s Reg.OUT = if s Reg.BAD = [] then [mk] else [] := by
  unfold outG gClear gPush
  by_cases h : s Reg.BAD = [] <;> simp [h, hd, topS, upd_apply]

def InvF {α : Type} (F : α → St) (P : α → Prop) (s : St) : Prop :=
  Gi s ∧ (s Reg.BAD ≠ [] ∨ ∃ a, P a ∧ s = F a)

lemma step_inv {α β : Type} (b : GB) (F : α → St) (P : α → Prop) (F2 : β → St) (Q : β → Prop)
    (hF : ∀ a, Gi (F a)) (hB : ∀ a, F a Reg.BAD = []) (hpre : ∀ a, P a → b.pre (F a))
    (hnext : ∀ a, P a → b.ok (F a) → ∃ c, Q c ∧ b.T (F a) = F2 c) (s : St) (h : InvF F P s) :
    InvF F2 Q (b.g s) := by
  refine ⟨b.h.1.2 s h.1, ?_⟩
  rcases h.2 with hb | ⟨a, ha, rfl⟩
  · exact Or.inl (b.h.2.1 _ hb)
  · have hh := b.h.2.2.2 (F a) (hF a) (hpre a ha) (hB a)
    by_cases hb : b.g (F a) Reg.BAD = []
    · right
      have ho := hh.1.1 hb
      obtain ⟨c, hc, he⟩ := hnext a ha ho
      exact ⟨c, hc, by rw [hh.2 ho]; exact he⟩
    · exact Or.inl hb

lemma poly_of_prog' (p : Prog) (g : St → St) (hp : PSp Inv0 p g) :
    ∃ k, ∀ x : List Al, ∃ s n, n ≤ x.length ^ k + k ∧
      p.Exec (fun j => if j = Reg.IN then x else []) s n ∧ s = g (init x) := by
  obtain ⟨d, hd⟩ := hp
  obtain ⟨k, hk⟩ := polynomial_absorb (2 ^ d) d 0
  refine ⟨k, fun x => ?_⟩
  obtain ⟨n, hn, ex⟩ := hd (init x) ⟨x, rfl⟩
  refine ⟨g (init x), n, ?_, ex, rfl⟩
  rw [S_init] at hn
  have h1 := hk x.length
  have h2 : (x.length + 2) ^ d ≤ 2 ^ d * (x.length + 1) ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  omega

theorem mem_P_of_prog' (p : Prog) (g : St → St) (hp : PSp Inv0 p g) (L : Lang Al)
    (hL : ∀ x, x ∈ L ↔ g (init x) Reg.OUT ≠ []) : L ∈ P Al := by
  have hpoly : PolyTimeComputable (fun x : List Al => g (init x) Reg.OUT) := by
    obtain ⟨k, hk⟩ := poly_of_prog' p g hp
    refine stack_program_polytime p Reg.IN Reg.OUT _ k (fun x => ?_)
    obtain ⟨s, n, hn, ex, hs⟩ := hk x
    exact ⟨s, n, hn, ex, by rw [hs]⟩
  refine mem_P_of_polyReducible L {w : List Al | w ≠ []} ⟨_, hpoly, fun x => ?_⟩ (neLang_mem_P Al)
  rw [hL]; rfl


end Stk

end Sec_RPV10

section Sec_RPV11
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def cZ4R (z : Z) (s d wt r : ℕ) (rest : List Al) : Z :=
  { z with w := rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb }

lemma cA_calcR (z : Z) (s d wt r n : ℕ) (rest : List Al)
    (hw : z.w = (encFlat [s, d, wt, r] ++ rest)) (hnb : z.nb = (Nat.bits n).map tkb)
    (htx : z.tx = []) (hhx : z.hx = []) (hwx : z.wx = []) (hrq : z.rq = []) (hh : z.h = []) :
    (cA.ok (Zs z) ↔ s < n ∧ d < n) ∧
    (cA.ok (Zs z) → cA.T (Zs z) = Zs { z with w := rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) }) := by
  obtain ⟨a1, a2⟩ := stC_calc_w_tx z (Nat.bits s) ((encFlat [d, wt, r] ++ rest)) (by rw [hw]; simp [encFlat]) (canon_bits _)
  obtain ⟨b1, b2⟩ := stC_calc_w_hx { z with w := (encFlat [d, wt, r] ++ rest), tx := (Nat.bits s).map tkb } (Nat.bits d) ((encFlat [wt, r] ++ rest)) (by simp [encFlat]) (canon_bits _)
  obtain ⟨c1, c2⟩ := stC_calc_w_wx { z with w := (encFlat [wt, r] ++ rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb } (Nat.bits wt) ((encFlat [r] ++ rest)) (by simp [encFlat]) (canon_bits _)
  obtain ⟨d1, d2⟩ := stC_calc_w_rq { z with w := (encFlat [r] ++ rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb } (Nat.bits r) (rest) (by simp [encFlat]) (canon_bits _)
  have a2' : (stC Reg.W Reg.TM).T (Zs z) = Zs { z with w := (encFlat [d, wt, r] ++ rest), tx := (Nat.bits s).map tkb } := by rw [a2, htx]; simp
  have b2' : (stC Reg.W Reg.TT).T (Zs { z with w := (encFlat [d, wt, r] ++ rest), tx := (Nat.bits s).map tkb }) = Zs { z with w := (encFlat [wt, r] ++ rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb } := by rw [b2, hhx]; simp
  have c2' : (stC Reg.W Reg.TR).T (Zs { z with w := (encFlat [wt, r] ++ rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb }) = Zs { z with w := (encFlat [r] ++ rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb } := by rw [c2, hwx]; simp
  have d2' : (stC Reg.W Reg.IN).T (Zs { z with w := (encFlat [r] ++ rest), tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb }) = Zs (cZ4R z s d wt r rest) := by rw [d2, hrq]; simp [cZ4R]
  obtain ⟨e1, e2⟩ := cmpLt_spec Reg.TM Reg.N (by decide) (Zs (cZ4R z s d wt r rest)) (Nat.bits s) (Nat.bits n) (by simp [Zs, cZ4R]) (by simp [Zs, cZ4R, hnb]) rfl rfl
  obtain ⟨f1, f2⟩ := cmpLt_spec Reg.TT Reg.N (by decide) (Zs { cZ4R z s d wt r rest with h := flag (decide (s < n)) }) (Nat.bits d) (Nat.bits n) (by simp [Zs, cZ4R]) (by simp [Zs, cZ4R, hnb]) rfl rfl
  simp only [val_bits] at e2 f2
  rw [upd_Zs_h] at e2 f2
  simp only [cA, seq_ok, seq_T, a2', b2', c2', d2', e2, f2, a1, b1, c1, d1, e1, f1, bBad_ok, bBad_T, true_and]
  simp only [topN, hd, flag, Zs, cZ4R]
  by_cases hs : s < n <;> by_cases hd : d < n <;> simp [hs, hd]

lemma cB_calcR (z : Z) (s d wt r n : ℕ) (rest : List Al) (b : Bool) (vrest : List Al)
    (hw : z.w = (encFlat [s, d, wt, r] ++ rest)) (hnb : z.nb = (Nat.bits n).map tkb)
    (hv : z.vis = tyb b :: vrest) (htx : z.tx = []) (hhx : z.hx = []) (hwx : z.wx = []) (hrq : z.rq = []) (hh : z.h = []) :
    (cB.ok (Zs z) ↔ s < n ∧ d < n ∧ r ≤ 1 ∧ (r = 1 → b = true)) ∧
    (cB.ok (Zs z) → cB.T (Zs z) = Zs { z with w := rest, vis := vrest, tx := [], hx := [], wx := [], rq := [], h := [] }) := by
  obtain ⟨a1, a2⟩ := cA_calcR z s d wt r n rest hw hnb htx hhx hwx hrq hh
  obtain ⟨b1, b2⟩ := cIn_calc { z with w := rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) } r b vrest rfl hv
  obtain ⟨c1, c2⟩ := cEnd_calc { { z with w := rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) } with rq := [], vis := vrest }
  have hok : cB.ok (Zs z) ↔ s < n ∧ d < n ∧ r ≤ 1 ∧ (r = 1 → b = true) := by
    simp only [cB, seq_ok, seq_T]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨(a1.1 h1).1, (a1.1 h1).2, (b1.1 (by rw [a2 h1] at h2; exact h2)).1, (b1.1 (by rw [a2 h1] at h2; exact h2)).2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have hA : cA.ok (Zs z) := a1.2 ⟨h1, h2⟩
      refine ⟨hA, ?_, ?_⟩
      · rw [a2 hA]; exact b1.2 ⟨h3, h4⟩
      · rw [a2 hA, b2 (b1.2 ⟨h3, h4⟩)]
        exact c1
  refine ⟨hok, fun h => ?_⟩
  have hA : cA.ok (Zs z) := (hok.1 h) |> fun h' => a1.2 ⟨h'.1, h'.2.1⟩
  have hI := b1.2 ⟨(hok.1 h).2.2.1, (hok.1 h).2.2.2⟩
  simp only [cB, seq_T]
  rw [a2 hA, b2 hI, c2]


def parse4 (y : List Al) : Option (ℕ × ℕ × ℕ × ℕ × List Al) :=
  match popNum y with
  | none => none
  | some (b1, r1) =>
    match popNum r1 with
    | none => none
    | some (b2, r2) =>
      match popNum r2 with
      | none => none
      | some (b3, r3) =>
        match popNum r3 with
        | none => none
        | some (b4, r4) => some (val b1, val b2, val b3, val b4, r4)

lemma popNum_enc' (n : ℕ) (rest : List Al) : popNum ((Nat.bits n).map tkb ++ tk BSym.sep :: rest) = some (Nat.bits n, rest) :=
  popNum_enc _ _ (canon_bits _)

lemma parse4_enc (s d wt r : ℕ) (rest : List Al) : parse4 (encFlat [s, d, wt, r] ++ rest) = some (s, d, wt, r, rest) := by
  have e : encFlat [s, d, wt, r] ++ rest = (Nat.bits s).map tkb ++ tk BSym.sep :: ((Nat.bits d).map tkb ++ tk BSym.sep :: ((Nat.bits wt).map tkb ++ tk BSym.sep :: ((Nat.bits r).map tkb ++ tk BSym.sep :: rest))) := by
    simp [encFlat]
  simp only [parse4, e, popNum_enc', val_bits]

lemma parse4_some (y : List Al) (s d wt r : ℕ) (rest : List Al) (h : parse4 y = some (s, d, wt, r, rest)) :
    y = encFlat [s, d, wt, r] ++ rest := by
  unfold parse4 at h
  rcases p1 : popNum y with _ | ⟨b1, r1⟩ <;> rw [p1] at h <;> simp only [] at h
  · simp at h
  rcases p2 : popNum r1 with _ | ⟨b2, r2⟩ <;> rw [p2] at h <;> simp only [] at h
  · simp at h
  rcases p3 : popNum r2 with _ | ⟨b3, r3⟩ <;> rw [p3] at h <;> simp only [] at h
  · simp at h
  rcases p4 : popNum r3 with _ | ⟨b4, r4⟩ <;> rw [p4] at h <;> simp only [] at h
  · simp at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨e1, c1⟩ := popNum_some _ _ _ p1
  obtain ⟨e2, c2⟩ := popNum_some _ _ _ p2
  obtain ⟨e3, c3⟩ := popNum_some _ _ _ p3
  obtain ⟨e4, c4⟩ := popNum_some _ _ _ p4
  subst h1 h2 h3 h4 h5
  simp only [encFlat]
  rw [e1, e2, e3, e4, bits_val_of_canon _ c1, bits_val_of_canon _ c2, bits_val_of_canon _ c3, bits_val_of_canon _ c4]
  simp

lemma cA_decR (z : Z) (hok : cA.ok (Zs z)) : ∃ s d wt r rest, parse4 z.w = some (s, d, wt, r, rest) := by
  simp only [cA, seq_ok, seq_T] at hok
  obtain ⟨o1, o2, o3, o4, _⟩ := hok
  obtain ⟨bl1, r1, p1⟩ := stC_dec_w_tx z o1
  obtain ⟨hw1, hc1⟩ := popNum_some _ _ _ p1
  obtain ⟨c1, c2⟩ := stC_calc_w_tx z bl1 r1 hw1 hc1
  rw [c2] at o2
  obtain ⟨bl2, r2, p2⟩ := stC_dec_w_hx _ o2
  obtain ⟨hw2, hc2⟩ := popNum_some _ _ _ p2
  obtain ⟨d1, d2⟩ := stC_calc_w_hx _ bl2 r2 hw2 hc2
  rw [c2, d2] at o3
  obtain ⟨bl3, r3, p3⟩ := stC_dec_w_wx _ o3
  obtain ⟨hw3, hc3⟩ := popNum_some _ _ _ p3
  obtain ⟨e1, e2⟩ := stC_calc_w_wx _ bl3 r3 hw3 hc3
  rw [c2, d2, e2] at o4
  obtain ⟨bl4, r4, p4⟩ := stC_dec_w_rq _ o4
  have p2' : popNum r1 = some (bl2, r2) := p2
  have p3' : popNum r2 = some (bl3, r3) := p3
  have p4' : popNum r3 = some (bl4, r4) := p4
  exact ⟨val bl1, val bl2, val bl3, val bl4, r4, by simp [parse4, p1, p2', p3', p4']⟩

def okCR (n : ℕ) (y : List Al) (b : Bool) : Prop :=
  match parse4 y with
  | some (s, d, _, r, _) => s < n ∧ d < n ∧ r ≤ 1 ∧ (r = 1 → b = true)
  | none => False

def nxtCR (y : List Al) (_ : Bool) : List Al :=
  match parse4 y with
  | some (_, _, _, _, rest) => rest
  | none => y

def E0CR (P : Z) (y : List Al) : St :=
  Zs { P with w := y, vis := [], tx := [], hx := [], wx := [], rq := [], h := [] }

lemma EfR_E0CR (P : Z) (y : List Al) (yv : List Al) :
    EfR Reg.NC (E0CR P) y yv = Zs { P with w := y, vis := yv, tx := [], hx := [], wx := [], rq := [], h := [] } := by
  simp [EfR, E0CR]

lemma coreCR (P : Z) (n : ℕ) (hnb : P.nb = (Nat.bits n).map tkb) (y : List Al) (b : Bool) (rest : List Al) :
    (cB.ok (EfR Reg.NC (E0CR P) y (encC b ++ rest)) ↔ okCR n y b) ∧
    (okCR n y b → cB.T (EfR Reg.NC (E0CR P) y (encC b ++ rest)) = EfR Reg.NC (E0CR P) (nxtCR y b) rest) := by
  rw [EfR_E0CR]
  cases hp : parse4 y with
  | none =>
    refine ⟨⟨fun h => ?_, fun h => by simp [okCR, hp] at h⟩, fun h => by simp [okCR, hp] at h⟩
    have hA : cA.ok (Zs { P with w := y, vis := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] }) := by
      simp only [cB, seq_ok] at h; exact h.1
    obtain ⟨s, d, wt, r, rs, hq⟩ := cA_decR _ hA
    simp [hp] at hq
  | some v =>
    obtain ⟨s, d, wt, r, rs⟩ := v
    have hy := parse4_some _ _ _ _ _ _ hp
    subst hy
    have := cB_calcR { P with w := encFlat [s, d, wt, r] ++ rs, vis := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] } s d wt r n rs b rest rfl hnb rfl rfl rfl rfl rfl rfl
    have hk : okCR n (encFlat [s, d, wt, r] ++ rs) b ↔ s < n ∧ d < n ∧ r ≤ 1 ∧ (r = 1 → b = true) := by
      simp [okCR, parse4_enc]
    refine ⟨this.1.trans hk.symm, fun h => ?_⟩
    rw [this.2 (this.1.2 (hk.1 h)), EfR_E0CR]
    simp [nxtCR, parse4_enc]

lemma S_E0CR (P : Z) (y : List Al) : S (E0CR P y) = y.length + S (E0CR P []) := by
  unfold E0CR
  rw [S_Zs, S_Zs]
  simp
  omega

lemma nxtCR_len (y : List Al) (b : Bool) : (nxtCR y b).length ≤ y.length := by
  unfold nxtCR
  cases hp : parse4 y with
  | none => simp
  | some v =>
    obtain ⟨s, d, wt, r, rs⟩ := v
    have := parse4_some _ _ _ _ _ _ hp
    simp only []
    rw [this]
    simp

theorem foldH_cBR (P : Z) (n : ℕ) (hnb : P.nb = (Nat.bits n).map tkb) :
    FoldH Reg.NC VvC encC cB (E0CR P) (okCR n) nxtCR S where
  lrB := by decide
  lrC := by decide
  lrR := by decide
  gi := fun y => ⟨rfl, rfl⟩
  bad := fun y => rfl
  lr0 := fun y => rfl
  pre := cB_pre
  encne := fun p => by simp [encC]
  vrest := fun p rest h a ha => h a (List.mem_append_right _ ha)
  dec := by
    intro y yv hv hne hno hok
    cases yv with
    | nil => exact hne rfl
    | cons a rest =>
      obtain ⟨b, hb⟩ := hv a (by simp)
      exact hno b rest (by simp [encC, hb])
  stepO := fun y p rest _ => (coreCR P n hnb y p rest).1
  stepT := fun y p rest _ hk => (coreCR P n hnb y p rest).2 hk
  potS := fun y => le_refl _
  potG := by
    intro y p _
    have h1 := S_E0CR P y
    have h2 := S_E0CR P (nxtCR y p)
    have h3 := nxtCR_len y p
    simp [encC]
    omega
  potL := fun y => by omega

def cIn0 : GB :=
  (GB.branch (topN Reg.IN) (bClear Reg.IN) ((bPop Reg.IN).seq <| bBad (topS Reg.IN))).seq (bPop Reg.NC2)

def cBa : GB := cA.seq (cIn0.seq cEnd)

lemma cIn0_calc (z : Z) (r : ℕ) (b : Bool) (vrest : List Al) (hrq : z.rq = (Nat.bits r).map tkb) (hv : z.tv = tyb b :: vrest) :
    (cIn0.ok (Zs z) ↔ r ≤ 1) ∧ (cIn0.ok (Zs z) → cIn0.T (Zs z) = Zs { z with rq := [], tv := vrest }) := by
  have hcases : (r = 0 ∧ Nat.bits r = []) ∨ (r = 1 ∧ Nat.bits r = [true]) ∨ ∃ a c l, Nat.bits r = a :: c :: l := by
    have h1 := val_bits r
    have h2 := canon_bits r
    cases hb : Nat.bits r with
    | nil => left; rw [hb] at h1; simp [val] at h1; exact ⟨h1.symm, rfl⟩
    | cons a l =>
      cases l with
      | nil =>
        right; left
        rw [hb] at h1 h2
        simp [canon] at h2
        subst h2
        simp [val] at h1
        exact ⟨h1.symm, rfl⟩
      | cons c l' => right; right; exact ⟨a, c, l', rfl⟩
  rcases hcases with ⟨hr0, hb⟩ | ⟨hr1, hb⟩ | ⟨a, c, l, hb⟩
  · have hq : (Zs z) Reg.IN = [] := by rw [show (Zs z) Reg.IN = z.rq from rfl, hrq, hb]; rfl
    have hT : cIn0.T (Zs z) = Zs { z with rq := [], tv := vrest } := by
      simp only [cIn0, seq_T, br_T, bClear_T, bPop_T]
      simp [topN, hd, hq, gClear, gPop]
      funext r'; cases r' <;> simp [Zs, upd_apply, hv, hrq, hb]
    refine ⟨?_, fun _ => hT⟩
    simp only [cIn0, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok]
    simp [topN, hd, hq, hr0]
  · have hq : (Zs z) Reg.IN = [tkb true] := by rw [show (Zs z) Reg.IN = z.rq from rfl, hrq, hb]; rfl
    have hT : cIn0.T (Zs z) = Zs { z with rq := [], tv := vrest } := by
      simp only [cIn0, seq_T, br_T, bClear_T, bPop_T, bBad_T]
      simp [topN, hd, hq, gClear, gPop]
      funext r'; cases r' <;> simp [Zs, upd_apply, hv, hrq, hb]
    refine ⟨?_, fun _ => hT⟩
    simp only [cIn0, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok, bBad_ok, bBad_T]
    simp [topN, topS, hd, hq, hr1, gPop, upd_apply]
  · have hq : (Zs z) Reg.IN = tkb a :: tkb c :: l.map tkb := by rw [show (Zs z) Reg.IN = z.rq from rfl, hrq, hb]; rfl
    have hr2 : ¬ (r ≤ 1) := by
      intro hle
      have h1 := val_bits r
      rw [hb] at h1
      have h3 := canon_bits r
      rw [hb] at h3
      have : 2 ≤ val (a :: c :: l) := by
        have e : (c :: l).getLast? = some true := by
          rcases h3 with h3 | h3
          · simpa [List.getLast?_cons_cons] using h3
          · simp at h3
        have := val_pos_last _ e
        rw [val_cons]; omega
      omega
    refine ⟨⟨fun h => ?_, fun h => absurd h hr2⟩, fun h => ?_⟩
    · exfalso
      simp only [cIn0, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok, bBad_ok, bBad_T] at h
      simp [topN, topS, hd, hq, gPop] at h
    · exfalso
      simp only [cIn0, seq_ok, seq_T, br_ok, br_T, bClear_ok, bPop_ok, bBad_ok, bBad_T] at h
      simp [topN, topS, hd, hq, gPop] at h

lemma cBa_calcR (z : Z) (s d wt r n : ℕ) (rest : List Al) (b : Bool) (vrest : List Al)
    (hw : z.w = encFlat [s, d, wt, r] ++ rest) (hnb : z.nb = (Nat.bits n).map tkb) (hv : z.tv = tyb b :: vrest)
    (htx : z.tx = []) (hhx : z.hx = []) (hwx : z.wx = []) (hrq : z.rq = []) (hh : z.h = []) :
    (cBa.ok (Zs z) ↔ s < n ∧ d < n ∧ r ≤ 1) ∧
    (cBa.ok (Zs z) → cBa.T (Zs z) = Zs { z with w := rest, tv := vrest, tx := [], hx := [], wx := [], rq := [], h := [] }) := by
  obtain ⟨a1, a2⟩ := cA_calcR z s d wt r n rest hw hnb htx hhx hwx hrq hh
  obtain ⟨b1, b2⟩ := cIn0_calc { z with w := rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) } r b vrest rfl hv
  obtain ⟨c1, c2⟩ := cEnd_calc { { z with w := rest, tx := (Nat.bits s).map tkb, hx := (Nat.bits d).map tkb, wx := (Nat.bits wt).map tkb, rq := (Nat.bits r).map tkb, h := flag (decide (d < n)) } with rq := [], tv := vrest }
  have hok : cBa.ok (Zs z) ↔ s < n ∧ d < n ∧ r ≤ 1 := by
    simp only [cBa, seq_ok, seq_T]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨(a1.1 h1).1, (a1.1 h1).2, (b1.1 (by rw [a2 h1] at h2; exact h2))⟩
    · rintro ⟨h1, h2, h3⟩
      have hA : cA.ok (Zs z) := a1.2 ⟨h1, h2⟩
      refine ⟨hA, ?_, ?_⟩
      · rw [a2 hA]; exact b1.2 h3
      · rw [a2 hA, b2 (b1.2 h3)]
        exact c1
  refine ⟨hok, fun h => ?_⟩
  have hA : cA.ok (Zs z) := (hok.1 h) |> fun h' => a1.2 ⟨h'.1, h'.2.1⟩
  have hI := b1.2 (hok.1 h).2.2
  simp only [cBa, seq_T]
  rw [a2 hA, b2 hI, c2]

lemma cBa_pre : ∀ s, cBa.pre s := by
  unfold cBa cA cIn0 cEnd
  repeat' first
    | (intro s; exact cmpLt_pre _ _ _ s)
    | apply seq_pre_all
    | apply branch_pre_all
    | (intro s; trivial)

def okAR (n : ℕ) (y : List Al) (_ : Bool) : Prop :=
  match parse4 y with
  | some (s, d, _, r, _) => s < n ∧ d < n ∧ r ≤ 1
  | none => False

def E0AR (P : Z) (y : List Al) : St :=
  Zs { P with w := y, tv := [], tx := [], hx := [], wx := [], rq := [], h := [] }

lemma EfR_E0AR (P : Z) (y : List Al) (yv : List Al) :
    EfR Reg.NC2 (E0AR P) y yv = Zs { P with w := y, tv := yv, tx := [], hx := [], wx := [], rq := [], h := [] } := by
  simp [EfR, E0AR]

lemma coreAR (P : Z) (n : ℕ) (hnb : P.nb = (Nat.bits n).map tkb) (y : List Al) (b : Bool) (rest : List Al) :
    (cBa.ok (EfR Reg.NC2 (E0AR P) y (encC b ++ rest)) ↔ okAR n y b) ∧
    (okAR n y b → cBa.T (EfR Reg.NC2 (E0AR P) y (encC b ++ rest)) = EfR Reg.NC2 (E0AR P) (nxtCR y b) rest) := by
  rw [EfR_E0AR]
  cases hp : parse4 y with
  | none =>
    refine ⟨⟨fun h => ?_, fun h => by simp [okAR, hp] at h⟩, fun h => by simp [okAR, hp] at h⟩
    have hA : cA.ok (Zs { P with w := y, tv := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] }) := by
      simp only [cBa, seq_ok] at h; exact h.1
    obtain ⟨s, d, wt, r, rs, hq⟩ := cA_decR _ hA
    simp [hp] at hq
  | some v =>
    obtain ⟨s, d, wt, r, rs⟩ := v
    have hy := parse4_some _ _ _ _ _ _ hp
    subst hy
    have := cBa_calcR { P with w := encFlat [s, d, wt, r] ++ rs, tv := encC b ++ rest, tx := [], hx := [], wx := [], rq := [], h := [] } s d wt r n rs b rest rfl hnb rfl rfl rfl rfl rfl rfl
    have hk : okAR n (encFlat [s, d, wt, r] ++ rs) b ↔ s < n ∧ d < n ∧ r ≤ 1 := by
      simp [okAR, parse4_enc]
    refine ⟨this.1.trans hk.symm, fun h => ?_⟩
    rw [this.2 (this.1.2 (hk.1 h)), EfR_E0AR]
    simp [nxtCR, parse4_enc]

lemma S_E0AR (P : Z) (y : List Al) : S (E0AR P y) = y.length + S (E0AR P []) := by
  unfold E0AR
  rw [S_Zs, S_Zs]
  simp
  omega

theorem foldH_cBa (P : Z) (n : ℕ) (hnb : P.nb = (Nat.bits n).map tkb) :
    FoldH Reg.NC2 VvC encC cBa (E0AR P) (okAR n) nxtCR S where
  lrB := by decide
  lrC := by decide
  lrR := by decide
  gi := fun y => ⟨rfl, rfl⟩
  bad := fun y => rfl
  lr0 := fun y => rfl
  pre := cBa_pre
  encne := fun p => by simp [encC]
  vrest := fun p rest h a ha => h a (List.mem_append_right _ ha)
  dec := by
    intro y yv hv hne hno hok
    cases yv with
    | nil => exact hne rfl
    | cons a rest =>
      obtain ⟨b, hb⟩ := hv a (by simp)
      exact hno b rest (by simp [encC, hb])
  stepO := fun y p rest _ => (coreAR P n hnb y p rest).1
  stepT := fun y p rest _ hk => (coreAR P n hnb y p rest).2 hk
  potS := fun y => le_refl _
  potG := by
    intro y p _
    have h1 := S_E0AR P y
    have h2 := S_E0AR P (nxtCR y p)
    have h3 := nxtCR_len y p
    simp [encC]
    omega
  potL := fun y => by omega

end Stk

end Sec_RPV11

section Sec_RPV12
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

structure Stage {α β : Type} (F : α → St) (P : α → Prop) (F2 : β → St) (Q : β → Prop) (p : Prog) (g : St → St) : Prop where
  psp : PSp (InvF F P) p g
  inv : ∀ s, InvF F P s → InvF F2 Q (g s)

lemma Stage.gb {α β : Type} (b : GB) (F : α → St) (P : α → Prop) (F2 : β → St) (Q : β → Prop)
    (hF : ∀ a, Gi (F a)) (hB : ∀ a, F a Reg.BAD = []) (hpre : ∀ a, P a → b.pre (F a))
    (hnext : ∀ a, P a → b.ok (F a) → ∃ c, Q c ∧ b.T (F a) = F2 c) : Stage F P F2 Q b.p b.g :=
  ⟨PSp.weaken b.h.1.1 (fun s hs => hs.1), step_inv b F P F2 Q hF hB hpre hnext⟩

lemma Stage.comp {α β γ : Type} {F : α → St} {P : α → Prop} {F2 : β → St} {Q : β → Prop} {F3 : γ → St} {R : γ → Prop}
    {p q : Prog} {g h : St → St} (h1 : Stage F P F2 Q p g) (h2 : Stage F2 Q F3 R q h) :
    Stage F P F3 R (.seq p q) (fun s => h (g s)) :=
  ⟨PSp.seq2 h1.psp h2.psp h1.inv, fun s hs => h2.inv _ (h1.inv s hs)⟩

lemma Stage.fold {α β : Type} {ι Y : Type} {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB}
    {E0 : Y → St} {okf : Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ}
    (h : FoldH LR Vv enc body E0 okf f pot) (F : α → St) (P : α → Prop)
    (Y0 : α → Y) (V0 : α → List Al)
    (hG : ∀ a, P a → Vv (V0 a) ∧ F a = EfR LR E0 (Y0 a) (V0 a))
    (F2 : β → St) (Q : β → Prop)
    (hnext : ∀ a, P a → ∀ l, V0 a = encs enc l → foldOK okf f (Y0 a) l →
      ∃ c, Q c ∧ EfR LR E0 (l.foldl f (Y0 a)) [] = F2 c) :
    Stage F P F2 Q (.loop (ltR LR) body.p) (lrun (ltR LR) body.g (muR LR)) := by
  have hJ : ∀ s, InvF F P s → JR LR Vv E0 s := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    rcases hs.2 with hb | ⟨a, ha, rfl⟩
    · exact Or.inl hb
    · obtain ⟨hv, he⟩ := hG a ha
      exact Or.inr ⟨Y0 a, V0 a, hv, he⟩
  refine ⟨PSp.weaken (fold_PSp h) hJ, fun s hs => ?_⟩
  have hk := lrun_keep h s (hJ s hs)
  refine ⟨hk.1, ?_⟩
  rcases hs.2 with hb | ⟨a, ha, rfl⟩
  · exact Or.inl (hk.2 hb)
  · by_cases hb : lrun (ltR LR) body.g (muR LR) (F a) Reg.BAD = []
    · right
      obtain ⟨hv, he⟩ := hG a ha
      rw [he] at hb ⊢
      obtain ⟨l, hl, hok⟩ := fold_sound h (V0 a).length (V0 a) (Y0 a) le_rfl hv hb
      obtain ⟨c, hc, hce⟩ := hnext a ha l hl hok
      refine ⟨c, hc, ?_⟩
      rw [hl, fold_complete h l (Y0 a) (hl ▸ hv) hok]
      exact hce
    · exact Or.inl hb


lemma fold_PSp_ex {A ι Y : Type} {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB}
    {E0 : A → Y → St} {okf : A → Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ}
    (h : ∀ a, FoldH LR Vv enc body (E0 a) (okf a) f pot) :
    PSp (fun s => ∃ a, JR LR Vv (E0 a) s) (.loop (ltR LR) body.p) (lrun (ltR LR) body.g (muR LR)) := by
  refine PSp.loopC (ltR LR) (lrun (ltR LR) body.g (muR LR)) (muR LR) (PhiR LR pot)
    (PSp.weaken body.h.1.1 (fun s ⟨_, hs⟩ => hs.1)) ?_ (fun s ⟨a, hs⟩ ht => ⟨a, fold_hinv (h a) s hs ht⟩) ?_ ?_ ?_
    (fun s _ ht => lrun_false _ _ _ s ht)
    (fun s ⟨a, hs⟩ ht => ⟨fold_hdec (h a) s hs ht, lrun_true (JR LR Vv (E0 a)) _ _ _ (fold_hinv (h a)) (fold_hdec (h a)) s hs ht⟩)
  · intro s
    unfold muR; split_ifs
    · have := len_le_S s LR; omega
    · exact Nat.zero_le _
  · intro s ⟨a, hs⟩ ht
    obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true (h a) s hs ht
    rw [PhiR_EfR (h a), muR_EfR (h a), S_EfR (h a)]
    have := (h a).potS y; omega
  · intro s ⟨a, hs⟩ ht
    obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true (h a) s hs ht
    rw [PhiR_EfR (h a), S_EfR (h a)]
    have := (h a).potL y; omega
  · intro s ⟨a, hs⟩ ht ht2
    obtain ⟨y, yv, hv, hne, rfl⟩ := JR_true (h a) s hs ht
    rcases fold_step (h a) y yv hv hne with hb | ⟨p, rest, he, hr, hk, hg⟩
    · rw [ltR_iff] at ht2; exact absurd ht2.2 hb
    · rw [hg, PhiR_EfR (h a), PhiR_EfR (h a), he]
      have := (h a).potG y p hk
      simp only [List.length_append]; omega

lemma Stage.fold_ex {α β : Type} {ι Y : Type} {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB}
    {E0 : α → Y → St} {okf : α → Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ} (a0 : α)
    (h : ∀ a, FoldH LR Vv enc body (E0 a) (okf a) f pot) (F : α → St) (P : α → Prop)
    (Y0 : α → Y) (V0 : α → List Al)
    (hG : ∀ a, P a → Vv (V0 a) ∧ F a = EfR LR (E0 a) (Y0 a) (V0 a))
    (F2 : β → St) (Q : β → Prop)
    (hnext : ∀ a, P a → ∀ l, V0 a = encs enc l → foldOK (okf a) f (Y0 a) l →
      ∃ c, Q c ∧ EfR LR (E0 a) (l.foldl f (Y0 a)) [] = F2 c) :
    Stage F P F2 Q (.loop (ltR LR) body.p) (lrun (ltR LR) body.g (muR LR)) := by
  have hJ : ∀ s, InvF F P s → ∃ a, JR LR Vv (E0 a) s := by
    intro s hs
    rcases hs.2 with hb | ⟨a, ha, rfl⟩
    · exact ⟨a0, hs.1, Or.inl hb⟩
    · obtain ⟨hv, he⟩ := hG a ha
      exact ⟨a, hs.1, Or.inr ⟨Y0 a, V0 a, hv, he⟩⟩
  refine ⟨PSp.weaken (fold_PSp_ex h) hJ, fun s hs => ?_⟩
  obtain ⟨a1, hs1⟩ := hJ s hs
  have hk := lrun_keep (h a1) s hs1
  refine ⟨hk.1, ?_⟩
  rcases hs.2 with hb | ⟨a, ha, rfl⟩
  · exact Or.inl (hk.2 hb)
  · by_cases hb : lrun (ltR LR) body.g (muR LR) (F a) Reg.BAD = []
    · right
      obtain ⟨hv, he⟩ := hG a ha
      rw [he] at hb ⊢
      obtain ⟨l, hl, hok⟩ := fold_sound (h a) (V0 a).length (V0 a) (Y0 a) le_rfl hv hb
      obtain ⟨c, hc, hce⟩ := hnext a ha l hl hok
      refine ⟨c, hc, ?_⟩
      rw [hl, fold_complete (h a) l (Y0 a) (hl ▸ hv) hok]
      exact hce
    · exact Or.inl hb


/-- x0-indexed stage with uniform polynomial-time bound -/
structure StageX {X α β : Type} (F : α → St) (P : X → α → Prop) (F2 : β → St) (Q : X → β → Prop) (p : Prog) (g : St → St) : Prop where
  psp : PSp (InvF F (fun a => ∃ x, P x a)) p g
  inv : ∀ x s, InvF F (P x) s → InvF F2 (Q x) (g s)

lemma StageX.invU {X α β : Type} [Inhabited X] {F : α → St} {P : X → α → Prop} {F2 : β → St} {Q : X → β → Prop} {p : Prog} {g : St → St}
    (h : StageX F P F2 Q p g) : ∀ s, InvF F (fun a => ∃ x, P x a) s → InvF F2 (fun c => ∃ x, Q x c) (g s) := by
  intro s hs
  rcases hs.2 with hb | ⟨a, ⟨x, hx⟩, rfl⟩
  · have := h.inv default s ⟨hs.1, Or.inl hb⟩
    exact ⟨this.1, this.2.imp id (fun ⟨c, hc, e⟩ => ⟨c, ⟨default, hc⟩, e⟩)⟩
  · have := h.inv x _ ⟨hs.1, Or.inr ⟨a, hx, rfl⟩⟩
    exact ⟨this.1, this.2.imp id (fun ⟨c, hc, e⟩ => ⟨c, ⟨x, hc⟩, e⟩)⟩

lemma StageX.comp {X α β γ : Type} [Inhabited X] {F : α → St} {P : X → α → Prop} {F2 : β → St} {Q : X → β → Prop} {F3 : γ → St} {R : X → γ → Prop}
    {p q : Prog} {g h : St → St} (h1 : StageX F P F2 Q p g) (h2 : StageX F2 Q F3 R q h) :
    StageX F P F3 R (.seq p q) (fun s => h (g s)) :=
  ⟨PSp.seq2 h1.psp h2.psp h1.invU, fun x s hs => h2.inv x _ (h1.inv x s hs)⟩

lemma StageX.gb {X α β : Type} (b : GB) (F : α → St) (P : X → α → Prop) (F2 : β → St) (Q : X → β → Prop)
    (hF : ∀ a, Gi (F a)) (hB : ∀ a, F a Reg.BAD = []) (hpre : ∀ x a, P x a → b.pre (F a))
    (hnext : ∀ x a, P x a → b.ok (F a) → ∃ c, Q x c ∧ b.T (F a) = F2 c) : StageX F P F2 Q b.p b.g :=
  ⟨(Stage.gb b F (fun a => ∃ x, P x a) F2 (fun c => ∃ x, Q x c) hF hB (fun a ⟨x, h⟩ => hpre x a h)
      (fun a ⟨x, h⟩ ok => let ⟨c, hc, e⟩ := hnext x a h ok; ⟨c, ⟨x, hc⟩, e⟩)).psp,
   fun x => (Stage.gb b F (P x) F2 (Q x) hF hB (hpre x) (hnext x)).inv⟩

lemma StageX.fold {X α β : Type} {ι Y : Type} {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB}
    {E0 : Y → St} {okf : Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ}
    (h : FoldH LR Vv enc body E0 okf f pot) (F : α → St) (P : X → α → Prop)
    (Y0 : α → Y) (V0 : α → List Al)
    (hG : ∀ x a, P x a → Vv (V0 a) ∧ F a = EfR LR E0 (Y0 a) (V0 a))
    (F2 : β → St) (Q : X → β → Prop)
    (hnext : ∀ x a, P x a → ∀ l, V0 a = encs enc l → foldOK okf f (Y0 a) l →
      ∃ c, Q x c ∧ EfR LR E0 (l.foldl f (Y0 a)) [] = F2 c) :
    StageX F P F2 Q (.loop (ltR LR) body.p) (lrun (ltR LR) body.g (muR LR)) :=
  ⟨(Stage.fold h F (fun a => ∃ x, P x a) Y0 V0 (fun a ⟨x, hx⟩ => hG x a hx) F2 (fun c => ∃ x, Q x c)
      (fun a ⟨x, hx⟩ l hl hok => let ⟨c, hc, e⟩ := hnext x a hx l hl hok; ⟨c, ⟨x, hc⟩, e⟩)).psp,
   fun x => (Stage.fold h F (P x) Y0 V0 (hG x) F2 (Q x) (hnext x)).inv⟩

lemma StageX.fold_ex {X α β : Type} {ι Y : Type} {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB}
    {E0 : α → Y → St} {okf : α → Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ} (a0 : α)
    (h : ∀ a, FoldH LR Vv enc body (E0 a) (okf a) f pot) (F : α → St) (P : X → α → Prop)
    (Y0 : α → Y) (V0 : α → List Al)
    (hG : ∀ x a, P x a → Vv (V0 a) ∧ F a = EfR LR (E0 a) (Y0 a) (V0 a))
    (F2 : β → St) (Q : X → β → Prop)
    (hnext : ∀ x a, P x a → ∀ l, V0 a = encs enc l → foldOK (okf a) f (Y0 a) l →
      ∃ c, Q x c ∧ EfR LR (E0 a) (l.foldl f (Y0 a)) [] = F2 c) :
    StageX F P F2 Q (.loop (ltR LR) body.p) (lrun (ltR LR) body.g (muR LR)) :=
  ⟨(Stage.fold_ex a0 h F (fun a => ∃ x, P x a) Y0 V0 (fun a ⟨x, hx⟩ => hG x a hx) F2 (fun c => ∃ x, Q x c)
      (fun a ⟨x, hx⟩ l hl hok => let ⟨c, hc, e⟩ := hnext x a hx l hl hok; ⟨c, ⟨x, hc⟩, e⟩)).psp,
   fun x => (Stage.fold_ex a0 h F (P x) Y0 V0 (hG x) F2 (Q x) (hnext x)).inv⟩

end Stk

end Sec_RPV12

section Sec_RPV13
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk


lemma init_Zs (x : List Al) : init x = Zs { rq := x } := by
  funext r; cases r <;> first | rfl | simp [init, Zs]

/-- ghost data -/
structure Gh where
  x : List Al
  w : List BSym
  y : List BSym
  n : ℕ
  L : ℕ
  rest : List Al
  t' : List Al

def Hh (g : Gh) : Prop :=
  g.x = g.w.map tk ++ mk :: g.y.map ty ∧
  g.w.map tk = (Nat.bits g.n).map tkb ++ tk BSym.sep :: ((Nat.bits g.L).map tkb ++ tk BSym.sep :: g.rest) ∧
  g.y.map ty = List.replicate g.L (ty BSym.zero) ++ ty BSym.sep :: g.t'

def zH (g : Gh) : Z := { nb := (Nat.bits g.n).map tkb, wa := g.rest, vis := List.replicate g.L (ty BSym.zero), t := g.t' }
def zH2 (g : Gh) : Z := { zH g with tv := List.replicate g.L (ty BSym.zero) }
def zH3 (g : Gh) : Z := { zH2 g with w := g.rest }

structure Gx where
  x : List Al
  w : List BSym
  y : List BSym

def Hx (g : Gx) : Prop := g.x = g.w.map tk ++ mk :: g.y.map ty

lemma stP0_pre : ∀ s, stP0.pre s := by
  intro s; unfold stP0
  repeat' first | apply seq_pre_all | (intro s; trivial)

def stH2 : GB :=
  (bMvP Reg.T Reg.NC (isA (ty BSym.zero))).seq <| (bPopIf Reg.T (isA (ty BSym.sep))).seq <|
  (bEq Reg.K Reg.NC).seq <| (bCopy Reg.W Reg.KP).seq <| bClear Reg.W

lemma tw_isA_rep (c : Al) (l : List Al) :
    (l.takeWhile (isA c)).reverse = List.replicate (l.takeWhile (isA c)).length c := by
  have : l.takeWhile (isA c) = List.replicate (l.takeWhile (isA c)).length c := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    have := List.mem_takeWhile_imp hb
    simpa [isA] using this
  rw [← this]
  rw [this, List.reverse_replicate]
  
lemma stH2_pre (s : St) (hv : s Reg.NC = []) : stH2.pre s := by
  unfold stH2
  simp only [GB.seq]
  refine ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => ?_⟩⟩
  refine ⟨?_, fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩⟩
  · show ∃ c, _ = List.replicate _ c
    refine ⟨ty BSym.zero, ?_⟩
    simp [bMvP, bPopIf, GB.ofGs, gs_mvP, gs_popIf, gMvP, gPop, topP, hd, hv, isA]
    exact tw_isA_rep _ _

lemma stCWN_pre (s : St) : (stC Reg.W Reg.N).pre s := by
  unfold stC
  repeat' first | apply seq_pre_all | (intro s; trivial)
lemma stCWK_pre (s : St) : (stC Reg.W Reg.K).pre s := by
  unfold stC
  repeat' first | apply seq_pre_all | (intro s; trivial)

lemma stH_pre (z : Z) (hv : z.vis = []) : stH.pre (Zs z) := by
  unfold stH; simp only [GB.seq]
  refine ⟨stCWN_pre _, fun _ _ h1 => ⟨stCWK_pre _, fun _ _ h2 => stH2_pre _ ?_⟩⟩
  obtain ⟨bl, rest, hp⟩ := stC_dec_w_nb z h1
  obtain ⟨hw1, hc1⟩ := popNum_some _ _ _ hp
  obtain ⟨a1, a2⟩ := stC_calc_w_nb z bl rest hw1 hc1
  rw [a2] at h2 ⊢
  obtain ⟨bl2, rest2, hp2⟩ := stC_dec_w_kk _ h2
  obtain ⟨hw2, hc2⟩ := popNum_some _ _ _ hp2
  obtain ⟨b1, b2⟩ := stC_calc_w_kk _ bl2 rest2 hw2 hc2
  rw [b2]
  simpa using hv

lemma st0 : StageX (fun x : List Al => Zs { rq := x }) (fun x0 x => x = x0)
    (fun g : Gx => Zs { w := g.w.map tk, t := g.y.map ty }) (fun x0 g => g.x = x0 ∧ Hx g) stP0.p stP0.g :=
  StageX.gb stP0 _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ _ => stP0_pre _) (by
    intro x0 a ha hok
    obtain ⟨w, y, hx⟩ := stP0_dec a hok
    subst hx
    exact ⟨⟨_, w, y⟩, ⟨ha, rfl⟩, (stP0_calc w y).2⟩)

lemma st1 : StageX (fun g : Gx => Zs { w := g.w.map tk, t := g.y.map ty }) (fun x0 g => g.x = x0 ∧ Hx g)
    (fun g : Gh => Zs (zH g)) (fun x0 g => g.x = x0 ∧ Hh g) stH.p stH.g :=
  StageX.gb stH _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ _ => stH_pre _ rfl) (by
    intro x0 a ha hok
    obtain ⟨n, L, rest, t', h1, h2⟩ := stH_dec { w := a.w.map tk, t := a.y.map ty } rfl rfl hok
    refine ⟨⟨a.x, a.w, a.y, n, L, rest, t'⟩, ⟨ha.1, ha.2, h1, h2⟩, ?_⟩
    simp only at h1 h2
    have := (stH_calc n L rest t').2
    rw [← h1, ← h2] at this
    exact this)

lemma st2 : StageX (fun g : Gh => Zs (zH g)) (fun x0 g => g.x = x0 ∧ Hh g)
    (fun g : Gh => Zs (zH2 g)) (fun x0 g => g.x = x0 ∧ Hh g) (bCopy Reg.NC Reg.NC2).p (bCopy Reg.NC Reg.NC2).g :=
  StageX.gb (bCopy Reg.NC Reg.NC2) _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ _ => trivial) (by
    intro x0 a ha _
    refine ⟨a, ha, ?_⟩
    funext r; cases r <;> simp [gCopy, upd, Zs, zH, zH2])

lemma st3 : StageX (fun g : Gh => Zs (zH2 g)) (fun x0 g => g.x = x0 ∧ Hh g)
    (fun g : Gh => Zs (zH3 g)) (fun x0 g => g.x = x0 ∧ Hh g) (bCopy Reg.KP Reg.W).p (bCopy Reg.KP Reg.W).g :=
  StageX.gb (bCopy Reg.KP Reg.W) _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ _ => trivial) (by
    intro x0 a ha _
    refine ⟨a, ha, ?_⟩
    funext r; cases r <;> simp [gCopy, upd, Zs, zH2, zH3, zH])

end Stk

end Sec_RPV13

section Sec_RPV14
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

abbrev Q4 := ℕ × ℕ × ℕ × ℕ

def flatQ : List Q4 → List ℕ
  | [] => []
  | (s, d, w, r) :: l => s :: d :: w :: r :: flatQ l

lemma encFlat_append (a b : List ℕ) : encFlat (a ++ b) = encFlat a ++ encFlat b := by
  induction a with
  | nil => rfl
  | cons n l ih => simp [encFlat, ih]

lemma flatQ_length (qs : List Q4) : (flatQ qs).length = 4 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q l ih => obtain ⟨s, d, w, r⟩ := q; simp [flatQ, ih]; omega

def QOk (n : ℕ) (q : Q4) : Prop := q.1 < n ∧ q.2.1 < n ∧ q.2.2.2 ≤ 1

lemma phaseA_data (n : ℕ) : ∀ (L : ℕ) (y : List Al), foldOK (okAR n) nxtCR y (List.replicate L false) →
    ∃ qs : List Q4, ∃ y' : List Al, qs.length = L ∧ (∀ q ∈ qs, QOk n q) ∧
      y = encFlat (flatQ qs) ++ y' ∧ (List.replicate L false).foldl nxtCR y = y' := by
  intro L
  induction L with
  | zero => intro y _; exact ⟨[], y, rfl, by simp, by simp [flatQ, encFlat], rfl⟩
  | succ L ih =>
    intro y h
    simp only [List.replicate_succ, foldOK] at h
    obtain ⟨h1, h2⟩ := h
    unfold okAR at h1
    rcases hp : parse4 y with _ | ⟨s, d, wt, r, rest⟩
    · rw [hp] at h1; exact h1.elim
    · rw [hp] at h1
      have hy := parse4_some y s d wt r rest hp
      have hn : nxtCR y false = rest := by simp [nxtCR, hp]
      rw [hn] at h2
      obtain ⟨qs, y', hl, hq, hy', hf⟩ := ih rest h2
      refine ⟨(s, d, wt, r) :: qs, y', by simp [hl], ?_, ?_, ?_⟩
      · intro q hq'
        rcases List.mem_cons.mp hq' with rfl | hm
        · exact h1
        · exact hq q hm
      · rw [hy, hy']; simp [flatQ, encFlat]
      · simp only [List.replicate_succ, List.foldl_cons, hn]; exact hf


lemma tyb_inj : Function.Injective tyb := by
  intro a b h; cases a <;> cases b <;> first | rfl | (exfalso; simp [tyb, ty] at h)

lemma encs_encC (l : List Bool) : encs encC l = l.map tyb := by
  unfold encs
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.flatMap_cons, ih, encC]; rfl

lemma map_tyb_rep (l : List Bool) (L : ℕ) (h : l.map tyb = List.replicate L (ty BSym.zero)) :
    l = List.replicate L false := by
  have h0 : ty BSym.zero = tyb false := by simp [tyb]
  rw [h0] at h
  rw [← List.map_replicate] at h
  exact List.map_injective_iff.mpr tyb_inj h

structure GA where
  g : Gh
  qs : List Q4
  y' : List Al

def HA (x0 : List Al) (c : GA) : Prop :=
  c.g.x = x0 ∧ Hh c.g ∧ c.qs.length = c.g.L ∧ (∀ q ∈ c.qs, QOk c.g.n q) ∧ c.g.rest = encFlat (flatQ c.qs) ++ c.y'

def zA (c : GA) : Z := { zH3 c.g with w := c.y', tv := [] }

lemma zH3_E (g : Gh) : Zs (zH3 g) = EfR Reg.NC2 (E0AR (zH3 g)) g.rest (List.replicate g.L (ty BSym.zero)) := by
  rw [EfR_E0AR]; rfl

lemma st4 : StageX (fun g : Gh => Zs (zH3 g)) (fun x0 g => g.x = x0 ∧ Hh g)
    (fun c : GA => Zs (zA c)) HA (.loop (ltR Reg.NC2) cBa.p) (lrun (ltR Reg.NC2) cBa.g (muR Reg.NC2)) := by
  refine StageX.fold_ex (⟨[], [], [], 0, 0, [], []⟩ : Gh) (fun g : Gh => foldH_cBa (zH3 g) g.n rfl) _ _
    (fun g => g.rest) (fun g => List.replicate g.L (ty BSym.zero)) ?_ _ _ ?_
  · intro x0 g _
    refine ⟨?_, zH3_E g⟩
    intro a ha
    rw [List.mem_replicate] at ha
    exact ⟨false, by rw [ha.2]; simp [tyb]⟩
  · intro x0 g hg l hl hok
    rw [encs_encC] at hl
    have hl' := map_tyb_rep l g.L hl.symm
    subst hl'
    obtain ⟨qs, y', hql, hq, hy, hf⟩ := phaseA_data g.n g.L g.rest hok
    refine ⟨⟨g, qs, y'⟩, ⟨hg.1, hg.2, hql, hq, hy⟩, ?_⟩
    rw [EfR_E0AR, hf]
    rfl

end Stk

end Sec_RPV14

section Sec_RPV15
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def stK : GB := (stC Reg.W Reg.K).seq <| (bBad (topS Reg.W)).seq <| bClear Reg.K

lemma stK_pre : ∀ s, stK.pre s := by
  intro s; unfold stK
  repeat' first | exact stCWK_pre _ | apply seq_pre_all | (intro s; trivial)

lemma stK_calc (z : Z) (k : ℕ) (hw : z.w = encFlat [k]) :
    stK.ok (Zs z) ∧ stK.T (Zs z) = Zs { z with w := [], kk := [] } := by
  obtain ⟨a1, a2⟩ := stC_calc_w_kk z (Nat.bits k) [] (by simpa [encFlat] using hw) (canon_bits k)
  simp only [stK, seq_ok, seq_T, a2]
  refine ⟨⟨a1, ?_⟩, ?_⟩
  · simp [topS, hd]
  · funext r; cases r <;> simp [gClear, upd, Zs]

lemma stK_dec (z : Z) (h : stK.ok (Zs z)) : ∃ k, z.w = encFlat [k] := by
  simp only [stK, seq_ok, seq_T] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨bl, rest, hp⟩ := stC_dec_w_kk z h1
  obtain ⟨hw, hc⟩ := popNum_some _ _ _ hp
  obtain ⟨a1, a2⟩ := stC_calc_w_kk z bl rest hw hc
  rw [a2] at h2
  have hr : rest = [] := by
    have := h2.1
    simpa [topS, hd] using this
  subst hr
  refine ⟨val bl, ?_⟩
  rw [hw, encFlat, bits_val_of_canon bl hc]; rfl

structure GK where
  c : GA
  k : ℕ

def HK (x0 : List Al) (c : GK) : Prop := HA x0 c.c ∧ c.c.y' = encFlat [c.k]

def zK (c : GK) : Z := { zA c.c with w := [] }

lemma st5 : StageX (fun c : GA => Zs (zA c)) HA (fun c : GK => Zs (zK c)) HK stK.p stK.g :=
  StageX.gb stK _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ _ => stK_pre _) (by
    intro x0 c hc hok
    obtain ⟨k, hk⟩ := stK_dec (zA c) hok
    refine ⟨⟨c, k⟩, ⟨hc, hk⟩, ?_⟩
    rw [(stK_calc (zA c) k hk).2]
    rfl)

end Stk

end Sec_RPV15

section Sec_RPV16
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def Y0 (c : GK) : Ys :=
  ⟨flatQ c.c.qs ++ [c.k], List.replicate c.c.g.L false, [], none, (Nat.bits c.c.g.n).map tkb⟩

structure GR where
  c : GK
  items : List (ℕ × Bool)

def HR (d : Bool) (x0 : List Al) (r : GR) : Prop :=
  HK x0 r.c ∧ r.c.c.g.t' = encs encI r.items ∧ foldOK (okf d) nxt (Y0 r.c) r.items

def zR (r : GR) : Z := { toZ (r.items.foldl nxt (Y0 r.c)) with t := [] }

lemma zK_E (c : GK) (hk : c.c.y' = encFlat [c.k]) (hy : c.c.g.rest = encFlat (flatQ c.c.qs) ++ c.c.y') :
    Zs (zK c) = EfR Reg.T E0R (Y0 c) c.c.g.t' := by
  have e : EfR Reg.T E0R (Y0 c) c.c.g.t' = Zs { toZ (Y0 c) with t := c.c.g.t' } := by simp [EfR, E0R]
  rw [e]
  have h1 : c.c.g.rest = encFlat (flatQ c.c.qs ++ [c.k]) := by rw [encFlat_append, hy, hk]
  have h2 : (List.replicate c.c.g.L false).map tyb = List.replicate c.c.g.L (ty BSym.zero) := by
    rw [List.map_replicate]; simp [tyb]
  simp [zK, zA, zH3, zH2, zH, toZ, Y0, h1, h2]

lemma vv_t' (g : Gh) (h : Hh g) : VvR g.t' := by
  intro a ha
  have h3 := h.2.2
  have : a ∈ g.y.map ty := by rw [h3]; simp [ha]
  simp only [List.mem_map] at this
  obtain ⟨b, _, rfl⟩ := this
  exact ⟨b, rfl⟩

lemma st6 (d : Bool) : StageX (fun c : GK => Zs (zK c)) HK (fun r : GR => Zs (zR r)) (HR d)
    (.loop (ltR Reg.T) (rR d).p) (lrun (ltR Reg.T) (rR d).g (muR Reg.T)) := by
  refine StageX.fold (foldH_rR d) _ _ Y0 (fun c => c.c.g.t') ?_ _ _ ?_
  · intro x0 c hc
    exact ⟨vv_t' c.c.g hc.1.2.1, zK_E c hc.2 hc.1.2.2.2.2⟩
  · intro x0 c hc items hl hok
    refine ⟨⟨c, items⟩, ⟨hc, hl, hok⟩, ?_⟩
    simp [EfR, E0R, zR]

end Stk

end Sec_RPV16

section Sec_RPV17
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma nxt_fl (y : Ys) (p : ℕ × Bool) : (nxt y p).fl = y.fl := by
  unfold nxt; split <;> rfl
lemma nxt_nb (y : Ys) (p : ℕ × Bool) : (nxt y p).nb = y.nb := by
  unfold nxt; split <;> rfl
lemma nxt_vis_len (y : Ys) (p : ℕ × Bool) : (nxt y p).vis.length = y.vis.length := by
  unfold nxt; split <;> simp

lemma foldl_nxt_fl (l : List (ℕ × Bool)) : ∀ y : Ys, (l.foldl nxt y).fl = y.fl := by
  induction l with
  | nil => intro y; rfl
  | cons p l ih => intro y; simp [List.foldl_cons, ih, nxt_fl]
lemma foldl_nxt_nb (l : List (ℕ × Bool)) : ∀ y : Ys, (l.foldl nxt y).nb = y.nb := by
  induction l with
  | nil => intro y; rfl
  | cons p l ih => intro y; simp [List.foldl_cons, ih, nxt_nb]
lemma foldl_nxt_vis_len (l : List (ℕ × Bool)) : ∀ y : Ys, (l.foldl nxt y).vis.length = y.vis.length := by
  induction l with
  | nil => intro y; rfl
  | cons p l ih => intro y; simp [List.foldl_cons, ih, nxt_vis_len]

def yE (r : GR) : Ys := r.items.foldl nxt (Y0 r.c)

def zR7 (r : GR) : Z := { zR r with w := encFlat (flatQ r.c.c.qs ++ [r.c.k]) }

lemma zR_wa (r : GR) : (zR r).wa = encFlat (flatQ r.c.c.qs ++ [r.c.k]) := by
  simp [zR, toZ, foldl_nxt_fl, Y0]

lemma zR_w (r : GR) : (zR r).w = [] := rfl

lemma st7 (d : Bool) : StageX (fun r : GR => Zs (zR r)) (HR d)
    (fun r : GR => Zs (zR7 r)) (HR d) (bCopy Reg.KP Reg.W).p (bCopy Reg.KP Reg.W).g :=
  StageX.gb (bCopy Reg.KP Reg.W) _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ _ => trivial) (by
    intro x0 a ha _
    refine ⟨a, ha, ?_⟩
    funext r; cases r <;> simp [gCopy, upd, Zs, zR7, zR_wa, zR_w])


def PBok (n : ℕ) : List Q4 → List Bool → Prop
  | [], _ => True
  | _ :: _, [] => True
  | q :: qs, b :: l => QOk n q ∧ (q.2.2.2 = 1 → b = true) ∧ PBok n qs l

lemma phaseB_data (n : ℕ) : ∀ (qs : List Q4) (l : List Bool) (rest : List Al), qs.length = l.length →
    (foldOK (okCR n) nxtCR (encFlat (flatQ qs) ++ rest) l ↔ PBok n qs l) ∧
    l.foldl nxtCR (encFlat (flatQ qs) ++ rest) = rest := by
  intro qs
  induction qs with
  | nil =>
    intro l rest h
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this
    simp [foldOK, PBok, flatQ, encFlat]
  | cons q qs ih =>
    intro l rest h
    obtain ⟨s, d, wt, r⟩ := q
    cases l with
    | nil => simp at h
    | cons b l =>
      have h' : qs.length = l.length := by simpa using h
      obtain ⟨i1, i2⟩ := ih l rest h'
      have e : encFlat (flatQ ((s, d, wt, r) :: qs)) ++ rest = encFlat [s, d, wt, r] ++ (encFlat (flatQ qs) ++ rest) := by
        simp [flatQ, encFlat]
      have hp := parse4_enc s d wt r (encFlat (flatQ qs) ++ rest)
      have hn : nxtCR (encFlat (flatQ ((s, d, wt, r) :: qs)) ++ rest) b = encFlat (flatQ qs) ++ rest := by
        rw [e]; simp [nxtCR, hp]
      have ho : okCR n (encFlat (flatQ ((s, d, wt, r) :: qs)) ++ rest) b ↔ QOk n (s, d, wt, r) ∧ (r = 1 → b = true) := by
        rw [e]; simp [okCR, hp, QOk]; tauto
      constructor
      · simp only [foldOK, hn, ho, PBok, i1]
        tauto
      · simp only [List.foldl_cons, hn]; exact i2


@[simp] lemma zR_tx (r : GR) : (zR r).tx = [] := rfl
@[simp] lemma zR_hx (r : GR) : (zR r).hx = [] := rfl
@[simp] lemma zR_wx (r : GR) : (zR r).wx = [] := rfl
@[simp] lemma zR_rq (r : GR) : (zR r).rq = [] := rfl
@[simp] lemma zR_h (r : GR) : (zR r).h = [] := rfl
lemma zR_vis (r : GR) : (zR r).vis = (yE r).vis.map tyb := rfl

def zRn (r : GR) : Z := { zR r with nb := (Nat.bits r.c.c.g.n).map tkb }

lemma zR_nb (r : GR) : (zR r).nb = (Nat.bits r.c.c.g.n).map tkb := by
  simp [zR, toZ, foldl_nxt_nb, Y0]

lemma zRn_eq (r : GR) : zRn r = zR r := by
  unfold zRn; rw [← zR_nb r]

def HB (d : Bool) (x0 : List Al) (r : GR) : Prop :=
  HR d x0 r ∧ PBok r.c.c.g.n r.c.c.qs (yE r).vis

def zB (r : GR) : Z := { zR r with w := encFlat [r.c.k], vis := [] }

lemma vis_len (r : GR) (h : r.c.c.qs.length = r.c.c.g.L) : r.c.c.qs.length = (yE r).vis.length := by
  simp [yE, foldl_nxt_vis_len, Y0, h]

lemma st8 (d : Bool) : StageX (fun r : GR => Zs (zR7 r)) (HR d)
    (fun r : GR => Zs (zB r)) (HB d)
    (.loop (ltR Reg.NC) cB.p) (lrun (ltR Reg.NC) cB.g (muR Reg.NC)) := by
  refine StageX.fold_ex (⟨⟨⟨⟨[], [], [], 0, 0, [], []⟩, [], []⟩, 0⟩, []⟩ : GR)
    (fun r : GR => foldH_cBR (zRn r) r.c.c.g.n rfl) _ _
    (fun r => encFlat (flatQ r.c.c.qs ++ [r.c.k])) (fun r => (yE r).vis.map tyb) ?_ _ _ ?_
  · intro x0 r hr
    refine ⟨?_, ?_⟩
    · intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨b, _, rfl⟩ := ha
      exact ⟨b, rfl⟩
    · rw [EfR_E0CR, zRn_eq]
      simp [zR7, zR_vis]
  · intro x0 r hr l hl hok
    rw [encs_encC] at hl
    have hl' : l = (yE r).vis := (List.map_injective_iff.mpr tyb_inj hl).symm
    subst hl'
    have hlen := vis_len r hr.1.1.2.2.1
    have hsplit : encFlat (flatQ r.c.c.qs ++ [r.c.k]) = encFlat (flatQ r.c.c.qs) ++ encFlat [r.c.k] := encFlat_append _ _
    rw [hsplit] at hok
    obtain ⟨i1, i2⟩ := phaseB_data r.c.c.g.n r.c.c.qs (yE r).vis (encFlat [r.c.k]) hlen
    refine ⟨r, ⟨hr, i1.mp hok⟩, ?_⟩
    rw [hsplit, i2, EfR_E0CR, zRn_eq]
    simp [zB]

end Stk

end Sec_RPV17

section Sec_RPV18
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def clo : Option (ℕ × ℕ) → Prop
  | none => True
  | some (f, m) => m = f

def Q9 (d : Bool) (x0 : List Al) (r : GR) : Prop :=
  HB d x0 r ∧ ¬ (r.c.k < val (yE r).a) ∧ clo (yE r).ch

lemma zB_ok (r : GR) : cFin.ok (Zs (zB r)) ↔ ¬ (r.c.k < val (yE r).a) ∧ clo (yE r).ch := by
  have hz : ∀ c : Ys, c = yE r → ((zB r).fst = (toZ c).fst ∧ (zB r).first = (toZ c).first ∧ (zB r).prev = (toZ c).prev ∧
      (zB r).acc = c.a.map tkb) := by
    intro c hc; subst hc; exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hz (yE r) rfl
  rcases hc : (yE r).ch with _ | ⟨f, m⟩
  · have := cFin_ok (zB r) r.c.k (yE r).a none rfl rfl h4 (by rw [h1]; simp [toZ, hc]) (by rw [h2]; simp [toZ, hc]) (by rw [h3]; simp [toZ, hc])
    rw [this]; simp [clo, hc]
  · have := cFin_ok (zB r) r.c.k (yE r).a (some (f, m)) rfl rfl h4 (by rw [h1]; simp [toZ, hc]) (by rw [h2]; simp [toZ, hc]) (by rw [h3]; simp [toZ, hc])
    rw [this]; simp [clo, hc]

lemma st9 (d : Bool) : StageX (fun r : GR => Zs (zB r)) (HB d) (fun r : GR => cFin.T (Zs (zB r))) (Q9 d)
    cFin.p cFin.g :=
  StageX.gb cFin _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ _ => cFin_pre _) (by
    intro x0 r hr hok
    exact ⟨r, ⟨hr, (zB_ok r).mp hok⟩, rfl⟩)


def vg (d : Bool) : St → St := fun s =>
  cFin.g (lrun (ltR Reg.NC) cB.g (muR Reg.NC) ((bCopy Reg.KP Reg.W).g (lrun (ltR Reg.T) (rR d).g (muR Reg.T)
    (stK.g (lrun (ltR Reg.NC2) cBa.g (muR Reg.NC2) ((bCopy Reg.KP Reg.W).g ((bCopy Reg.NC Reg.NC2).g
    (stH.g (stP0.g s)))))))))

def vp (d : Bool) : Prog :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq stP0.p stH.p) (bCopy Reg.NC Reg.NC2).p) (bCopy Reg.KP Reg.W).p)
    (.loop (ltR Reg.NC2) cBa.p)) stK.p) (.loop (ltR Reg.T) (rR d).p)) (bCopy Reg.KP Reg.W).p)
    (.loop (ltR Reg.NC) cB.p)) cFin.p

lemma bOut_g (s : St) : bOut.g s = outG s := rfl

lemma chain (d : Bool) : StageX (fun x : List Al => Zs { rq := x }) (fun x0 x => x = x0)
    (fun r : GR => cFin.T (Zs (zB r))) (Q9 d) (vp d) (vg d) :=
  ((((((((st0.comp st1).comp st2).comp st3).comp st4).comp st5).comp (st6 d)).comp (st7 d)).comp (st8 d)).comp (st9 d)

theorem verifier_core (d : Bool) : PSp Inv0 ((vp d).seq bOut.p) (fun s => bOut.g (vg d s)) ∧
    ∀ x : List Al, bOut.g (vg d (init x)) Reg.OUT ≠ [] → ∃ r : GR, Q9 d x r := by
  have hs := chain d
  refine ⟨?_, ?_⟩
  · refine PSp.weaken (PSp.seq2 hs.psp (PSp.weaken bOut.h.1.1 (fun s hs => hs.1)) hs.invU) ?_
    intro s ⟨x, hx⟩
    subst hx
    exact ⟨by rw [init_Zs]; exact Zs_Gi _, Or.inr ⟨x, ⟨x, rfl⟩, init_Zs x⟩⟩
  · intro x hx
    have h1 := hs.inv x (init x) ⟨by rw [init_Zs]; exact Zs_Gi _, Or.inr ⟨x, rfl, init_Zs x⟩⟩
    rw [bOut_g, outG_OUT] at hx
    by_cases hb : vg d (init x) Reg.BAD = []
    · rcases h1.2 with h | ⟨c, hc, _⟩
      · exact absurd hb h
      · exact ⟨c, hc⟩
    · simp [hb] at hx

end Stk

end Sec_RPV18

section Sec_RPV19
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

/-- completeness side of a stage: on good ghosts the program lands exactly on the ideal state, with BAD empty -/
structure Cmp {α β : Type} (F : α → St) (P : α → Prop) (F2 : β → St) (Q : β → Prop) (g : St → St) : Prop where
  step : ∀ a, P a → ∃ c, Q c ∧ g (F a) = F2 c ∧ g (F a) Reg.BAD = []

lemma Cmp.comp {α β γ : Type} {F : α → St} {P : α → Prop} {F2 : β → St} {Q : β → Prop} {F3 : γ → St} {R : γ → Prop}
    {g h : St → St} (h1 : Cmp F P F2 Q g) (h2 : Cmp F2 Q F3 R h) : Cmp F P F3 R (fun s => h (g s)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc, e1, _⟩ := h1.step a ha
  obtain ⟨c2, hc2, e2, e3⟩ := h2.step c hc
  refine ⟨c2, hc2, ?_, ?_⟩
  · simp only [e1]; exact e2
  · simp only [e1]; exact e3

lemma Cmp.gb {α β : Type} (b : GB) (F : α → St) (P : α → Prop) (F2 : β → St) (Q : β → Prop)
    (hF : ∀ a, Gi (F a)) (hB : ∀ a, F a Reg.BAD = []) (hpre : ∀ a, P a → b.pre (F a))
    (hnext : ∀ a, P a → b.ok (F a) ∧ ∃ c, Q c ∧ b.T (F a) = F2 c) : Cmp F P F2 Q b.g := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨ho, c, hc, he⟩ := hnext a ha
  have hh := b.h.2.2.2 (F a) (hF a) (hpre a ha) (hB a)
  exact ⟨c, hc, by rw [hh.2 ho]; exact he, hh.1.2 ho⟩

lemma Cmp.fold {α β : Type} {ι Y : Type} {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB}
    {E0 : Y → St} {okf : Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ}
    (h : FoldH LR Vv enc body E0 okf f pot) (F : α → St) (P : α → Prop)
    (Y0 : α → Y) (V0 : α → List Al) (F2 : β → St) (Q : β → Prop)
    (hnext : ∀ a, P a → ∃ l, V0 a = encs enc l ∧ Vv (V0 a) ∧ F a = EfR LR E0 (Y0 a) (V0 a) ∧ foldOK okf f (Y0 a) l ∧
      ∃ c, Q c ∧ EfR LR E0 (l.foldl f (Y0 a)) [] = F2 c) :
    Cmp F P F2 Q (lrun (ltR LR) body.g (muR LR)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨l, hl, hv, he, hok, c, hc, hce⟩ := hnext a ha
  have key : lrun (ltR LR) body.g (muR LR) (F a) = EfR LR E0 (l.foldl f (Y0 a)) [] := by
    rw [he, hl]; exact fold_complete h l (Y0 a) (hl ▸ hv) hok
  exact ⟨c, hc, by rw [key]; exact hce, by rw [key]; exact EfR_BAD h _ _⟩

lemma Cmp.fold_ex {α β : Type} {ι Y : Type} {LR : Reg} {Vv : List Al → Prop} {enc : ι → List Al} {body : GB}
    {E0 : α → Y → St} {okf : α → Y → ι → Prop} {f : Y → ι → Y} {pot : St → ℕ}
    (h : ∀ a, FoldH LR Vv enc body (E0 a) (okf a) f pot) (F : α → St) (P : α → Prop)
    (Y0 : α → Y) (V0 : α → List Al) (F2 : β → St) (Q : β → Prop)
    (hnext : ∀ a, P a → ∃ l, V0 a = encs enc l ∧ Vv (V0 a) ∧ F a = EfR LR (E0 a) (Y0 a) (V0 a) ∧ foldOK (okf a) f (Y0 a) l ∧
      ∃ c, Q c ∧ EfR LR (E0 a) (l.foldl f (Y0 a)) [] = F2 c) :
    Cmp F P F2 Q (lrun (ltR LR) body.g (muR LR)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨l, hl, hv, he, hok, c, hc, hce⟩ := hnext a ha
  have key : lrun (ltR LR) body.g (muR LR) (F a) = EfR LR (E0 a) (l.foldl f (Y0 a)) [] := by
    rw [he, hl]; exact fold_complete (h a) l (Y0 a) (hl ▸ hv) hok
  exact ⟨c, hc, by rw [key]; exact hce, by rw [key]; exact EfR_BAD (h a) _ _⟩

end Stk

end Sec_RPV19

section Sec_RPV20
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma phaseA_conv (n : ℕ) : ∀ (qs : List Q4) (y' : List Al), (∀ q ∈ qs, QOk n q) →
    foldOK (okAR n) nxtCR (encFlat (flatQ qs) ++ y') (List.replicate qs.length false) ∧
    (List.replicate qs.length false).foldl nxtCR (encFlat (flatQ qs) ++ y') = y' := by
  intro qs
  induction qs with
  | nil => intro y' _; exact ⟨trivial, rfl⟩
  | cons q qs ih =>
    intro y' hq
    obtain ⟨s, d, wt, r⟩ := q
    have hp : parse4 (encFlat (flatQ ((s, d, wt, r) :: qs)) ++ y') = some (s, d, wt, r, encFlat (flatQ qs) ++ y') := by
      have := parse4_enc s d wt r (encFlat (flatQ qs) ++ y')
      simpa [flatQ, encFlat, List.append_assoc] using this
    have hn : nxtCR (encFlat (flatQ ((s, d, wt, r) :: qs)) ++ y') false = encFlat (flatQ qs) ++ y' := by
      simp [nxtCR, hp]
    obtain ⟨i1, i2⟩ := ih y' (fun q h => hq q (List.mem_cons_of_mem _ h))
    simp only [List.length_cons, List.replicate_succ, foldOK, List.foldl_cons, hn]
    refine ⟨⟨?_, i1⟩, i2⟩
    simp only [okAR, hp]
    exact hq _ (List.mem_cons_self ..)

section
variable (gH : Gh) (hH : Hh gH)
include hH

lemma c0 : Cmp (fun x : List Al => Zs { rq := x }) (fun x => x = gH.x)
    (fun g : Gx => Zs { w := g.w.map tk, t := g.y.map ty }) (fun a => a = ⟨gH.x, gH.w, gH.y⟩) stP0.g :=
  Cmp.gb stP0 _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ => stP0_pre _) (by
    intro x ha
    subst ha
    rw [hH.1]
    exact ⟨(stP0_calc _ _).1, _, rfl, (stP0_calc _ _).2⟩)

lemma c1 : Cmp (fun g : Gx => Zs { w := g.w.map tk, t := g.y.map ty }) (fun a => a = ⟨gH.x, gH.w, gH.y⟩)
    (fun g : Gh => Zs (zH g)) (fun g => g = gH) stH.g :=
  Cmp.gb stH _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ => stH_pre _ rfl) (by
    intro a ha
    subst ha
    have h1 := hH.2.1
    have h2 := hH.2.2
    have := stH_calc gH.n gH.L gH.rest gH.t'
    rw [← h1, ← h2] at this
    exact ⟨this.1, gH, rfl, this.2⟩)

lemma c2 : Cmp (fun g : Gh => Zs (zH g)) (fun g => g = gH)
    (fun g : Gh => Zs (zH2 g)) (fun g => g = gH) (bCopy Reg.NC Reg.NC2).g :=
  Cmp.gb (bCopy Reg.NC Reg.NC2) _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ => trivial) (by
    intro a ha
    refine ⟨?_, a, ha, ?_⟩
    · trivial
    funext r; cases r <;> simp [gCopy, upd, Zs, zH, zH2])


lemma c3 : Cmp (fun g : Gh => Zs (zH2 g)) (fun g => g = gH)
    (fun g : Gh => Zs (zH3 g)) (fun g => g = gH) (bCopy Reg.KP Reg.W).g :=
  Cmp.gb (bCopy Reg.KP Reg.W) _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ => trivial) (by
    intro a ha
    refine ⟨trivial, a, ha, ?_⟩
    funext r; cases r <;> simp [gCopy, upd, Zs, zH2, zH3, zH])

variable (qs0 : List Q4) (y0 : List Al) (hL : qs0.length = gH.L) (hq : ∀ q ∈ qs0, QOk gH.n q)
  (hr : gH.rest = encFlat (flatQ qs0) ++ y0)
include hL hq hr

lemma c4 : Cmp (fun g : Gh => Zs (zH3 g)) (fun g => g = gH)
    (fun c : GA => Zs (zA c)) (fun c => c = ⟨gH, qs0, y0⟩) (lrun (ltR Reg.NC2) cBa.g (muR Reg.NC2)) := by
  refine Cmp.fold_ex (fun g : Gh => foldH_cBa (zH3 g) g.n rfl) _ _
    (fun g => g.rest) (fun g => List.replicate g.L (ty BSym.zero)) _ _ ?_
  intro g hg
  subst g
  refine ⟨List.replicate qs0.length false, ?_, ?_, zH3_E _, ?_, ⟨gH, qs0, y0⟩, rfl, ?_⟩
  · rw [encs_encC, hL, List.map_replicate]; simp [tyb]
  · intro a ha
    rw [List.mem_replicate] at ha
    exact ⟨false, by rw [ha.2]; simp [tyb]⟩
  · rw [hr]; exact (phaseA_conv _ qs0 y0 hq).1
  · rw [EfR_E0AR, hr, (phaseA_conv _ qs0 y0 hq).2]; rfl

variable (k0 : ℕ) (hk : y0 = encFlat [k0])
include hk

lemma c5 : Cmp (fun c : GA => Zs (zA c)) (fun c => c = ⟨gH, qs0, y0⟩)
    (fun c : GK => Zs (zK c)) (fun c => c = ⟨⟨gH, qs0, y0⟩, k0⟩) stK.g :=
  Cmp.gb stK _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ => stK_pre _) (by
    intro c hc
    subst hc
    have := stK_calc (zA ⟨gH, qs0, y0⟩) k0 hk
    refine ⟨this.1, _, rfl, ?_⟩
    rw [this.2]; rfl)

variable (d : Bool) (items0 : List (ℕ × Bool)) (ht : gH.t' = encs encI items0)
  (hok6 : foldOK (okf d) nxt (Y0 ⟨⟨gH, qs0, y0⟩, k0⟩) items0)
include ht hok6

lemma c6 : Cmp (fun c : GK => Zs (zK c)) (fun c => c = ⟨⟨gH, qs0, y0⟩, k0⟩)
    (fun r : GR => Zs (zR r)) (fun r => r = ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩)
    (lrun (ltR Reg.T) (rR d).g (muR Reg.T)) := by
  refine Cmp.fold (foldH_rR d) _ _ Y0 (fun c => c.c.g.t') _ _ ?_
  intro c hc
  subst hc
  refine ⟨items0, ht, vv_t' gH hH, zK_E _ hk (by simpa using hr), hok6, _, rfl, ?_⟩
  simp [EfR, E0R, zR]

lemma c7 : Cmp (fun r : GR => Zs (zR r)) (fun r => r = ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩)
    (fun r : GR => Zs (zR7 r)) (fun r => r = ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩) (bCopy Reg.KP Reg.W).g :=
  Cmp.gb (bCopy Reg.KP Reg.W) _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ => trivial) (by
    intro a ha
    refine ⟨trivial, a, ha, ?_⟩
    funext r; cases r <;> simp [gCopy, upd, Zs, zR7, zR_wa, zR_w])

variable (hB : PBok gH.n qs0 (yE ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩).vis)
include hB

lemma c8 : Cmp (fun r : GR => Zs (zR7 r)) (fun r => r = ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩)
    (fun r : GR => Zs (zB r)) (fun r => r = ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩)
    (lrun (ltR Reg.NC) cB.g (muR Reg.NC)) := by
  refine Cmp.fold_ex (fun r : GR => foldH_cBR (zRn r) r.c.c.g.n rfl) _ _
    (fun r => encFlat (flatQ r.c.c.qs ++ [r.c.k])) (fun r => (yE r).vis.map tyb) _ _ ?_
  intro r hr
  subst hr
  have hlen := vis_len ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩ hL
  have hsplit : encFlat (flatQ qs0 ++ [k0]) = encFlat (flatQ qs0) ++ encFlat [k0] := encFlat_append _ _
  obtain ⟨i1, i2⟩ := phaseB_data gH.n qs0 (yE ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩).vis (encFlat [k0]) hlen
  refine ⟨(yE ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩).vis, ?_, ?_, ?_, ?_, ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩, rfl, ?_⟩
  · rw [encs_encC]
  · intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    exact ⟨b, rfl⟩
  · rw [EfR_E0CR, zRn_eq]
    simp [zR7, zR_vis]
  · show foldOK (okCR gH.n) nxtCR (encFlat (flatQ qs0 ++ [k0])) _
    rw [hsplit]; exact i1.mpr hB
  · show EfR _ _ (List.foldl nxtCR (encFlat (flatQ qs0 ++ [k0])) _) [] = _
    rw [hsplit, i2, EfR_E0CR, zRn_eq]
    simp [zB]

variable (hfin : ¬ k0 < val (yE ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩).a ∧ clo (yE ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩).ch)
include hfin

lemma c9 : Cmp (fun r : GR => Zs (zB r)) (fun r => r = ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩)
    (fun r : GR => cFin.T (Zs (zB r))) (fun r => r = ⟨⟨⟨gH, qs0, y0⟩, k0⟩, items0⟩) cFin.g :=
  Cmp.gb cFin _ _ _ _ (fun _ => Zs_Gi _) (fun _ => Zs_BAD _) (fun _ _ => cFin_pre _) (by
    intro r hr
    subst hr
    exact ⟨(zB_ok _).mpr hfin, _, rfl, rfl⟩)

theorem complete_core : bOut.g (vg d (init gH.x)) Reg.OUT ≠ [] := by
  have hc := (((((((((c0 gH hH).comp (c1 gH hH)).comp (c2 gH hH)).comp (c3 gH hH)).comp
    (c4 gH hH qs0 y0 hL hq hr)).comp (c5 gH hH qs0 y0 hL hq hr k0 hk)).comp
    (c6 gH hH qs0 y0 hL hq hr k0 hk d items0 ht hok6)).comp (c7 gH hH qs0 y0 hL hq hr k0 hk d items0 ht hok6)).comp
    (c8 gH hH qs0 y0 hL hq hr k0 hk d items0 ht hok6 hB)).comp (c9 gH hH qs0 y0 hL hq hr k0 hk d items0 ht hok6 hB hfin)
  obtain ⟨c, _, e, hbad⟩ := hc.step gH.x rfl
  have hbad' : vg d (init gH.x) Reg.BAD = [] := by rw [init_Zs]; exact hbad
  rw [bOut_g, outG_OUT]
  simp [hbad']

end
end Stk

end Sec_RPV20

section Sec_RP1

namespace RuralPostman.NPC
namespace RPInstance

def Walk (I : RPInstance) : Fin I.n → Fin I.n → List I.Traversal → Prop
  | a, b, [] => a = b
  | a, b, t :: r => I.trSrc t = a ∧ Walk I (I.trDst t) b r

theorem walk_append (I : RPInstance) (u v : List I.Traversal) :
    ∀ a b, I.Walk a b (u ++ v) ↔ ∃ c, I.Walk a c u ∧ I.Walk c b v := by
  induction u with
  | nil =>
    intro a b
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨c, hc, h⟩
      have : a = c := hc
      subst this; exact h
  | cons t r ih =>
    intro a b
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨c, hc1, hc2⟩ := (ih _ _).mp h2
      exact ⟨c, ⟨h1, hc1⟩, hc2⟩
    · rintro ⟨c, ⟨h1, hc1⟩, hc2⟩
      exact ⟨h1, (ih _ _).mpr ⟨c, hc1, hc2⟩⟩

theorem erase_loops (I : RPInstance) (S : Finset (Fin I.n)) :
    ∀ (ws : List I.Traversal) (a b : Fin I.n), (∀ t ∈ ws, I.trSrc t ∈ S) → I.Walk a b ws →
    ∃ ws', ws'.Sublist ws ∧ I.Walk a b ws' ∧ (ws'.map I.trSrc).Nodup := by
  intro ws
  induction ws with
  | nil =>
    intro a b _ h
    exact ⟨[], List.Sublist.slnil, h, List.nodup_nil⟩
  | cons t r ih =>
    intro a b hS h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨r', hr1, hr2, hr3⟩ := ih (I.trDst t) b (fun s hs => hS s (List.mem_cons_of_mem _ hs)) h2
    by_cases hm : a ∈ r'.map I.trSrc
    · obtain ⟨s, hs, hsa⟩ := List.mem_map.mp hm
      obtain ⟨u, v, huv⟩ := List.append_of_mem hs
      rw [huv] at hr2
      obtain ⟨c, hc1, hc2⟩ := (walk_append I u (s :: v) _ _).mp hr2
      have hcs : I.trSrc s = c := hc2.1
      have hca : c = a := by rw [← hcs]; exact hsa
      subst hca
      refine ⟨s :: v, ?_, hc2, ?_⟩
      · have h3 : (s :: v).Sublist r' := by
          rw [huv]; exact List.sublist_append_right u (s :: v)
        exact (h3.trans hr1).trans (List.sublist_cons_self t r)
      · have h3 : (s :: v).Sublist r' := by
          rw [huv]; exact List.sublist_append_right u (s :: v)
        exact hr3.sublist (h3.map _)
    · refine ⟨t :: r', hr1.cons_cons t, ⟨h1, hr2⟩, ?_⟩
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hr3⟩
      rw [h1]; exact hm

theorem nodup_len (I : RPInstance) (S : Finset (Fin I.n)) (ws : List I.Traversal)
    (hS : ∀ t ∈ ws, I.trSrc t ∈ S) (hn : (ws.map I.trSrc).Nodup) : ws.length ≤ S.card := by
  have h1 : (ws.map I.trSrc).toFinset.card = ws.length := by
    rw [List.toFinset_card_of_nodup hn, List.length_map]
  rw [← h1]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact hS t ht

theorem first_in (I : RPInstance) (T : Finset (Fin I.arcs.length)) :
    ∀ ws : List I.Traversal, (∃ s ∈ ws, s.1 ∈ T) →
    ∃ u t v, ws = u ++ t :: v ∧ t.1 ∈ T ∧ ∀ s ∈ u, s.1 ∉ T := by
  intro ws
  induction ws with
  | nil => rintro ⟨s, hs, _⟩; cases hs
  | cons x r ih =>
    rintro ⟨s, hs, hsT⟩
    by_cases hx : x.1 ∈ T
    · exact ⟨[], x, r, rfl, hx, fun s hs => by cases hs⟩
    · have : ∃ s ∈ r, s.1 ∈ T := by
        rcases List.mem_cons.mp hs with h | h
        · subst h; exact absurd hsT hx
        · exact ⟨s, h, hsT⟩
      obtain ⟨u, t, v, h1, h2, h3⟩ := ih this
      refine ⟨x :: u, t, v, by rw [h1]; rfl, h2, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with h | h
      · rw [h]; exact hx
      · exact h3 s h

theorem cover_walk (I : RPInstance) (S : Finset (Fin I.n)) :
    ∀ (n : ℕ) (T : Finset (Fin I.arcs.length)), T.card = n →
    ∀ (ws : List I.Traversal) (a b : Fin I.n), (∀ t ∈ ws, I.trSrc t ∈ S) → I.Walk a b ws →
    (∀ e ∈ T, ∃ x, (e, x) ∈ ws) →
    ∃ ws', ws'.Sublist ws ∧ I.Walk a b ws' ∧ (∀ e ∈ T, ∃ x, (e, x) ∈ ws') ∧
      ws'.length ≤ (n + 1) * S.card + n := by
  intro n
  induction n with
  | zero =>
    intro T hT ws a b hS hw hc
    obtain ⟨ws', h1, h2, h3⟩ := erase_loops I S ws a b hS hw
    have hT0 : T = ∅ := Finset.card_eq_zero.mp hT
    refine ⟨ws', h1, h2, ?_, ?_⟩
    · intro e he; rw [hT0] at he; cases he
    · have := nodup_len I S ws' (fun t ht => hS t (h1.subset ht)) h3
      omega
  | succ n ih =>
    intro T hT ws a b hS hw hc
    have hne : T.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨e0, he0⟩ := hne
    obtain ⟨x0, hx0⟩ := hc e0 he0
    obtain ⟨u, t, v, hws, ht, hu⟩ := first_in I T ws ⟨(e0, x0), hx0, he0⟩
    subst hws
    obtain ⟨c1, hc1, hc2⟩ := (walk_append I u (t :: v) _ _).mp hw
    have hts : I.trSrc t = c1 := hc2.1
    have hvw : I.Walk (I.trDst t) b v := hc2.2
    have hT' : (T.erase t.1).card = n := by
      rw [Finset.card_erase_of_mem ht]; omega
    have hcv : ∀ e ∈ T.erase t.1, ∃ x, (e, x) ∈ v := by
      intro e he
      have heT : e ∈ T := Finset.mem_of_mem_erase he
      have hne : e ≠ t.1 := Finset.ne_of_mem_erase he
      obtain ⟨x, hx⟩ := hc e heT
      rcases List.mem_append.mp hx with h | h
      · exact absurd heT (by simpa using hu _ h)
      · rcases List.mem_cons.mp h with h | h
        · exact absurd (congrArg Prod.fst h) hne
        · exact ⟨x, h⟩
    obtain ⟨v', hv1, hv2, hv3, hv4⟩ := ih (T.erase t.1) hT' v (I.trDst t) b
      (fun s hs => hS s (by simp [hs])) hvw hcv
    obtain ⟨u', hu1, hu2, hu3⟩ := erase_loops I S u a c1
      (fun s hs => hS s (by simp [hs])) hc1
    have hlen := nodup_len I S u' (fun s hs => hS s (by simp [hu1.subset hs])) hu3
    refine ⟨u' ++ t :: v', hu1.append (hv1.cons_cons t), ?_, ?_, ?_⟩
    · exact (walk_append I u' (t :: v') _ _).mpr ⟨c1, hu2, hts, hv2⟩
    · intro e he
      by_cases hee : e = t.1
      · exact ⟨t.2, by subst hee; simp⟩
      · obtain ⟨x, hx⟩ := hv3 e (Finset.mem_erase.mpr ⟨hee, he⟩)
        exact ⟨x, by simp [hx]⟩
    · rw [List.length_append, List.length_cons]
      have : (n + 1 + 1) * S.card = S.card + (n + 1) * S.card := by ring
      omega

end RPInstance
end RuralPostman.NPC

end Sec_RP1

section Sec_RP2

namespace RuralPostman.NPC
namespace RPInstance

theorem walk_props (I : RPInstance) : ∀ (l : List I.Traversal) (a b : Fin I.n), I.Walk a b l →
    (∀ i (h : i + 1 < l.length), I.trDst (l[i]'(by omega)) = I.trSrc (l[i+1]'h)) ∧
    ∀ (h : l ≠ []), I.trSrc (l.head h) = a ∧ I.trDst (l.getLast h) = b := by
  intro l
  induction l with
  | nil =>
    intro a b _
    refine ⟨fun i h => by simp at h, fun h => absurd rfl h⟩
  | cons t r ih =>
    intro a b w
    obtain ⟨h1, h2⟩ := w
    refine ⟨?_, ?_⟩
    · intro i hi
      cases r with
      | nil => simp at hi
      | cons s r' =>
        cases i with
        | zero =>
          have := h2.1
          simpa using this.symm
        | succ k =>
          have := (ih _ _ h2).1 k (by simpa using hi)
          simpa using this
    · intro _
      refine ⟨by simpa using h1, ?_⟩
      cases r with
      | nil => have : I.trDst t = b := h2; simpa using this
      | cons s r' =>
        have := (ih _ _ h2).2 (by simp)
        simpa [List.getLast_cons] using this.2

theorem walk_of_chain (I : RPInstance) : ∀ (l : List I.Traversal) (h : l ≠ []),
    (∀ i (hi : i + 1 < l.length), I.trDst (l[i]'(by omega)) = I.trSrc (l[i+1]'hi)) →
    I.Walk (I.trSrc (l.head h)) (I.trDst (l.getLast h)) l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons t r ih =>
    intro _ hc
    cases r with
    | nil => exact ⟨rfl, rfl⟩
    | cons s r' =>
      have h0 := hc 0 (by simp)
      have h1 := ih (by simp) (fun i hi => by
        have := hc (i+1) (by simpa using hi)
        simpa using this)
      refine ⟨rfl, ?_⟩
      simp only [List.head_cons] at h1
      have h0' : I.trDst t = I.trSrc s := by simpa using h0
      rw [h0']
      simpa [List.getLast_cons] using h1

theorem finRot_succ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) : (finRotate n i).val = i.val + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    have : i ≠ Fin.last m := by
      intro hh; rw [hh] at hi; simp at hi
    simp [this]

theorem finRot_last (n : ℕ) (i : Fin n) (hi : i.val + 1 = n) : (finRotate n i).val = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    have : i = Fin.last m := Fin.ext (by simpa using hi)
    simp [this]

theorem tour_to_walk (I : RPInstance) (τ : List I.Traversal) (hne : τ ≠ [])
    (h : ∀ i : Fin τ.length, I.trDst (τ.get i) = I.trSrc (τ.get (finRotate τ.length i))) :
    I.Walk (I.trSrc (τ.head hne)) (I.trSrc (τ.head hne)) τ := by
  have hc : ∀ i (hi : i + 1 < τ.length), I.trDst (τ[i]'(by omega)) = I.trSrc (τ[i+1]'hi) := by
    intro i hi
    have := h ⟨i, by omega⟩
    have hr : finRotate τ.length ⟨i, by omega⟩ = ⟨i+1, hi⟩ :=
      Fin.ext (finRot_succ _ _ hi)
    rw [hr] at this
    simpa using this
  have hw := walk_of_chain I τ hne hc
  have hlen : 0 < τ.length := List.length_pos_of_ne_nil hne
  have hl := h ⟨τ.length - 1, by omega⟩
  have hr : finRotate τ.length ⟨τ.length - 1, by omega⟩ = ⟨0, hlen⟩ :=
    Fin.ext (finRot_last _ _ (by simp; omega))
  rw [hr] at hl
  have e1 : I.trDst (τ.getLast hne) = I.trSrc (τ.head hne) := by
    rw [List.getLast_eq_getElem, List.head_eq_getElem]
    simpa using hl
  rw [e1] at hw
  exact hw

theorem walk_to_tour (I : RPInstance) (τ : List I.Traversal) (a : Fin I.n) (hw : I.Walk a a τ) :
    ∀ i : Fin τ.length, I.trDst (τ.get i) = I.trSrc (τ.get (finRotate τ.length i)) := by
  obtain ⟨hc, hb⟩ := walk_props I τ a a hw
  intro i
  by_cases hi : i.val + 1 < τ.length
  · have hr : finRotate τ.length i = ⟨i.val+1, hi⟩ := Fin.ext (finRot_succ _ _ hi)
    rw [hr]
    simpa using hc i.val hi
  · have hne : τ ≠ [] := by
      intro hh; have h2 := i.2; simp [hh] at h2
    have hi' : i.val + 1 = τ.length := by have := i.2; omega
    have hr : finRotate τ.length i = ⟨0, by omega⟩ := Fin.ext (finRot_last _ _ hi')
    rw [hr]
    obtain ⟨hb1, hb2⟩ := hb hne
    have : τ.get i = τ.getLast hne := by
      rw [List.getLast_eq_getElem]
      simp only [List.get_eq_getElem]
      congr 1
      omega
    rw [this, hb2]
    have : τ.get ⟨0, by omega⟩ = τ.head hne := by
      rw [List.head_eq_getElem]; simp
    rw [this, hb1]

end RPInstance
end RuralPostman.NPC

end Sec_RP2

section Sec_RP3

namespace RuralPostman.NPC
namespace RPInstance

theorem tour_compress (I : RPInstance) (d : Bool) (τ : List I.Traversal) (h : I.IsTour d τ) :
    ∃ τ', I.IsTour d τ' ∧ τ'.Sublist τ ∧
      τ'.length ≤ (I.arcs.length + 1) * (2 * I.arcs.length) + I.arcs.length := by
  obtain ⟨hd, hcyc, hreq⟩ := h
  by_cases hne : τ = []
  · subst hne
    exact ⟨[], ⟨hd, hcyc, hreq⟩, List.Sublist.slnil, Nat.zero_le _⟩
  · have hw := tour_to_walk I τ hne hcyc
    let S : Finset (Fin I.n) :=
      (Finset.univ.image fun e : Fin I.arcs.length => (I.arcs.get e).1) ∪
      (Finset.univ.image fun e : Fin I.arcs.length => (I.arcs.get e).2.1)
    have hSc : S.card ≤ 2 * I.arcs.length := by
      calc S.card ≤ (Finset.univ.image fun e : Fin I.arcs.length => (I.arcs.get e).1).card +
            (Finset.univ.image fun e : Fin I.arcs.length => (I.arcs.get e).2.1).card :=
            Finset.card_union_le _ _
        _ ≤ I.arcs.length + I.arcs.length := by
            apply Nat.add_le_add
            · calc _ ≤ (Finset.univ : Finset (Fin I.arcs.length)).card := Finset.card_image_le
                _ = _ := by simp
            · calc _ ≤ (Finset.univ : Finset (Fin I.arcs.length)).card := Finset.card_image_le
                _ = _ := by simp
        _ = 2 * I.arcs.length := by omega
    have hS : ∀ t ∈ τ, I.trSrc t ∈ S := by
      intro t _
      unfold trSrc
      by_cases hb : t.2 = true
      · rw [if_pos hb]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t.1, Finset.mem_univ _, rfl⟩)
      · rw [if_neg hb]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t.1, Finset.mem_univ _, rfl⟩)
    let T : Finset (Fin I.arcs.length) := Finset.univ.filter fun e => I.IsRequired e
    have hTc : T.card ≤ I.arcs.length := by
      calc T.card ≤ (Finset.univ : Finset (Fin I.arcs.length)).card := Finset.card_filter_le _ _
        _ = _ := by simp
    have hcov : ∀ e ∈ T, ∃ x, (e, x) ∈ τ := by
      intro e he
      have : I.IsRequired e := (Finset.mem_filter.mp he).2
      exact hreq e this
    obtain ⟨τ', h1, h2, h3, h4⟩ := cover_walk I S T.card T rfl τ _ _ hS hw hcov
    refine ⟨τ', ⟨?_, walk_to_tour I τ' _ h2, ?_⟩, h1, ?_⟩
    · intro hdd t ht; exact hd hdd t (h1.subset ht)
    · intro e he
      exact h3 e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    · calc τ'.length ≤ (T.card + 1) * S.card + T.card := h4
        _ ≤ (I.arcs.length + 1) * (2 * I.arcs.length) + I.arcs.length :=
          Nat.add_le_add (Nat.mul_le_mul (by omega) hSc) hTc

theorem RPYes_short (I : RPInstance) (d : Bool) (h : I.RPYes d) :
    ∃ τ, I.IsTour d τ ∧ I.tourWeight τ ≤ I.k ∧
      τ.length ≤ (I.arcs.length + 1) * (2 * I.arcs.length) + I.arcs.length := by
  obtain ⟨τ, h1, h2⟩ := h
  obtain ⟨τ', h3, h4, h5⟩ := tour_compress I d τ h1
  refine ⟨τ', h3, le_trans ?_ h2, h5⟩
  unfold tourWeight
  exact (h4.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

end RPInstance
end RuralPostman.NPC

end Sec_RP3

section Sec_RPV21
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def arcQ (qs : List Q4) (i : ℕ) : Option (ℕ × ℕ × ℕ) := (qs[i]?).map (fun q => (q.1, q.2.1, q.2.2.1))

lemma arcOf_flat (k : ℕ) : ∀ (qs : List Q4) (i : ℕ), arcOf (flatQ qs ++ [k]) i = arcQ qs i := by
  intro qs
  induction qs with
  | nil =>
    intro i
    simp only [arcQ, flatQ, List.nil_append, List.getElem?_nil, Option.map_none]
    unfold arcOf
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have : (4 * i) ≥ 1 := by omega
      rw [List.drop_of_length_le (by simp; omega)]
  | cons q qs ih =>
    intro i
    obtain ⟨s, d, wt, r⟩ := q
    cases i with
    | zero => simp [arcOf, arcQ, flatQ]
    | succ i =>
      have e : flatQ ((s, d, wt, r) :: qs) ++ [k] = s :: d :: wt :: r :: (flatQ qs ++ [k]) := by simp [flatQ]
      have e2 : 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 := by omega
      have := ih i
      simp only [arcOf, arcQ, e, e2, List.drop_succ_cons] at this ⊢
      simpa using this

def srcQ (qs : List Q4) (p : ℕ × Bool) : ℕ :=
  match qs[p.1]? with | some q => (st' p.2 q.1 q.2.1).1 | none => 0
def dstQ (qs : List Q4) (p : ℕ × Bool) : ℕ :=
  match qs[p.1]? with | some q => (st' p.2 q.1 q.2.1).2 | none => 0

def chainFrom (qs : List Q4) : Option ℕ → List (ℕ × Bool) → Prop
  | _, [] => True
  | none, p :: l => chainFrom qs (some (dstQ qs p)) l
  | some m, p :: l => m = srcQ qs p ∧ chainFrom qs (some (dstQ qs p)) l

lemma okf_iff (d : Bool) (qs : List Q4) (k : ℕ) (y : Ys) (hy : y.fl = flatQ qs ++ [k]) (p : ℕ × Bool) :
    okf d y p ↔ (p.1 < qs.length ∧ p.1 < y.vis.length ∧ (d = true → p.2 = false)) ∧
      (match y.ch with | none => True | some (_, m) => m = srcQ qs p) := by
  unfold okf
  rw [hy, arcOf_flat]
  unfold arcQ
  rcases hq : qs[p.1]? with _ | q
  · simp only [Option.map_none]
    have : ¬ p.1 < qs.length := by
      intro h; rw [List.getElem?_eq_getElem h] at hq; simp at hq
    simp [this]
  · simp only [Option.map_some]
    have hlt : p.1 < qs.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hq; simp at hq
    simp only [srcQ, hq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨hlt, h2, ?_⟩, h3⟩
      intro hd; by_contra hp; exact h1 ⟨hd, by simpa using hp⟩
    · rintro ⟨⟨_, h2, h1⟩, h3⟩
      refine ⟨?_, h2, h3⟩
      rintro ⟨hd, hp⟩; have := h1 hd; simp [hp] at this

lemma nxt_ch_snd (qs : List Q4) (k : ℕ) (y : Ys) (hy : y.fl = flatQ qs ++ [k]) (p : ℕ × Bool) (hp : p.1 < qs.length) :
    (nxt y p).ch.map Prod.snd = some (dstQ qs p) := by
  unfold nxt
  rw [hy, arcOf_flat]
  unfold arcQ
  have hq : qs[p.1]? = some qs[p.1] := List.getElem?_eq_getElem hp
  simp only [hq, Option.map_some, dstQ]

lemma fold_iff (d : Bool) (qs : List Q4) (k : ℕ) : ∀ (items : List (ℕ × Bool)) (y : Ys), y.fl = flatQ qs ++ [k] →
    (foldOK (okf d) nxt y items ↔ (∀ p ∈ items, p.1 < qs.length ∧ p.1 < y.vis.length ∧ (d = true → p.2 = false)) ∧
      chainFrom qs (y.ch.map Prod.snd) items) := by
  intro items
  induction items with
  | nil => intro y _; simp [foldOK, chainFrom]
  | cons p l ih =>
    intro y hy
    simp only [foldOK]
    rw [okf_iff d qs k y hy p]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩
      have hy' : (nxt y p).fl = flatQ qs ++ [k] := by rw [nxt_fl, hy]
      obtain ⟨i1, i2⟩ := (ih _ hy').mp h5
      rw [nxt_vis_len] at i1
      rw [nxt_ch_snd qs k y hy p h1] at i2
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hm
        · exact ⟨h1, h2, h3⟩
        · exact i1 q hm
      · rcases hc : y.ch with _ | ⟨f, m⟩
        · simpa [hc, chainFrom] using i2
        · rw [hc] at h4
          simpa [hc, chainFrom] using ⟨h4, i2⟩
    · rintro ⟨i1, i2⟩
      have hp := i1 p (List.mem_cons_self ..)
      have hy' : (nxt y p).fl = flatQ qs ++ [k] := by rw [nxt_fl, hy]
      refine ⟨⟨hp, ?_⟩, (ih _ hy').mpr ⟨?_, ?_⟩⟩
      · rcases hc : y.ch with _ | ⟨f, m⟩
        · simp
        · rw [hc] at i2
          simpa [chainFrom] using i2.1
      · intro q hq
        have := i1 q (List.mem_cons_of_mem _ hq)
        rwa [nxt_vis_len]
      · rw [nxt_ch_snd qs k y hy p hp.1]
        rcases hc : y.ch with _ | ⟨f, m⟩
        · simpa [hc, chainFrom] using i2
        · rw [hc] at i2; simpa [chainFrom] using i2.2

def lastOf : (ℕ × Bool) → List (ℕ × Bool) → (ℕ × Bool)
  | p, [] => p
  | _, q :: l => lastOf q l

lemma nxt_ch_fst (qs : List Q4) (k : ℕ) (y : Ys) (hy : y.fl = flatQ qs ++ [k]) (p : ℕ × Bool) (hp : p.1 < qs.length) :
    ∃ f m, (nxt y p).ch = some (f, m) ∧ m = dstQ qs p ∧
      f = (match y.ch with | none => srcQ qs p | some (f0, _) => f0) := by
  unfold nxt
  rw [hy, arcOf_flat]
  unfold arcQ
  have hq : qs[p.1]? = some qs[p.1] := List.getElem?_eq_getElem hp
  simp only [hq, Option.map_some, dstQ, srcQ]
  rcases hc : y.ch with _ | ⟨f, m⟩ <;> simp

lemma foldl_ch (qs : List Q4) (k : ℕ) : ∀ (l : List (ℕ × Bool)) (p : ℕ × Bool) (y : Ys), y.fl = flatQ qs ++ [k] →
    (∀ q ∈ p :: l, q.1 < qs.length) →
    ∃ f, (l.foldl nxt (nxt y p)).ch = some (f, dstQ qs (lastOf p l)) ∧
      f = (match y.ch with | none => srcQ qs p | some (f0, _) => f0) := by
  intro l
  induction l with
  | nil =>
    intro p y hy hl
    obtain ⟨f, m, h1, h2, h3⟩ := nxt_ch_fst qs k y hy p (hl p (by simp))
    exact ⟨f, by simp [lastOf, h1, h2], h3⟩
  | cons q l ih =>
    intro p y hy hl
    have hy' : (nxt y p).fl = flatQ qs ++ [k] := by rw [nxt_fl, hy]
    obtain ⟨f, m, h1, h2, h3⟩ := nxt_ch_fst qs k y hy p (hl p (by simp))
    obtain ⟨f', e1, e2⟩ := ih q (nxt y p) hy' (fun x hx => hl x (by
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
    refine ⟨f', by simpa [lastOf] using e1, ?_⟩
    rw [e2, h1, h3]

def wtQ (qs : List Q4) (p : ℕ × Bool) : ℕ :=
  match qs[p.1]? with | some q => q.2.2.1 | none => 0

lemma nxt_va (qs : List Q4) (k : ℕ) (y : Ys) (hy : y.fl = flatQ qs ++ [k]) (p : ℕ × Bool) (hp : p.1 < qs.length) :
    (nxt y p).vis = y.vis.set p.1 true ∧ val (nxt y p).a = val y.a + wtQ qs p := by
  unfold nxt
  rw [hy, arcOf_flat]
  unfold arcQ
  have hq : qs[p.1]? = some qs[p.1] := List.getElem?_eq_getElem hp
  simp only [hq, Option.map_some, wtQ]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl | simp [val_addBits, val_bits]

lemma foldl_va (qs : List Q4) (k : ℕ) : ∀ (l : List (ℕ × Bool)) (y : Ys), y.fl = flatQ qs ++ [k] →
    (∀ q ∈ l, q.1 < qs.length ∧ q.1 < y.vis.length) →
    val (l.foldl nxt y).a = val y.a + (l.map (wtQ qs)).sum ∧
    (l.foldl nxt y).vis.length = y.vis.length ∧
    ∀ i, (l.foldl nxt y).vis[i]? = if (∃ b, (i, b) ∈ l) then some true else y.vis[i]? := by
  intro l
  induction l with
  | nil => intro y _ _; simp
  | cons p l ih =>
    intro y hy hl
    have hy' : (nxt y p).fl = flatQ qs ++ [k] := by rw [nxt_fl, hy]
    obtain ⟨h1, h2⟩ := nxt_va qs k y hy p (hl p (by simp)).1
    have hlen : (nxt y p).vis.length = y.vis.length := by rw [h1, List.length_set]
    obtain ⟨i1, i2, i3⟩ := ih (nxt y p) hy' (fun q hq => by
      have := hl q (List.mem_cons_of_mem _ hq); rw [hlen]; exact this)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.foldl_cons, List.map_cons, List.sum_cons, i1, h2]; ring
    · simp only [List.foldl_cons, i2, hlen]
    · intro i
      simp only [List.foldl_cons, i3, h1]
      by_cases hb : ∃ b, (i, b) ∈ l
      · have : ∃ b, (i, b) ∈ p :: l := by obtain ⟨b, hb⟩ := hb; exact ⟨b, List.mem_cons_of_mem _ hb⟩
        rw [if_pos hb, if_pos this]
      · by_cases hi : i = p.1
        · subst hi
          have : ∃ b, (p.1, b) ∈ p :: l := ⟨p.2, by simp⟩
          have hlt := (hl p (by simp)).2
          rw [if_neg hb, if_pos this]; simp [hlt]
        · have : ¬ ∃ b, (i, b) ∈ p :: l := by
            rintro ⟨b, hb'⟩
            rcases List.mem_cons.mp hb' with h | h
            · exact hi (by rw [← h])
            · exact hb ⟨b, h⟩
          rw [if_neg hb, if_neg this, List.getElem?_set_ne (Ne.symm hi)]

open RuralPostman.NPC in
def mkI (n : ℕ) (qs : List Q4) (k : ℕ) (hq : ∀ q ∈ qs, QOk n q) : RPInstance :=
  ⟨n, qs.pmap (fun q h => ((⟨q.1, h.1⟩ : Fin n), (⟨q.2.1, h.2.1⟩ : Fin n), q.2.2.1, decide (q.2.2.2 = 1))) hq, k⟩

open RuralPostman.NPC in
lemma mkI_len (n : ℕ) (qs : List Q4) (k : ℕ) (hq : ∀ q ∈ qs, QOk n q) : (mkI n qs k hq).arcs.length = qs.length := by
  simp [mkI]

open RuralPostman.NPC in
lemma mkI_get (n : ℕ) (qs : List Q4) (k : ℕ) (hq : ∀ q ∈ qs, QOk n q) (j : ℕ) (hj : j < (mkI n qs k hq).arcs.length) :
    ∃ hj' : j < qs.length, ((mkI n qs k hq).arcs[j]).1.val = (qs[j]'hj').1 ∧ ((mkI n qs k hq).arcs[j]).2.1.val = (qs[j]'hj').2.1 ∧
      ((mkI n qs k hq).arcs[j]).2.2.1 = (qs[j]'hj').2.2.1 ∧ ((mkI n qs k hq).arcs[j]).2.2.2 = decide ((qs[j]'hj').2.2.2 = 1) := by
  have hj' : j < qs.length := by rw [mkI_len] at hj; exact hj
  refine ⟨hj', ?_⟩
  simp [mkI, List.getElem_pmap]


lemma chain_idx (qs : List Q4) : ∀ (l : List (ℕ × Bool)) (m : ℕ), chainFrom qs (some m) l →
    (∀ p l', l = p :: l' → m = srcQ qs p) ∧ ∀ j (hj : j + 1 < l.length), dstQ qs l[j] = srcQ qs l[j+1] := by
  intro l
  induction l with
  | nil => intro m _; simp
  | cons p l ih =>
    intro m h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih _ h2
    refine ⟨?_, ?_⟩
    · intro p' l' e; cases e; exact h1
    · intro j hj
      cases j with
      | zero =>
        cases l with
        | nil => simp at hj
        | cons q l' => exact ih1 q l' rfl
      | succ j => exact ih2 j (by simpa using hj)

lemma lastOf_eq (p : ℕ × Bool) : ∀ (l : List (ℕ × Bool)) (h : (p :: l) ≠ []), lastOf p l = (p :: l).getLast h := by
  intro l
  induction l generalizing p with
  | nil => intro h; simp [lastOf]
  | cons q l ih =>
    intro h
    rw [lastOf, ih q (by simp), List.getLast_cons_cons]


open RuralPostman.NPC in
lemma tr_val (n : ℕ) (qs : List Q4) (k : ℕ) (hq : ∀ q ∈ qs, QOk n q) (p : ℕ × Bool)
    (h : p.1 < (mkI n qs k hq).arcs.length) :
    ((mkI n qs k hq).trSrc (⟨p.1, h⟩, !p.2)).val = srcQ qs p ∧
    ((mkI n qs k hq).trDst (⟨p.1, h⟩, !p.2)).val = dstQ qs p ∧
    (((mkI n qs k hq).arcs.get ⟨p.1, h⟩).2.2.1 = wtQ qs p) := by
  obtain ⟨hj', h1, h2, h3, h4⟩ := mkI_get n qs k hq p.1 h
  have hq' : qs[p.1]? = some qs[p.1] := List.getElem?_eq_getElem hj'
  obtain ⟨a, b⟩ := p
  cases b <;> simp [RPInstance.trSrc, RPInstance.trDst, srcQ, dstQ, wtQ, hq', st', h1, h2, h3] at *


open RuralPostman.NPC in
lemma isTour_of (d : Bool) (n : ℕ) (qs : List Q4) (k : ℕ) (hq : ∀ q ∈ qs, QOk n q) (items : List (ℕ × Bool))
    (hb1 : ∀ p ∈ items, p.1 < qs.length) (hb2 : d = true → ∀ p ∈ items, p.2 = false)
    (hch : ∀ j (hj : j + 1 < items.length), dstQ qs items[j] = srcQ qs items[j+1])
    (hcl : ∀ p l, items = p :: l → dstQ qs (lastOf p l) = srcQ qs p)
    (hcov : ∀ e (he : e < qs.length), (qs[e]).2.2.2 = 1 → ∃ b, (e, b) ∈ items) :
    ∃ τ : List (mkI n qs k hq).Traversal, (mkI n qs k hq).IsTour d τ ∧
      (mkI n qs k hq).tourWeight τ = (items.map (wtQ qs)).sum := by
  have hb1' : ∀ p ∈ items, p.1 < (mkI n qs k hq).arcs.length := fun p hp => by rw [mkI_len]; exact hb1 p hp
  let τ : List (mkI n qs k hq).Traversal :=
    items.pmap (fun p h => ((⟨p.1, h⟩ : Fin (mkI n qs k hq).arcs.length), !p.2)) hb1'
  have hlen : τ.length = items.length := by simp [τ]
  have hget : ∀ j (hj : j < τ.length), ∃ hj2 : j < items.length,
      τ[j] = ((⟨(items[j]).1, hb1' _ (List.getElem_mem hj2)⟩ : Fin (mkI n qs k hq).arcs.length), !(items[j]).2) := by
    intro j hj
    have hj2 : j < items.length := by rw [← hlen]; exact hj
    exact ⟨hj2, by simp [τ, List.getElem_pmap]⟩
  have hv : ∀ j (hj : j < τ.length), ∃ hj2 : j < items.length,
      ((mkI n qs k hq).trSrc τ[j]).val = srcQ qs items[j] ∧ ((mkI n qs k hq).trDst τ[j]).val = dstQ qs items[j] ∧
      ((mkI n qs k hq).arcs.get τ[j].1).2.2.1 = wtQ qs items[j] := by
    intro j hj
    obtain ⟨hj2, e⟩ := hget j hj
    refine ⟨hj2, ?_⟩
    rw [e]
    exact tr_val n qs k hq _ _
  refine ⟨τ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro hd t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_pmap.mp ht
    simp [hb2 hd a ha]
  · intro i
    have hi : i.val < τ.length := i.2
    obtain ⟨hj2, a1, a2, a3⟩ := hv i.val hi
    apply Fin.ext
    have hg : τ.get i = τ[i.val] := rfl
    rw [hg, a2]
    by_cases hlast : i.val + 1 < τ.length
    · have hr : (finRotate τ.length i).val = i.val + 1 := RPInstance.finRot_succ _ _ hlast
      have hg2 : τ.get (finRotate τ.length i) = τ[i.val + 1] := by
        simp only [List.get_eq_getElem, hr]
      obtain ⟨hj3, b1, b2, b3⟩ := hv (i.val + 1) hlast
      rw [hg2, b1]
      exact hch i.val (by rw [← hlen]; exact hlast)
    · have hr : (finRotate τ.length i).val = 0 := RPInstance.finRot_last _ _ (by omega)
      have hne : 0 < τ.length := by omega
      have hg2 : τ.get (finRotate τ.length i) = τ[0] := by
        simp only [List.get_eq_getElem, hr]
      obtain ⟨hj3, b1, b2, b3⟩ := hv 0 hne
      rw [hg2, b1]
      obtain ⟨p, l, hl⟩ : ∃ p l, items = p :: l :=
        List.exists_cons_of_ne_nil (by intro h; rw [h] at hj2; simp at hj2)
      have h1 := hcl p l hl
      have h' : lastOf p l = items.getLast (by rw [hl]; simp) := by
        subst hl; exact lastOf_eq p l _
      have e1 : items[i.val] = lastOf p l := by
        rw [h', List.getLast_eq_getElem]
        congr 1
        have := i.2; omega
      have e2 : ∀ h, items[0]'h = p := by intro h; subst hl; rfl
      rw [e1, e2]
      exact h1
  · intro e he
    unfold RPInstance.IsRequired at he
    obtain ⟨hj', h1, h2, h3, h4⟩ := mkI_get n qs k hq e.val e.2
    have he1 : (qs[e.val]'hj').2.2.2 = 1 := by
      have : (mkI n qs k hq).arcs[e.val] = (mkI n qs k hq).arcs.get e := rfl
      rw [← this, h4] at he; simpa using he
    obtain ⟨b, hb⟩ := hcov e.val hj' he1
    refine ⟨!b, List.mem_pmap.mpr ⟨(e.val, b), hb, ?_⟩⟩
    simp
  · unfold RPInstance.tourWeight
    have : τ.map (fun t => ((mkI n qs k hq).arcs.get t.1).2.2.1) = items.map (wtQ qs) := by
      apply List.ext_getElem (by simp [hlen])
      intro j h1 h2
      obtain ⟨hj2, a1, a2, a3⟩ := hv j (by simpa using h1)
      simpa using a3
    rw [this]


lemma chain_none (qs : List Q4) (p : ℕ × Bool) (l : List (ℕ × Bool)) (h : chainFrom qs none (p :: l)) :
    ∀ j (hj : j + 1 < (p :: l).length), dstQ qs (p :: l)[j] = srcQ qs (p :: l)[j+1] := by
  obtain ⟨ih1, ih2⟩ := chain_idx qs l _ h
  intro j hj
  cases j with
  | zero =>
    cases l with
    | nil => simp at hj
    | cons q l' => exact ih1 q l' rfl
  | succ j => exact ih2 j (by simpa using hj)

lemma PBok_get (n : ℕ) : ∀ (qs : List Q4) (vis : List Bool), PBok n qs vis → qs.length ≤ vis.length →
    ∀ e (he : e < qs.length), (qs[e]).2.2.2 = 1 → vis[e]? = some true := by
  intro qs
  induction qs with
  | nil => intro vis _ _ e he; simp at he
  | cons q qs ih =>
    intro vis hp hl e he hr
    cases vis with
    | nil => simp at hl
    | cons b vis =>
      obtain ⟨_, h2, h3⟩ := hp
      cases e with
      | zero => simp at hr ⊢; exact h2 hr
      | succ e =>
        simp at hr ⊢
        exact ih vis h3 (by simpa using hl) e (by simpa using he) hr

lemma sound_RP (d : Bool) (x0 : List Al) (r : GR) (h : Q9 d x0 r) :
    ∃ hq : ∀ q ∈ r.c.c.qs, QOk r.c.c.g.n q,
      (mkI r.c.c.g.n r.c.c.qs r.c.k hq).RPYes d := by
  obtain ⟨⟨⟨⟨⟨_, _, hlen, hq, _⟩, _⟩, _, hfold⟩, hpb⟩, hk, hcl⟩ := h
  refine ⟨hq, ?_⟩
  set qs := r.c.c.qs with hqs
  set k := r.c.k with hkk
  set items := r.items with hit
  have hy : (Y0 r.c).fl = flatQ qs ++ [k] := rfl
  have hch0 : (Y0 r.c).ch = none := rfl
  have hvl : (Y0 r.c).vis = List.replicate r.c.c.g.L false := rfl
  have hfi := (fold_iff d qs k items (Y0 r.c) hy).mp hfold
  obtain ⟨hb, hchain⟩ := hfi
  rw [hch0] at hchain
  simp only [Option.map_none] at hchain
  have hvlen : (Y0 r.c).vis.length = qs.length := by rw [hvl, List.length_replicate, hlen]
  have hb1 : ∀ p ∈ items, p.1 < qs.length := fun p hp => (hb p hp).1
  have hb1v : ∀ p ∈ items, p.1 < qs.length ∧ p.1 < (Y0 r.c).vis.length :=
    fun p hp => ⟨(hb p hp).1, (hb p hp).2.1⟩
  obtain ⟨va1, va2, va3⟩ := foldl_va qs k items (Y0 r.c) hy hb1v
  have hyE : yE r = items.foldl nxt (Y0 r.c) := rfl
  have hcov : ∀ e (he : e < qs.length), (qs[e]).2.2.2 = 1 → ∃ b, (e, b) ∈ items := by
    intro e he hr
    have h1 := PBok_get r.c.c.g.n qs (yE r).vis hpb (by rw [hyE, va2, hvlen]) e he hr
    rw [hyE, va3 e] at h1
    by_cases hx : ∃ b, (e, b) ∈ items
    · exact hx
    · rw [if_neg hx, hvl] at h1
      simp [List.getElem?_replicate, ← hlen, he] at h1
  have hnil : items = [] ∨ ∃ p l, items = p :: l := by
    cases items with
    | nil => left; rfl
    | cons p l => right; exact ⟨p, l, rfl⟩
  have hch : ∀ j (hj : j + 1 < items.length), dstQ qs items[j] = srcQ qs items[j+1] := by
    rcases hnil with he | ⟨p, l, he⟩
    · intro j hj; rw [he] at hj; simp at hj
    · have := chain_none qs p l (by rw [← he]; exact hchain)
      intro j hj
      have h2 := this j (by rw [← he]; exact hj)
      simpa [he] using h2
  have hcl' : ∀ p l, items = p :: l → dstQ qs (lastOf p l) = srcQ qs p := by
    intro p l he
    have hall : ∀ q ∈ p :: l, q.1 < qs.length := fun q hq => hb1 q (by rw [he]; exact hq)
    obtain ⟨f, hf1, hf2⟩ := foldl_ch qs k l p (Y0 r.c) hy hall
    have : yE r = l.foldl nxt (nxt (Y0 r.c) p) := by rw [hyE, he]; rfl
    rw [this, hf1] at hcl
    simp only [clo] at hcl
    rw [hch0] at hf2
    simp only at hf2
    rw [hcl, hf2]
  obtain ⟨τ, htour, hw⟩ := isTour_of d r.c.c.g.n qs k hq items hb1
    (fun hd p hp => (hb p hp).2.2 hd) hch hcl' hcov
  refine ⟨τ, htour, ?_⟩
  show (mkI r.c.c.g.n qs k hq).tourWeight τ ≤ k
  rw [hw]
  have : val (yE r).a = (items.map (wtQ qs)).sum := by
    rw [hyE, va1]; simp [Y0, val]
  omega


lemma encFlat_encNats : ∀ l : List ℕ, (encNats l).map tk = encFlat l := by
  intro l
  induction l with
  | nil => simp [encNats, encFlat]
  | cons a l ih =>
    have : encNats (a :: l) = encNat a ++ encNats l := by simp [encNats]
    rw [this, List.map_append, ih]
    simp [encNat, encFlat, tkb, tk]

lemma flat_pmap (n : ℕ) : ∀ (qs : List Q4) (hq : ∀ q ∈ qs, QOk n q),
    (qs.pmap (fun q h => ((⟨q.1, h.1⟩ : Fin n), (⟨q.2.1, h.2.1⟩ : Fin n), q.2.2.1, decide (q.2.2.2 = 1))) hq).flatMap
      (fun a => [a.1.val, a.2.1.val, a.2.2.1, if a.2.2.2 then 1 else 0]) = flatQ qs := by
  intro qs
  induction qs with
  | nil => intro hq; simp [flatQ]
  | cons q qs ih =>
    intro hq
    obtain ⟨s, d, w, r⟩ := q
    have hr : r ≤ 1 := (hq (s, d, w, r) (by simp)).2.2
    have := ih (fun q h => hq q (List.mem_cons_of_mem _ h))
    simp only [List.pmap, List.flatMap_cons, this, flatQ]
    have h1 : (if r = 1 then 1 else 0) = r := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with rfl | rfl <;> simp
    simp [h1]


open RuralPostman.NPC in
lemma w_eq (g : Gh) (hH : Hh g) (qs : List Q4) (hL : qs.length = g.L) (hq : ∀ q ∈ qs, QOk g.n q)
    (y' : List Al) (hr : g.rest = encFlat (flatQ qs) ++ y') (k : ℕ) (hk : y' = encFlat [k]) :
    g.w = rpCode (mkI g.n qs k hq) := by
  have hinj : Function.Injective tk := by intro a b h; simpa [tk] using h
  apply List.map_injective_iff.mpr hinj
  unfold rpCode
  rw [encFlat_encNats]
  have hf : ((mkI g.n qs k hq).arcs.flatMap fun a => [a.1.val, a.2.1.val, a.2.2.1, if a.2.2.2 then 1 else 0]) = flatQ qs :=
    flat_pmap g.n qs hq
  have hl : (mkI g.n qs k hq).arcs.length = g.L := by rw [mkI_len, hL]
  rw [hf, hl]
  have hk' : (mkI g.n qs k hq).k = k := rfl
  rw [hk', hH.2.1, hr, hk]
  have hn : (mkI g.n qs k hq).n = g.n := rfl
  rw [hn]
  simp [encFlat, encFlat_append]


lemma split_mk : ∀ (a a' : List BSym) (b b' : List BSym),
    a.map tk ++ mk :: b.map ty = a'.map tk ++ mk :: b'.map ty → a = a' ∧ b = b' := by
  intro a
  induction a with
  | nil =>
    intro a' b b' h
    cases a' with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      refine ⟨rfl, ?_⟩
      exact List.map_injective_iff.mpr (by intro x y e; simpa [ty] using e) h
    | cons x a' => simp [mk, tk] at h
  | cons x a ih =>
    intro a' b b' h
    cases a' with
    | nil => simp [mk, tk] at h
    | cons x' a' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      have hx : x = x' := by simpa [tk] using h.1
      obtain ⟨e1, e2⟩ := ih a' b b' h.2
      exact ⟨by rw [hx, e1], e2⟩

open RuralPostman.NPC in
lemma sound_lang (d : Bool) (w y : List BSym) (r : GR) (h : Q9 d (w.map tk ++ mk :: y.map ty) r) :
    ∃ I : RPInstance, I.RPYes d ∧ w = rpCode I := by
  obtain ⟨hq, hy⟩ := sound_RP d _ r h
  refine ⟨_, hy, ?_⟩
  obtain ⟨⟨⟨⟨⟨hx, hH, hlen, hq', hrest⟩, hk⟩, _, _⟩, _⟩, _, _⟩ := h
  have hw : r.c.c.g.w = w := (split_mk _ _ _ _ (by rw [← hH.1, hx])).1
  rw [← hw]
  exact w_eq r.c.c.g hH r.c.c.qs hlen hq r.c.c.y' hrest r.c.k hk

end Stk

end Sec_RPV21

section Sec_RPV22
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma chain_of_idx (qs : List Q4) : ∀ (l : List (ℕ × Bool)) (m : ℕ),
    (∀ p l', l = p :: l' → m = srcQ qs p) → (∀ j (hj : j + 1 < l.length), dstQ qs l[j] = srcQ qs l[j+1]) →
    chainFrom qs (some m) l := by
  intro l
  induction l with
  | nil => intro m _ _; trivial
  | cons p l ih =>
    intro m h1 h2
    refine ⟨h1 p l rfl, ih _ ?_ ?_⟩
    · intro q l' e; cases e; exact h2 0 (by simp)
    · intro j hj; exact h2 (j + 1) (by simpa using hj)

lemma chain_none_of (qs : List Q4) (p : ℕ × Bool) (l : List (ℕ × Bool))
    (h : ∀ j (hj : j + 1 < (p :: l).length), dstQ qs (p :: l)[j] = srcQ qs (p :: l)[j+1]) :
    chainFrom qs none (p :: l) := by
  show chainFrom qs (some (dstQ qs p)) l
  apply chain_of_idx
  · intro q l' e; cases e; exact h 0 (by simp)
  · intro j hj; exact h (j + 1) (by simpa using hj)

lemma PBok_of (n : ℕ) : ∀ (qs : List Q4) (vis : List Bool), qs.length = vis.length → (∀ q ∈ qs, QOk n q) →
    (∀ e (he : e < qs.length), (qs[e]).2.2.2 = 1 → vis[e]? = some true) → PBok n qs vis := by
  intro qs
  induction qs with
  | nil => intro vis _ _ _; trivial
  | cons q qs ih =>
    intro vis hl hq hc
    cases vis with
    | nil => simp at hl
    | cons b vis =>
      refine ⟨hq q (by simp), ?_, ih vis (by simpa using hl) (fun q' h => hq q' (List.mem_cons_of_mem _ h)) ?_⟩
      · intro hr
        have := hc 0 (by simp) (by simpa using hr)
        simpa using this
      · intro e he hr
        have := hc (e + 1) (by simpa using he) (by simpa using hr)
        simpa using this


open RuralPostman.NPC in
def qsOf (I : RPInstance) : List Q4 :=
  I.arcs.map (fun a => (a.1.val, a.2.1.val, a.2.2.1, if a.2.2.2 then 1 else 0))

open RuralPostman.NPC in
lemma qsOf_len (I : RPInstance) : (qsOf I).length = I.arcs.length := by simp [qsOf]

open RuralPostman.NPC in
lemma qsOf_ok (I : RPInstance) : ∀ q ∈ qsOf I, QOk I.n q := by
  intro q hq
  simp only [qsOf, List.mem_map] at hq
  obtain ⟨a, _, rfl⟩ := hq
  refine ⟨a.1.2, a.2.1.2, ?_⟩
  show (if a.2.2.2 = true then 1 else 0) ≤ 1
  split <;> omega

open RuralPostman.NPC in
lemma flat_qsOf (I : RPInstance) :
    I.arcs.flatMap (fun a => [a.1.val, a.2.1.val, a.2.2.1, if a.2.2.2 then 1 else 0]) = flatQ (qsOf I) := by
  unfold qsOf
  induction I.arcs with
  | nil => simp [flatQ]
  | cons a l ih => simp [flatQ, ih]

open RuralPostman.NPC in
lemma qsOf_get (I : RPInstance) (e : Fin I.arcs.length) :
    ∃ he : e.val < (qsOf I).length, (qsOf I)[e.val] =
      ((I.arcs.get e).1.val, (I.arcs.get e).2.1.val, (I.arcs.get e).2.2.1, if (I.arcs.get e).2.2.2 then 1 else 0) := by
  refine ⟨by rw [qsOf_len]; exact e.2, ?_⟩
  simp [qsOf]

open RuralPostman.NPC in
lemma tr_val2 (I : RPInstance) (t : I.Traversal) :
    srcQ (qsOf I) (t.1.val, !t.2) = (I.trSrc t).val ∧ dstQ (qsOf I) (t.1.val, !t.2) = (I.trDst t).val ∧
    wtQ (qsOf I) (t.1.val, !t.2) = (I.arcs.get t.1).2.2.1 := by
  obtain ⟨he, hg⟩ := qsOf_get I t.1
  have hq : (qsOf I)[t.1.val]? = some ((qsOf I)[t.1.val]) := List.getElem?_eq_getElem he
  obtain ⟨e, b⟩ := t
  cases b <;> simp [RPInstance.trSrc, RPInstance.trDst, srcQ, dstQ, wtQ, st', hq, hg] at *


lemma lastOf_eq' (items : List (ℕ × Bool)) (p : ℕ × Bool) (l : List (ℕ × Bool)) (hl : items = p :: l)
    (h : items ≠ []) : lastOf p l = items.getLast h := by
  subst hl; exact lastOf_eq p l _

lemma head_eq' (items : List (ℕ × Bool)) (p : ℕ × Bool) (l : List (ℕ × Bool)) (hl : items = p :: l)
    (h : 0 < items.length) : items[0]'h = p := by
  subst hl; rfl

open RuralPostman.NPC in
def itemsOf (I : RPInstance) (τ : List I.Traversal) : List (ℕ × Bool) := τ.map (fun t => (t.1.val, !t.2))

open RuralPostman.NPC in
lemma items_of_tour (I : RPInstance) (d : Bool) (τ : List I.Traversal) (hT : I.IsTour d τ) :
    (∀ p ∈ itemsOf I τ, p.1 < (qsOf I).length) ∧ (d = true → ∀ p ∈ itemsOf I τ, p.2 = false) ∧
    (∀ j (hj : j + 1 < (itemsOf I τ).length), dstQ (qsOf I) (itemsOf I τ)[j] = srcQ (qsOf I) (itemsOf I τ)[j+1]) ∧
    (∀ p l, itemsOf I τ = p :: l → dstQ (qsOf I) (lastOf p l) = srcQ (qsOf I) p) ∧
    (∀ e (he : e < (qsOf I).length), ((qsOf I)[e]).2.2.2 = 1 → ∃ b, (e, b) ∈ itemsOf I τ) ∧
    ((itemsOf I τ).map (wtQ (qsOf I))).sum = I.tourWeight τ := by
  obtain ⟨h1, h2, h3⟩ := hT
  have hlen : (itemsOf I τ).length = τ.length := by simp [itemsOf]
  have hget : ∀ j (hj : j < τ.length), (itemsOf I τ)[j]'(by rw [hlen]; exact hj) = ((τ[j]).1.val, !(τ[j]).2) := by
    intro j hj; simp [itemsOf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [itemsOf, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    rw [qsOf_len]; exact t.1.2
  · intro hd p hp
    simp only [itemsOf, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    simp [h1 hd t ht]
  · intro j hj
    have hj' : j + 1 < τ.length := by rw [← hlen]; exact hj
    have hj0 : j < τ.length := by omega
    have c := h2 ⟨j, hj0⟩
    have hr := RPInstance.finRot_succ τ.length ⟨j, hj0⟩ hj'
    have hg2 : τ.get (finRotate τ.length ⟨j, hj0⟩) = τ[j+1] := by simp only [List.get_eq_getElem, hr]
    rw [hg2] at c
    simp only [List.get_eq_getElem] at c
    rw [hget j hj0, hget (j+1) hj', (tr_val2 I τ[j]).2.1, (tr_val2 I τ[j+1]).1, c]
  · intro p l hl
    have hne : 0 < τ.length := by
      have : 0 < (itemsOf I τ).length := by rw [hl]; simp
      omega
    have hlast : (itemsOf I τ).length - 1 < τ.length := by omega
    have c := h2 ⟨τ.length - 1, by omega⟩
    have hr := RPInstance.finRot_last τ.length ⟨τ.length - 1, by omega⟩ (by simp; omega)
    have hg2 : τ.get (finRotate τ.length ⟨τ.length - 1, by omega⟩) = τ[0] := by simp only [List.get_eq_getElem, hr]
    rw [hg2] at c
    simp only [List.get_eq_getElem] at c
    have e1 : lastOf p l = ((τ[τ.length - 1]).1.val, !(τ[τ.length - 1]).2) := by
      have h' : lastOf p l = (itemsOf I τ).getLast (by rw [hl]; simp) := lastOf_eq' _ p l hl _
      rw [h', List.getLast_eq_getElem]
      have := hget (τ.length - 1) (by omega)
      simp only [hlen] at this ⊢
      exact this
    have e2 : p = ((τ[0]).1.val, !(τ[0]).2) := by
      have := hget 0 hne
      rw [← this]
      exact (head_eq' _ p l hl _).symm
    rw [e1]
    conv_rhs => rw [e2]
    rw [(tr_val2 I _).2.1, (tr_val2 I _).1, c]
  · intro e he hr
    obtain ⟨he', hg⟩ := qsOf_get I ⟨e, by rw [qsOf_len] at he; exact he⟩
    have hreq : I.IsRequired ⟨e, by rw [qsOf_len] at he; exact he⟩ := by
      unfold RPInstance.IsRequired
      rw [hg] at hr
      simp only at hr
      split at hr <;> simp_all
    obtain ⟨b, hb⟩ := h3 _ hreq
    exact ⟨!b, List.mem_map.mpr ⟨(⟨e, _⟩, b), hb, by simp⟩⟩
  · unfold RPInstance.tourWeight
    have : (itemsOf I τ).map (wtQ (qsOf I)) = τ.map (fun t => (I.arcs.get t.1).2.2.1) := by
      apply List.ext_getElem (by simp [hlen])
      intro j hj1 hj2
      have hj0 : j < τ.length := by simpa [hlen] using hj1
      have := (tr_val2 I τ[j]).2.2
      simpa [itemsOf] using this
    rw [this]


def ysI (p : ℕ × Bool) : List BSym := List.replicate p.1 BSym.zero ++ [if p.2 then BSym.minus else BSym.one]

lemma ysI_map (p : ℕ × Bool) : (ysI p).map ty = encI p := by
  unfold ysI encI
  cases p.2 <;> simp [List.map_replicate, ty]

lemma ysI_len (p : ℕ × Bool) : (ysI p).length = p.1 + 1 := by simp [ysI]

open RuralPostman.NPC in
lemma Q9_of_items (I : RPInstance) (d : Bool) (items : List (ℕ × Bool))
    (F1 : ∀ p ∈ items, p.1 < (qsOf I).length) (F2 : d = true → ∀ p ∈ items, p.2 = false)
    (F3 : ∀ j (hj : j + 1 < items.length), dstQ (qsOf I) items[j] = srcQ (qsOf I) items[j+1])
    (F4 : ∀ p l, items = p :: l → dstQ (qsOf I) (lastOf p l) = srcQ (qsOf I) p)
    (F5 : ∀ e (he : e < (qsOf I).length), ((qsOf I)[e]).2.2.2 = 1 → ∃ b, (e, b) ∈ items)
    (hw : (items.map (wtQ (qsOf I))).sum ≤ I.k) :
    ∃ (y : List BSym) (r : GR), Q9 d ((rpCode I).map tk ++ mk :: y.map ty) r ∧
      y.length = I.arcs.length + 1 + (items.map (fun p => p.1 + 1)).sum := by
  let y : List BSym := List.replicate I.arcs.length BSym.zero ++ BSym.sep :: items.flatMap ysI
  let gH : Gh := { x := (rpCode I).map tk ++ mk :: y.map ty, w := rpCode I, y := y, n := I.n, L := I.arcs.length,
                   rest := encFlat (flatQ (qsOf I)) ++ encFlat [I.k], t' := encs encI items }
  have hflat : (rpCode I).map tk = encFlat (I.n :: I.arcs.length :: (flatQ (qsOf I) ++ [I.k])) := by
    unfold rpCode
    rw [encFlat_encNats, flat_qsOf]
    simp
  have hH : Hh gH := by
    refine ⟨rfl, ?_, ?_⟩
    · show (rpCode I).map tk = (Nat.bits I.n).map tkb ++ tk BSym.sep ::
        ((Nat.bits I.arcs.length).map tkb ++ tk BSym.sep :: (encFlat (flatQ (qsOf I)) ++ encFlat [I.k]))
      rw [hflat]
      simp [encFlat, encFlat_append]
    · show y.map ty = List.replicate I.arcs.length (ty BSym.zero) ++ ty BSym.sep :: encs encI items
      simp [y, List.map_append, List.map_replicate, List.map_flatMap, encs, ysI_map]
  have hlenq : (qsOf I).length = I.arcs.length := qsOf_len I
  refine ⟨y, ⟨⟨⟨gH, qsOf I, encFlat [I.k]⟩, I.k⟩, items⟩, ?_, ?_⟩
  · set r : GR := ⟨⟨⟨gH, qsOf I, encFlat [I.k]⟩, I.k⟩, items⟩ with hr
    have hfl : (Y0 r.c).fl = flatQ (qsOf I) ++ [I.k] := rfl
    have hch0 : (Y0 r.c).ch = none := rfl
    have hvl : (Y0 r.c).vis = List.replicate I.arcs.length false := rfl
    have hvlen : (Y0 r.c).vis.length = (qsOf I).length := by rw [hvl, List.length_replicate, hlenq]
    have hb : ∀ p ∈ items, p.1 < (qsOf I).length ∧ p.1 < (Y0 r.c).vis.length ∧ (d = true → p.2 = false) :=
      fun p hp => ⟨F1 p hp, by rw [hvlen]; exact F1 p hp, fun hd => F2 hd p hp⟩
    have hchain : chainFrom (qsOf I) none items := by
      cases hit : items with
      | nil => trivial
      | cons p l =>
        apply chain_none_of
        rw [hit] at F3
        exact F3
    have hfold : foldOK (okf d) nxt (Y0 r.c) items := by
      rw [fold_iff d (qsOf I) I.k items (Y0 r.c) hfl]
      refine ⟨hb, ?_⟩
      rw [hch0]; exact hchain
    obtain ⟨va1, va2, va3⟩ := foldl_va (qsOf I) I.k items (Y0 r.c) hfl
      (fun p hp => ⟨F1 p hp, by rw [hvlen]; exact F1 p hp⟩)
    have hyE : yE r = items.foldl nxt (Y0 r.c) := rfl
    have hpb : PBok I.n (qsOf I) (yE r).vis := by
      apply PBok_of
      · rw [hyE, va2, hvlen]
      · exact qsOf_ok I
      · intro e he hrq
        obtain ⟨b, hbm⟩ := F5 e he hrq
        rw [hyE, va3 e, if_pos ⟨b, hbm⟩]
    refine ⟨⟨⟨⟨⟨rfl, hH, hlenq, qsOf_ok I, rfl⟩, rfl⟩, rfl, hfold⟩, hpb⟩, ?_, ?_⟩
    · have : val (yE r).a = (items.map (wtQ (qsOf I))).sum := by
        rw [hyE, va1]; simp [Y0, val]
      show ¬ I.k < val (yE r).a
      rw [this]; omega
    · cases hit : items with
      | nil => show clo (yE r).ch; rw [hyE, hit]; exact trivial
      | cons p l =>
        have hall : ∀ q ∈ p :: l, q.1 < (qsOf I).length := fun q hq => F1 q (by rw [hit]; exact hq)
        obtain ⟨f, hf1, hf2⟩ := foldl_ch (qsOf I) I.k l p (Y0 r.c) hfl hall
        have : yE r = l.foldl nxt (nxt (Y0 r.c) p) := by rw [hyE, hit]; rfl
        rw [this, hf1]
        show dstQ (qsOf I) (lastOf p l) = f
        rw [hch0] at hf2
        simp only at hf2
        rw [hf2]
        exact F4 p l hit
  · simp [y, ysI_len, List.length_flatMap]
    omega


lemma encFlat_len_ge : ∀ l : List ℕ, l.length ≤ (encFlat l).length := by
  intro l
  induction l with
  | nil => simp [encFlat]
  | cons a l ih => simp [encFlat]; omega

open RuralPostman.NPC in
lemma rpCode_len (I : RPInstance) : 4 * I.arcs.length + 3 ≤ (rpCode I).length := by
  have h : (rpCode I).map tk = encFlat (I.n :: I.arcs.length :: (flatQ (qsOf I) ++ [I.k])) := by
    unfold rpCode
    rw [encFlat_encNats, flat_qsOf]
    simp
  have h2 := encFlat_len_ge (I.n :: I.arcs.length :: (flatQ (qsOf I) ++ [I.k]))
  have h3 : (rpCode I).length = (encFlat (I.n :: I.arcs.length :: (flatQ (qsOf I) ++ [I.k]))).length := by
    rw [← h, List.length_map]
  have h4 := flatQ_length (qsOf I)
  rw [qsOf_len] at h4
  simp at h2
  omega

open RuralPostman.NPC in
theorem complete_model (I : RPInstance) (d : Bool) (hY : I.RPYes d) :
    ∃ y : List BSym, y.length ≤ (rpCode I).length ^ 3 ∧ ∃ r : GR, Q9 d ((rpCode I).map tk ++ mk :: y.map ty) r := by
  obtain ⟨τ, hT, hw, hlt⟩ := RPInstance.RPYes_short I d hY
  obtain ⟨F1, F2, F3, F4, F5, F6⟩ := items_of_tour I d τ hT
  obtain ⟨y, r, hQ, hyl⟩ := Q9_of_items I d (itemsOf I τ) F1 F2 F3 F4 F5 (by rw [F6]; exact hw)
  refine ⟨y, ?_, r, hQ⟩
  set L := I.arcs.length with hL
  have hlen : (itemsOf I τ).length = τ.length := by simp [itemsOf]
  have hs : ((itemsOf I τ).map (fun p => p.1 + 1)).sum ≤ (itemsOf I τ).length * L := by
    have := List.sum_le_card_nsmul ((itemsOf I τ).map (fun p => p.1 + 1)) L (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      have := F1 p hp
      rw [qsOf_len] at this
      omega)
    simpa using this
  have hW := rpCode_len I
  have hpow : (4 * L + 3) ^ 3 ≤ (rpCode I).length ^ 3 := Nat.pow_le_pow_left hW 3
  have h1 : y.length ≤ (4 * L + 3) ^ 3 := by
    rw [hyl]
    have h5 : (itemsOf I τ).length * L ≤ ((L + 1) * (2 * L) + L) * L := Nat.mul_le_mul_right _ (by omega)
    nlinarith [Nat.zero_le L, Nat.zero_le (L * L), Nat.zero_le (L * L * L)]
  omega

end Stk

end Sec_RPV22

section Sec_RPV23
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma complete_of_Q9 (d : Bool) (x0 : List Al) (r : GR) (h : Q9 d x0 r) :
    bOut.g (vg d (init x0)) Reg.OUT ≠ [] := by
  obtain ⟨⟨⟨⟨⟨hx, hH, hlen, hq, hrest⟩, hk⟩, ht, hfold⟩, hpb⟩, hk2, hcl⟩ := h
  have := complete_core r.c.c.g hH r.c.c.qs r.c.c.y' hlen hq hrest r.c.k hk d r.items ht hfold hpb ⟨hk2, hcl⟩
  rw [hx] at this
  exact this

def Rrel (d : Bool) : List BSym → List BSym → Prop := fun w y => ∃ r : GR, Q9 d (w.map tk ++ mk :: y.map ty) r

lemma checkLang_iff (d : Bool) (x : List Al) :
    x ∈ checkLang (Rrel d) ↔ bOut.g (vg d (init x)) Reg.OUT ≠ [] := by
  constructor
  · rintro ⟨w, y, ⟨r, hr⟩, rfl⟩
    exact complete_of_Q9 d _ r hr
  · intro h
    obtain ⟨r, hr0⟩ := (verifier_core d).2 x h
    obtain ⟨⟨⟨⟨⟨hx, hH, _, _, _⟩, _⟩, _, _⟩, _⟩, _, _⟩ := id hr0
    refine ⟨r.c.c.g.w, r.c.c.g.y, ⟨r, ?_⟩, ?_⟩
    · rw [← hH.1, hx]; exact hr0
    · rw [← hx, hH.1]; rfl

open RuralPostman.NPC in
theorem mem_NP_rp (d : Bool) : {w : List BSym | ∃ I : RPInstance, I.RPYes d ∧ w = rpCode I} ∈ NP BSym := by
  refine ⟨BSym, inferInstance, ⟨BSym.zero⟩, Rrel d, 3, ?_, ?_⟩
  · exact mem_P_of_prog' _ _ (verifier_core d).1 _ (checkLang_iff d)
  · intro w
    constructor
    · rintro ⟨I, hI, rfl⟩
      obtain ⟨y, hy, hr⟩ := complete_model I d hI
      exact ⟨y, hy, hr⟩
    · rintro ⟨y, _, r, hr⟩
      exact sound_lang d w y r hr

end Stk

end Sec_RPV23

set_option autoImplicit false

theorem solution : RuralPostman.NPC.urpLang ∈ CookPvsNP.NP ProjSchedTW.Complexity.BSym :=
  Stk.mem_NP_rp false
