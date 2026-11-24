-- Prove2me | solution 1 for ShortestPlanarDisjoint.Main.corollary_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T17:54:40.781199+00:00
-- url     : https://prove2.me/submissions/c60d5eed-5be4-4ef8-b22c-4c0a34761524

import Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature

set_option autoImplicit false

namespace SPDAux

/-- strict lexicographic order along a list of coordinates. -/
def lexLT {α : Type*} : List α → (α → ℤ) → (α → ℤ) → Prop
  | [], _, _ => False
  | x :: l, a, b => a x < b x ∨ (a x = b x ∧ lexLT l a b)

section Order
variable {α : Type*}

theorem lexLT_irrefl (l : List α) (a : α → ℤ) : ¬ lexLT l a a := by
  induction l with
  | nil => simp [lexLT]
  | cons x l ih => simp [lexLT, ih]

theorem lexLT_trans (l : List α) (a b c : α → ℤ) :
    lexLT l a b → lexLT l b c → lexLT l a c := by
  induction l with
  | nil => simp [lexLT]
  | cons x l ih =>
    simp only [lexLT]
    rintro (h1 | ⟨h1, h2⟩) (h3 | ⟨h3, h4⟩)
    · exact Or.inl (lt_trans h1 h3)
    · exact Or.inl (h3 ▸ h1)
    · exact Or.inl (h1 ▸ h3)
    · exact Or.inr ⟨h1.trans h3, ih h2 h4⟩

theorem lexLT_tri (l : List α) (a b : α → ℤ) :
    (∀ x ∈ l, a x = b x) ∨ lexLT l a b ∨ lexLT l b a := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases lt_trichotomy (a x) (b x) with h | h | h
    · exact Or.inr (Or.inl (Or.inl h))
    · rcases ih with ih | ih | ih
      · exact Or.inl (by simpa [h] using ih)
      · exact Or.inr (Or.inl (Or.inr ⟨h, ih⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, ih⟩))
    · exact Or.inr (Or.inr (Or.inl h))

theorem lexLT_total (l : List α) (a b : α → ℤ) (hl : ∀ x, x ∈ l) :
    lexLT l a b ∨ a = b ∨ lexLT l b a := by
  rcases lexLT_tri l a b with h | h | h
  · exact Or.inr (Or.inl (funext fun x => h x (hl x)))
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem lexLT_add (l : List α) (a b c : α → ℤ) :
    lexLT l a b → lexLT l (a + c) (b + c) := by
  induction l with
  | nil => simp [lexLT]
  | cons x l ih =>
    simp only [lexLT, Pi.add_apply]
    rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, ih h2⟩

end Order


section Lead
variable {E : Type*} [AddCommGroup E] (lt : E → E → Prop)

structure TOrd : Prop where
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a
  add : ∀ a b c, lt a b → lt (a + c) (b + c)

/-- `p` has leading exponent `a` (coefficient one). -/
def Lead (p : AddMonoidAlgebra (ZMod 2) E) (a : E) : Prop :=
  p.coeff a = 1 ∧ ∀ c, p.coeff c ≠ 0 → c = a ∨ lt c a

/-- all exponents of `p` are strictly below `a`. -/
def Below (p : AddMonoidAlgebra (ZMod 2) E) (a : E) : Prop :=
  ∀ c, p.coeff c ≠ 0 → lt c a

variable {lt}

theorem TOrd.add_lt (h : TOrd lt) {a b c d : E} (h1 : lt a b) (h2 : lt c d) :
    lt (a + c) (b + d) := by
  have := h.add _ _ c h1
  have h3 := h.add _ _ b h2
  rw [add_comm c b, add_comm d b] at h3
  exact h.trans _ _ _ this h3

theorem TOrd.add_le_lt (h : TOrd lt) {a b c d : E} (h1 : a = b ∨ lt a b) (h2 : lt c d) :
    lt (a + c) (b + d) := by
  rcases h1 with rfl | h1
  · have := h.add _ _ a h2
    rwa [add_comm c a, add_comm d a] at this
  · exact h.add_lt h1 h2

theorem TOrd.add_lt_le (h : TOrd lt) {a b c d : E} (h1 : lt a b) (h2 : c = d ∨ lt c d) :
    lt (a + c) (b + d) := by
  rcases h2 with rfl | h2
  · exact h.add _ _ _ h1
  · exact h.add_lt h1 h2

theorem TOrd.add_le (h : TOrd lt) {a b c d : E} (h1 : a = b ∨ lt a b) (h2 : c = d ∨ lt c d) :
    a + c = b + d ∨ lt (a + c) (b + d) := by
  rcases h2 with rfl | h2
  · rcases h1 with rfl | h1
    · exact Or.inl rfl
    · exact Or.inr (h.add _ _ _ h1)
  · exact Or.inr (h.add_le_lt h1 h2)

theorem Lead.mul (h : TOrd lt) {p q : AddMonoidAlgebra (ZMod 2) E} {a b : E}
    (hp : Lead lt p a) (hq : Lead lt q b) : Lead lt (p * q) (a + b) := by
  classical
  have key : ∀ m, (p * q).coeff m ≠ 0 → ∃ x y, p.coeff x ≠ 0 ∧ q.coeff y ≠ 0 ∧ x + y = m := by
    intro m hm
    by_contra hcon
    push Not at hcon
    apply hm
    rw [AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    rw [if_neg]
    intro hxy
    exact hcon x y (Finsupp.mem_support_iff.1 hx) (Finsupp.mem_support_iff.1 hy) hxy
  refine ⟨?_, ?_⟩
  · rw [AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp [hp.1, hq.1]
      · intro y hy hyb
        rw [if_neg]
        intro hxy
        exact hyb (add_left_cancel hxy)
      · intro hb
        exact absurd (Finsupp.mem_support_iff.2 (by rw [hq.1]; exact one_ne_zero)) hb
    · intro x hx hxa
      apply Finset.sum_eq_zero
      intro y hy
      rw [if_neg]
      intro hxy
      have h1 := hp.2 x (Finsupp.mem_support_iff.1 hx)
      have h2 := hq.2 y (Finsupp.mem_support_iff.1 hy)
      have h3 : lt (x + y) (a + b) := by
        rcases h1 with h1 | h1
        · exact absurd h1 hxa
        · exact h.add_lt_le h1 h2
      rw [hxy] at h3
      exact h.irrefl _ h3
    · intro ha
      exact absurd (Finsupp.mem_support_iff.2 (by rw [hp.1]; exact one_ne_zero)) ha
  · intro c hc
    obtain ⟨x, y, hx, hy, rfl⟩ := key c hc
    exact h.add_le (hp.2 x hx) (hq.2 y hy)

theorem Lead.add_below (h : TOrd lt) {p q : AddMonoidAlgebra (ZMod 2) E} {a : E}
    (hp : Lead lt p a) (hq : Below lt q a) : Lead lt (p + q) a := by
  refine ⟨?_, ?_⟩
  · have : q.coeff a = 0 := by
      by_contra hne
      exact h.irrefl _ (hq a hne)
    simp [AddMonoidAlgebra.coeff_add, hp.1, this]
  · intro c hc
    have : p.coeff c ≠ 0 ∨ q.coeff c ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hc
      simp [AddMonoidAlgebra.coeff_add, hn.1, hn.2]
    rcases this with h1 | h1
    · exact hp.2 c h1
    · exact Or.inr (hq c h1)

theorem Lead.below (h : TOrd lt) {p : AddMonoidAlgebra (ZMod 2) E} {a b : E}
    (hp : Lead lt p a) (hab : lt a b) : Below lt p b := by
  intro c hc
  rcases hp.2 c hc with rfl | h1
  · exact hab
  · exact h.trans _ _ _ h1 hab

theorem Lead.add_lt (h : TOrd lt) {p q : AddMonoidAlgebra (ZMod 2) E} {a b : E}
    (hp : Lead lt p a) (hq : Lead lt q b) (hab : lt b a) : Lead lt (p + q) a :=
  hp.add_below h (hq.below h hab)

theorem lead_single (h : TOrd lt) (a : E) :
    Lead lt (AddMonoidAlgebra.single a (1 : ZMod 2)) a := by
  classical
  refine ⟨by simp, ?_⟩
  intro c hc
  left
  by_contra hne
  apply hc
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne]

open Classical in
/-- the larger of two exponents. -/
noncomputable def mx (lt : E → E → Prop) (a b : E) : E := if lt a b then b else a

theorem Lead.add_ne (h : TOrd lt) {p q : AddMonoidAlgebra (ZMod 2) E} {a b : E}
    (hp : Lead lt p a) (hq : Lead lt q b) (hab : a ≠ b) : Lead lt (p + q) (mx lt a b) := by
  classical
  unfold mx
  by_cases hlt : lt a b
  · rw [if_pos hlt, add_comm]
    exact hq.add_lt h hp hlt
  · rw [if_neg hlt]
    rcases h.total a b with h1 | h1 | h1
    · exact absurd h1 hlt
    · exact absurd h1 hab
    · exact hp.add_lt h hq h1

theorem Lead.list_prod (h : TOrd lt) {ι : Type*} (l : List ι) (f : ι → AddMonoidAlgebra (ZMod 2) E)
    (g : ι → E) (hf : ∀ i ∈ l, Lead lt (f i) (g i)) :
    Lead lt (l.map f).prod (l.map g).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    rw [AddMonoidAlgebra.one_def]
    exact lead_single h 0
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact Lead.mul h (hf x (by simp)) (ih fun i hi => hf i (by simp [hi]))


theorem coeff_mul_ne_zero {p q : AddMonoidAlgebra (ZMod 2) E} {m : E}
    (hm : (p * q).coeff m ≠ 0) : ∃ x y, p.coeff x ≠ 0 ∧ q.coeff y ≠ 0 ∧ x + y = m := by
  classical
  by_contra hcon
  push Not at hcon
  apply hm
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  rw [if_neg]
  intro hxy
  exact hcon x y (Finsupp.mem_support_iff.1 hx) (Finsupp.mem_support_iff.1 hy) hxy

theorem TOrd.add_lt_iff (h : TOrd lt) (a b g : E) : lt (g + a) (g + b) ↔ lt a b := by
  constructor
  · intro hl
    have := h.add _ _ (-g) hl
    simpa [add_comm, add_left_comm] using this
  · intro hl
    have := h.add _ _ g hl
    rwa [add_comm a g, add_comm b g] at this

theorem mx_add_left (h : TOrd lt) (g a b : E) : mx lt (g + a) (g + b) = g + mx lt a b := by
  classical
  unfold mx
  simp only [h.add_lt_iff]
  split_ifs <;> rfl

theorem mx_eq (a b : E) : mx lt a b = a ∨ mx lt a b = b := by
  classical
  unfold mx
  split_ifs <;> simp

end Lead

section Sig
open ShortestPlanarDisjoint.Main
variable {k r : ℕ}

abbrev Ex (k r : ℕ) := SignatureVariable k r → ℤ
abbrev SR (k r : ℕ) := SignatureRing k r

def ex (x : SignatureVariable k r) (n : ℤ := 1) : Ex k r := Pi.single x n

def Pure (x : Ex k r) : Prop := ∀ s, x (Sum.inl s) = 0

/-- the exponent order: seams first, then `rest`. -/
abbrev LT (k r : ℕ) (rest : List (SignatureVariable k r)) : Ex k r → Ex k r → Prop :=
  lexLT ((List.finRange r).map Sum.inl ++ rest)

theorem lexTOrd {α : Type*} (l : List α) (hl : ∀ x, x ∈ l) : TOrd (lexLT (α := α) l) :=
  ⟨lexLT_irrefl l, lexLT_trans l, fun a b => lexLT_total l a b hl, lexLT_add l⟩

theorem pure_ex {x : SignatureVariable k r} (hx : ∀ s, x ≠ Sum.inl s) (n : ℤ) : Pure (ex x n) := by
  intro s
  simp [ex, Pi.single_apply, (hx s).symm]

theorem pure_add {a b : Ex k r} (ha : Pure a) (hb : Pure b) : Pure (a + b) := by
  intro s; simp [ha s, hb s]

theorem pure_mx (rest : List (SignatureVariable k r)) {a b : Ex k r} (ha : Pure a) (hb : Pure b) :
    Pure (mx (LT k r rest) a b) := by
  rcases mx_eq (lt := LT k r rest) a b with h | h <;> rw [h]; exacts [ha, hb]

theorem ex_inl_apply (s t : Fin r) (n : ℤ) :
    (ex (Sum.inl s) n : Ex k r) (Sum.inl t) = if t = s then n else 0 := by
  simp [ex, Pi.single_apply]

/-- the seam exponents of every monomial of `p` are bounded by `σ`. -/
def SeamLe (σ : Fin r → ℤ) (p : SR k r) : Prop :=
  ∀ c, p.coeff c ≠ 0 → ∀ s, c (Sum.inl s) ≤ σ s

theorem SeamLe.mono {σ τ : Fin r → ℤ} {p : SR k r} (h : SeamLe σ p) (hst : ∀ s, σ s ≤ τ s) :
    SeamLe τ p := fun c hc s => (h c hc s).trans (hst s)

theorem SeamLe.add {σ : Fin r → ℤ} {p q : SR k r} (hp : SeamLe σ p) (hq : SeamLe σ q) :
    SeamLe σ (p + q) := by
  intro c hc s
  have : p.coeff c ≠ 0 ∨ q.coeff c ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hc
    simp [AddMonoidAlgebra.coeff_add, hn.1, hn.2]
  rcases this with h | h
  · exact hp c h s
  · exact hq c h s

theorem SeamLe.mul {σ τ : Fin r → ℤ} {p q : SR k r} (hp : SeamLe σ p) (hq : SeamLe τ q) :
    SeamLe (fun s => σ s + τ s) (p * q) := by
  intro c hc s
  obtain ⟨x, y, hx, hy, rfl⟩ := coeff_mul_ne_zero hc
  have := hp x hx s
  have := hq y hy s
  simp only [Pi.add_apply]
  omega

theorem seamLe_single (a : Ex k r) : SeamLe (fun s => a (Sum.inl s)) (AddMonoidAlgebra.single a (1 : ZMod 2)) := by
  classical
  intro c hc s
  have : c = a := by
    by_contra hne
    apply hc
    simp [AddMonoidAlgebra.coeff_single, hne]
  rw [this]

theorem seamLe_zero_of_pure {p : SR k r} (σ : Fin r → ℤ) (hσ : ∀ s, 0 ≤ σ s) (h : SeamLe 0 p) : SeamLe σ p :=
  h.mono hσ

theorem lexLT_seam_aux (rest : List (SignatureVariable k r)) (ss : List (Fin r)) (c g : Ex k r)
    (h1 : ∀ s ∈ ss, c (Sum.inl s) ≤ g (Sum.inl s)) (h2 : ∃ s ∈ ss, c (Sum.inl s) < g (Sum.inl s)) :
    lexLT (ss.map Sum.inl ++ rest) c g := by
  induction ss with
  | nil => simp at h2
  | cons s ss ih =>
    simp only [List.map_cons, List.cons_append, lexLT]
    by_cases hs : c (Sum.inl s) < g (Sum.inl s)
    · exact Or.inl hs
    · right
      have heq : c (Sum.inl s) = g (Sum.inl s) := le_antisymm (h1 s (by simp)) (not_lt.1 hs)
      refine ⟨heq, ih (fun t ht => h1 t (by simp [ht])) ?_⟩
      obtain ⟨t, ht, hlt⟩ := h2
      rcases List.mem_cons.1 ht with rfl | ht
      · exact absurd hlt hs
      · exact ⟨t, ht, hlt⟩

theorem SeamLe.below (rest : List (SignatureVariable k r)) {σ : Fin r → ℤ} {q : SR k r}
    (hq : SeamLe σ q) {g : Ex k r} (h1 : ∀ s, σ s ≤ g (Sum.inl s))
    (h2 : ∃ s, σ s < g (Sum.inl s)) : Below (LT k r rest) q g := by
  intro c hc
  apply lexLT_seam_aux rest (List.finRange r) c g
  · intro s _; exact (hq c hc s).trans (h1 s)
  · obtain ⟨s, hs⟩ := h2
    exact ⟨s, by simp, lt_of_le_of_lt (hq c hc s) hs⟩


variable (rest : List (SignatureVariable k r))

theorem crossing_mulVec (s : Fin r) (e : Bool) (y : Vec2 (SignatureRing k r)) :
    (crossingMatrix s e).mulVec y 0 = seamVariable s * sideVariable s e *
        (sideVariable s (!e) * y 1 + y 0) + seamVariable s (-1) * y 1 ∧
    (crossingMatrix s e).mulVec y 1 = seamVariable s * (sideVariable s (!e) * y 1 + y 0) := by
  constructor <;>
  · simp [crossingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, outerProduct, switchMatrix,
      terminalVector, Matrix.mul_apply]
    ring

theorem crossing_trace (s : Fin r) (e : Bool) (N : Mat2 (SignatureRing k r)) :
    Matrix.trace (crossingMatrix s e * N) =
      seamVariable s * ((N.mulVec (terminalVector (sideVariable s e))) 0 +
        sideVariable s (!e) * (N.mulVec (terminalVector (sideVariable s e))) 1) +
      seamVariable s (-1) * (N.mulVec ![1, 0]) 1 := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply]
  simp [crossingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, outerProduct,
    switchMatrix, terminalVector, Matrix.mul_apply]
  ring

theorem seamLe_var_mul {σ : Fin r → ℤ} {p : SR k r} (x : SignatureVariable k r)
    (hx : ∀ s, x ≠ Sum.inl s) (n : ℤ) (hp : SeamLe σ p) : SeamLe σ (signatureVariable x n * p) := by
  have h := (seamLe_single (ex x n : Ex k r)).mul hp
  refine SeamLe.mono h ?_
  intro t
  have : (ex x n : Ex k r) (Sum.inl t) = 0 := by simp [ex, Pi.single_apply, (hx t).symm]
  simp [this]

theorem seamLe_seam_mul {σ : Fin r → ℤ} {p : SR k r} (s : Fin r) (n : ℤ) (hp : SeamLe σ p) :
    SeamLe (fun t => (if t = s then n else 0) + σ t) (signatureVariable (Sum.inl s) n * p) := by
  have h := (seamLe_single (ex (Sum.inl s) n : Ex k r)).mul hp
  refine SeamLe.mono h ?_
  intro t
  simp [ex_inl_apply]

theorem lead_var (hO : TOrd (LT k r rest)) (x : SignatureVariable k r) (n : ℤ) :
    Lead (LT k r rest) (signatureVariable x n) (ex x n) := lead_single hO _

theorem step_lead (hO : TOrd (LT k r rest)) (s : Fin r) (e : Bool) (y : Vec2 (SR k r))
    (g u : Ex k r) (σ : Fin r → ℤ)
    (hy1 : Lead (LT k r rest) (y 1) g) (hy0 : Lead (LT k r rest) (y 0) (g + u))
    (hu : Pure u) (hg : ∀ t, g (Sum.inl t) = σ t)
    (hne : (ex (Sum.inr (Sum.inr (s, !e))) : Ex k r) ≠ u)
    (hs1 : SeamLe σ (y 1)) (hs0 : SeamLe σ (y 0)) :
    Lead (LT k r rest) ((crossingMatrix s e).mulVec y 1)
        (ex (Sum.inl s) + (g + mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e)))) u)) ∧
    Lead (LT k r rest) ((crossingMatrix s e).mulVec y 0)
        (ex (Sum.inl s) + ex (Sum.inr (Sum.inr (s, e))) +
          (g + mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e)))) u)) ∧
    SeamLe (fun t => (if t = s then 1 else 0) + σ t) ((crossingMatrix s e).mulVec y 1) ∧
    SeamLe (fun t => (if t = s then 1 else 0) + σ t) ((crossingMatrix s e).mulVec y 0) := by
  obtain ⟨h0, h1⟩ := crossing_mulVec (k := k) s e y
  have hub : Pure (ex (Sum.inr (Sum.inr (s, !e))) : Ex k r) := pure_ex (by simp) 1
  have hmx : Pure (mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e)))) u) := pure_mx rest hub hu
  -- the binomial
  have hz1 : Lead (LT k r rest) (sideVariable s (!e) * y 1)
      (g + ex (Sum.inr (Sum.inr (s, !e)))) := by
    have := Lead.mul hO (lead_var rest hO (Sum.inr (Sum.inr (s, !e))) 1) hy1
    rwa [add_comm] at this
  have hz : Lead (LT k r rest) (sideVariable s (!e) * y 1 + y 0)
      (g + mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e)))) u) := by
    rw [← mx_add_left hO]
    exact Lead.add_ne hO hz1 hy0 (fun h => hne (add_left_cancel h))
  have hzs : SeamLe σ (sideVariable s (!e) * y 1 + y 0) :=
    (seamLe_var_mul (Sum.inr (Sum.inr (s, !e))) (by simp) 1 hs1).add hs0
  have hlam := lead_var rest hO (Sum.inl s) 1
  have hlam' : SeamLe (fun t => (if t = s then 1 else 0) + σ t) (seamVariable s * (sideVariable s (!e) * y 1 + y 0) : SR k r) :=
    seamLe_seam_mul s 1 hzs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; exact Lead.mul hO hlam hz
  · rw [h0]
    have hmain := Lead.mul hO (Lead.mul hO hlam (lead_var rest hO (Sum.inr (Sum.inr (s, e))) 1)) hz
    refine Lead.add_below hO hmain ?_
    have hinv : SeamLe (fun t => (if t = s then -1 else 0) + σ t) (seamVariable s (-1) * y 1 : SR k r) :=
      seamLe_seam_mul s (-1) hs1
    refine hinv.below rest ?_ ?_
    · intro t
      have h2 : (mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e)))) u : Ex k r) (Sum.inl t) = 0 := hmx t
      simp only [Pi.add_apply, ex_inl_apply, hg, h2]
      have : (ex (Sum.inr (Sum.inr (s, e))) : Ex k r) (Sum.inl t) = 0 := by
        simp [ex, Pi.single_apply]
      rw [this]
      split_ifs <;> omega
    · refine ⟨s, ?_⟩
      have h2 : (mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e)))) u : Ex k r) (Sum.inl s) = 0 := hmx s
      have : (ex (Sum.inr (Sum.inr (s, e))) : Ex k r) (Sum.inl s) = 0 := by
        simp [ex, Pi.single_apply]
      simp only [Pi.add_apply, ex_inl_apply, hg, h2, this]
      simp
  · rw [h1]; exact hlam'
  · rw [h0]
    refine SeamLe.add ?_ ?_
    · have := seamLe_var_mul (σ := fun t => (if t = s then 1 else 0) + σ t) (Sum.inr (Sum.inr (s, e))) (by simp) 1 hlam'
      have h3 := seamLe_seam_mul (k := k) s 1 (seamLe_var_mul (σ := σ) (Sum.inr (Sum.inr (s, e))) (by simp) 1 hzs)
      rw [mul_assoc]; exact h3
    · have hinv : SeamLe (fun t => (if t = s then -1 else 0) + σ t) (seamVariable s (-1) * y 1 : SR k r) :=
        seamLe_seam_mul s (-1) hs1
      refine hinv.mono ?_
      intro t
      split_ifs <;> omega


theorem cross_seam {σ : Fin r → ℤ} (s : Fin r) (e : Bool) (y : Vec2 (SR k r))
    (hs1 : SeamLe σ (y 1)) (hs0 : SeamLe σ (y 0)) :
    SeamLe (fun t => (if t = s then 1 else 0) + σ t) ((crossingMatrix s e).mulVec y 1) ∧
    SeamLe (fun t => (if t = s then 1 else 0) + σ t) ((crossingMatrix s e).mulVec y 0) := by
  obtain ⟨h0, h1⟩ := crossing_mulVec (k := k) s e y
  have hzs : SeamLe σ (sideVariable s (!e) * y 1 + y 0) :=
    (seamLe_var_mul (Sum.inr (Sum.inr (s, !e))) (by simp) 1 hs1).add hs0
  have hlam' : SeamLe (fun t => (if t = s then 1 else 0) + σ t) (seamVariable s * (sideVariable s (!e) * y 1 + y 0) : SR k r) :=
    seamLe_seam_mul s 1 hzs
  refine ⟨by rw [h1]; exact hlam', ?_⟩
  rw [h0]
  refine SeamLe.add ?_ ?_
  · have h3 := seamLe_seam_mul (k := k) s 1 (seamLe_var_mul (σ := σ) (Sum.inr (Sum.inr (s, e))) (by simp) 1 hzs)
    rw [mul_assoc]; exact h3
  · have hinv : SeamLe (fun t => (if t = s then -1 else 0) + σ t) (seamVariable s (-1) * y 1 : SR k r) :=
      seamLe_seam_mul s (-1) hs1
    refine hinv.mono ?_
    intro t
    split_ifs <;> omega

def lamE : List (Fin r × Bool) → Ex k r
  | [] => 0
  | c :: cs => ex (Sum.inl c.1) + lamE cs

def hd (uw : Ex k r) : List (Fin r × Bool) → Ex k r
  | [] => uw
  | c :: _ => ex (Sum.inr (Sum.inr (c.1, c.2)))

noncomputable def pairE (uw : Ex k r) : List (Fin r × Bool) → Ex k r
  | [] => 0
  | c :: cs => mx (LT k r rest) (ex (Sum.inr (Sum.inr (c.1, !c.2)))) (hd uw cs) + pairE uw cs

def chainOK (uw : Ex k r) : List (Fin r × Bool) → Prop
  | [] => True
  | c :: cs => (ex (Sum.inr (Sum.inr (c.1, !c.2))) : Ex k r) ≠ hd uw cs ∧ chainOK uw cs

theorem pure_hd {uw : Ex k r} (h : Pure uw) (cs : List (Fin r × Bool)) : Pure (hd uw cs) := by
  cases cs with
  | nil => exact h
  | cons c cs => exact pure_ex (by simp) 1

theorem pure_pairE {uw : Ex k r} (h : Pure uw) (cs : List (Fin r × Bool)) : Pure (pairE rest uw cs) := by
  induction cs with
  | nil => intro s; simp [pairE]
  | cons c cs ih =>
    exact pure_add (pure_mx rest (pure_ex (by simp) 1) (pure_hd h cs)) ih

theorem lamE_apply (cs : List (Fin r × Bool)) (t : Fin r) :
    (lamE cs : Ex k r) (Sum.inl t) = ((cs.filter fun c => c.1 = t).length : ℤ) := by
  induction cs with
  | nil => simp [lamE]
  | cons c cs ih =>
    simp only [lamE, Pi.add_apply, ex_inl_apply, ih, List.filter_cons]
    by_cases h : c.1 = t
    · simp [h]; omega
    · simp [h, Ne.symm h]

theorem crossingTransport_cons (c : Fin r × Bool) (cs : List (Fin r × Bool)) :
    crossingTransport (k := k) (c :: cs) = crossingMatrix c.1 c.2 * crossingTransport cs := by
  simp [crossingTransport, transport]

theorem crossingTransport_nil : crossingTransport (k := k) (r := r) [] = 1 := by
  simp [crossingTransport, transport]

theorem vec_seam (cs : List (Fin r × Bool)) (w : Vec2 (SR k r))
    (h1 : SeamLe (fun _ => 0) (w 1)) (h0 : SeamLe (fun _ => 0) (w 0)) :
    SeamLe (fun t => (lamE cs : Ex k r) (Sum.inl t)) ((crossingTransport cs).mulVec w 1) ∧
    SeamLe (fun t => (lamE cs : Ex k r) (Sum.inl t)) ((crossingTransport cs).mulVec w 0) := by
  induction cs with
  | nil =>
    rw [crossingTransport_nil, Matrix.one_mulVec]
    exact ⟨h1.mono (by intro t; simp [lamE]), h0.mono (by intro t; simp [lamE])⟩
  | cons c cs ih =>
    rw [crossingTransport_cons, ← Matrix.mulVec_mulVec]
    have := cross_seam (k := k) c.1 c.2 _ ih.1 ih.2
    refine ⟨this.1.mono ?_, this.2.mono ?_⟩ <;>
    · intro t
      simp [lamE, ex_inl_apply]

theorem vec_lead (hO : TOrd (LT k r rest)) (cs : List (Fin r × Bool)) (w : Vec2 (SR k r))
    (gw uw : Ex k r) (hgw : Pure gw) (huw : Pure uw)
    (hw1 : Lead (LT k r rest) (w 1) gw) (hw0 : Lead (LT k r rest) (w 0) (gw + uw))
    (hs1 : SeamLe (fun _ => 0) (w 1)) (hs0 : SeamLe (fun _ => 0) (w 0))
    (hok : chainOK uw cs) :
    Lead (LT k r rest) ((crossingTransport cs).mulVec w 1) (gw + lamE cs + pairE rest uw cs) ∧
    Lead (LT k r rest) ((crossingTransport cs).mulVec w 0)
      (gw + lamE cs + pairE rest uw cs + hd uw cs) := by
  induction cs with
  | nil =>
    rw [crossingTransport_nil, Matrix.one_mulVec]
    simp only [lamE, pairE, hd, add_zero]
    exact ⟨hw1, hw0⟩
  | cons c cs ih =>
    obtain ⟨hne, hok'⟩ := hok
    obtain ⟨ih1, ih0⟩ := ih hok'
    obtain ⟨hv1, hv0⟩ := vec_seam cs w hs1 hs0
    rw [crossingTransport_cons, ← Matrix.mulVec_mulVec]
    have hgp : ∀ t, (gw + lamE cs + pairE rest uw cs : Ex k r) (Sum.inl t) = (lamE cs : Ex k r) (Sum.inl t) := by
      intro t
      simp [hgw t, pure_pairE rest huw cs t]
    have := step_lead rest hO c.1 c.2 _ (gw + lamE cs + pairE rest uw cs) (hd uw cs)
      (fun t => (lamE cs : Ex k r) (Sum.inl t)) ih1 (by simpa using ih0) (pure_hd huw cs) hgp hne hv1 hv0
    obtain ⟨r1, r0, -, -⟩ := this
    constructor
    · convert r1 using 1
      simp only [lamE, pairE]
      abel
    · convert r0 using 1
      simp only [lamE, pairE, hd]
      abel


theorem lead_one (hO : TOrd (LT k r rest)) : Lead (LT k r rest) (1 : SR k r) 0 := by
  rw [AddMonoidAlgebra.one_def]; exact lead_single hO 0

theorem seamLe_one : SeamLe (fun _ => 0) (1 : SR k r) := by
  rw [AddMonoidAlgebra.one_def]
  exact (seamLe_single (0 : Ex k r))

theorem seamLe_var (x : SignatureVariable k r) (hx : ∀ s, x ≠ Sum.inl s) :
    SeamLe (fun _ => 0) (signatureVariable x 1 : SR k r) := by
  refine (seamLe_single (ex x 1 : Ex k r)).mono ?_
  intro t
  simp [ex, Pi.single_apply, (hx t).symm]

theorem pathSignature_eq (i j : Fin (2 * k)) (cs : List (Fin r × Bool)) :
    pathSignature i j cs = terminalVariable i *
        ((crossingTransport cs).mulVec (terminalVector (terminalVariable j))) 1 +
      ((crossingTransport cs).mulVec (terminalVector (terminalVariable j))) 0 := by
  simp [pathSignature, bracket, Fin.sum_univ_two, switchMatrix, terminalVector]

theorem path_lead (hO : TOrd (LT k r rest)) (i j : Fin (2 * k)) (cs : List (Fin r × Bool))
    (hok : chainOK (ex (Sum.inr (Sum.inl j)) : Ex k r) cs)
    (hne : (ex (Sum.inr (Sum.inl i)) : Ex k r) ≠ hd (ex (Sum.inr (Sum.inl j))) cs) :
    Lead (LT k r rest) (pathSignature i j cs)
      (lamE cs + pairE rest (ex (Sum.inr (Sum.inl j))) cs +
        mx (LT k r rest) (ex (Sum.inr (Sum.inl i))) (hd (ex (Sum.inr (Sum.inl j))) cs)) := by
  rw [pathSignature_eq]
  have hpure : Pure (ex (Sum.inr (Sum.inl j)) : Ex k r) := pure_ex (by simp) 1
  have hv := vec_lead rest hO cs (terminalVector (terminalVariable j)) 0
    (ex (Sum.inr (Sum.inl j))) (fun _ => rfl) hpure
    (by simpa [terminalVector] using lead_one rest hO)
    (by simpa [terminalVector, terminalVariable] using lead_var rest hO (Sum.inr (Sum.inl j)) 1)
    (by simpa [terminalVector] using seamLe_one)
    (by simpa [terminalVector, terminalVariable] using seamLe_var (Sum.inr (Sum.inl j)) (by simp))
    hok
  obtain ⟨hv1, hv0⟩ := hv
  rw [zero_add] at hv1 hv0
  have h1 := Lead.mul hO (lead_var rest hO (Sum.inr (Sum.inl i)) 1) hv1
  rw [add_comm (ex _ 1)] at h1
  have := Lead.add_ne hO h1 hv0 (fun h => hne (add_left_cancel h))
  rw [mx_add_left hO] at this
  exact this

theorem cycle_lead (hO : TOrd (LT k r rest)) (c : Fin r × Bool) (cs : List (Fin r × Bool))
    (hok : chainOK (ex (Sum.inr (Sum.inr (c.1, c.2))) : Ex k r) (c :: cs)) :
    Lead (LT k r rest) (cycleSignature (c :: cs))
      (lamE (c :: cs) + pairE rest (ex (Sum.inr (Sum.inr (c.1, c.2)))) (c :: cs)) := by
  obtain ⟨hne, hok'⟩ := hok
  obtain ⟨s, e⟩ := c
  simp only at hne ⊢
  unfold cycleSignature
  rw [crossingTransport_cons, crossing_trace]
  have hpure : Pure (ex (Sum.inr (Sum.inr (s, e))) : Ex k r) := pure_ex (by simp) 1
  have hv := vec_lead rest hO cs (terminalVector (sideVariable s e)) 0
    (ex (Sum.inr (Sum.inr (s, e)))) (fun _ => rfl) hpure
    (by simpa [terminalVector] using lead_one rest hO)
    (by simpa [terminalVector, sideVariable] using lead_var rest hO (Sum.inr (Sum.inr (s, e))) 1)
    (by simpa [terminalVector] using seamLe_one)
    (by simpa [terminalVector, sideVariable] using seamLe_var (Sum.inr (Sum.inr (s, e))) (by simp))
    hok'
  obtain ⟨hv1, hv0⟩ := hv
  rw [zero_add] at hv1 hv0
  set y := (crossingTransport cs).mulVec (terminalVector (sideVariable s e)) with hy
  have hub : Pure (ex (Sum.inr (Sum.inr (s, !e))) : Ex k r) := pure_ex (by simp) 1
  have h1 := Lead.mul hO (lead_var rest hO (Sum.inr (Sum.inr (s, !e))) 1) hv1
  rw [add_comm (ex _ 1)] at h1
  have hz := Lead.add_ne hO h1 hv0 (fun h => hne (add_left_cancel h))
  have hmx : Pure (mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e))))
      (hd (ex (Sum.inr (Sum.inr (s, e)))) cs) : Ex k r) :=
    pure_mx rest hub (pure_hd hpure cs)
  have hmain := Lead.mul hO (lead_var rest hO (Sum.inl s) 1) hz
  have hlo : SeamLe (fun t => (lamE cs : Ex k r) (Sum.inl t))
      ((crossingTransport (k := k) cs).mulVec (![1, 0] : Vec2 (SR k r)) 1) := by
    refine (vec_seam cs (![1, 0] : Vec2 (SR k r)) ?_ ?_).1
    · intro c hc; simp at hc
    · simpa using seamLe_one
  have hinv := seamLe_seam_mul s (-1) hlo
  have hpp := pure_pairE rest hpure cs
  rw [mx_add_left hO] at hmain
  have key : lamE ((s, e) :: cs) + pairE rest (ex (Sum.inr (Sum.inr (s, e)))) ((s, e) :: cs) =
      ex (Sum.inl s) + (lamE cs + pairE rest (ex (Sum.inr (Sum.inr (s, e)))) cs +
        mx (LT k r rest) (ex (Sum.inr (Sum.inr (s, !e)))) (hd (ex (Sum.inr (Sum.inr (s, e)))) cs)) := by
    simp only [lamE, pairE]
    abel
  rw [key, add_comm (y 0)]
  refine Lead.add_below hO hmain ?_
  refine hinv.below rest ?_ ?_
  · intro t
    simp only [Pi.add_apply, ex_inl_apply, hpp t, hmx t, lamE_apply]
    split_ifs <;> omega
  · refine ⟨s, ?_⟩
    simp only [Pi.add_apply, ex_inl_apply, hpp s, hmx s]
    simp


end Sig

end SPDAux

namespace SPDAux
open ShortestPlanarDisjoint.Main
variable {k f r : ℕ} (L : DiskLayout k f r) (q : Fin r → ℕ)

/-- the endpoints of one side -/
def sideEndpoints (side : DiskSide f r) : List (DiskEndpoint k r q) :=
  match side with
  | .inl j => (L.block j).map Sum.inl
  | .inr (s, e) => (List.finRange (q s)).map fun i => Sum.inr ⟨s, e, i⟩

theorem endpoints_eq : L.endpoints q = L.sideOrder.flatMap (sideEndpoints L q) := by
  rfl

theorem block_disjoint {j j' : Fin f} (h : j ≠ j') : List.Disjoint (L.block j) (L.block j') := by
  have h1 := L.terminals_nodup
  rw [List.nodup_flatten] at h1
  have h2 := h1.2
  rw [List.pairwise_ofFn] at h2
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact h2 hlt
  · exact (h2 hlt).symm

theorem block_nodup (j : Fin f) : (L.block j).Nodup := by
  have h1 := L.terminals_nodup
  rw [List.nodup_flatten] at h1
  exact h1.1 _ (List.mem_ofFn.2 ⟨j, rfl⟩)

theorem sideEndpoints_nodup (side : DiskSide f r) : (sideEndpoints L q side).Nodup := by
  cases side with
  | inl j => exact (block_nodup L j).map Sum.inl_injective
  | inr se =>
    obtain ⟨s, e⟩ := se
    refine (List.nodup_finRange _).map ?_
    intro i j h
    simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
    exact h

theorem sideEndpoints_disjoint {a b : DiskSide f r} (h : a ≠ b) :
    List.Disjoint (sideEndpoints L q a) (sideEndpoints L q b) := by
  cases a with
  | inl j =>
    cases b with
    | inl j' =>
      have hj : j ≠ j' := fun hh => h (by rw [hh])
      intro x hx hy
      simp only [sideEndpoints, List.mem_map] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', hh⟩ := hy
      have := Sum.inl_injective hh
      subst this
      exact block_disjoint L hj hu hu'
    | inr se =>
      intro x hx hy
      simp only [sideEndpoints, List.mem_map] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', hh⟩ := hy
      cases hh
  | inr se =>
    obtain ⟨s, e⟩ := se
    cases b with
    | inl j' =>
      intro x hx hy
      simp only [sideEndpoints, List.mem_map] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', hh⟩ := hy
      cases hh
    | inr se' =>
      obtain ⟨s', e'⟩ := se'
      intro x hx hy
      simp only [sideEndpoints, List.mem_map] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', hh⟩ := hy
      simp only [Sum.inr.injEq, Sigma.mk.injEq] at hh
      obtain ⟨rfl, hh2⟩ := hh
      simp only [heq_eq_eq, Prod.mk.injEq] at hh2
      obtain ⟨rfl, -⟩ := hh2
      exact h rfl

theorem endpoints_nodup : (L.endpoints q).Nodup := by
  rw [endpoints_eq, List.nodup_flatMap]
  refine ⟨fun a _ => sideEndpoints_nodup L q a, ?_⟩
  have := L.sides_nodup
  rw [List.Nodup] at this
  exact this.imp (fun h => sideEndpoints_disjoint L q h)

theorem mem_endpoints (p : DiskEndpoint k r q) : p ∈ L.endpoints q := by
  rw [endpoints_eq, List.mem_flatMap]
  rcases p with i | ⟨s, e, i⟩
  · have hi := L.terminals_complete i
    simp only [List.mem_flatten, List.mem_ofFn] at hi
    obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hi
    exact ⟨Sum.inl j, L.sides_complete _, by simpa [sideEndpoints] using hl⟩
  · exact ⟨Sum.inr (s, e), L.sides_complete _, by simp [sideEndpoints]⟩

instance instLawfulBEqEndpoint : LawfulBEq (DiskEndpoint k r q) where
  rfl := by
    intro a
    rcases a with i | x
    · change (i == i) = true
      exact beq_self_eq_true i
    · change (x == x) = true
      exact beq_self_eq_true x
  eq_of_beq := by
    intro a b h
    rcases a with i | x <;> rcases b with j | y
    · change (i == j) = true at h
      rw [eq_of_beq h]
    · exact absurd h (by simp [BEq.beq, Sum.instBEq.beq])
    · exact absurd h (by simp [BEq.beq, Sum.instBEq.beq])
    · change (x == y) = true at h
      rw [eq_of_beq h]

theorem rank_inj {p u : DiskEndpoint k r q} (h : L.rank p = L.rank u) : p = u := by
  unfold DiskLayout.rank at h
  exact (List.idxOf_inj (mem_endpoints L q p)).1 h


theorem idx_split {α : Type*} [BEq α] [LawfulBEq α] {A S B : List α}
    (hnd : (A ++ S ++ B).Nodup) :
    (∀ z ∈ A, ∀ x ∈ S, (A ++ S ++ B).idxOf z < (A ++ S ++ B).idxOf x) ∧
    (∀ x ∈ S, ∀ z ∈ B, (A ++ S ++ B).idxOf x < (A ++ S ++ B).idxOf z) := by
  rw [List.append_assoc] at hnd ⊢
  rw [List.nodup_append] at hnd
  obtain ⟨hA, hSB, hdis⟩ := hnd
  rw [List.nodup_append] at hSB
  obtain ⟨hS, hB, hSBd⟩ := hSB
  constructor
  · intro z hz x hx
    rw [List.idxOf_append_of_mem hz]
    have hxA : x ∉ A := fun h => hdis _ h _ (List.mem_append_left _ hx) rfl
    rw [List.idxOf_append_of_notMem hxA]
    have := (List.idxOf_lt_length_iff.2 hz)
    omega
  · intro x hx z hz
    have hxA : x ∉ A := fun h => hdis _ h _ (List.mem_append_left _ hx) rfl
    have hzA : z ∉ A := fun h => hdis _ h _ (List.mem_append_right _ hz) rfl
    have hzS : z ∉ S := fun h => hSBd _ h _ hz rfl
    rw [List.idxOf_append_of_notMem hxA, List.idxOf_append_of_notMem hzA,
      List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem hzS]
    have := (List.idxOf_lt_length_iff.2 hx)
    omega

theorem ep_split (a : DiskSide f r) : ∃ A B, L.endpoints q = A ++ sideEndpoints L q a ++ B := by
  obtain ⟨pre, post, h⟩ := List.append_of_mem (L.sides_complete a)
  refine ⟨pre.flatMap (sideEndpoints L q), post.flatMap (sideEndpoints L q), ?_⟩
  rw [endpoints_eq, h]
  simp [List.flatMap_append]

theorem rank_outside (a : DiskSide f r) {x y z : DiskEndpoint k r q}
    (hx : x ∈ sideEndpoints L q a) (hy : y ∈ sideEndpoints L q a)
    (hz : z ∉ sideEndpoints L q a) :
    (L.rank z < L.rank x ↔ L.rank z < L.rank y) := by
  obtain ⟨A, B, h⟩ := ep_split L q a
  have hnd := endpoints_nodup L q
  rw [h] at hnd
  have hs := idx_split hnd
  have hzm : z ∈ A ++ sideEndpoints L q a ++ B := h ▸ mem_endpoints L q z
  unfold DiskLayout.rank
  rw [h]
  simp only [List.mem_append] at hzm
  rcases hzm with (hzA | hzS) | hzB
  · exact ⟨fun _ => hs.1 z hzA y hy, fun _ => hs.1 z hzA x hx⟩
  · exact absurd hzS hz
  · exact ⟨fun hh => absurd hh (not_lt.2 (hs.2 x hx z hzB).le),
      fun hh => absurd hh (not_lt.2 (hs.2 y hy z hzB).le)⟩

theorem rank_side_affine (a : DiskSide f r) :
    ∃ n, ∀ x ∈ sideEndpoints L q a, L.rank x = n + (sideEndpoints L q a).idxOf x := by
  obtain ⟨A, B, h⟩ := ep_split L q a
  have hnd := endpoints_nodup L q
  rw [h] at hnd
  refine ⟨A.length, fun x hx => ?_⟩
  rw [List.append_assoc, List.nodup_append] at hnd
  obtain ⟨hA, hSB, hdis⟩ := hnd
  have hxA : x ∉ A := fun h' => hdis _ h' _ (List.mem_append_left _ hx) rfl
  unfold DiskLayout.rank
  rw [h, List.append_assoc, List.idxOf_append_of_notMem hxA, List.idxOf_append_of_mem hx]

theorem idxOf_seam (s : Fin r) (e : Bool) (i : Fin (q s)) :
    (sideEndpoints L q (Sum.inr (s, e))).idxOf (Sum.inr ⟨s, e, i⟩) = i.val := by
  have hnd := sideEndpoints_nodup L q (Sum.inr (s, e))
  have h := hnd.idxOf_getElem i.val (by simp [sideEndpoints])
  have h2 : (sideEndpoints L q (Sum.inr (s, e)))[i.val]'(by simp [sideEndpoints]) =
      Sum.inr ⟨s, e, i⟩ := by
    simp [sideEndpoints]
  rw [h2] at h
  exact h

theorem rank_seam_lt (s : Fin r) (e : Bool) (i j : Fin (q s)) :
    L.rank (Sum.inr ⟨s, e, i⟩ : DiskEndpoint k r q) < L.rank (Sum.inr ⟨s, e, j⟩) ↔ i < j := by
  obtain ⟨n, hn⟩ := rank_side_affine L q (Sum.inr (s, e))
  have hi : (Sum.inr ⟨s, e, i⟩ : DiskEndpoint k r q) ∈ sideEndpoints L q (Sum.inr (s, e)) := by
    simp [sideEndpoints]
  have hj : (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) ∈ sideEndpoints L q (Sum.inr (s, e)) := by
    simp [sideEndpoints]
  rw [hn _ hi, hn _ hj, idxOf_seam, idxOf_seam]
  simp only [Nat.add_lt_add_iff_left]
  exact Iff.rfl

/-- Closings precede openings on each seam side. -/
theorem closings_before_openings {b : ℕ} (D : DiskState L b) : D.ClosingsBeforeOpenings := by
  intro s e i j hij hi
  by_contra hj
  set x : DiskEndpoint k r D.q := Sum.inr ⟨s, e, i⟩ with hx
  set y : DiskEndpoint k r D.q := Sum.inr ⟨s, e, j⟩ with hy
  have hxS : x ∈ sideEndpoints L D.q (Sum.inr (s, e)) := by simp [hx, sideEndpoints]
  have hyS : y ∈ sideEndpoints L D.q (Sum.inr (s, e)) := by simp [hy, sideEndpoints]
  have hxy : L.rank x < L.rank y := (rank_seam_lt L D.q s e i j).2 hij
  have hnS : ∀ z : DiskEndpoint k r D.q, ∀ w ∈ sideEndpoints L D.q (Sum.inr (s, e)),
      D.mate w = z → z ∉ sideEndpoints L D.q (Sum.inr (s, e)) := by
    intro z w hw hz hzS
    simp only [sideEndpoints, List.mem_map] at hw hzS
    obtain ⟨w', -, rfl⟩ := hw
    obtain ⟨z', -, rfl⟩ := hzS
    exact D.no_return s e w' z' hz
  have hjc : L.rank (D.mate y) < L.rank y := by
    unfold DiskState.Opens at hj
    have hne : D.mate y ≠ y := D.no_fixed y
    rcases lt_trichotomy (L.rank (D.mate y)) (L.rank y) with h | h | h
    · exact h
    · exact absurd (rank_inj L _ h) hne
    · exact absurd h hj
  have hia : L.rank x < L.rank (D.mate x) := hi
  have hmx := hnS _ x hxS rfl
  have hmy := hnS _ y hyS rfl
  have h1 : ¬ L.rank (D.mate x) < L.rank y := by
    intro h
    have := (rank_outside L D.q _ hyS hxS hmx).1 h
    exact absurd hia (not_lt.2 this.le)
  have h2 : L.rank (D.mate y) < L.rank x := (rank_outside L D.q _ hxS hyS hmy).2 hjc
  have hmm : D.mate (D.mate y) = y := D.involutive y
  have hop1 : L.rank (D.mate y) < L.rank (D.mate (D.mate y)) := by rw [hmm]; exact hjc
  have hnc := D.noncrossing (D.mate y) x hop1 hi
  rw [hmm] at hnc
  apply hnc
  refine ⟨h2, hxy, ?_⟩
  rcases lt_trichotomy (L.rank y) (L.rank (D.mate x)) with h | h | h
  · exact h
  · exact absurd (rank_inj L _ h) (fun hh => hmx (hh ▸ hyS))
  · exact absurd h h1


section Matching
variable {X : Type*} (rk : X → ℕ) (hrk : Function.Injective rk) (m m' : X → X)
include hrk

theorem matching_aux (hm : ∀ x, m (m x) = x) (hm' : ∀ x, m' (m' x) = x)
    (hnf : ∀ x, m x ≠ x) (hnf' : ∀ x, m' x ≠ x)
    (hnc : ∀ p u, rk p < rk (m p) → rk u < rk (m u) →
      ¬ (rk p < rk u ∧ rk u < rk (m p) ∧ rk (m p) < rk (m u)))
    (hop : ∀ x, rk x < rk (m x) ↔ rk x < rk (m' x))
    (c : X) (hc : rk (m c) < rk c)
    (IH : ∀ d, rk d < rk c → rk (m d) < rk d → m d = m' d)
    (hlt : rk (m c) < rk (m' c)) : False := by
  set p := m c with hp
  set p' := m' c with hp'
  have hpne : p ≠ p' := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  have hcl' : rk (m' c) < rk c := by
    by_contra hh
    have h1 : rk c < rk (m' c) := lt_of_le_of_ne (not_lt.1 hh) (fun h => hnf' c (hrk h).symm)
    have h2 := (hop c).2 h1
    exact absurd hc (not_lt.2 h2.le)
  have hp'op : rk p' < rk (m' p') := by rw [hp', hm']; exact hcl'
  have hp'op2 : rk p' < rk (m p') := (hop p').2 hp'op
  have hpop : rk p < rk (m p) := by rw [hp, hm]; exact hc
  have hn := hnc p p' hpop hp'op2
  have hd : rk (m p') ≤ rk c := by
    by_contra hh
    exact hn ⟨hlt, by rw [hp, hm]; exact hcl', by rw [hp, hm]; exact not_le.1 hh⟩
  have hdc : m p' ≠ c := by
    intro h
    apply hpne
    have : m (m p') = m c := by rw [h]
    rw [hm] at this
    exact this.symm
  have hdlt : rk (m p') < rk c := lt_of_le_of_ne hd (fun h => hdc (hrk h))
  have hdcl : rk (m (m p')) < rk (m p') := by rw [hm]; exact hp'op2
  have := IH (m p') hdlt hdcl
  rw [hm] at this
  -- m' (m p') = p' = m' c
  have h2 : m' (m p') = m' c := by rw [← this]
  have := congrArg m' h2
  rw [hm', hm'] at this
  exact hdc this

theorem matching_unique (hm : ∀ x, m (m x) = x) (hm' : ∀ x, m' (m' x) = x)
    (hnf : ∀ x, m x ≠ x) (hnf' : ∀ x, m' x ≠ x)
    (hnc : ∀ p u, rk p < rk (m p) → rk u < rk (m u) →
      ¬ (rk p < rk u ∧ rk u < rk (m p) ∧ rk (m p) < rk (m u)))
    (hnc' : ∀ p u, rk p < rk (m' p) → rk u < rk (m' u) →
      ¬ (rk p < rk u ∧ rk u < rk (m' p) ∧ rk (m' p) < rk (m' u)))
    (hop : ∀ x, rk x < rk (m x) ↔ rk x < rk (m' x)) : ∀ x, m x = m' x := by
  have hcl' : ∀ n, ∀ c0, rk c0 = n → rk (m c0) < rk c0 → m c0 = m' c0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c0 h hc
    by_contra hne
    rcases lt_trichotomy (rk (m c0)) (rk (m' c0)) with h1 | h1 | h1
    · refine matching_aux rk hrk m m' hm hm' hnf hnf' hnc hop c0 hc ?_ h1
      intro d hd hcd
      exact ih (rk d) (h ▸ hd) d rfl hcd
    · exact hne (hrk h1)
    · refine matching_aux rk hrk m' m hm' hm hnf' hnf hnc' (fun x => (hop x).symm) c0 ?_ ?_ h1
      · have h2 : rk (m' c0) < rk c0 := by
          by_contra hh
          have h1' : rk c0 < rk (m' c0) := lt_of_le_of_ne (not_lt.1 hh) (fun h => hnf' c0 (hrk h).symm)
          have h2 := (hop c0).2 h1'
          exact absurd hc (not_lt.2 h2.le)
        exact h2
      · intro d hd hcd
        have hcd' : rk (m d) < rk d := by
          by_contra hh
          have h1' : rk d < rk (m d) := lt_of_le_of_ne (not_lt.1 hh) (fun h => hnf d (hrk h).symm)
          have h2 := (hop d).1 h1'
          exact absurd hcd (not_lt.2 h2.le)
        exact (ih (rk d) (h ▸ hd) d rfl hcd').symm
  have hcl : ∀ c, rk (m c) < rk c → m c = m' c := fun c hc => hcl' _ c rfl hc
  intro x
  by_cases hx : rk (m x) < rk x
  · exact hcl x hx
  · have hxo : rk x < rk (m x) := lt_of_le_of_ne (not_lt.1 hx) (fun h => hnf x (hrk h).symm)
    have hcm : rk (m (m x)) < rk (m x) := by rw [hm]; exact hxo
    have := hcl (m x) hcm
    rw [hm] at this
    have h2 := congrArg m' this
    rw [hm'] at h2
    exact h2.symm
end Matching

theorem len_filter_card (n : ℕ) (P : Fin n → Prop) [DecidablePred P] :
    ((List.finRange n).filter fun j => decide (P j)).length = (Finset.univ.filter P).card := by
  rw [Fin.univ_def, Finset.card_def, Finset.filter_val]
  simp

theorem upset_imp {n : ℕ} (P P' : Fin n → Prop) [DecidablePred P] [DecidablePred P']
    (hP : ∀ i j, i < j → P i → P j) (hP' : ∀ i j, i < j → P' i → P' j)
    (hc : ((List.finRange n).filter fun j => decide (P j)).length =
      ((List.finRange n).filter fun j => decide (P' j)).length) :
    ∀ i, P i → P' i := by
  intro i hi
  by_contra hni
  rw [len_filter_card, len_filter_card] at hc
  have hsub : Finset.univ.filter P' ⊂ Finset.univ.filter P := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [hi], by simp [hni]⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rcases lt_trichotomy j i with h | h | h
      · exact absurd (hP' j i h hj) hni
      · exact absurd (h ▸ hj) hni
      · exact hP i j h hi
  exact absurd hc (Finset.card_lt_card hsub).ne'

theorem topExponent_injective' {b : ℕ} (L : DiskLayout k f r) :
    Function.Injective (fun D : DiskState L b => D.topExponent) := by
  intro D D' h
  simp only at h
  have hq : D.q = D'.q := by
    funext s
    have := congrFun h (Sum.inl s)
    simpa [DiskState.topExponent] using this
  have hcbo := closings_before_openings L D
  have hcbo' := closings_before_openings L D'
  obtain ⟨q, bud, m, inv, nf, nc, nr⟩ := D
  obtain ⟨q', bud', m', inv', nf', nc', nr'⟩ := D'
  simp only at hq
  subst hq
  have hterm : ∀ i : Fin (2 * k), L.rank (Sum.inl i : DiskEndpoint k r q) < L.rank (m (Sum.inl i)) ↔
      L.rank (Sum.inl i : DiskEndpoint k r q) < L.rank (m' (Sum.inl i)) := by
    intro i
    have := congrFun h (Sum.inr (Sum.inl i))
    simp only [DiskState.topExponent, DiskState.Opens] at this
    by_cases a : L.rank (Sum.inl i : DiskEndpoint k r q) < L.rank (m (Sum.inl i)) <;>
    by_cases a' : L.rank (Sum.inl i : DiskEndpoint k r q) < L.rank (m' (Sum.inl i)) <;>
      simp [a, a'] at this ⊢
  have hseam : ∀ s e (j : Fin (q s)), L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m (Sum.inr ⟨s, e, j⟩)) →
      L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m' (Sum.inr ⟨s, e, j⟩)) := by
    intro s e
    have := congrFun h (Sum.inr (Sum.inr (s, e)))
    simp only [DiskState.topExponent, DiskState.sideOpenCount] at this
    have hc := by exact_mod_cast this
    exact upset_imp (fun j : Fin (q s) => L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m (Sum.inr ⟨s, e, j⟩)))
      (fun j : Fin (q s) => L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m' (Sum.inr ⟨s, e, j⟩)))
      (fun i j hij => hcbo s e i j hij) (fun i j hij => hcbo' s e i j hij) hc
  have hseam' : ∀ s e (j : Fin (q s)), L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m' (Sum.inr ⟨s, e, j⟩)) →
      L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m (Sum.inr ⟨s, e, j⟩)) := by
    intro s e
    have := congrFun h (Sum.inr (Sum.inr (s, e)))
    simp only [DiskState.topExponent, DiskState.sideOpenCount] at this
    have hc := by exact_mod_cast this.symm
    exact upset_imp (fun j : Fin (q s) => L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m' (Sum.inr ⟨s, e, j⟩)))
      (fun j : Fin (q s) => L.rank (Sum.inr ⟨s, e, j⟩ : DiskEndpoint k r q) < L.rank (m (Sum.inr ⟨s, e, j⟩)))
      (fun i j hij => hcbo' s e i j hij) (fun i j hij => hcbo s e i j hij) hc
  have hop : ∀ x : DiskEndpoint k r q, L.rank x < L.rank (m x) ↔ L.rank x < L.rank (m' x) := by
    intro x
    rcases x with i | ⟨s, e, j⟩
    · exact hterm i
    · exact ⟨hseam s e j, hseam' s e j⟩
  have hmm : m = m' := by
    apply Equiv.ext
    exact matching_unique (L.rank) (fun x y hxy => rank_inj L q hxy) m m' inv inv' nf nf' nc nc' hop
  subst hmm
  rfl

end SPDAux

namespace SPDAux

section Assembly
open ShortestPlanarDisjoint.Main

theorem exists_max {E ι : Type*} [AddCommGroup E] {lt : E → E → Prop} (h : TOrd lt) (a : ι → E)
    (s : Finset ι) (hs : s.Nonempty) : ∃ i ∈ s, ∀ j ∈ s, a j = a i ∨ lt (a j) (a i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton x => exact ⟨x, by simp, fun j hj => Or.inl (by simp at hj; rw [hj])⟩
  | cons x s hx hne ih =>
    obtain ⟨i, hi, hmax⟩ := ih
    rcases h.total (a x) (a i) with h1 | h1 | h1
    · refine ⟨i, Finset.mem_cons_of_mem hi, fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact Or.inr h1
      · exact hmax j hj
    · refine ⟨i, Finset.mem_cons_of_mem hi, fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact Or.inl h1
      · exact hmax j hj
    · refine ⟨x, Finset.mem_cons_self _ _, fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact Or.inl rfl
      · rcases hmax j hj with h2 | h2
        · exact Or.inr (h2 ▸ h1)
        · exact Or.inr (h.trans _ _ _ h2 h1)

theorem linIndep_of_leads {E ι : Type*} [AddCommGroup E] {lt : E → E → Prop} (h : TOrd lt)
    (p : ι → AddMonoidAlgebra (ZMod 2) E) (a : ι → E) (hlead : ∀ i, Lead lt (p i) (a i))
    (hinj : Function.Injective a) : LinearIndependent (ZMod 2) p := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i0 hi0
  by_contra hg0
  set s' := s.filter (fun i => g i ≠ 0) with hs'
  have hne : s'.Nonempty := ⟨i0, by simp [hs', hi0, hg0]⟩
  obtain ⟨i, hi, hmax⟩ := exists_max h a s' hne
  have hcoef : (∑ j ∈ s, g j • p j).coeff (a i) = 0 := by rw [hsum]; rfl
  have hsum' : (∑ j ∈ s, g j • p j).coeff (a i) = ∑ j ∈ s, g j * (p j).coeff (a i) := by
    rw [AddMonoidAlgebra.coeff_sum]
    simp [Finsupp.finsetSum_apply]
  rw [hsum'] at hcoef
  rw [Finset.sum_eq_single i] at hcoef
  · rw [(hlead i).1] at hcoef
    have : g i ≠ 0 := (Finset.mem_filter.1 hi).2
    simp at hcoef
    exact this hcoef
  · intro j hj hji
    by_cases hgj : g j = 0
    · simp [hgj]
    · have hjs' : j ∈ s' := by simp [hs', hj, hgj]
      have hcz : (p j).coeff (a i) = 0 := by
        by_contra hc
        rcases (hlead j).2 _ hc with h1 | h1
        · exact hji (hinj h1.symm)
        · rcases hmax j hjs' with h2 | h2
          · rw [h2] at h1; exact h.irrefl _ h1
          · exact h.irrefl _ (h.trans _ _ _ h1 h2)
      simp [hcz]
  · intro hi'
    exact absurd (Finset.mem_filter.1 hi).1 hi'


variable {k f r b : ℕ}

def restOrder (L : DiskLayout k f r) : List (SignatureVariable k r) :=
  L.sideOrder.flatMap (fun side => match side with
    | .inl j => (L.block j).map fun i => Sum.inr (Sum.inl i)
    | .inr (s, e) => [Sum.inr (Sum.inr (s, e))])

theorem variableOrder_eq (L : DiskLayout k f r) :
    L.variableOrder = (List.finRange r).map Sum.inl ++ restOrder L := rfl

theorem variableOrder_complete (L : DiskLayout k f r) (x : SignatureVariable k r) :
    x ∈ (List.finRange r).map Sum.inl ++ restOrder L := by
  rcases x with s | i | ⟨s, e⟩
  · simp
  · have hi := L.terminals_complete i
    simp only [List.mem_flatten, List.mem_ofFn] at hi
    obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hi
    refine List.mem_append_right _ ?_
    unfold restOrder
    rw [List.mem_flatMap]
    exact ⟨Sum.inl j, L.sides_complete _, by simpa using hl⟩
  · refine List.mem_append_right _ ?_
    unfold restOrder
    rw [List.mem_flatMap]
    exact ⟨Sum.inr (s, e), L.sides_complete _, by simp⟩

section PermFacts
variable {X : Type*} (M G : Equiv.Perm X)

theorem perm_inv_of_invol (hM : ∀ x, M (M x) = x) : M⁻¹ = M := by
  rw [inv_eq_iff_mul_eq_one]; ext x; simp [hM]

theorem conj_tau (hM : ∀ x, M (M x) = x) (hG : ∀ x, G (G x) = x) (n : ℤ) (x : X) :
    M (((G * M) ^ n) x) = ((G * M) ^ (-n)) (M x) := by
  have hMi := perm_inv_of_invol M hM
  have hGi := perm_inv_of_invol G hG
  have h1 : M * (G * M) * M⁻¹ = (G * M)⁻¹ := by
    rw [mul_inv_rev, hMi, hGi]; ext y; simp [hM]
  have h2 := conj_zpow (i := n) (a := M) (b := G * M)
  rw [h1, inv_zpow'] at h2
  have := congrArg (fun P : Equiv.Perm X => P (M x)) h2
  simp only [Equiv.Perm.mul_apply, hMi, hM] at this
  exact this.symm

theorem conj_tau_g (hM : ∀ x, M (M x) = x) (hG : ∀ x, G (G x) = x) (n : ℤ) (x : X) :
    G (((G * M) ^ n) x) = ((G * M) ^ (-n)) (G x) := by
  have hMi := perm_inv_of_invol M hM
  have hGi := perm_inv_of_invol G hG
  have h1 : G * (G * M) * G⁻¹ = (G * M)⁻¹ := by
    rw [mul_inv_rev, hMi, hGi]; ext y; simp [hG]
  have h2 := conj_zpow (i := n) (a := G) (b := G * M)
  rw [h1, inv_zpow'] at h2
  have := congrArg (fun P : Equiv.Perm X => P (G x)) h2
  simp only [Equiv.Perm.mul_apply, hGi, hG] at this
  exact this.symm

theorem pow_succ_apply' (P : Equiv.Perm X) (n : ℕ) (y : X) : (P ^ (n + 1)) y = (P ^ n) (P y) := by
  rw [pow_succ, Equiv.Perm.mul_apply]

theorem zpow_add_apply (P : Equiv.Perm X) (a b : ℤ) (y : X) :
    (P ^ (a + b)) y = (P ^ a) ((P ^ b) y) := by
  rw [zpow_add, Equiv.Perm.mul_apply]

end PermFacts

theorem glue_invol {k r : ℕ} {q : Fin r → ℕ} (same : Fin r → Bool) :
    Function.Involutive (glueEndpoint (k := k) (q := q) same) := by
  intro x
  rcases x with i | ⟨s, e, j⟩
  · rfl
  · simp only [glueEndpoint]
    split_ifs with h
    · simp
    · simp only [Bool.not_not, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and]
      ext; simp; omega

def glueP {k r : ℕ} {q : Fin r → ℕ} (same : Fin r → Bool) : Equiv.Perm (DiskEndpoint k r q) :=
  Function.Involutive.toPerm _ (glue_invol same)

theorem glueP_apply {k r : ℕ} {q : Fin r → ℕ} (same : Fin r → Bool) (x : DiskEndpoint k r q) :
    glueP same x = glueEndpoint same x := rfl

theorem glue_isLeft {k r : ℕ} {q : Fin r → ℕ} (same : Fin r → Bool) (x : DiskEndpoint k r q) :
    (glueEndpoint same x).isLeft = x.isLeft := by
  rcases x with i | ⟨s, e, j⟩ <;> rfl

theorem glue_fix_iff {k r : ℕ} {q : Fin r → ℕ} (same : Fin r → Bool) (x : DiskEndpoint k r q) :
    glueEndpoint same x = x ↔ x.isLeft = true := by
  rcases x with i | ⟨s, e, j⟩
  · simp [glueEndpoint]
  · simp only [glueEndpoint, Sum.isLeft_inr, Bool.false_eq_true, iff_false]
    intro h
    simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    have := congrArg (fun p : Bool × Fin (q s) => p.1) h
    simp at this

def crO {k r : ℕ} {q : Fin r → ℕ} : DiskEndpoint k r q → Option (Fin r × Bool)
  | .inl _ => none
  | .inr ⟨s, e, _⟩ => some (s, e)

def var {k r : ℕ} {q : Fin r → ℕ} : DiskEndpoint k r q → SignatureVariable k r
  | .inl i => .inr (.inl i)
  | .inr ⟨s, e, _⟩ => .inr (.inr (s, e))

def ev {k r : ℕ} {q : Fin r → ℕ} (x : DiskEndpoint k r q) : Ex k r := ex (var x)

def lam {k r : ℕ} {q : Fin r → ℕ} : DiskEndpoint k r q → Ex k r
  | .inl _ => 0
  | .inr ⟨s, _, _⟩ => ex (.inl s)

theorem ev_glue {k r : ℕ} {q : Fin r → ℕ} (same : Fin r → Bool) (s : Fin r) (e : Bool)
    (j : Fin (q s)) :
    ev (glueEndpoint (k := k) same (Sum.inr ⟨s, e, j⟩)) = ex (Sum.inr (Sum.inr (s, !e))) := by
  rfl

theorem ex_inj {k r : ℕ} {v w : SignatureVariable k r} (h : (ex v : Ex k r) = ex w) : v = w := by
  have := congrFun h v
  unfold ex at this
  by_contra hne
  simp [Pi.single_apply, hne] at this

section Runs
variable {L : DiskLayout k f r} (D : DiskState L b) (same : Fin r → Bool)

def tau : Equiv.Perm (DiskEndpoint k r D.q) := glueP same * D.mate

theorem tau_apply (x : DiskEndpoint k r D.q) : tau D same x = glueEndpoint same (D.mate x) := rfl

theorem mate_mate (x : DiskEndpoint k r D.q) : D.mate (D.mate x) = x := D.involutive x

theorem m_tau (n : ℤ) (x : DiskEndpoint k r D.q) :
    D.mate ((tau D same ^ n) x) = (tau D same ^ (-n)) (D.mate x) :=
  conj_tau D.mate (glueP same) (mate_mate D) (glue_invol same) n x

theorem g_tau (n : ℤ) (x : DiskEndpoint k r D.q) :
    glueEndpoint same ((tau D same ^ n) x) = (tau D same ^ (-n)) (glueEndpoint same x) :=
  conj_tau_g D.mate (glueP same) (mate_mate D) (glue_invol same) n x

theorem g_eq_m_tauinv (x : DiskEndpoint k r D.q) :
    glueEndpoint same x = D.mate ((tau D same ^ (-1 : ℤ)) x) := by
  rw [m_tau]; simp only [neg_neg, zpow_one, tau_apply, mate_mate]

theorem ev_ne (x : DiskEndpoint k r D.q) : ev x ≠ ev (D.mate x) := by
  intro h
  have h' := ex_inj h
  revert h'
  rcases x with i | ⟨s, e, j⟩
  · rcases hm : D.mate (Sum.inl i) with i' | ⟨s', e', j'⟩ <;> intro hh <;> simp [var] at hh
    subst hh; exact D.no_fixed _ hm
  · rcases hm : D.mate (Sum.inr ⟨s, e, j⟩) with i' | ⟨s', e', j'⟩ <;> intro hh <;>
      simp [var] at hh
    obtain ⟨rfl, rfl⟩ := hh
    exact D.no_return s e j j' hm

def csOf (h : ℕ) (y : DiskEndpoint k r D.q) : List (Fin r × Bool) :=
  (List.range h).filterMap (fun n => crO (D.mate ((tau D same ^ n) y)))

theorem csOf_zero (y : DiskEndpoint k r D.q) : csOf D same 0 y = [] := rfl

theorem csOf_succ (h : ℕ) (y : DiskEndpoint k r D.q) (s : Fin r) (e : Bool) (jj : Fin (D.q s))
    (hy : D.mate y = Sum.inr ⟨s, e, jj⟩) :
    csOf D same (h + 1) y = (s, e) :: csOf D same h (tau D same y) := by
  unfold csOf
  rw [List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
  simp only [pow_zero, Equiv.Perm.one_apply, hy, crO]
  congr 1

theorem follow_path (start : DiskEndpoint k r D.q) (j : Fin (2 * k)) :
    ∀ (h t : ℕ) (y : DiskEndpoint k r D.q), h < t →
    (∀ n < h, (D.mate ((tau D same ^ n) y)).isLeft = false) →
    D.mate ((tau D same ^ h) y) = Sum.inl j →
    (∀ n < h, (tau D same ^ (n + 1)) y ≠ start) →
    D.follow same start t y = (csOf D same h y, some j) := by
  intro h
  induction h with
  | zero =>
    intro t y ht _ hj _
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [pow_zero, Equiv.Perm.one_apply] at hj
    simp [DiskState.follow, hj, csOf_zero]
  | succ h ih =>
    intro t y ht hs hj hn
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h0 := hs 0 (by omega)
    simp only [pow_zero, Equiv.Perm.one_apply] at h0
    rcases hmy : D.mate y with i | ⟨s, e, jj⟩
    · rw [hmy] at h0; simp at h0
    have hty : tau D same y = glueEndpoint same (Sum.inr ⟨s, e, jj⟩) := by rw [tau_apply, hmy]
    have hne : glueEndpoint same (Sum.inr ⟨s, e, jj⟩) ≠ start := by
      rw [← hty]; simpa using hn 0 (by omega)
    have hrec := ih t (tau D same y) (by omega)
      (fun n hn' => by rw [← pow_succ_apply']; exact hs (n + 1) (by omega))
      (by rw [← pow_succ_apply']; exact hj)
      (fun n hn' => by rw [← pow_succ_apply']; exact hn (n + 1) (by omega))
    rw [csOf_succ D same h y s e jj hmy]
    simp only [DiskState.follow, hmy]
    rw [if_neg hne, ← hty, hrec]

theorem follow_cycle (start : DiskEndpoint k r D.q) :
    ∀ (h t : ℕ) (y : DiskEndpoint k r D.q), 0 < h → h ≤ t →
    (∀ n < h, (D.mate ((tau D same ^ n) y)).isLeft = false) →
    (tau D same ^ h) y = start →
    (∀ n, 0 < n → n < h → (tau D same ^ n) y ≠ start) →
    D.follow same start t y = (csOf D same h y, none) := by
  intro h
  induction h with
  | zero => intro t y h0; omega
  | succ h ih =>
    intro t y _ ht hs hj hn
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h0 := hs 0 (by omega)
    simp only [pow_zero, Equiv.Perm.one_apply] at h0
    rcases hmy : D.mate y with i | ⟨s, e, jj⟩
    · rw [hmy] at h0; simp at h0
    have hty : tau D same y = glueEndpoint same (Sum.inr ⟨s, e, jj⟩) := by rw [tau_apply, hmy]
    rw [csOf_succ D same h y s e jj hmy]
    simp only [DiskState.follow, hmy]
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · have : glueEndpoint same (Sum.inr ⟨s, e, jj⟩) = start := by
        rw [← hty]; simpa using hj
      rw [if_pos this, csOf_zero]
    · have hne : glueEndpoint same (Sum.inr ⟨s, e, jj⟩) ≠ start := by
        rw [← hty]; simpa using hn 1 (by omega) (by omega)
      have hrec := ih t (tau D same y) hpos (by omega)
        (fun n hn' => by rw [← pow_succ_apply']; exact hs (n + 1) (by omega))
        (by rw [← pow_succ_apply']; exact hj)
        (fun n h1 h2 => by rw [← pow_succ_apply']; exact hn (n + 1) (by omega) (by omega))
      rw [if_neg hne, ← hty, hrec]

variable (rest : List (SignatureVariable k r))

noncomputable def pl (x : DiskEndpoint k r D.q) : Ex k r := mx (LT k r rest) (ev x) (ev (D.mate x))

noncomputable def Wt (x : DiskEndpoint k r D.q) : Ex k r := pl D rest x + lam (D.mate x)

theorem chain_exp (uw : Ex k r) : ∀ (h : ℕ) (y : DiskEndpoint k r D.q),
    (∀ n < h, (D.mate ((tau D same ^ n) y)).isLeft = false) →
    uw = ev (D.mate ((tau D same ^ h) y)) →
    hd uw (csOf D same h y) = ev (D.mate y) ∧ chainOK uw (csOf D same h y) ∧
    lamE (csOf D same h y) + pairE rest uw (csOf D same h y) =
      ∑ n ∈ Finset.range h, (lam (D.mate ((tau D same ^ n) y)) +
        pl D rest ((tau D same ^ (n + 1)) y)) := by
  intro h
  induction h with
  | zero =>
    intro y _ hu
    simp only [pow_zero, Equiv.Perm.one_apply] at hu
    simp [csOf_zero, hd, chainOK, lamE, pairE, hu]
  | succ h ih =>
    intro y hs hu
    have h0 := hs 0 (by omega)
    simp only [pow_zero, Equiv.Perm.one_apply] at h0
    rcases hmy : D.mate y with i | ⟨s, e, jj⟩
    · rw [hmy] at h0; simp at h0
    have hty : tau D same y = glueEndpoint same (Sum.inr ⟨s, e, jj⟩) := by rw [tau_apply, hmy]
    obtain ⟨ih1, ih2, ih3⟩ := ih (tau D same y)
      (fun n hn' => by rw [← pow_succ_apply']; exact hs (n + 1) (by omega))
      (by rw [← pow_succ_apply']; exact hu)
    rw [csOf_succ D same h y s e jj hmy]
    have hevt : ev (tau D same y) = ex (Sum.inr (Sum.inr (s, !e))) := by rw [hty, ev_glue]
    refine ⟨rfl, ⟨?_, ih2⟩, ?_⟩
    · simp only
      rw [ih1, ← hevt]; exact ev_ne D _
    · simp only [lamE, pairE]
      rw [ih1, ← hevt, Finset.sum_range_succ']
      have hcongr : ∑ n ∈ Finset.range h, (lam (D.mate ((tau D same ^ (n + 1)) y)) +
          pl D rest ((tau D same ^ (n + 1 + 1)) y)) =
          lamE (csOf D same h (tau D same y)) + pairE rest uw (csOf D same h (tau D same y)) := by
        rw [ih3]; apply Finset.sum_congr rfl; intro n _
        rw [pow_succ_apply' (tau D same) n y, pow_succ_apply' (tau D same) (n + 1) y]
      rw [hcongr]
      simp only [pow_zero, Equiv.Perm.one_apply, zero_add, pow_one, hmy, lam, pl]
      abel

end Runs
section Runs2
variable {L : DiskLayout k f r} (D : DiskState L b) (same : Fin r → Bool)

theorem pow_succ_apply'' {X : Type*} (P : Equiv.Perm X) (n : ℕ) (y : X) :
    (P ^ (n + 1)) y = P ((P ^ n) y) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem zc {X : Type*} (P : Equiv.Perm X) {a c : ℤ} (h : a = c) (y : X) :
    (P ^ a) y = (P ^ c) y := by rw [h]

theorem tau_zpow_one {X : Type*} (P : Equiv.Perm X) (y : X) : P y = (P ^ (1 : ℤ)) y := by
  rw [zpow_one]

theorem npow_eq_zpow {X : Type*} (P : Equiv.Perm X) (n : ℕ) (y : X) :
    (P ^ n) y = (P ^ (n : ℤ)) y := by
  rw [zpow_natCast]

theorem conn_symm {x y : DiskEndpoint k r D.q} (h : D.Connected same x y) :
    D.Connected same y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih =>
    refine Relation.ReflTransGen.head ?_ ih
    rcases hr with hac | hac
    · exact Or.inl (by rw [← hac, mate_mate])
    · exact Or.inr (by rw [← hac, glue_invol])

theorem conn_trans {x y z : DiskEndpoint k r D.q} (h1 : D.Connected same x y)
    (h2 : D.Connected same y z) : D.Connected same x z := h1.trans h2

theorem conn_mate (x : DiskEndpoint k r D.q) : D.Connected same x (D.mate x) :=
  Relation.ReflTransGen.single (Or.inl rfl)

theorem conn_glue (x : DiskEndpoint k r D.q) : D.Connected same x (glueEndpoint same x) :=
  Relation.ReflTransGen.single (Or.inr rfl)

theorem conn_pow (x : DiskEndpoint k r D.q) (n : ℕ) :
    D.Connected same x ((tau D same ^ n) x) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [pow_succ_apply'', tau_apply]
    exact conn_trans D same ih (conn_trans D same (conn_mate D same _) (conn_glue D same _))

def runSet (len : ℕ) (y : DiskEndpoint k r D.q) : Finset (DiskEndpoint k r D.q) :=
  (Finset.range len).image (fun n => (tau D same ^ n) y)

theorem mem_runSet (len : ℕ) (y x : DiskEndpoint k r D.q) :
    x ∈ runSet D same len y ↔ ∃ n < len, (tau D same ^ n) y = x := by
  simp [runSet]

theorem glue_mate (x : DiskEndpoint k r D.q) :
    glueEndpoint same (D.mate x) = tau D same x := rfl

theorem glue_eq_tau_mate (x : DiskEndpoint k r D.q) :
    glueEndpoint same x = tau D same (D.mate x) := by
  rw [tau_apply, mate_mate]

theorem pow_inj_aux (y : DiskEndpoint k r D.q) (a b : ℕ) (hab : a < b)
    (h : (tau D same ^ a) y = (tau D same ^ b) y) : (tau D same ^ (b - a)) y = y := by
  have : (tau D same ^ b) y = (tau D same ^ a) ((tau D same ^ (b - a)) y) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add]; congr 2; omega
  rw [this] at h
  exact ((tau D same ^ a).injective h).symm

/-- `τ^{-1} t = m t` for a terminal `t`. -/
theorem tauinv_term (t : DiskEndpoint k r D.q) (ht : t.isLeft = true) :
    (tau D same ^ (-1 : ℤ)) t = D.mate t := by
  have : tau D same (D.mate t) = t := by
    rw [tau_apply, mate_mate]; exact (glue_fix_iff same t).2 ht
  calc (tau D same ^ (-1 : ℤ)) t = (tau D same ^ (-1 : ℤ)) (tau D same (D.mate t)) := by
        rw [this]
    _ = D.mate t := by rw [zpow_neg_one]; exact Equiv.Perm.inv_eq_iff_eq.mpr rfl

section Path
variable (t : DiskEndpoint k r D.q) (ht : t.isLeft = true) (h : ℕ)
  (hmin : ∀ n < h, (D.mate ((tau D same ^ n) t)).isLeft = false)
  (hh : (D.mate ((tau D same ^ h) t)).isLeft = true)
include ht hmin

theorem path_seam (n : ℕ) (h0 : 0 < n) (hn : n ≤ h) : ((tau D same ^ n) t).isLeft = false := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ_apply'', tau_apply, glue_isLeft]
  exact hmin n (by omega)

theorem path_inj (a c : ℕ) (ha : a ≤ h) (hc : c ≤ h)
    (hac : (tau D same ^ a) t = (tau D same ^ c) t) : a = c := by
  rcases lt_trichotomy a c with h1 | h1 | h1
  · have := pow_inj_aux D same t a c h1 hac
    have h2 := path_seam D same t ht h hmin (c - a) (by omega) (by omega)
    rw [this, ht] at h2; exact absurd h2 (by simp)
  · exact h1
  · have := pow_inj_aux D same t c a h1 hac.symm
    have h2 := path_seam D same t ht h hmin (a - c) (by omega) (by omega)
    rw [this, ht] at h2; exact absurd h2 (by simp)

theorem path_disj (a c : ℕ) (ha : a ≤ h) (hc : c ≤ h) :
    (tau D same ^ a) t ≠ D.mate ((tau D same ^ c) t) := by
  intro hac
  rw [npow_eq_zpow, npow_eq_zpow, m_tau, ← tauinv_term D same t ht, ← zpow_add_apply] at hac
  have hfix : (tau D same ^ ((a + c + 1 : ℕ) : ℤ)) t = t := by
    calc (tau D same ^ ((a + c + 1 : ℕ) : ℤ)) t
        = (tau D same ^ ((c : ℤ) + 1)) ((tau D same ^ (a : ℤ)) t) := by
          rw [← zpow_add_apply]; exact zc _ (by push_cast; ring) _
      _ = (tau D same ^ ((c : ℤ) + 1)) ((tau D same ^ (-(c : ℤ) + -1)) t) := by rw [hac]
      _ = t := by rw [← zpow_add_apply, zc _ (show (c : ℤ) + 1 + (-(c : ℤ) + -1) = 0 by ring),
                    zpow_zero]; rfl
  have hper : ∀ z : ℤ, (tau D same ^ (z + ((a + c + 1 : ℕ) : ℤ))) t = (tau D same ^ z) t := by
    intro z; rw [zpow_add_apply, hfix]
  obtain ⟨u, hu | hu⟩ := Nat.even_or_odd' (a + c + 1)
  · -- glue fixes τ^u t
    have hg : glueEndpoint same ((tau D same ^ (u : ℤ)) t) = (tau D same ^ (u : ℤ)) t := by
      rw [g_tau, (glue_fix_iff same t).2 ht]
      have := hper (-(u : ℤ))
      rw [hu] at this; push_cast at this
      rw [← this]; congr 2; ring
    rw [glue_fix_iff, ← npow_eq_zpow, path_seam D same t ht h hmin u (by omega) (by omega)] at hg
    exact absurd hg (by simp)
  · apply D.no_fixed ((tau D same ^ (u : ℤ)) t)
    rw [m_tau, ← tauinv_term D same t ht, ← zpow_add_apply]
    have := hper (-(u : ℤ) - 1)
    rw [hu] at this; push_cast at this
    exact (zc _ (by ring) _).trans (this.symm.trans (zc _ (by ring) _))

theorem path_inv (x : DiskEndpoint k r D.q) (hx : x ∈ runSet D same (h + 1) t)
    (hxl : x.isLeft = false) : (tau D same ^ (-1 : ℤ)) x ∈ runSet D same (h + 1) t := by
  rw [mem_runSet] at hx ⊢
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp [ht] at hxl
    · omega⟩
  refine ⟨n, by omega, ?_⟩
  rw [pow_succ_apply'', zpow_neg_one]; exact (Equiv.Perm.inv_eq_iff_eq.mpr rfl).symm

include hh in
theorem path_fwd (x : DiskEndpoint k r D.q) (hx : x ∈ runSet D same (h + 1) t)
    (hxl : (D.mate x).isLeft = false) : tau D same x ∈ runSet D same (h + 1) t := by
  rw [mem_runSet] at hx ⊢
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨n + 1, ?_, pow_succ_apply'' _ _ _⟩
  rcases Nat.lt_or_ge n h with h1 | h1
  · omega
  · have : n = h := by omega
    subst this; rw [hh] at hxl; exact absurd hxl (by simp)

include hh in
theorem path_conn (x : DiskEndpoint k r D.q) :
    D.Connected same t x ↔
      x ∈ runSet D same (h + 1) t ∨ D.mate x ∈ runSet D same (h + 1) t := by
  constructor
  · intro hc
    induction hc with
    | refl => exact Or.inl ((mem_runSet _ _ _ _ _).2 ⟨0, by omega, by simp⟩)
    | tail _ hr ih =>
      rename_i x z _
      rcases hr with hr | hr
      · subst hr; rw [mate_mate]; exact ih.symm
      · subst hr
        rcases ih with ih | ih
        · obtain ⟨n, hn, rfl⟩ := (mem_runSet _ _ _ _ _).1 ih
          rcases Nat.eq_zero_or_pos n with rfl | h0
          · left; simp only [pow_zero, Equiv.Perm.one_apply]
            rw [(glue_fix_iff same t).2 ht]
            exact (mem_runSet _ _ _ _ _).2 ⟨0, by omega, by simp⟩
          · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            right
            rw [pow_succ_apply'', tau_apply, glue_invol, mate_mate]
            exact (mem_runSet _ _ _ _ _).2 ⟨n, by omega, rfl⟩
        · rcases hl : x.isLeft
          · rw [glue_eq_tau_mate]; left
            exact path_fwd D same t ht h hmin hh _ ih (by rw [mate_mate]; exact hl)
          · rw [(glue_fix_iff same x).2 hl]; right; exact ih
  · rintro (hx | hx)
    · obtain ⟨n, _, rfl⟩ := (mem_runSet _ _ _ _ _).1 hx
      exact conn_pow D same t n
    · obtain ⟨n, _, hn⟩ := (mem_runSet _ _ _ _ _).1 hx
      have := conn_trans D same (conn_pow D same t n) (conn_mate D same _)
      rwa [hn, mate_mate] at this

include hh in
theorem path_term (i' : Fin (2 * k)) (hc : D.Connected same t (Sum.inl i')) :
    Sum.inl i' = t ∨ Sum.inl i' = D.mate ((tau D same ^ h) t) := by
  rcases (path_conn D same t ht h hmin hh _).1 hc with hx | hx
  · obtain ⟨n, hn, hx⟩ := (mem_runSet _ _ _ _ _).1 hx
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · left; simpa using hx.symm
    · have := path_seam D same t ht h hmin n h0 (by omega)
      rw [hx] at this; simp at this
  · obtain ⟨n, hn, hx⟩ := (mem_runSet _ _ _ _ _).1 hx
    right
    have hx' : Sum.inl i' = D.mate ((tau D same ^ n) t) := by rw [hx, mate_mate]
    rcases Nat.lt_or_ge n h with h1 | h1
    · have := hmin n h1; rw [← hx'] at this; simp at this
    · rw [hx']; congr 3; omega

theorem path_sum {E : Type*} [AddCommMonoid E] (F : DiskEndpoint k r D.q → E) :
    ∑ x ∈ runSet D same (h + 1) t, F x = ∑ n ∈ Finset.range (h + 1), F ((tau D same ^ n) t) := by
  unfold runSet
  rw [Finset.sum_image]
  intro a ha c hc hac
  exact path_inj D same t ht h hmin a c (by simp at ha; omega) (by simp at hc; omega) hac

end Path

section Cycle
variable (p : DiskEndpoint k r D.q)
  (hfree : ∀ x, D.Connected same p x → x.isLeft = false) (h : ℕ) (hpos : 0 < h)
  (hper : (tau D same ^ h) p = p)
  (hmin : ∀ n, 0 < n → n < h → (tau D same ^ n) p ≠ p)

include hpos hper in
theorem cyc_mem (z : ℤ) : (tau D same ^ z) p ∈ runSet D same h p := by
  rw [mem_runSet]
  have hh : (tau D same ^ ((h : ℕ) : ℤ)) p = p := by rw [zpow_natCast]; exact hper
  have hmul : ∀ w : ℤ, (tau D same ^ ((h : ℤ) * w)) p = p := by
    intro w; rw [zpow_mul]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hh w
  have hz : (tau D same ^ z) p = (tau D same ^ (z % (h : ℤ))) p := by
    conv_lhs => rw [← Int.emod_add_mul_ediv z h]
    rw [zpow_add_apply, hmul]
  have h1 : 0 ≤ z % (h : ℤ) := Int.emod_nonneg _ (by omega)
  have h2 : z % (h : ℤ) < h := Int.emod_lt_of_pos _ (by omega)
  refine ⟨(z % (h : ℤ)).toNat, by omega, ?_⟩
  rw [hz, npow_eq_zpow, Int.toNat_of_nonneg h1]

include hmin in
theorem cyc_inj (a c : ℕ) (ha : a < h) (hc : c < h)
    (hac : (tau D same ^ a) p = (tau D same ^ c) p) : a = c := by
  rcases lt_trichotomy a c with h1 | h1 | h1
  · exact absurd (pow_inj_aux D same p a c h1 hac) (hmin _ (by omega) (by omega))
  · exact h1
  · exact absurd (pow_inj_aux D same p c a h1 hac.symm) (hmin _ (by omega) (by omega))

include hfree hpos hper in
theorem cyc_disj (x : DiskEndpoint k r D.q) (hx : x ∈ runSet D same h p) :
    D.mate x ∉ runSet D same h p := by
  intro hm
  obtain ⟨a, _, rfl⟩ := (mem_runSet _ _ _ _ _).1 hx
  obtain ⟨c, _, hc⟩ := (mem_runSet _ _ _ _ _).1 hm
  rw [npow_eq_zpow, npow_eq_zpow, m_tau] at hc
  have hmp : D.mate p = (tau D same ^ ((a + c : ℕ) : ℤ)) p := by
    have := congrArg (fun z => (tau D same ^ (a : ℤ)) z) hc
    simp only [← zpow_add_apply] at this
    rw [show (a : ℤ) + -(a : ℤ) = 0 by ring, zpow_zero, Equiv.Perm.one_apply] at this
    exact this.symm.trans (zc _ (by push_cast; ring) _)
  obtain ⟨u, hu | hu⟩ := Nat.even_or_odd' (a + c)
  · apply D.no_fixed ((tau D same ^ (u : ℤ)) p)
    rw [m_tau, hmp, ← zpow_add_apply, hu]; congr 2; push_cast; ring
  · have hg : glueEndpoint same ((tau D same ^ ((u + 1 : ℕ) : ℤ)) p) =
        (tau D same ^ ((u + 1 : ℕ) : ℤ)) p := by
      rw [g_tau, glue_eq_tau_mate, hmp, tau_zpow_one (tau D same) ((tau D same ^ _) p),
        ← zpow_add_apply, ← zpow_add_apply]
      exact zc _ (by push_cast; omega) _
    rw [glue_fix_iff, ← npow_eq_zpow, hfree _ (conn_pow D same p _)] at hg
    exact absurd hg (by simp)

include hpos hper in
theorem cyc_conn (x : DiskEndpoint k r D.q) :
    D.Connected same p x ↔ x ∈ runSet D same h p ∨ D.mate x ∈ runSet D same h p := by
  constructor
  · intro hc
    induction hc with
    | refl => exact Or.inl ((mem_runSet _ _ _ _ _).2 ⟨0, hpos, by simp⟩)
    | tail _ hr ih =>
      rename_i x z _
      rcases hr with hr | hr
      · subst hr; rw [mate_mate]; exact ih.symm
      · subst hr
        rcases ih with ih | ih
        · obtain ⟨n, hn, rfl⟩ := (mem_runSet _ _ _ _ _).1 ih
          right
          rw [g_eq_m_tauinv, mate_mate, npow_eq_zpow, ← zpow_add_apply]
          exact cyc_mem D same p h hpos hper _
        · obtain ⟨n, hn, hx⟩ := (mem_runSet _ _ _ _ _).1 ih
          left
          rw [glue_eq_tau_mate, ← hx, ← pow_succ_apply'', npow_eq_zpow]
          exact cyc_mem D same p h hpos hper _
  · rintro (hx | hx)
    · obtain ⟨n, _, rfl⟩ := (mem_runSet _ _ _ _ _).1 hx
      exact conn_pow D same p n
    · obtain ⟨n, _, hn⟩ := (mem_runSet _ _ _ _ _).1 hx
      have := conn_trans D same (conn_pow D same p n) (conn_mate D same _)
      rwa [hn, mate_mate] at this

include hmin in
theorem cyc_sum {E : Type*} [AddCommMonoid E] (F : DiskEndpoint k r D.q → E) :
    ∑ x ∈ runSet D same h p, F x = ∑ n ∈ Finset.range h, F ((tau D same ^ n) p) := by
  unfold runSet
  rw [Finset.sum_image]
  intro a ha c hc hac
  exact cyc_inj D same p h hmin a c (by simpa using ha) (by simpa using hc) hac

end Cycle
end Runs2

theorem accounting {X E : Type*} [DecidableEq X] [AddCommMonoid E] (m : X → X)
    (hm : ∀ x, m (m x) = x) (C : X → X → Prop) (hCs : ∀ x y, C x y → C y x)
    (hCt : ∀ x y z, C x y → C y z → C x z) (S : Finset X) (R : X → Finset X) (W : X → E)
    (h2 : ∀ s ∈ S, ∀ x ∈ R s, m x ∉ R s) (h3 : ∀ s ∈ S, ∀ x, C s x ↔ x ∈ R s ∨ m x ∈ R s)
    (g1 : ∀ x, ∃ s ∈ S, C s x) (g2 : ∀ s ∈ S, ∀ s' ∈ S, C s s' → s = s') :
    (∑ s ∈ S, ∑ x ∈ R s, W x = ∑ x ∈ S.biUnion R, W x) ∧
      (∀ x, x ∈ S.biUnion R ↔ m x ∉ S.biUnion R) := by
  constructor
  · rw [Finset.sum_biUnion]
    intro s hs s' hs' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    exact hne (g2 s hs s' hs' (hCt _ _ _ ((h3 s hs x).2 (Or.inl hx))
      (hCs _ _ ((h3 s' hs' x).2 (Or.inl hx')))))
  · intro x
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨s, hs, hx⟩ ⟨s', hs', hx'⟩
      have h1 : C s (m x) := (h3 s hs _).2 (Or.inr (by rw [hm]; exact hx))
      have h1' : C s' (m x) := (h3 s' hs' _).2 (Or.inl hx')
      have := g2 s hs s' hs' (hCt _ _ _ h1 (hCs _ _ h1'))
      subst this
      exact h2 s hs x hx hx'
    · intro hn
      obtain ⟨s, hs, hc⟩ := g1 x
      rcases (h3 s hs x).1 hc with h | h
      · exact ⟨s, hs, h⟩
      · exact absurd ⟨s, hs, h⟩ hn
section Order2

instance instLawfulBEqSum' {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  rfl := by
    intro a
    rcases a with i | x
    · change (i == i) = true
      exact beq_self_eq_true i
    · change (x == x) = true
      exact beq_self_eq_true x
  eq_of_beq := by
    intro a b h
    rcases a with i | x <;> rcases b with j | y
    · change (i == j) = true at h
      rw [eq_of_beq h]
    · exact absurd h (by simp [BEq.beq, Sum.instBEq.beq])
    · exact absurd h (by simp [BEq.beq, Sum.instBEq.beq])
    · change (x == y) = true at h
      rw [eq_of_beq h]

theorem idxOf_map_inj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (g : α → β)
    (hg : Function.Injective g) (a : α) (l : List α) : (l.map g).idxOf (g a) = l.idxOf a := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases h : c = a
    · subst h; simp [List.idxOf_cons_self]
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun h' => h (hg h')), List.idxOf_cons_ne _ h, ih]

theorem lex_ex {V : Type*} [DecidableEq V] [BEq V] [LawfulBEq V] : ∀ (l : List V) (v w : V), v ∈ l →
    l.idxOf v < l.idxOf w → lexLT l (Pi.single w (1 : ℤ)) (Pi.single v 1) := by
  intro l
  induction l with
  | nil => intro v w hv; simp at hv
  | cons y l ih =>
    intro v w hv hlt
    by_cases hy : y = v
    · subst hy
      have hw : w ≠ y := by rintro rfl; omega
      left; simp [Pi.single_apply, hw]
    · have hyw : y ≠ w := by
        rintro rfl
        rw [List.idxOf_cons_self] at hlt; omega
      right
      refine ⟨by simp [Pi.single_apply, Ne.symm hy, Ne.symm hyw], ?_⟩
      rw [List.idxOf_cons_ne _ hy, List.idxOf_cons_ne _ hyw] at hlt
      exact ih v w (by simpa [Ne.symm hy] using hv) (by omega)

theorem lex_prefix {V : Type*} (A B : List V) (a c : V → ℤ) (hA : ∀ x ∈ A, a x = c x)
    (h : lexLT B a c) : lexLT (A ++ B) a c := by
  induction A with
  | nil => exact h
  | cons x A ih =>
    right
    exact ⟨hA x (by simp), ih (fun y hy => hA y (by simp [hy]))⟩

variable {L : DiskLayout k f r}

def VS (L : DiskLayout k f r) (side : DiskSide f r) : List (SignatureVariable k r) :=
  match side with
  | .inl j => (L.block j).map fun i => Sum.inr (Sum.inl i)
  | .inr (s, e) => [Sum.inr (Sum.inr (s, e))]

theorem restOrder_eq' : restOrder L = L.sideOrder.flatMap (VS L) := rfl

theorem mem_VS_iff {q : Fin r → ℕ} (side : DiskSide f r) (x : DiskEndpoint k r q) :
    var x ∈ VS L side ↔ x ∈ sideEndpoints L q side := by
  rcases side with j | ⟨s, e⟩ <;> rcases x with i | ⟨s', e', j'⟩
  · simp [var, VS, sideEndpoints]
  · simp [var, VS, sideEndpoints]
  · simp [var, VS, sideEndpoints]
  · constructor
    · intro h; simp [var, VS] at h; obtain ⟨rfl, rfl⟩ := h; simp [sideEndpoints]
    · intro h; simp only [sideEndpoints, List.mem_map, List.mem_finRange, true_and] at h
      obtain ⟨a, ha⟩ := h
      simp only [Sum.inr.injEq] at ha
      cases ha; simp [var, VS]

theorem within_side {q : Fin r → ℕ} (side : DiskSide f r) (a c : DiskEndpoint k r q)
    (ha : a ∈ sideEndpoints L q side) (hc : c ∈ sideEndpoints L q side)
    (hlt : (sideEndpoints L q side).idxOf a < (sideEndpoints L q side).idxOf c)
    (hne : var a ≠ var c) : (VS L side).idxOf (var a) < (VS L side).idxOf (var c) := by
  rcases side with j | ⟨s, e⟩
  · simp only [sideEndpoints, List.mem_map] at ha hc
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨i', _, rfl⟩ := hc
    simp only [sideEndpoints] at hlt
    rw [idxOf_map_inj _ Sum.inl_injective, idxOf_map_inj _ Sum.inl_injective] at hlt
    simp only [VS, var]
    rw [idxOf_map_inj (fun i => (Sum.inr (Sum.inl i) : SignatureVariable k r))
        (fun x y h => by simpa using h),
      idxOf_map_inj (fun i => (Sum.inr (Sum.inl i) : SignatureVariable k r))
        (fun x y h => by simpa using h)]
    exact hlt
  · exfalso; apply hne
    simp only [sideEndpoints, List.mem_map] at ha hc
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨i', _, rfl⟩ := hc
    rfl

theorem order_aux {q : Fin r → ℕ} : ∀ (l : List (DiskSide f r)) (a c : DiskEndpoint k r q),
    a ∈ l.flatMap (sideEndpoints L q) → c ∈ l.flatMap (sideEndpoints L q) →
    (l.flatMap (sideEndpoints L q)).idxOf a < (l.flatMap (sideEndpoints L q)).idxOf c →
    var a ≠ var c → (l.flatMap (VS L)).idxOf (var a) < (l.flatMap (VS L)).idxOf (var c) := by
  intro l
  induction l with
  | nil => intro a c ha; simp at ha
  | cons side l ih =>
    intro a c ha hc hlt hne
    simp only [List.flatMap_cons] at ha hc hlt ⊢
    by_cases has : a ∈ sideEndpoints L q side <;> by_cases hcs : c ∈ sideEndpoints L q side
    · rw [List.idxOf_append_of_mem has, List.idxOf_append_of_mem hcs] at hlt
      rw [List.idxOf_append_of_mem ((mem_VS_iff side a).2 has),
        List.idxOf_append_of_mem ((mem_VS_iff side c).2 hcs)]
      exact within_side side a c has hcs hlt hne
    · rw [List.idxOf_append_of_mem ((mem_VS_iff side a).2 has),
        List.idxOf_append_of_notMem (fun h => hcs ((mem_VS_iff side c).1 h))]
      have := List.idxOf_lt_length_iff.2 ((mem_VS_iff side a).2 has)
      omega
    · rw [List.idxOf_append_of_notMem has, List.idxOf_append_of_mem hcs] at hlt
      have := List.idxOf_lt_length_iff.2 hcs
      omega
    · rw [List.idxOf_append_of_notMem has, List.idxOf_append_of_notMem hcs] at hlt
      rw [List.idxOf_append_of_notMem (fun h => has ((mem_VS_iff side a).1 h)),
        List.idxOf_append_of_notMem (fun h => hcs ((mem_VS_iff side c).1 h))]
      have := ih a c (by simpa [has] using ha) (by simpa [hcs] using hc) (by omega) hne
      omega

theorem rank_var_lt {q : Fin r → ℕ} (a c : DiskEndpoint k r q) (hlt : L.rank a < L.rank c)
    (hne : var a ≠ var c) :
    LT k r (restOrder L) (ev c) (ev a) := by
  unfold DiskLayout.rank at hlt
  rw [endpoints_eq] at hlt
  have h := order_aux L.sideOrder a c (by rw [← endpoints_eq]; exact mem_endpoints L q a)
    (by rw [← endpoints_eq]; exact mem_endpoints L q c) hlt hne
  rw [← restOrder_eq'] at h
  obtain ⟨side, hs, hx⟩ := List.mem_flatMap.1 (show a ∈ L.sideOrder.flatMap (sideEndpoints L q) by
    rw [← endpoints_eq]; exact mem_endpoints L q a)
  have hmem : var a ∈ restOrder L := by
    rw [restOrder_eq', List.mem_flatMap]; exact ⟨side, hs, (mem_VS_iff side a).2 hx⟩
  unfold LT ev ex
  refine lex_prefix _ _ _ _ (fun x hx => ?_) (lex_ex _ _ _ hmem h)
  simp only [List.mem_map, List.mem_finRange, true_and] at hx
  obtain ⟨s, rfl⟩ := hx
  have h1 : ∀ y : DiskEndpoint k r q, (Sum.inl s : SignatureVariable k r) ≠ var y := by
    intro y; rcases y with i | ⟨s', e', j'⟩ <;> simp [var]
  simp [Pi.single_apply, h1]

end Order2
section Top
variable {L : DiskLayout k f r} (D : DiskState L b) (same : Fin r → Bool)

theorem opens_mate_iff (x : DiskEndpoint k r D.q) : D.Opens (D.mate x) ↔ ¬ D.Opens x := by
  unfold DiskState.Opens
  rw [mate_mate]
  have hne : L.rank x ≠ L.rank (D.mate x) := fun h => D.no_fixed x (rank_inj L D.q h).symm
  omega

theorem pl_eq (x : DiskEndpoint k r D.q) :
    pl D (restOrder L) x = ev (if D.Opens x then x else D.mate x) := by
  have hO : TOrd (LT k r (restOrder L)) := lexTOrd _ (variableOrder_complete L)
  have hvne : var x ≠ var (D.mate x) := fun h => ev_ne D x (by unfold ev; rw [h])
  unfold pl mx
  by_cases hx : D.Opens x
  · rw [if_pos hx]
    have h1 := rank_var_lt x (D.mate x) hx hvne
    rw [if_neg]; intro h2; exact hO.irrefl _ (hO.trans _ _ _ h1 h2)
  · rw [if_neg hx]
    have h0 := (opens_mate_iff D x).2 hx
    unfold DiskState.Opens at h0; rw [mate_mate] at h0
    rw [if_pos (rank_var_lt (D.mate x) x h0 (Ne.symm hvne))]

theorem sum_pl (Y : Finset (DiskEndpoint k r D.q)) (hY : ∀ x, x ∈ Y ↔ D.mate x ∉ Y) :
    ∑ x ∈ Y, pl D (restOrder L) x = ∑ z ∈ Finset.univ.filter (fun z => D.Opens z), ev z := by
  rw [Finset.sum_congr rfl (fun x _ => pl_eq D x)]
  apply Finset.sum_nbij' (fun x => if D.Opens x then x else D.mate x)
    (fun z => if z ∈ Y then z else D.mate z)
  · intro x _
    by_cases h : D.Opens x
    · simp [h]
    · simp [h, (opens_mate_iff D x).2 h]
  · intro z _
    by_cases h : z ∈ Y
    · simp [h]
    · simp only [h, if_false]; by_contra h'; exact h ((hY z).2 h')
  · intro x hx
    by_cases h : D.Opens x
    · simp [h, hx]
    · have : D.mate x ∉ Y := (hY x).1 hx
      simp [h, this, mate_mate]
  · intro z hz
    have hz' : D.Opens z := by simpa using hz
    by_cases h : z ∈ Y
    · simp [h, hz']
    · have : ¬ D.Opens (D.mate z) := fun h2 => ((opens_mate_iff D z).1 h2) hz'
      simp [h, this, mate_mate]
  · intro x _; rfl

theorem sum_lam (Y : Finset (DiskEndpoint k r D.q)) (hY : ∀ x, x ∈ Y ↔ D.mate x ∉ Y) :
    ∑ x ∈ Y, lam (D.mate x) = ∑ z ∈ Finset.univ.filter (fun z => z ∉ Y), lam z := by
  apply Finset.sum_nbij' (fun x => D.mate x) (fun z => D.mate z)
  · intro x hx; simpa using (hY x).1 hx
  · intro z hz
    have : z ∉ Y := by simpa using hz
    by_contra h'; exact this ((hY z).2 h')
  · intro x _; exact mate_mate D x
  · intro z _; exact mate_mate D z
  · intro x _; rfl

theorem invol_count {J : Type*} [Fintype J] (φ : J → J) (hφ : ∀ w, φ (φ w) = w)
    (P : J → Prop) [DecidablePred P] (hP : ∀ w, P w ↔ ¬ P (φ w)) :
    2 * (Finset.univ.filter (fun w => ¬ P w)).card = Fintype.card J := by
  have h1 : (Finset.univ.filter P).card = (Finset.univ.filter (fun w => ¬ P w)).card := by
    apply Finset.card_nbij' φ φ
    · intro w hw; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw ⊢
      exact (hP w).1 hw
    · intro w hw; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw ⊢
      rw [hP (φ w), hφ]; exact hw
    · intro w _; exact hφ w
    · intro w _; exact hφ w
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  rw [Finset.card_univ] at h2
  omega

def gidx (s : Fin r) (q : Fin r → ℕ) (w : Bool × Fin (q s)) : Bool × Fin (q s) :=
  (!w.1, if same s then w.2 else ⟨q s - 1 - w.2.val, by omega⟩)

theorem glue_inr {q : Fin r → ℕ} (s : Fin r) (w : Bool × Fin (q s)) :
    glueEndpoint same (Sum.inr ⟨s, w⟩ : DiskEndpoint k r q) = Sum.inr ⟨s, gidx same s q w⟩ := by
  rcases w with ⟨e, j⟩; rfl

theorem gidx_invol {q : Fin r → ℕ} (s : Fin r) (w : Bool × Fin (q s)) :
    gidx same s q (gidx same s q w) = w := by
  have := glue_invol (k := 0) (q := q) same (Sum.inr ⟨s, w⟩)
  rw [glue_inr (k := 0), glue_inr (k := 0)] at this
  simpa using this

theorem lam_seam (s : Fin r) (z : DiskEndpoint k r D.q) :
    lam z (Sum.inl s) = if (∃ w : Bool × Fin (D.q s), z = Sum.inr ⟨s, w⟩) then 1 else 0 := by
  rcases z with i | ⟨s', w⟩
  · simp [lam]
  · by_cases h : s' = s
    · subst h; simp [lam, ex]
    · have : ¬ ∃ w' : Bool × Fin (D.q s), (Sum.inr ⟨s', w⟩ : DiskEndpoint k r D.q) = Sum.inr ⟨s, w'⟩ := by
        rintro ⟨w', hw'⟩
        simp only [Sum.inr.injEq, Sigma.mk.injEq] at hw'
        exact h hw'.1
      rw [if_neg this]
      simp [lam, ex, Pi.single_apply, Ne.symm h]

theorem ev_term (i : Fin (2 * k)) (z : DiskEndpoint k r D.q) :
    ev z (Sum.inr (Sum.inl i)) = if z = Sum.inl i then 1 else 0 := by
  rcases z with i' | ⟨s', e', j'⟩
  · by_cases h : i' = i
    · subst h; simp [ev, ex, var]
    · simp [ev, ex, var, Pi.single_apply, Ne.symm h, h]
  · simp [ev, ex, var, Pi.single_apply]

theorem ev_side (s : Fin r) (e : Bool) (z : DiskEndpoint k r D.q) :
    ev z (Sum.inr (Sum.inr (s, e))) =
      if (∃ j : Fin (D.q s), z = Sum.inr ⟨s, (e, j)⟩) then 1 else 0 := by
  rcases z with i' | ⟨s', e', j'⟩
  · simp [ev, ex, var, Pi.single_apply]
  · by_cases h : s' = s ∧ e' = e
    · obtain ⟨rfl, rfl⟩ := h; simp [ev, ex, var]
    · have : ¬ ∃ j : Fin (D.q s),
          (Sum.inr ⟨s', (e', j')⟩ : DiskEndpoint k r D.q) = Sum.inr ⟨s, (e, j)⟩ := by
        rintro ⟨j, hj⟩
        simp only [Sum.inr.injEq] at hj
        cases hj; exact h ⟨rfl, rfl⟩
      rw [if_neg this]
      have h2 : (Sum.inr (Sum.inr (s, e)) : SignatureVariable k r) ≠ Sum.inr (Sum.inr (s', e')) := by
        intro h3; simp only [Sum.inr.injEq, Prod.mk.injEq] at h3; exact h ⟨h3.1.symm, h3.2.symm⟩
      simp [ev, ex, var, Pi.single_apply, h2]

theorem ev_seam0 (s : Fin r) (z : DiskEndpoint k r D.q) : ev z (Sum.inl s) = 0 := by
  rcases z with i' | ⟨s', e', j'⟩ <;> simp [ev, ex, var, Pi.single_apply]

theorem lam_inr0 (v : Fin (2 * k) ⊕ (Fin r × Bool)) (z : DiskEndpoint k r D.q) :
    lam z (Sum.inr v) = 0 := by
  rcases z with i' | ⟨s', e', j'⟩ <;> simp [lam, ex, Pi.single_apply]

theorem top_sum (Y : Finset (DiskEndpoint k r D.q)) (hY : ∀ x, x ∈ Y ↔ D.mate x ∉ Y)
    (hYg : ∀ x : DiskEndpoint k r D.q, x.isLeft = false → (x ∈ Y ↔ glueEndpoint same x ∉ Y)) :
    ∑ x ∈ Y, Wt D (restOrder L) x = D.topExponent := by
  classical
  unfold Wt
  rw [Finset.sum_add_distrib, sum_pl D Y hY, sum_lam D Y hY]
  funext v
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
  rcases v with s | i | ⟨s, e⟩
  · simp only [ev_seam0, Finset.sum_const_zero, zero_add, DiskState.topExponent]
    simp only [lam_seam D s]
    rw [Finset.sum_boole]
    have hc := invol_count (gidx same s D.q) (gidx_invol same s)
      (fun w => (Sum.inr ⟨s, w⟩ : DiskEndpoint k r D.q) ∈ Y)
      (fun w => by rw [hYg _ rfl, glue_inr])
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at hc
    have hcard : ((Finset.univ.filter (fun z => z ∉ Y)).filter
        (fun z => ∃ w : Bool × Fin (D.q s), z = Sum.inr ⟨s, w⟩)).card =
        (Finset.univ.filter (fun w : Bool × Fin (D.q s) =>
          ¬ (Sum.inr ⟨s, w⟩ : DiskEndpoint k r D.q) ∈ Y)).card := by
      symm
      apply Finset.card_bij (fun w _ => (Sum.inr ⟨s, w⟩ : DiskEndpoint k r D.q))
      · intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact ⟨hw, w, rfl⟩
      · intro w _ w' _ h; simpa using h
      · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨hz, w, rfl⟩ := hz
        exact ⟨w, by simpa using hz, rfl⟩
    rw [hcard]; push_cast; omega
  · simp only [lam_inr0, Finset.sum_const_zero, add_zero, DiskState.topExponent, ev_term D i]
    rw [Finset.sum_ite_eq']
    simp
  · simp only [lam_inr0, Finset.sum_const_zero, add_zero, DiskState.topExponent, ev_side D s e]
    rw [Finset.sum_boole, DiskState.sideOpenCount,
      len_filter_card (D.q s) (fun j => D.Opens (Sum.inr ⟨s, (e, j)⟩))]
    congr 1
    symm
    apply Finset.card_bij (fun j _ => (Sum.inr ⟨s, (e, j)⟩ : DiskEndpoint k r D.q))
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨hj, j, rfl⟩
    · intro j _ j' _ h; simpa using h
    · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨hz, j, rfl⟩ := hz
      exact ⟨j, by simpa using hz, rfl⟩

end Top
section Global
variable {L : DiskLayout k f r} (D : DiskState L b) (same : Fin r → Bool)

theorem exP (t : DiskEndpoint k r D.q) (ht : t.isLeft = true) :
    ∃ n, (D.mate ((tau D same ^ n) t)).isLeft = true := by
  refine ⟨orderOf (tau D same) - 1, ?_⟩
  have hpos := orderOf_pos (tau D same)
  rw [npow_eq_zpow, m_tau, ← tauinv_term D same t ht, ← zpow_add_apply]
  have : -(((orderOf (tau D same) - 1 : ℕ)) : ℤ) + -1 = -((orderOf (tau D same) : ℕ) : ℤ) := by
    omega
  rw [zc _ this, zpow_neg, zpow_natCast, pow_orderOf_eq_one, inv_one, Equiv.Perm.one_apply]
  exact ht

open Classical in
noncomputable def hP (t : DiskEndpoint k r D.q) : ℕ :=
  if hx : ∃ n, (D.mate ((tau D same ^ n) t)).isLeft = true then Nat.find hx else 0

theorem hP_spec (t : DiskEndpoint k r D.q) (ht : t.isLeft = true) :
    (∀ n < hP D same t, (D.mate ((tau D same ^ n) t)).isLeft = false) ∧
      (D.mate ((tau D same ^ hP D same t) t)).isLeft = true := by
  classical
  have hx := exP D same t ht
  unfold hP
  rw [dif_pos hx]
  refine ⟨fun n hn => ?_, Nat.find_spec hx⟩
  have := Nat.find_min hx hn
  simpa using this

theorem exC (p : DiskEndpoint k r D.q) : ∃ n, 0 < n ∧ (tau D same ^ n) p = p :=
  ⟨orderOf (tau D same), orderOf_pos _, by rw [pow_orderOf_eq_one]; rfl⟩

open Classical in
noncomputable def hC (p : DiskEndpoint k r D.q) : ℕ := Nat.find (exC D same p)

theorem hC_spec (p : DiskEndpoint k r D.q) :
    0 < hC D same p ∧ (tau D same ^ hC D same p) p = p ∧
      ∀ n, 0 < n → n < hC D same p → (tau D same ^ n) p ≠ p := by
  classical
  unfold hC
  refine ⟨(Nat.find_spec (exC D same p)).1, (Nat.find_spec (exC D same p)).2, ?_⟩
  intro n h0 hn heq
  exact Nat.find_min (exC D same p) hn ⟨h0, heq⟩

noncomputable def endT (i : Fin (2 * k)) : Fin (2 * k) :=
  (D.mate ((tau D same ^ hP D same (Sum.inl i)) (Sum.inl i))).elim id (fun _ => i)

theorem endT_spec (i : Fin (2 * k)) :
    D.mate ((tau D same ^ hP D same (Sum.inl i)) (Sum.inl i)) = Sum.inl (endT D same i) := by
  have := (hP_spec D same (Sum.inl i) rfl).2
  unfold endT
  rcases hm : D.mate ((tau D same ^ hP D same (Sum.inl i)) (Sum.inl i)) with j | z
  · rfl
  · rw [hm] at this; simp at this

theorem card_X : Fintype.card (DiskEndpoint k r D.q) = 2 * k + 2 * ∑ s, D.q s := by
  simp [Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, Finset.mul_sum]

theorem trace_path (i : Fin (2 * k)) :
    D.traceFrom same (Sum.inl i) =
      (csOf D same (hP D same (Sum.inl i)) (Sum.inl i), some (endT D same i)) := by
  obtain ⟨hmin, hh⟩ := hP_spec D same (Sum.inl i) rfl
  have hcard : (runSet D same (hP D same (Sum.inl i) + 1) (Sum.inl i)).card =
      hP D same (Sum.inl i) + 1 := by
    unfold runSet
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha c hc hac
    exact path_inj D same _ rfl _ hmin a c (by simp at ha; omega) (by simp at hc; omega) hac
  have hle := Finset.card_le_univ (runSet D same (hP D same (Sum.inl i) + 1) (Sum.inl i))
  rw [hcard, card_X] at hle
  unfold DiskState.traceFrom
  apply follow_path D same _ (endT D same i) _ _ _ (by omega) hmin (endT_spec D same i)
  intro n hn heq
  have := path_seam D same _ rfl _ hmin (n + 1) (by omega) (by omega)
  rw [heq] at this; simp at this

theorem mem_reps (p : DiskEndpoint k r D.q) :
    p ∈ D.cycleRepresentatives same ↔
      (∀ i, ¬ D.Connected same p (Sum.inl i)) ∧
        ∀ u, D.Connected same p u → L.rank p ≤ L.rank u := by
  unfold DiskState.cycleRepresentatives
  simp [List.mem_filter, mem_endpoints]

theorem reps_free (p : DiskEndpoint k r D.q) (hp : p ∈ D.cycleRepresentatives same) :
    ∀ x, D.Connected same p x → x.isLeft = false := by
  intro x hx
  rcases x with i | z
  · exact absurd hx (((mem_reps D same p).1 hp).1 i)
  · rfl

theorem trace_cyc (p : DiskEndpoint k r D.q) (hfree : ∀ x, D.Connected same p x → x.isLeft = false) :
    D.traceFrom same p = (csOf D same (hC D same p) p, none) := by
  obtain ⟨hpos, hper, hmin⟩ := hC_spec D same p
  have hcard : (runSet D same (hC D same p) p).card = hC D same p := by
    unfold runSet
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha c hc hac
    exact cyc_inj D same p _ hmin a c (by simpa using ha) (by simpa using hc) hac
  have hle := Finset.card_le_univ (runSet D same (hC D same p) p)
  rw [hcard, card_X] at hle
  unfold DiskState.traceFrom
  apply follow_cycle D same _ _ _ _ hpos (by omega) _ hper hmin
  intro n _
  exact hfree _ (conn_trans D same (conn_pow D same p n) (conn_mate D same _))

noncomputable def Sset : Finset (DiskEndpoint k r D.q) := by
  classical
  exact ((Finset.univ.filter (fun i : Fin (2 * k) => i < endT D same i)).image Sum.inl) ∪
    (D.cycleRepresentatives same).toFinset

noncomputable def Rf (s : DiskEndpoint k r D.q) : Finset (DiskEndpoint k r D.q) :=
  if s.isLeft = true then runSet D same (hP D same s + 1) s else runSet D same (hC D same s) s

theorem mem_Sset (s : DiskEndpoint k r D.q) :
    s ∈ Sset D same ↔ (∃ i, i < endT D same i ∧ Sum.inl i = s) ∨
      s ∈ D.cycleRepresentatives same := by
  classical
  unfold Sset
  simp

theorem endT_ne (i : Fin (2 * k)) : endT D same i ≠ i := by
  intro h
  obtain ⟨hmin, hh⟩ := hP_spec D same (Sum.inl i) rfl
  have := path_disj D same _ rfl _ hmin 0 (hP D same (Sum.inl i)) (by omega) le_rfl
  rw [endT_spec, h] at this
  exact this (by simp)

/-- the path from the other end returns. -/
theorem endT_endT (i : Fin (2 * k)) : endT D same (endT D same i) = i := by
  obtain ⟨hmin, hh⟩ := hP_spec D same (Sum.inl i) rfl
  set j := endT D same i with hj
  have hc : D.Connected same (Sum.inl j) (Sum.inl i) := by
    apply conn_symm
    have := conn_trans D same (conn_pow D same (Sum.inl i) (hP D same (Sum.inl i)))
      (conn_mate D same _)
    rwa [endT_spec] at this
  obtain ⟨hmin', hh'⟩ := hP_spec D same (Sum.inl j) rfl
  rcases path_term D same _ rfl _ hmin' hh' i hc with h | h
  · exfalso; apply endT_ne D same i
    simpa [hj] using h.symm
  · rw [endT_spec] at h
    simpa using h.symm

theorem Sset_facts (s : DiskEndpoint k r D.q) (hs : s ∈ Sset D same) :
    (∀ x ∈ Rf D same s, D.mate x ∉ Rf D same s) ∧
    (∀ x, D.Connected same s x ↔ x ∈ Rf D same s ∨ D.mate x ∈ Rf D same s) ∧
    (∀ x ∈ Rf D same s, x.isLeft = false → (tau D same ^ (-1 : ℤ)) x ∈ Rf D same s) ∧
    (∀ x ∈ Rf D same s, (D.mate x).isLeft = false → tau D same x ∈ Rf D same s) := by
  rcases (mem_Sset D same s).1 hs with ⟨i, _, rfl⟩ | hp
  · obtain ⟨hmin, hh⟩ := hP_spec D same (Sum.inl i) rfl
    have hR : Rf D same (Sum.inl i) = runSet D same (hP D same (Sum.inl i) + 1) (Sum.inl i) := by
      unfold Rf; simp
    rw [hR]
    refine ⟨?_, path_conn D same _ rfl _ hmin hh, path_inv D same _ rfl _ hmin,
      path_fwd D same _ rfl _ hmin hh⟩
    intro x hx hm
    obtain ⟨a, ha, rfl⟩ := (mem_runSet _ _ _ _ _).1 hx
    obtain ⟨c, hc, hc'⟩ := (mem_runSet _ _ _ _ _).1 hm
    exact path_disj D same _ rfl _ hmin c a (by omega) (by omega) hc'
  · have hfree := reps_free D same s hp
    have hsl : s.isLeft = false := hfree s Relation.ReflTransGen.refl
    obtain ⟨hpos, hper, hmin⟩ := hC_spec D same s
    have hR : Rf D same s = runSet D same (hC D same s) s := by
      unfold Rf; simp [hsl]
    rw [hR]
    refine ⟨cyc_disj D same s hfree _ hpos hper, cyc_conn D same s _ hpos hper, ?_, ?_⟩
    · intro x hx _
      obtain ⟨n, _, rfl⟩ := (mem_runSet _ _ _ _ _).1 hx
      rw [npow_eq_zpow, ← zpow_add_apply]
      exact cyc_mem D same s _ hpos hper _
    · intro x hx _
      obtain ⟨n, _, rfl⟩ := (mem_runSet _ _ _ _ _).1 hx
      rw [← pow_succ_apply'', npow_eq_zpow]
      exact cyc_mem D same s _ hpos hper _

theorem Sset_cover (x : DiskEndpoint k r D.q) : ∃ s ∈ Sset D same, D.Connected same s x := by
  classical
  by_cases hT : ∃ i, D.Connected same x (Sum.inl i)
  · obtain ⟨i, hi⟩ := hT
    have hix := conn_symm D same hi
    rcases lt_or_gt_of_ne (endT_ne D same i).symm with h | h
    · exact ⟨Sum.inl i, (mem_Sset D same _).2 (Or.inl ⟨i, h, rfl⟩), hix⟩
    · refine ⟨Sum.inl (endT D same i), (mem_Sset D same _).2 (Or.inl ⟨endT D same i,
        by rw [endT_endT]; exact h, rfl⟩), ?_⟩
      have hc : D.Connected same (Sum.inl i) (Sum.inl (endT D same i)) := by
        have := conn_trans D same (conn_pow D same (Sum.inl i) (hP D same (Sum.inl i)))
          (conn_mate D same _)
        rwa [endT_spec] at this
      exact conn_trans D same (conn_symm D same hc) hix
  · push Not at hT
    obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun u => D.Connected same x u)) (fun u => L.rank u)
      ⟨x, by simp; exact Relation.ReflTransGen.refl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hmin
    refine ⟨p, (mem_Sset D same _).2 (Or.inr ((mem_reps D same p).2 ⟨?_, ?_⟩)),
      conn_symm D same hp⟩
    · intro i hc; exact hT i (conn_trans D same hp hc)
    · intro u hu; exact hmin u (conn_trans D same hp hu)

theorem Sset_unique (s : DiskEndpoint k r D.q) (hs : s ∈ Sset D same)
    (s' : DiskEndpoint k r D.q) (hs' : s' ∈ Sset D same) (hc : D.Connected same s s') :
    s = s' := by
  rcases (mem_Sset D same s).1 hs with ⟨i, hi, rfl⟩ | hp <;>
    rcases (mem_Sset D same s').1 hs' with ⟨i', hi', rfl⟩ | hp'
  · obtain ⟨hmin, hh⟩ := hP_spec D same (Sum.inl i) rfl
    obtain ⟨hmin', hh'⟩ := hP_spec D same (Sum.inl i') rfl
    rcases path_term D same _ rfl _ hmin hh i' hc with h | h
    · exact h.symm
    rcases path_term D same _ rfl _ hmin' hh' i (conn_symm D same hc) with h' | h'
    · exact h'
    rw [endT_spec] at h h'
    simp only [Sum.inl.injEq] at h h'
    exfalso; rw [← h] at hi; rw [← h'] at hi'; exact absurd hi (not_lt.2 hi'.le)
  · exact absurd (conn_symm D same hc) (((mem_reps D same s').1 hp').1 i)
  · exact absurd hc (((mem_reps D same s).1 hp).1 i')
  · have h1 := ((mem_reps D same s).1 hp).2 s' hc
    have h2 := ((mem_reps D same s').1 hp').2 s (conn_symm D same hc)
    exact rank_inj L D.q (le_antisymm h1 h2)

end Global
section Assemble
variable {L : DiskLayout k f r} (D : DiskState L b) (same : Fin r → Bool)

theorem path_lead_run (i : Fin (2 * k)) :
    Lead (LT k r (restOrder L))
      (pathSignature i (endT D same i) (csOf D same (hP D same (Sum.inl i)) (Sum.inl i)))
      (∑ x ∈ runSet D same (hP D same (Sum.inl i) + 1) (Sum.inl i), Wt D (restOrder L) x) := by
  have hO : TOrd (LT k r (restOrder L)) := lexTOrd _ (variableOrder_complete L)
  obtain ⟨hmin, hh⟩ := hP_spec D same (Sum.inl i) rfl
  have huw : (ex (Sum.inr (Sum.inl (endT D same i))) : Ex k r) =
      ev (D.mate ((tau D same ^ hP D same (Sum.inl i)) (Sum.inl i))) := by
    rw [endT_spec]; rfl
  obtain ⟨h1, h2, h3⟩ := chain_exp D same (restOrder L) _ (hP D same (Sum.inl i)) (Sum.inl i)
    hmin huw
  have hl := path_lead (restOrder L) hO i (endT D same i) _ h2
    (by rw [h1]; exact ev_ne D (Sum.inl i))
  convert hl using 1
  rw [h3, h1, path_sum D same _ rfl _ hmin]
  unfold Wt
  set h := hP D same (Sum.inl i)
  have hlam0 : lam (D.mate ((tau D same ^ h) (Sum.inl i))) = 0 := by rw [endT_spec]; rfl
  have e1 := Finset.sum_range_succ' (fun n => pl D (restOrder L) ((tau D same ^ n) (Sum.inl i))) h
  have e2 := Finset.sum_range_succ (fun n => lam (D.mate ((tau D same ^ n) (Sum.inl i)))) h
  have e0 : pl D (restOrder L) (Sum.inl i) = mx (LT k r (restOrder L))
      (ex (Sum.inr (Sum.inl i))) (ev (D.mate (Sum.inl i))) := rfl
  simp only [pow_zero, Equiv.Perm.one_apply] at e1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, hlam0, ← e0]
  abel

theorem cyc_lead_run (p : DiskEndpoint k r D.q)
    (hfree : ∀ x, D.Connected same p x → x.isLeft = false) :
    Lead (LT k r (restOrder L)) (cycleSignature (csOf D same (hC D same p) p))
      (∑ x ∈ runSet D same (hC D same p) p, Wt D (restOrder L) x) := by
  have hO : TOrd (LT k r (restOrder L)) := lexTOrd _ (variableOrder_complete L)
  obtain ⟨hpos, hper, hmin⟩ := hC_spec D same p
  have hs : ∀ n < hC D same p, (D.mate ((tau D same ^ n) p)).isLeft = false := fun n _ =>
    hfree _ (conn_trans D same (conn_pow D same p n) (conn_mate D same _))
  have hsum := cyc_sum D same p (hC D same p) hmin (Wt D (restOrder L))
  rw [hsum]
  generalize hC D same p = h at hpos hper hmin hs
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have h0 := hs 0 (by omega)
  simp only [pow_zero, Equiv.Perm.one_apply] at h0
  rcases hm : D.mate p with i | ⟨s, e, jj⟩
  · rw [hm] at h0; simp at h0
  have huw : (ex (Sum.inr (Sum.inr (s, e))) : Ex k r) =
      ev (D.mate ((tau D same ^ (h' + 1)) p)) := by rw [hper, hm]; rfl
  obtain ⟨_, h2, h3⟩ := chain_exp D same (restOrder L) _ (h' + 1) p hs huw
  rw [csOf_succ D same h' p s e jj hm] at h2 h3 ⊢
  have hl := cycle_lead (restOrder L) hO (s, e) _ h2
  convert hl using 1
  rw [h3]
  unfold Wt
  have e3 : ∑ n ∈ Finset.range (h' + 1), pl D (restOrder L) ((tau D same ^ (n + 1)) p) =
      ∑ n ∈ Finset.range (h' + 1), pl D (restOrder L) ((tau D same ^ n) p) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun n => pl D (restOrder L) ((tau D same ^ n) p)),
      hper]
    simp only [pow_zero, Equiv.Perm.one_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e3]
  abel

end Assemble
section Final
variable {L : DiskLayout k f r} (D : DiskState L b) (same : Fin r → Bool)

theorem filterMap_ite {α β : Type*} (l : List α) (P : α → Prop) [DecidablePred P] (F : α → β) :
    l.filterMap (fun a => if P a then some (F a) else none) =
      (l.filter (fun a => decide (P a))).map F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : P a
    · simp [List.filterMap_cons, List.filter_cons, h, ih]
    · simp [List.filterMap_cons, List.filter_cons, h, ih]

theorem sum_filter_list {α E : Type*} [AddCommMonoid E] (l : List α) (P : α → Prop)
    [DecidablePred P] (g : α → E) :
    ((l.filter (fun a => decide (P a))).map g).sum = (l.map (fun a => if P a then g a else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : P a
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem words_paths :
    (D.words same).paths = ((List.finRange (2 * k)).filter (fun i => decide (i < endT D same i))).map
      (fun i => (i, endT D same i, csOf D same (hP D same (Sum.inl i)) (Sum.inl i))) := by
  rw [← filterMap_ite]
  unfold DiskState.words
  dsimp only
  apply List.filterMap_congr
  intro i _
  rw [trace_path]

theorem words_cycles :
    (D.words same).cycles = (D.cycleRepresentatives same).map
      (fun p => csOf D same (hC D same p) p) := by
  unfold DiskState.words
  dsimp only
  apply List.map_congr_left
  intro p hp
  rw [trace_cyc D same p (reps_free D same p hp)]

theorem reps_nodup : (D.cycleRepresentatives same).Nodup := by
  unfold DiskState.cycleRepresentatives
  exact (endpoints_nodup L D.q).filter _

end Final

/-- Lemma 5.3: the leading exponent of the signature of a state. -/
theorem signature_lead (L : DiskLayout k f r) (sameOrder : Fin r → Bool) (D : DiskState L b) :
    Lead (LT k r (restOrder L)) (D.signature sameOrder) D.topExponent := by
  classical
  set same := sameOrder
  have hO : TOrd (LT k r (restOrder L)) := lexTOrd _ (variableOrder_complete L)
  set A := (List.finRange (2 * k)).filter (fun i => decide (i < endT D same i)) with hA
  set reps := D.cycleRepresentatives same with hreps
  have hP1 := Lead.list_prod hO A
    (fun i => pathSignature i (endT D same i) (csOf D same (hP D same (Sum.inl i)) (Sum.inl i)))
    (fun i => ∑ x ∈ runSet D same (hP D same (Sum.inl i) + 1) (Sum.inl i), Wt D (restOrder L) x)
    (fun i _ => path_lead_run D same i)
  have hC1 := Lead.list_prod hO reps
    (fun p => cycleSignature (csOf D same (hC D same p) p))
    (fun p => ∑ x ∈ runSet D same (hC D same p) p, Wt D (restOrder L) x)
    (fun p hp => cyc_lead_run D same p (reps_free D same p hp))
  have hmul := Lead.mul hO hP1 hC1
  have hsig : D.signature same = (A.map (fun i => pathSignature i (endT D same i)
      (csOf D same (hP D same (Sum.inl i)) (Sum.inl i)))).prod *
      (reps.map (fun p => cycleSignature (csOf D same (hC D same p) p))).prod := by
    unfold DiskState.signature curveSignature
    rw [words_paths, words_cycles, List.map_map, List.map_map]
    rfl
  rw [hsig]
  convert hmul using 1
  -- the exponent
  set Y := (Sset D same).biUnion (Rf D same) with hY
  have hfacts := Sset_facts D same
  obtain ⟨hsum, hYm⟩ := accounting D.mate (mate_mate D) (D.Connected same)
    (fun x y h => conn_symm D same h) (fun x y z h1 h2 => conn_trans D same h1 h2)
    (Sset D same) (Rf D same) (Wt D (restOrder L))
    (fun s hs => (hfacts s hs).1) (fun s hs => (hfacts s hs).2.1)
    (Sset_cover D same) (Sset_unique D same)
  have hYg : ∀ x : DiskEndpoint k r D.q, x.isLeft = false → (x ∈ Y ↔ glueEndpoint same x ∉ Y) := by
    intro x hx
    constructor
    · intro hxY
      obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.1 hxY
      have h1 := (hfacts s hs).2.2.1 x hxs hx
      rw [(hYm _), g_eq_m_tauinv, mate_mate, not_not]
      exact Finset.mem_biUnion.2 ⟨s, hs, h1⟩
    · intro hg
      by_contra hxY
      have hm : D.mate x ∈ Y := by
        by_contra h'; exact hxY ((hYm x).2 h')
      obtain ⟨s, hs, hms⟩ := Finset.mem_biUnion.1 hm
      have h1 := (hfacts s hs).2.2.2 (D.mate x) hms (by rw [mate_mate]; exact hx)
      rw [← glue_eq_tau_mate] at h1
      exact hg (Finset.mem_biUnion.2 ⟨s, hs, h1⟩)
  rw [← top_sum D same Y hYm hYg, ← hsum]
  -- split the sum over starts
  have hdisj : Disjoint ((Finset.univ.filter (fun i : Fin (2 * k) => i < endT D same i)).image
      Sum.inl) reps.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
    have := reps_free D same _ (List.mem_toFinset.1 hx') _ Relation.ReflTransGen.refl
    simp at this
  have hS : Sset D same = ((Finset.univ.filter (fun i : Fin (2 * k) => i < endT D same i)).image
      Sum.inl) ∪ reps.toFinset := by
    unfold Sset; rfl
  have hpaths : ∑ x ∈ (Finset.univ.filter (fun i : Fin (2 * k) => i < endT D same i)).image
      Sum.inl, ∑ y ∈ Rf D same x, Wt D (restOrder L) y =
      (A.map (fun i => ∑ x ∈ runSet D same (hP D same (Sum.inl i) + 1) (Sum.inl i),
        Wt D (restOrder L) x)).sum := by
    rw [Finset.sum_image (fun a _ b _ h => Sum.inl_injective h), Finset.sum_filter,
      Fin.sum_univ_def, hA, sum_filter_list]
    congr 1
  have hcyc : ∑ x ∈ reps.toFinset, ∑ y ∈ Rf D same x, Wt D (restOrder L) y =
      (reps.map (fun p => ∑ x ∈ runSet D same (hC D same p) p, Wt D (restOrder L) x)).sum := by
    rw [List.sum_toFinset _ (reps_nodup D same)]
    congr 1
    apply List.map_congr_left
    intro p hp
    have hpl : p.isLeft = false := reps_free D same p hp p Relation.ReflTransGen.refl
    unfold Rf
    simp [hpl]
  rw [hS, Finset.sum_union hdisj, hpaths, hcyc]

/-- Lemma 5.2: a state is determined by its top exponent. -/
theorem topExponent_injective (L : DiskLayout k f r) :
    Function.Injective (fun D : DiskState L b => D.topExponent) :=
  topExponent_injective' L

theorem independence (L : DiskLayout k f r) (sameOrder : Fin r → Bool) :
    LinearIndependent (ZMod 2) (fun D : DiskState L b => D.signature sameOrder) :=
  linIndep_of_leads (lexTOrd _ (variableOrder_complete L)) _ _
    (signature_lead L sameOrder) (topExponent_injective L)

end Assembly
end SPDAux

theorem solution {k f r b : ℕ} (L : ShortestPlanarDisjoint.Main.DiskLayout k f r) (hb : 1 ≤ b)
    (sameOrder : Fin r → Bool) :
    LinearIndependent (ZMod 2) (fun D : ShortestPlanarDisjoint.Main.DiskState L b =>
      D.signature sameOrder) :=
  SPDAux.independence L sameOrder
