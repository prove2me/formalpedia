-- Prove2me | solution 1 for StrongConv.cNorm_iteratedDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:02:32.532511+00:00
-- url     : https://prove2.me/submissions/dbfe8251-434c-459f-8f7a-42a74e0ba27e

import Definitions.Def_StrongConv
import Mathlib

section
section
section
open Polynomial
namespace StrongConv.VM
/-!
# V. Markov's inequality: Blueprint

Shadrin, *Twelve proofs of the Markov inequality*, §5.3 (Theorem 5.15 with q = T_n, Lemma 5.17).
Assembled from the Blueprint and its Parts.
-/
/-- `ω_t = ∏_{s ∈ S, s ≠ t} (X - s)`. -/
noncomputable def delProd (S : Finset ℝ) (t : ℝ) : ℝ[X] := ∏ s ∈ S.erase t, (X - C s)

/-- The Chebyshev extremal nodes `cos(iπ/n)`, `i = 0, …, n`. -/
noncomputable def chebNodes (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 1)).image (Polynomial.Chebyshev.node n)

/-- Shadrin's majorant `r_k = (1/k)(x² - 1) T_n^{(k+1)} + x T_n^{(k)}`. -/
noncomputable def rPoly (n k : ℕ) : ℝ[X] :=
  C (1 / (k : ℝ)) * (X ^ 2 - 1) * derivative^[k + 1] (Chebyshev.T ℝ n) +
    X * derivative^[k] (Chebyshev.T ℝ n)

/-- Left ends of the Chebyshev intervals: `a, η₀, …, η_{m-1}`. -/
noncomputable def chebLo {m : ℕ} (a : ℝ) (η : Fin m → ℝ) (j : Fin (m + 1)) : ℝ :=
  if h : j.val = 0 then a else η ⟨j.val - 1, by omega⟩

/-- Right ends of the Chebyshev intervals: `ξ₀, …, ξ_{m-1}, b`. -/
noncomputable def chebHi {m : ℕ} (b : ℝ) (ξ : Fin m → ℝ) (j : Fin (m + 1)) : ℝ :=
  if h : j.val < m then ξ ⟨j.val, h⟩ else b

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartI
open StrongConv.VM
open Finset
/-- strictly increasing on `[0, d)` -/
def SM (d : ℕ) (r : ℕ → ℝ) : Prop := ∀ i j, i < j → j < d → r i < r j

def HR (f : ℝ[X]) (d : ℕ) (r : ℕ → ℝ) : Prop :=
  SM d r ∧ ∃ c : ℝ, 0 < c ∧ f = C c * ∏ i ∈ range d, (X - C (r i))

noncomputable def L (d : ℕ) (r : ℕ → ℝ) (x : ℝ) : ℝ := ∑ i ∈ range d, (x - r i)⁻¹

lemma SM.le {d : ℕ} {r : ℕ → ℝ} (h : SM d r) {i j : ℕ} (hij : i ≤ j) (hj : j < d) :
    r i ≤ r j := by
  rcases hij.lt_or_eq with h1 | h1
  · exact (h i j h1 hj).le
  · rw [h1]

lemma term_le (p q x : ℝ) (hpq : p ≤ q) (h : q < x ∨ x < p) : (x - p)⁻¹ ≤ (x - q)⁻¹ := by
  rcases h with h | h
  · exact (inv_le_inv₀ (by linarith) (by linarith)).2 (by linarith)
  · exact (inv_le_inv_of_neg (by linarith) (by linarith)).2 (by linarith)

lemma term_lt (p q x : ℝ) (hpq : p < q) (h : q < x ∨ x < p) : (x - p)⁻¹ < (x - q)⁻¹ := by
  rcases h with h | h
  · exact (inv_lt_inv₀ (by linarith) (by linarith)).2 (by linarith)
  · exact (inv_lt_inv_of_neg (by linarith) (by linarith)).2 (by linarith)

lemma sum_cmp (d : ℕ) (p q : ℕ → ℝ) (x : ℝ)
    (h : ∀ i < d, p i ≤ q i ∧ (q i < x ∨ x < p i)) :
    ∑ i ∈ range d, (x - p i)⁻¹ ≤ ∑ i ∈ range d, (x - q i)⁻¹ := by
  apply Finset.sum_le_sum
  intro i hi
  rw [mem_range] at hi
  exact term_le _ _ _ (h i hi).1 (h i hi).2

lemma sum_cmp_lt (d : ℕ) (p q : ℕ → ℝ) (x : ℝ)
    (h : ∀ i < d, p i ≤ q i ∧ (q i < x ∨ x < p i)) (hex : ∃ i < d, p i < q i) :
    ∑ i ∈ range d, (x - p i)⁻¹ < ∑ i ∈ range d, (x - q i)⁻¹ := by
  obtain ⟨i0, hi0, hlt⟩ := hex
  apply Finset.sum_lt_sum
  · intro i hi
    rw [mem_range] at hi
    exact term_le _ _ _ (h i hi).1 (h i hi).2
  · exact ⟨i0, mem_range.2 hi0, term_lt _ _ _ hlt (h i0 hi0).2⟩

/-- `L` is strictly decreasing on each gap. -/
lemma L_anti {e : ℕ} {r : ℕ → ℝ} (hr : SM (e + 1) r) {l : ℕ} (hl : l < e) {x y : ℝ}
    (hx : r l < x) (hxy : x < y) (hy : y < r (l + 1)) : L (e + 1) r y < L (e + 1) r x := by
  unfold L
  apply Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩
  intro i hi
  rw [mem_range] at hi
  rcases le_or_gt i l with h | h
  · have := hr.le h (by omega)
    exact (inv_lt_inv₀ (by linarith) (by linarith)).2 (by linarith)
  · have := hr.le (show l + 1 ≤ i by omega) hi
    exact (inv_lt_inv_of_neg (by linarith) (by linarith)).2 (by linarith)

lemma L_pos {e : ℕ} {r : ℕ → ℝ} (hr : SM (e + 1) r) {l : ℕ} (hl : l < e) {x z : ℝ}
    (hz : z < r (l + 1)) (h0 : L (e + 1) r z = 0)
    (hx : r l < x) (hxz : x < z) : 0 < L (e + 1) r x := by
  have := L_anti hr hl hx hxz hz
  linarith

lemma L_nonneg {e : ℕ} {r : ℕ → ℝ} (hr : SM (e + 1) r) {l : ℕ} (hl : l < e) {x z : ℝ}
    (hz : z < r (l + 1)) (h0 : L (e + 1) r z = 0)
    (hx : r l < x) (hxz : x ≤ z) : 0 ≤ L (e + 1) r x := by
  rcases hxz.lt_or_eq with h | h
  · exact (L_pos hr hl hz h0 hx h).le
  · rw [h, h0]

/-- Gap data: `ρ i ∈ (r i, r (i+1))` and `L r (ρ i) = 0`. -/
def Gap (e : ℕ) (r ρ : ℕ → ℝ) : Prop :=
  ∀ i < e, r i < ρ i ∧ ρ i < r (i + 1) ∧ L (e + 1) r (ρ i) = 0

lemma mono_le {e : ℕ} {r r' ρ ρ' : ℕ → ℝ} (hr : SM (e + 1) r) (hr' : SM (e + 1) r')
    (hg : Gap e r ρ) (hg' : Gap e r' ρ') (hle : ∀ i < e + 1, r i ≤ r' i) :
    ∀ l < e, ρ l ≤ ρ' l := by
  intro l hl
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨h1, h2, h3⟩ := hg l hl
  obtain ⟨h1', h2', h3'⟩ := hg' l hl
  have hpos : 0 < L (e + 1) r (ρ' l) :=
    L_pos hr hl h2 h3 (by linarith [hle l (by omega)]) hcon
  have hc : L (e + 1) r (ρ' l) ≤ L (e + 1) r' (ρ' l) := by
    unfold L
    apply sum_cmp
    intro i hi
    refine ⟨hle i hi, ?_⟩
    rcases le_or_gt i l with h | h
    · left; have := hr'.le h (by omega); linarith
    · right; have := hr.le (show l + 1 ≤ i by omega) hi; linarith
  linarith

lemma mono_lt {e : ℕ} {r r' ρ ρ' : ℕ → ℝ} (hr : SM (e + 1) r) (hr' : SM (e + 1) r')
    (hg : Gap e r ρ) (hg' : Gap e r' ρ') (hle : ∀ i < e + 1, r i ≤ r' i)
    (hex : ∃ i < e + 1, r i < r' i) :
    ∀ l < e, ρ l < ρ' l := by
  intro l hl
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨h1, h2, h3⟩ := hg l hl
  obtain ⟨h1', h2', h3'⟩ := hg' l hl
  have hpos : 0 ≤ L (e + 1) r (ρ' l) :=
    L_nonneg hr hl h2 h3 (by linarith [hle l (by omega)]) hcon
  have hc : L (e + 1) r (ρ' l) < L (e + 1) r' (ρ' l) := by
    unfold L
    apply sum_cmp_lt _ _ _ _ _ hex
    intro i hi
    refine ⟨hle i hi, ?_⟩
    rcases le_or_gt i l with h | h
    · left; have := hr'.le h (by omega); linarith
    · right; have := hr.le (show l + 1 ≤ i by omega) hi; linarith
  linarith

lemma interl {e : ℕ} {r r' ρ ρ' : ℕ → ℝ} (hr : SM (e + 1) r) (hr' : SM (e + 1) r')
    (hg : Gap e r ρ) (hg' : Gap e r' ρ') (hsh : ∀ i, i + 1 < e + 1 → r' i ≤ r (i + 1)) :
    ∀ j, j + 1 < e → ρ' j < ρ (j + 1) := by
  intro j hj
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨h1, h2, h3⟩ := hg (j + 1) hj
  obtain ⟨h1', h2', h3'⟩ := hg' j (by omega)
  have hnn : 0 ≤ L (e + 1) r' (ρ (j + 1)) :=
    L_nonneg hr' (by omega) h2' h3' (by linarith [hsh j (by omega)]) hcon
  have hc : ∑ i ∈ range e, (ρ (j + 1) - r' i)⁻¹ ≤ ∑ i ∈ range e, (ρ (j + 1) - r (i + 1))⁻¹ := by
    apply sum_cmp
    intro i hi
    refine ⟨hsh i (by omega), ?_⟩
    rcases le_or_gt i j with h | h
    · left; have := hr.le (show i + 1 ≤ j + 1 by omega) (by omega); linarith
    · right; have := hr'.le (show j + 1 ≤ i by omega) (by omega); linarith
  have hneg : (ρ (j + 1) - r' e)⁻¹ < 0 := by
    have := hr'.le (show j + 1 ≤ e by omega) (by omega)
    exact inv_lt_zero.2 (by linarith)
  have hp : 0 < (ρ (j + 1) - r 0)⁻¹ := by
    have := hr.le (show 0 ≤ j + 1 by omega) (by omega)
    exact inv_pos.2 (by linarith)
  have e1 : L (e + 1) r' (ρ (j + 1)) =
      ∑ i ∈ range e, (ρ (j + 1) - r' i)⁻¹ + (ρ (j + 1) - r' e)⁻¹ := by
    unfold L; rw [sum_range_succ]
  have e2 : L (e + 1) r (ρ (j + 1)) =
      ∑ i ∈ range e, (ρ (j + 1) - r (i + 1))⁻¹ + (ρ (j + 1) - r 0)⁻¹ := by
    unfold L; rw [sum_range_succ']
  linarith

/-! ## One derivative step -/
lemma eval_prod_ne {d : ℕ} {r : ℕ → ℝ} {x : ℝ} (hx : ∀ i < d, x ≠ r i) :
    (∏ i ∈ range d, (X - C (r i))).eval x ≠ 0 := by
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.2
  intro i hi
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.2 (hx i (mem_range.1 hi))

lemma deriv_eval_prod (d : ℕ) (r : ℕ → ℝ) (x : ℝ) (hx : ∀ i < d, x ≠ r i) :
    (derivative (∏ i ∈ range d, (X - C (r i)))).eval x =
      (∏ i ∈ range d, (X - C (r i))).eval x * L d r x := by
  induction d with
  | zero => simp [L]
  | succ d ih =>
    have ih' := ih (fun i hi => hx i (by omega))
    have hd : x - r d ≠ 0 := sub_ne_zero.2 (hx d (by omega))
    rw [prod_range_succ, derivative_mul]
    simp only [eval_add, eval_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
      eval_sub, eval_X, eval_C, mul_one]
    rw [ih']
    unfold L
    rw [sum_range_succ]
    field_simp

lemma monic_prod (d : ℕ) (r : ℕ → ℝ) : (∏ i ∈ range d, (X - C (r i))).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))

lemma natDegree_prod (d : ℕ) (r : ℕ → ℝ) : (∏ i ∈ range d, (X - C (r i))).natDegree = d := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))]
  simp

lemma step {f : ℝ[X]} {e : ℕ} {r : ℕ → ℝ} (h : HR f (e + 1) r) :
    ∃ ρ : ℕ → ℝ, HR (derivative f) e ρ ∧ Gap e r ρ := by
  obtain ⟨hsm, c, hc, rfl⟩ := h
  set P := ∏ i ∈ range (e + 1), (X - C (r i)) with hP
  have hroot : ∀ i < e + 1, (C c * P).eval (r i) = 0 := by
    intro i hi
    rw [eval_mul, hP, eval_prod, Finset.prod_eq_zero (mem_range.2 hi)]
    · simp
    · simp
  have hR : ∀ i, ∃ y, i < e → r i < y ∧ y < r (i + 1) ∧ (derivative (C c * P)).eval y = 0 := by
    intro i
    by_cases hi : i < e
    · obtain ⟨y, hy, hd⟩ := exists_deriv_eq_zero (f := fun x => (C c * P).eval x)
        (hsm i (i + 1) (by omega) (by omega)) (C c * P).continuous.continuousOn
        (by rw [hroot i (by omega), hroot (i + 1) (by omega)])
      rw [Polynomial.deriv] at hd
      exact ⟨y, fun _ => ⟨hy.1, hy.2, hd⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose ρ hρ using hR
  have hne : ∀ l < e, ∀ i < e + 1, ρ l ≠ r i := by
    intro l hl i hi
    obtain ⟨h1, h2, -⟩ := hρ l hl
    rcases le_or_gt i l with h | h
    · have := hsm.le h (by omega); intro h'; linarith
    · have := hsm.le (show l + 1 ≤ i by omega) hi; intro h'; linarith
  have hgap : Gap e r ρ := by
    intro l hl
    obtain ⟨h1, h2, h3⟩ := hρ l hl
    refine ⟨h1, h2, ?_⟩
    rw [derivative_C_mul, eval_mul, deriv_eval_prod _ _ _ (hne l hl), eval_C] at h3
    have := eval_prod_ne (hne l hl)
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hc.ne'
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h this
      · exact h
  have hsmρ : SM e ρ := by
    intro i j hij hj
    have := hsm.le (show i + 1 ≤ j by omega) (by omega)
    linarith [(hρ i (by omega)).2.1, (hρ j hj).1]
  refine ⟨ρ, ⟨hsmρ, c * (e + 1), by positivity, ?_⟩, hgap⟩
  set Q := ∏ i ∈ range e, (X - C (ρ i)) with hQ
  have hPd := natDegree_prod (e + 1) r
  have hQd := natDegree_prod e ρ
  have hPm := monic_prod (e + 1) r
  have hQm := monic_prod e ρ
  rw [← hP] at hPd hPm
  rw [← hQ] at hQd hQm
  apply eq_of_degree_sub_lt_of_eval_index_eq (range e) (v := ρ)
  · intro i hi j hj hij
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact (hsmρ i j h (mem_range.1 hj)).ne hij
    · exact (hsmρ j i h (mem_range.1 hi)).ne hij.symm
  · rw [card_range, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_sub, coeff_derivative, coeff_C_mul, coeff_C_mul]
    rcases hm.lt_or_eq with hm | hm
    · rw [coeff_eq_zero_of_natDegree_lt (p := P) (by omega),
        coeff_eq_zero_of_natDegree_lt (p := Q) (by omega)]
      ring
    · subst hm
      have h1 : P.coeff (e + 1) = 1 := by
        have := hPm.coeff_natDegree; rwa [hPd] at this
      have h2 : Q.coeff e = 1 := by
        have := hQm.coeff_natDegree; rwa [hQd] at this
      rw [h1, h2]
      ring
  · intro i hi
    rw [(hρ i (mem_range.1 hi)).2.2, eval_mul, hQ, eval_prod,
      Finset.prod_eq_zero hi (by simp)]
    ring

/-! ## The interlacing invariant after one derivative -/
lemma stepAll {fA fB : ℝ[X]} {e : ℕ} {A B : ℕ → ℝ} {a b : ℝ}
    (hA : HR fA (e + 1) A) (hB : HR fB (e + 1) B)
    (hAB : ∀ i < e + 1, A i ≤ B i) (hex : ∃ i < e + 1, A i < B i)
    (hBA : ∀ i, i + 1 < e + 1 → B i ≤ A (i + 1))
    (hbd : ∀ i < e + 1, a ≤ A i ∧ B i ≤ b) :
    ∃ A' B' : ℕ → ℝ, HR (derivative fA) e A' ∧ HR (derivative fB) e B' ∧
      (∀ i < e, A' i < B' i) ∧ (∀ i, i + 1 < e → B' i < A' (i + 1)) ∧
      (∀ i < e, a < A' i ∧ B' i < b) ∧
      ∀ (fT : ℝ[X]) (T : ℕ → ℝ), HR fT (e + 1) T → (∀ i < e + 1, A i ≤ T i ∧ T i ≤ B i) →
        ∃ T', HR (derivative fT) e T' ∧ ∀ i < e, A' i ≤ T' i ∧ T' i ≤ B' i := by
  obtain ⟨A', hA', gA⟩ := step hA
  obtain ⟨B', hB', gB⟩ := step hB
  refine ⟨A', B', hA', hB', mono_lt hA.1 hB.1 gA gB hAB hex,
    interl hA.1 hB.1 gA gB hBA, ?_, ?_⟩
  · intro i hi
    exact ⟨by linarith [(gA i hi).1, (hbd i (by omega)).1],
      by linarith [(gB i hi).2.1, (hbd (i + 1) (by omega)).2]⟩
  · intro fT T hT hATB
    obtain ⟨T', hT', gT⟩ := step hT
    exact ⟨T', hT', fun i hi =>
      ⟨mono_le hA.1 hT.1 gA gT (fun j hj => (hATB j hj).1) i hi,
       mono_le hT.1 hB.1 gT gB (fun j hj => (hATB j hj).2) i hi⟩⟩

/-! ## Sign of the `k`-th derivative on the Chebyshev intervals -/
lemma sign_claim {f : ℝ[X]} {m : ℕ} {A B T : ℕ → ℝ} (hT : HR f m T)
    (hATB : ∀ i < m, A i ≤ T i ∧ T i ≤ B i) (j : ℕ) (hj : j ≤ m) (x : ℝ)
    (hlo : ∀ i, i < j → B i ≤ x) (hhi : ∀ i, j ≤ i → i < m → x ≤ A i) :
    0 ≤ (-1 : ℝ) ^ (m - j) * f.eval x := by
  obtain ⟨-, c, hc, rfl⟩ := hT
  obtain ⟨p, rfl⟩ : ∃ p, m = j + p := ⟨m - j, by omega⟩
  rw [Nat.add_sub_cancel_left, eval_mul, eval_C, eval_prod, prod_range_add]
  have h1 : 0 ≤ ∏ i ∈ range j, eval x (X - C (T i)) := by
    apply prod_nonneg
    intro i hi
    rw [mem_range] at hi
    simp only [eval_sub, eval_X, eval_C]
    linarith [hlo i hi, (hATB i (by omega)).2]
  have h2 : 0 ≤ ∏ i ∈ range p, ((-1 : ℝ) * eval x (X - C (T (j + i)))) := by
    apply prod_nonneg
    intro i hi
    rw [mem_range] at hi
    simp only [eval_sub, eval_X, eval_C]
    linarith [hhi (j + i) (by omega) (by omega), (hATB (j + i) (by omega)).1]
  rw [prod_mul_distrib, prod_const, card_range] at h2
  have := mul_nonneg hc.le (mul_nonneg h1 h2)
  linarith [show (-1 : ℝ) ^ p * (c * ((∏ i ∈ range j, eval x (X - C (T i))) *
      ∏ i ∈ range p, eval x (X - C (T (j + i))))) =
      c * ((∏ i ∈ range j, eval x (X - C (T i))) *
      ((-1) ^ p * ∏ i ∈ range p, eval x (X - C (T (j + i))))) by ring]

/-! ## The initial configuration -/
/-- extend a `Fin n`-tuple by zero -/
noncomputable def ext {n : ℕ} (F : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then F ⟨i, h⟩ else 0

lemma ext_lt {n : ℕ} (F : Fin n → ℝ) {i : ℕ} (h : i < n) : ext F i = F ⟨i, h⟩ := by
  simp [ext, h]

lemma delProd_eq (S : Finset ℝ) (n : ℕ) (hS : S.card = n + 1) (q : Fin (n + 1)) :
    delProd S (S.orderEmbOfFin hS q) =
      ∏ i ∈ range n, (X - C (ext (fun i => S.orderEmbOfFin hS (q.succAbove i)) i)) := by
  set s := S.orderEmbOfFin hS
  have hS' : univ.map s.toEmbedding = S := map_orderEmbOfFin_univ S hS
  have hmem : s q ∈ S := orderEmbOfFin_mem S hS q
  have key : ∏ x ∈ S, (X - C x) = ∏ j : Fin (n + 1), (X - C (s j)) := by
    rw [← hS', prod_map]; rfl
  rw [Fin.prod_univ_succAbove _ q, ← mul_prod_erase S _ hmem] at key
  have key2 := mul_left_cancel₀ (X_sub_C_ne_zero (s q)) key
  unfold delProd
  rw [key2, prod_range]
  apply prod_congr rfl
  intro i _
  rw [ext_lt _ i.2]

lemma HR_init (S : Finset ℝ) (n : ℕ) (hS : S.card = n + 1) (q : Fin (n + 1)) :
    HR (delProd S (S.orderEmbOfFin hS q)) n
      (ext (fun i => S.orderEmbOfFin hS (q.succAbove i))) := by
  refine ⟨?_, 1, one_pos, by rw [delProd_eq S n hS q, C_1, one_mul]⟩
  intro i j hij hj
  rw [ext_lt _ (by omega), ext_lt _ hj]
  simp only [OrderEmbedding.lt_iff_lt, Fin.succAbove_lt_succAbove_iff, Fin.mk_lt_mk]
  exact hij

lemma succAbove_bounds {n : ℕ} (q : Fin (n + 1)) (i : Fin n) :
    i.castSucc ≤ q.succAbove i ∧ q.succAbove i ≤ i.succ := by
  rcases lt_or_ge i.castSucc q with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    exact ⟨le_rfl, Fin.castSucc_lt_succ.le⟩
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    exact ⟨Fin.castSucc_lt_succ.le, le_rfl⟩

/-! ## Iteration -/
/-- The invariant after `j ≥ 1` derivatives. -/
def Inv (S : Finset ℝ) (a b : ℝ) (n j : ℕ) : Prop :=
  ∃ A B : ℕ → ℝ, HR (derivative^[j] (delProd S b)) (n - j) A ∧
    HR (derivative^[j] (delProd S a)) (n - j) B ∧
    (∀ i < n - j, A i < B i) ∧ (∀ i, i + 1 < n - j → B i < A (i + 1)) ∧
    (∀ i < n - j, a < A i ∧ B i < b) ∧
    ∀ t ∈ S, ∃ T, HR (derivative^[j] (delProd S t)) (n - j) T ∧
      ∀ i < n - j, A i ≤ T i ∧ T i ≤ B i

lemma inv_one {S : Finset ℝ} {a b : ℝ} {n : ℕ} (hn : 1 ≤ n) {A0 B0 : ℕ → ℝ}
    (hA : HR (delProd S b) n A0) (hB : HR (delProd S a) n B0)
    (hAB : ∀ i < n, A0 i ≤ B0 i) (hex : ∃ i < n, A0 i < B0 i)
    (hBA : ∀ i, i + 1 < n → B0 i ≤ A0 (i + 1))
    (hbd : ∀ i < n, a ≤ A0 i ∧ B0 i ≤ b)
    (hT : ∀ t ∈ S, ∃ T, HR (delProd S t) n T ∧ ∀ i < n, A0 i ≤ T i ∧ T i ≤ B0 i) :
    Inv S a b n 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  obtain ⟨A', B', hA', hB', g1, g2, g3, gT⟩ := stepAll hA hB hAB hex hBA hbd
  simp only [Inv, Function.iterate_one, Nat.add_sub_cancel]
  refine ⟨A', B', hA', hB', g1, g2, g3, ?_⟩
  intro t ht
  obtain ⟨T, hT1, hT2⟩ := hT t ht
  exact gT _ T hT1 hT2

lemma inv_succ {S : Finset ℝ} {a b : ℝ} {n j : ℕ} (hj : j + 1 ≤ n) (h : Inv S a b n j) :
    Inv S a b n (j + 1) := by
  obtain ⟨A, B, hA, hB, h1, h2, h3, hT⟩ := h
  obtain ⟨e, he⟩ : ∃ e, n - j = e + 1 := ⟨n - j - 1, by omega⟩
  have he' : n - (j + 1) = e := by omega
  unfold Inv
  rw [he']
  rw [he] at hA hB h1 h2 h3 hT
  obtain ⟨A', B', hA', hB', g1, g2, g3, gT⟩ := stepAll hA hB (fun i hi => (h1 i hi).le)
    ⟨0, by omega, h1 0 (by omega)⟩ (fun i hi => (h2 i hi).le)
    (fun i hi => ⟨(h3 i hi).1.le, (h3 i hi).2.le⟩)
  refine ⟨A', B', ?_, ?_, g1, g2, g3, ?_⟩
  · rw [Function.iterate_succ_apply']; exact hA'
  · rw [Function.iterate_succ_apply']; exact hB'
  · intro t ht
    obtain ⟨T, hT1, hT2⟩ := hT t ht
    obtain ⟨T', hT', hb⟩ := gT _ T hT1 hT2
    exact ⟨T', by rw [Function.iterate_succ_apply']; exact hT', hb⟩

lemma HR_eval_root {f : ℝ[X]} {d : ℕ} {r : ℕ → ℝ} (h : HR f d r) {i : ℕ} (hi : i < d) :
    f.eval (r i) = 0 := by
  obtain ⟨-, c, -, rfl⟩ := h
  rw [eval_mul, eval_prod, Finset.prod_eq_zero (mem_range.2 hi) (by simp)]
  ring

lemma inv_stage (S : Finset ℝ) (n : ℕ) (hS : S.card = n + 1) (hn : 1 ≤ n)
    (a b : ℝ) (ha : a ∈ S) (hb : b ∈ S) (hab : ∀ s ∈ S, a ≤ s ∧ s ≤ b) :
    Inv S a b n 1 := by
  obtain ⟨s, hs⟩ : ∃ s, s = S.orderEmbOfFin hS := ⟨_, rfl⟩
  have hsmem : ∀ q, s q ∈ S := by rw [hs]; exact orderEmbOfFin_mem S hS
  have hrange : ∀ t ∈ S, ∃ q, s q = t := by
    intro t ht
    have : t ∈ Set.range s := by rw [hs, range_orderEmbOfFin]; exact ht
    exact this
  have hinit : ∀ q, HR (delProd S (s q)) n (ext (fun i => s (q.succAbove i))) := by
    rw [hs]; exact HR_init S n hS
  have ha0 : s 0 = a := by
    obtain ⟨q, hq⟩ := hrange a ha
    have h1 : a ≤ s 0 := (hab _ (hsmem 0)).1
    have : q ≤ 0 := by rw [← s.le_iff_le, hq]; exact h1
    rw [← hq, le_antisymm this (Fin.zero_le _)]
  have hbl : s (Fin.last n) = b := by
    obtain ⟨q, hq⟩ := hrange b hb
    have h1 : s (Fin.last n) ≤ b := (hab _ (hsmem _)).2
    have : Fin.last n ≤ q := by rw [← s.le_iff_le, hq]; exact h1
    rw [← hq, le_antisymm (Fin.le_last _) this]
  have hA := hinit (Fin.last n)
  have hB := hinit 0
  rw [hbl] at hA
  rw [ha0] at hB
  simp only [Fin.succAbove_last] at hA
  simp only [Fin.succAbove_zero] at hB
  apply inv_one hn hA hB
  · intro i hi
    rw [ext_lt _ hi, ext_lt _ hi, s.le_iff_le]
    exact Fin.castSucc_lt_succ.le
  · refine ⟨0, hn, ?_⟩
    rw [ext_lt _ hn, ext_lt _ hn, s.lt_iff_lt]
    exact Fin.castSucc_lt_succ
  · intro i hi
    rw [ext_lt _ (by omega), ext_lt _ hi]
    exact le_of_eq (congrArg s (Fin.ext (by simp)))
  · intro i hi
    rw [ext_lt _ hi, ext_lt _ hi]
    exact ⟨(hab _ (hsmem _)).1, (hab _ (hsmem _)).2⟩
  · intro t ht
    obtain ⟨q, rfl⟩ := hrange t ht
    refine ⟨_, hinit q, fun i hi => ?_⟩
    rw [ext_lt _ hi, ext_lt _ hi, ext_lt _ hi, s.le_iff_le, s.le_iff_le]
    exact succAbove_bounds q ⟨i, hi⟩

/-! ## Main theorem -/
theorem interlace (S : Finset ℝ) (n k : ℕ) (hS : S.card = n + 1) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (a b : ℝ) (ha : a ∈ S) (hb : b ∈ S) (hab : ∀ s ∈ S, a ≤ s ∧ s ≤ b) :
    ∃ ξ η : Fin (n - k) → ℝ, StrictMono ξ ∧ StrictMono η ∧ (∀ j, ξ j < η j) ∧
      (∀ j j' : Fin (n - k), j.val + 1 = j'.val → η j < ξ j') ∧
      (∀ j, a < ξ j ∧ η j < b) ∧
      (∀ j, (derivative^[k] (delProd S b)).eval (ξ j) = 0) ∧
      (∀ j, (derivative^[k] (delProd S a)).eval (η j) = 0) ∧
      (∀ j : Fin (n - k + 1), ∀ x ∈ Set.Icc (chebLo a η j) (chebHi b ξ j), ∀ t ∈ S,
        0 ≤ (-1 : ℝ) ^ (n - k - j.val) * (derivative^[k] (delProd S t)).eval x) := by
  have hInv : Inv S a b n k := by
    induction k, hk1 using Nat.le_induction with
    | base => exact inv_stage S n hS (by omega) a b ha hb hab
    | succ j hj ih => exact inv_succ hkn (ih (by omega))
  obtain ⟨A, B, hA, hB, h1, h2, h3, hT⟩ := hInv
  refine ⟨fun j => A j.val, fun j => B j.val, fun i j h => hA.1 i j h j.2,
    fun i j h => hB.1 i j h j.2, fun j => h1 j j.2, ?_, fun j => h3 j j.2,
    fun j => HR_eval_root hA j.2, fun j => HR_eval_root hB j.2, ?_⟩
  · intro j j' hjj
    have := h2 j (by omega)
    rw [hjj] at this
    exact this
  · intro j x hx t ht
    obtain ⟨T, hT1, hT2⟩ := hT t ht
    apply sign_claim hT1 hT2 j.val (by omega) x
    · intro i hi
      have hj0 : j.val ≠ 0 := by omega
      have hx1 := hx.1
      simp only [chebLo, hj0, dite_false] at hx1
      have := hB.1.le (show i ≤ j.val - 1 by omega) (by omega)
      linarith
    · intro i hji him
      have hjm : j.val < n - k := by omega
      have hx2 := hx.2
      simp only [chebHi, hjm, dite_true] at hx2
      have := hA.1.le hji him
      linarith

end StrongConv.VM.PartI
end

section
open Polynomial
namespace StrongConv.VM
/-! ## Part I: interlacing of the k-th derivatives of the deleted products (generic) -/
alias interlace := StrongConv.VM.PartI.interlace

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
/-! ## Basic facts about deleted products -/
lemma natDegree_delProd_le (S : Finset ℝ) (n : ℕ) (hS : S.card = n + 1) (t : ℝ) (ht : t ∈ S) :
    (delProd S t).natDegree ≤ n := by
  unfold delProd
  refine (natDegree_prod_le _ _).trans ?_
  simp [natDegree_X_sub_C, Finset.card_erase_of_mem ht, hS]

lemma monic_delProd (S : Finset ℝ) (t : ℝ) : (delProd S t).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C s

lemma natDegree_delProd (S : Finset ℝ) (n : ℕ) (hS : S.card = n + 1) (t : ℝ) (ht : t ∈ S) :
    (delProd S t).natDegree = n := by
  unfold delProd
  rw [natDegree_prod_of_monic _ _ (fun s _ => monic_X_sub_C s)]
  simp [natDegree_X_sub_C, Finset.card_erase_of_mem ht, hS]

lemma eval_delProd (S : Finset ℝ) (t x : ℝ) :
    (delProd S t).eval x = ∏ s ∈ S.erase t, (x - s) := by
  simp [delProd, eval_prod]

lemma eval_delProd_self_ne (S : Finset ℝ) (t : ℝ) : (delProd S t).eval t ≠ 0 := by
  rw [eval_delProd, Finset.prod_ne_zero_iff]
  intro s hs
  exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm

lemma eval_delProd_other (S : Finset ℝ) (t s : ℝ) (hs : s ∈ S) (hst : s ≠ t) :
    (delProd S t).eval s = 0 := by
  rw [eval_delProd]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hst, hs⟩) (by simp)

lemma degree_lt_of_natDegree_le {p : ℝ[X]} {n : ℕ} (h : p.natDegree ≤ n) :
    p.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt degree_le_natDegree ?_
  exact_mod_cast Nat.lt_succ_of_le h

theorem lagrange_iter (S : Finset ℝ) (n k : ℕ) (hS : S.card = n + 1) (P : ℝ[X])
    (hP : P.natDegree ≤ n) (x : ℝ) :
    (derivative^[k] P).eval x =
      ∑ t ∈ S, P.eval t / (delProd S t).eval t * (derivative^[k] (delProd S t)).eval x := by
  set Q : ℝ[X] := ∑ t ∈ S, C (P.eval t / (delProd S t).eval t) * delProd S t with hQ
  have hQdeg : Q.natDegree ≤ n := by
    refine natDegree_sum_le_of_forall_le _ _ (fun t ht => ?_)
    exact (natDegree_C_mul_le _ _).trans (natDegree_delProd_le S n hS t ht)
  have hPQ : P = Q := by
    refine eq_of_degrees_lt_of_eval_finset_eq S ?_ ?_ ?_
    · rw [hS]; exact degree_lt_of_natDegree_le hP
    · rw [hS]; exact degree_lt_of_natDegree_le hQdeg
    · intro s hs
      rw [hQ, eval_finsetSum, Finset.sum_eq_single s]
      · rw [eval_mul, eval_C]
        field_simp [eval_delProd_self_ne S s]
      · intro t ht hts
        rw [eval_mul, eval_delProd_other S t s hs (Ne.symm hts), mul_zero]
      · intro h; exact absurd hs h
  have hPQ' : (derivative^[k] P).eval x = (derivative^[k] Q).eval x := by rw [hPQ]
  rw [hPQ', hQ, iterate_derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [iterate_derivative_C_mul, eval_mul, eval_C]

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
/-! ## Part C: Lagrange formula and the Chebyshev-specific facts -/
alias lagrange_iter := StrongConv.VM.PartC.lagrange_iter

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
theorem chebNodes_card (n : ℕ) : (chebNodes n).card = n + 1 := by
  unfold chebNodes
  rw [Finset.card_image_of_injOn (Chebyshev.strictAntiOn_node n).injOn, Finset.card_range]

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias chebNodes_card := StrongConv.VM.PartC.chebNodes_card

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
lemma mem_chebNodes {n : ℕ} {t : ℝ} :
    t ∈ chebNodes n ↔ ∃ i, i < n + 1 ∧ Chebyshev.node n i = t := by
  simp [chebNodes]

theorem chebNodes_bounds (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ℝ) ∈ chebNodes n ∧ (1 : ℝ) ∈ chebNodes n ∧
      ∀ s ∈ chebNodes n, -1 ≤ s ∧ s ≤ 1 := by
  refine ⟨mem_chebNodes.mpr ⟨n, by omega, Chebyshev.node_eq_neg_one (by omega)⟩,
    mem_chebNodes.mpr ⟨0, by omega, Chebyshev.node_eq_one⟩, ?_⟩
  intro s hs
  obtain ⟨i, _, rfl⟩ := mem_chebNodes.mp hs
  exact Chebyshev.node_mem_Icc

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias chebNodes_bounds := StrongConv.VM.PartC.chebNodes_bounds

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
lemma erase_chebNodes (n i : ℕ) (hi : i < n + 1) :
    (chebNodes n).erase (Chebyshev.node n i) =
      ((Finset.range (n + 1)).erase i).image (Chebyshev.node n) := by
  have hinj := (Chebyshev.strictAntiOn_node n).injOn
  ext s
  simp only [Finset.mem_erase, Finset.mem_image, chebNodes, Finset.mem_range]
  constructor
  · rintro ⟨hne, j, hj, rfl⟩
    exact ⟨j, ⟨fun h => hne (by rw [h]), hj⟩, rfl⟩
  · rintro ⟨j, ⟨hji, hj⟩, rfl⟩
    refine ⟨fun h => hji ?_, j, hj, rfl⟩
    exact hinj (by simpa using hj) (by simpa using hi) h

theorem sign_coeff (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ chebNodes n) :
    0 < (Chebyshev.T ℝ n).eval t / (delProd (chebNodes n) t).eval t ∧
      |(Chebyshev.T ℝ n).eval t| = 1 := by
  obtain ⟨i, hi, rfl⟩ := mem_chebNodes.mp ht
  have hT : (Chebyshev.T ℝ n).eval (Chebyshev.node n i) = (-1) ^ i :=
    Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (by omega))
  have hprod : (delProd (chebNodes n) (Chebyshev.node n i)).eval (Chebyshev.node n i) =
      ∏ j ∈ (Finset.range (n + 1)).erase i,
        (Chebyshev.node n i - Chebyshev.node n j) := by
    rw [eval_delProd, erase_chebNodes n i hi, Finset.prod_image]
    intro a ha b hb hab
    exact (Chebyshev.strictAntiOn_node n).injOn
      (by simpa using (Finset.mem_of_mem_erase ha))
      (by simpa using (Finset.mem_of_mem_erase hb)) hab
  have hpos := Chebyshev.zero_lt_prod_node_sub_node (n := n) (i := i) (by omega)
  rw [hT, hprod]
  refine ⟨?_, by simp⟩
  set p := ∏ j ∈ (Finset.range (n + 1)).erase i, (Chebyshev.node n i - Chebyshev.node n j)
  have hp : p ≠ 0 := by
    rintro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  have : (-1 : ℝ) ^ i / p = ((-1) ^ i * p) / (p * p) := by field_simp
  rw [this]
  exact div_pos hpos (mul_self_pos.mpr hp)

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias sign_coeff := StrongConv.VM.PartC.sign_coeff

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
/-! ## The deleted products at `±1` -/
lemma derivative_T_node_eq_zero (n i : ℕ) (hi0 : 0 < i) (hin : i < n) :
    (derivative (Chebyshev.T ℝ n)).eval (Chebyshev.node n i) = 0 := by
  have h := Chebyshev.isLocalExtr_T_real (n := n) (k := i) (by omega) hi0 hin
  have := h.deriv_eq_zero
  rw [Polynomial.deriv] at this
  exact this

lemma iterate_derivative_X_sub_mul (b : ℝ) (p : ℝ[X]) (k : ℕ) :
    derivative^[k] ((X - C b) * derivative p) =
      (X - C b) * derivative^[k + 1] p + (k : ℝ[X]) * derivative^[k] p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply' _ (k + 1),
      Function.iterate_succ_apply' _ k]
    simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_C,
      derivative_natCast, Function.iterate_succ_apply']
    push_cast
    ring

lemma delProd_pm_one (n : ℕ) (hn : 1 ≤ n) (a b : ℝ)
    (hab : (a = -1 ∧ b = 1) ∨ (a = 1 ∧ b = -1)) :
    ∃ c : ℝ, c ≠ 0 ∧ (X - C b) * derivative (Chebyshev.T ℝ n) = C c * delProd (chebNodes n) a := by
  set q : ℝ[X] := (X - C b) * derivative (Chebyshev.T ℝ n) with hq
  have hT1 : (derivative (Chebyshev.T ℝ n)).eval 1 = (n : ℝ) ^ 2 := by
    rw [Chebyshev.derivative_T_eval_one]; push_cast; ring
  have hT0 : derivative (Chebyshev.T ℝ n) ≠ 0 := by
    intro h; rw [h, eval_zero] at hT1
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact pow_ne_zero 2 this hT1.symm
  have hq0 : q ≠ 0 := mul_ne_zero (X_sub_C_ne_zero b) hT0
  have hqdeg : q.natDegree ≤ n := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_X_sub_C]
    have := natDegree_derivative_le (Chebyshev.T ℝ n)
    simp only [Chebyshev.natDegree_T, Int.natAbs_natCast] at this
    omega
  have hmem : a ∈ chebNodes n := by
    rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (chebNodes_bounds n hn).1
    · exact (chebNodes_bounds n hn).2.1
  -- the deleted product divides `q`
  have hdvd : delProd (chebNodes n) a ∣ q := by
    have hle : ((chebNodes n).erase a).val ≤ q.roots := by
      rw [Multiset.le_iff_subset ((chebNodes n).erase a).nodup]
      intro s hs
      have hs' : s ∈ (chebNodes n).erase a := hs
      rw [mem_roots hq0, IsRoot.def, hq, eval_mul]
      obtain ⟨hsa, hsS⟩ := Finset.mem_erase.mp hs'
      obtain ⟨i, hi, rfl⟩ := mem_chebNodes.mp hsS
      by_cases hi0 : i = 0
      · subst hi0
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [Chebyshev.node_eq_one]
        · exact absurd Chebyshev.node_eq_one hsa
      by_cases hin : i = n
      · subst hin
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd (Chebyshev.node_eq_neg_one (by omega)) hsa
        · simp [Chebyshev.node_eq_neg_one (show i ≠ 0 by omega)]
      rw [derivative_T_node_eq_zero n i (by omega) (by omega), mul_zero]
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hq0 _).mpr hle
    unfold delProd
    rw [Finset.prod_eq_multiset_prod]
    exact this
  obtain ⟨r, hr⟩ := hdvd
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hr; exact hq0 hr
  have hdeg := (monic_delProd (chebNodes n) a).natDegree_mul' hr0
  rw [← hr, natDegree_delProd _ n (chebNodes_card n) a hmem] at hdeg
  have hr' : r = C (r.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
  refine ⟨r.coeff 0, ?_, ?_⟩
  · intro h; rw [h, C_0] at hr'; exact hr0 hr'
  · rw [hr, mul_comm, ← hr']

lemma iterate_delProd_eval (n k : ℕ) (hn : 1 ≤ n) (a b : ℝ)
    (hab : (a = -1 ∧ b = 1) ∨ (a = 1 ∧ b = -1)) (x : ℝ) :
    ∃ c : ℝ, c ≠ 0 ∧ c * (derivative^[k] (delProd (chebNodes n) a)).eval x =
      (x - b) * (derivative^[k + 1] (Chebyshev.T ℝ n)).eval x +
        k * (derivative^[k] (Chebyshev.T ℝ n)).eval x := by
  obtain ⟨c, hc, h⟩ := delProd_pm_one n hn a b hab
  refine ⟨c, hc, ?_⟩
  have h2 := congrArg (fun p => (derivative^[k] p).eval x) h
  simp only [iterate_derivative_X_sub_mul, iterate_derivative_C_mul] at h2
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_natCast] at h2
  linarith

lemma eval_rPoly (n k : ℕ) (x : ℝ) :
    (rPoly n k).eval x = 1 / (k : ℝ) * (x ^ 2 - 1) *
      (derivative^[k + 1] (Chebyshev.T ℝ n)).eval x +
        x * (derivative^[k] (Chebyshev.T ℝ n)).eval x := by
  simp only [rPoly, eval_add, eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_one]

theorem r_lo (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (x : ℝ)
    (hx : (x + 1) * (derivative^[k] (delProd (chebNodes n) (-1))).eval x = 0) :
    (rPoly n k).eval x = -(derivative^[k] (Chebyshev.T ℝ n)).eval x := by
  obtain ⟨c, hc, h⟩ := iterate_delProd_eval n k (by omega) (-1) 1 (Or.inl ⟨rfl, rfl⟩) x
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have h' : (x + 1) * ((x - 1) * (derivative^[k + 1] (Chebyshev.T ℝ n)).eval x +
      k * (derivative^[k] (Chebyshev.T ℝ n)).eval x) = 0 := by
    rw [← h, mul_left_comm, hx, mul_zero]
  rw [eval_rPoly]
  field_simp
  linear_combination h'

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias r_lo := StrongConv.VM.PartC.r_lo

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
theorem r_hi (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (x : ℝ)
    (hx : (x - 1) * (derivative^[k] (delProd (chebNodes n) 1)).eval x = 0) :
    (rPoly n k).eval x = (derivative^[k] (Chebyshev.T ℝ n)).eval x := by
  obtain ⟨c, hc, h⟩ := iterate_delProd_eval n k (by omega) 1 (-1) (Or.inr ⟨rfl, rfl⟩) x
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have h' : (x - 1) * ((x - -1) * (derivative^[k + 1] (Chebyshev.T ℝ n)).eval x +
      k * (derivative^[k] (Chebyshev.T ℝ n)).eval x) = 0 := by
    rw [← h, mul_left_comm, hx, mul_zero]
  rw [eval_rPoly]
  field_simp
  linear_combination h'

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias r_hi := StrongConv.VM.PartC.r_hi

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
/-! ## Coefficients of `rPoly` -/
lemma coeff_T_eq_zero (n j : ℕ) (hj : n < j) : (Chebyshev.T ℝ n).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by simpa using hj)

theorem r_coeff (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (rPoly n k).natDegree ≤ n - k + 1 ∧ (rPoly n k).coeff (n - k + 1) ≠ 0 := by
  have hc : ∀ N : ℕ, (rPoly n k).coeff N =
      1 / (k : ℝ) * ((if 2 ≤ N then (N - 2 + (k + 1)).descFactorial (k + 1) •
          (Chebyshev.T ℝ n).coeff (N - 2 + (k + 1)) else 0)
        - (N + (k + 1)).descFactorial (k + 1) • (Chebyshev.T ℝ n).coeff (N + (k + 1))) +
      (if 1 ≤ N then (N - 1 + k).descFactorial k • (Chebyshev.T ℝ n).coeff (N - 1 + k)
        else 0) := by
    intro N
    rw [rPoly, mul_assoc, coeff_add, coeff_C_mul, sub_mul, one_mul, coeff_sub,
      coeff_X_pow_mul', ← pow_one (X : ℝ[X]), coeff_X_pow_mul']
    simp only [coeff_iterate_derivative]
  refine ⟨?_, ?_⟩
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hN' : n - k + 1 < N := by exact_mod_cast hN
    rw [hc N, if_pos (by omega), if_pos (by omega),
      coeff_T_eq_zero n (N - 2 + (k + 1)) (by omega),
      coeff_T_eq_zero n (N + (k + 1)) (by omega),
      coeff_T_eq_zero n (N - 1 + k) (by omega)]
    simp
  · rw [hc, if_pos (show 1 ≤ n - k + 1 by omega), coeff_T_eq_zero n (n - k + 1 + (k + 1)) (by omega),
      show n - k + 1 - 1 + k = n by omega]
    have hlead : (Chebyshev.T ℝ n).coeff n = 2 ^ (n - 1) := by
      have := Chebyshev.leadingCoeff_T ℝ n
      simpa [leadingCoeff] using this
    have hA : (0 : ℝ) ≤ (if 2 ≤ n - k + 1 then (n - k + 1 - 2 + (k + 1)).descFactorial (k + 1) •
          (Chebyshev.T ℝ n).coeff (n - k + 1 - 2 + (k + 1)) else 0) := by
      split_ifs
      · by_cases hh : n - k + 1 - 2 + (k + 1) = n
        · rw [hh, hlead, nsmul_eq_mul]; positivity
        · rw [coeff_T_eq_zero n _ (by omega)]; simp
      · exact le_refl _
    have hB : (0 : ℝ) < (n).descFactorial k • (Chebyshev.T ℝ n).coeff n := by
      rw [hlead, nsmul_eq_mul]
      have : 0 < (n).descFactorial k := Nat.descFactorial_pos.mpr hkn
      positivity
    have hk : (0 : ℝ) < 1 / (k : ℝ) := by
      have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      positivity
    rw [smul_zero, sub_zero]
    have := mul_nonneg hk.le hA
    exact (by linarith : (0 : ℝ) < _).ne'

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias r_coeff := StrongConv.VM.PartC.r_coeff

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
/-! ## The bound on `rPoly` (Shadrin Lemma 5.17) -/
lemma g_T_bound (m k : ℕ) (hk1 : 1 ≤ k) (x : ℝ) (hx : |x| ≤ 1) :
    |1 / (k : ℝ) * (x ^ 2 - 1) * (derivative^[2] (Chebyshev.T ℝ m)).eval x +
      x * (derivative (Chebyshev.T ℝ m)).eval x| ≤
      (derivative (Chebyshev.T ℝ m)).eval 1 := by
  have hode := congrArg (fun p => p.eval x)
    (Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℝ) (m : ℤ))
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_intCast] at hode
  push_cast at hode
  have h1 : (derivative (Chebyshev.T ℝ m)).eval 1 = (m : ℝ) ^ 2 := by
    rw [Chebyshev.derivative_T_eval_one]; push_cast; ring
  have hT : |(Chebyshev.T ℝ m).eval x| ≤ 1 := Chebyshev.abs_eval_T_real_le_one m hx
  have hT' : |(derivative (Chebyshev.T ℝ m)).eval x| ≤ (m : ℝ) ^ 2 := by
    have := Chebyshev.abs_iterate_derivative_T_real_le (m : ℤ) 1 hx
    simpa [h1] using this
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  set A := (derivative^[2] (Chebyshev.T ℝ m)).eval x
  set B := (derivative (Chebyshev.T ℝ m)).eval x
  set U := (Chebyshev.T ℝ m).eval x
  have heq : 1 / (k : ℝ) * (x ^ 2 - 1) * A + x * B =
      ((m : ℝ) ^ 2 / k) * U + (1 - 1 / k) * (x * B) := by
    field_simp
    linear_combination (-1 : ℝ) * hode
  rw [heq, h1]
  have ha : (0 : ℝ) ≤ (m : ℝ) ^ 2 / k := by positivity
  have hb : (0 : ℝ) ≤ 1 - 1 / k := by
    rw [sub_nonneg, div_le_one hkpos]; exact hk
  have hxB : |x * B| ≤ (m : ℝ) ^ 2 := by
    rw [abs_mul]
    calc |x| * |B| ≤ 1 * (m : ℝ) ^ 2 := by
          exact mul_le_mul hx hT' (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc |(m : ℝ) ^ 2 / k * U + (1 - 1 / k) * (x * B)|
      ≤ |(m : ℝ) ^ 2 / k * U| + |(1 - 1 / k) * (x * B)| := abs_add_le _ _
    _ = (m : ℝ) ^ 2 / k * |U| + (1 - 1 / k) * |x * B| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ (m : ℝ) ^ 2 / k * 1 + (1 - 1 / k) * (m : ℝ) ^ 2 := by
        gcongr
    _ = (m : ℝ) ^ 2 := by field_simp; ring

theorem abs_r_le (n k : ℕ) (hk1 : 1 ≤ k) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(rPoly n k).eval x| ≤ (derivative^[k] (Chebyshev.T ℝ n)).eval 1 := by
  have hxa : |x| ≤ 1 := abs_le.mpr hx
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hspan := Chebyshev.T_iterate_derivative_mem_span_T (R := ℝ) n j
  obtain ⟨f, hfsupp, hfderiv⟩ := Submodule.mem_span_set.mp hspan
  replace hfderiv : ∑ p ∈ f.support, f p • p = derivative^[j] (Chebyshev.T ℝ n) := by
    rw [← hfderiv]; rfl
  have hD1 : ∀ y, (derivative^[j + 1] (Chebyshev.T ℝ n)).eval y =
      ∑ p ∈ f.support, (f p : ℝ) * (derivative p).eval y := by
    intro y
    rw [Function.iterate_succ_apply', ← hfderiv, derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [derivative_smul, eval_smul, nsmul_eq_mul]
  have hD2 : ∀ y, (derivative^[j + 1 + 1] (Chebyshev.T ℝ n)).eval y =
      ∑ p ∈ f.support, (f p : ℝ) * (derivative^[2] p).eval y := by
    intro y
    rw [show j + 1 + 1 = 2 + j by omega, Function.iterate_add_apply, ← hfderiv,
      iterate_derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [iterate_derivative_smul, eval_smul, nsmul_eq_mul]
  rw [eval_rPoly, hD1, hD1, hD2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
  obtain ⟨m, -, rfl⟩ := (Set.mem_image ..).mp (hfsupp hp)
  have := g_T_bound m (j + 1) hk1 x hxa
  have hf : (0 : ℝ) ≤ f (Chebyshev.T ℝ m) := Nat.cast_nonneg _
  calc |1 / ((j + 1 : ℕ) : ℝ) * (x ^ 2 - 1) *
          ((f (Chebyshev.T ℝ m) : ℝ) * (derivative^[2] (Chebyshev.T ℝ m)).eval x) +
        x * ((f (Chebyshev.T ℝ m) : ℝ) * (derivative (Chebyshev.T ℝ m)).eval x)|
      = (f (Chebyshev.T ℝ m) : ℝ) * |1 / ((j + 1 : ℕ) : ℝ) * (x ^ 2 - 1) *
          (derivative^[2] (Chebyshev.T ℝ m)).eval x +
          x * (derivative (Chebyshev.T ℝ m)).eval x| := by
        rw [← abs_of_nonneg hf, ← abs_mul, abs_of_nonneg hf]; ring_nf
    _ ≤ (f (Chebyshev.T ℝ m) : ℝ) * (derivative (Chebyshev.T ℝ m)).eval 1 :=
        mul_le_mul_of_nonneg_left this hf

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias abs_r_le := StrongConv.VM.PartC.abs_r_le

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartC
open StrongConv.VM
/-! ## `T^{(k)}(1)` -/
lemma prod_odd_eq_doubleFactorial (k : ℕ) :
    ∏ l ∈ Finset.range k, (2 * l + 1) = (2 * k - 1).doubleFactorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    rcases k with _ | k
    · simp
    · rw [show 2 * (k + 1 + 1) - 1 = (2 * (k + 1) - 1) + 2 by omega,
        Nat.doubleFactorial_add_two]
      rw [show 2 * (k + 1) - 1 + 2 = 2 * (k + 1) + 1 by omega, mul_comm]

theorem T_iter_one_le (n k : ℕ) :
    (derivative^[k] (Chebyshev.T ℝ n)).eval 1 ≤
      (n : ℝ) ^ (2 * k) / ((2 * k - 1).doubleFactorial : ℝ) := by
  have h := Chebyshev.iterate_derivative_T_eval_one (R := ℝ) (n : ℤ) k
  push_cast at h
  have hprod : (∏ l ∈ Finset.range k, (2 * (l : ℝ) + 1)) =
      ((2 * k - 1).doubleFactorial : ℝ) := by
    rw [← prod_odd_eq_doubleFactorial]; push_cast; rfl
  rw [hprod] at h
  have hpos : (0 : ℝ) < ((2 * k - 1).doubleFactorial : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  rw [le_div_iff₀ hpos, mul_comm, h]
  push_cast
  by_cases hkn : k ≤ n
  · calc ∏ l ∈ Finset.range k, ((n : ℝ) ^ 2 - (l : ℝ) ^ 2)
        ≤ ∏ l ∈ Finset.range k, (n : ℝ) ^ 2 := by
          apply Finset.prod_le_prod
          · intro l hl
            have : (l : ℝ) ≤ n := by
              exact_mod_cast (show l ≤ n by have := Finset.mem_range.mp hl; omega)
            nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
          · intro l _; nlinarith [sq_nonneg (l : ℝ)]
      _ = (n : ℝ) ^ (2 * k) := by rw [Finset.prod_const, Finset.card_range, pow_mul]
  · rw [Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr (by omega)) (by ring)]
    positivity

end StrongConv.VM.PartC
end

section
open Polynomial
namespace StrongConv.VM
alias T_iter_one_le := StrongConv.VM.PartC.T_iter_one_le

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartE
open StrongConv.VM
theorem no_root_in_gap (m : ℕ) (H : ℝ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ m + 1)
    (lo hi : Fin (m + 1) → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hsep : ∀ j j' : Fin (m + 1), j.val + 1 = j'.val → hi j < lo j')
    (hsign : ∀ j, H.eval (lo j) * H.eval (hi j) ≤ 0)
    (x : ℝ) (hx : ∀ j, x < lo j ∨ hi j < x) : H.eval x ≠ 0 := by
  intro hHx
  have hroot : ∀ j, ∃ c ∈ Set.Icc (lo j) (hi j), H.eval c = 0 := by
    intro j
    have hcont : ContinuousOn (fun y => H.eval y) (Set.Icc (lo j) (hi j)) :=
      H.continuous.continuousOn
    rcases mul_nonpos_iff.mp (hsign j) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (hle j) hcont ⟨h2, h1⟩
      exact ⟨c, hc, hc0⟩
    · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc (hle j) hcont ⟨h1, h2⟩
      exact ⟨c, hc, hc0⟩
  choose c hc hc0 using hroot
  have hmono : StrictMono c := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact lt_of_le_of_lt (hc i.castSucc).2
      (lt_of_lt_of_le (hsep _ _ (by simp)) (hc i.succ).1)
  have hxc : ∀ j, c j ≠ x := by
    intro j h
    rcases hx j with h' | h'
    · have := (hc j).1; rw [h] at this; linarith
    · have := (hc j).2; rw [h] at this; linarith
  have hxnot : x ∉ Finset.univ.image c := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hxc
  have hcard : (insert x (Finset.univ.image c)).card = m + 2 := by
    rw [Finset.card_insert_of_notMem hxnot, Finset.card_image_of_injective _ hmono.injective,
      Finset.card_univ, Fintype.card_fin]
  have hsub : insert x (Finset.univ.image c) ⊆ H.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, mem_roots hH0, IsRoot.def]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hHx
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hc0 j
  have h1 := Finset.card_le_card hsub
  have h2 := Multiset.toFinset_card_le H.roots
  have h3 := Polynomial.card_roots' H
  omega

end StrongConv.VM.PartE
end

section
open Polynomial
namespace StrongConv.VM
/-! ## Part E: zero counting and the normalized inequality -/
alias no_root_in_gap := StrongConv.VM.PartE.no_root_in_gap

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartE
open StrongConv.VM
/-- Claim (D): on a Chebyshev interval, `|P^{(k)}| ≤ σ T^{(k)}`. -/
lemma chebD (n k : ℕ) (hn : 1 ≤ n) (P : ℝ[X]) (hP : P.natDegree ≤ n)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) (y : ℝ) (e : ℕ)
    (hsgn : ∀ t ∈ chebNodes n,
      0 ≤ (-1 : ℝ) ^ e * (derivative^[k] (delProd (chebNodes n) t)).eval y) :
    |(derivative^[k] P).eval y| ≤ (-1 : ℝ) ^ e * (derivative^[k] (Chebyshev.T ℝ n)).eval y := by
  have hS := StrongConv.VM.chebNodes_card n
  rw [StrongConv.VM.lagrange_iter (chebNodes n) n k hS P hP y,
    StrongConv.VM.lagrange_iter (chebNodes n) n k hS (Chebyshev.T ℝ n) (by simp) y,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht => ?_)
  obtain ⟨hpos, habs⟩ := StrongConv.VM.sign_coeff n hn t ht
  have hbd := (StrongConv.VM.chebNodes_bounds n hn).2.2 t ht
  have hPt : |P.eval t| ≤ |(Chebyshev.T ℝ n).eval t| := by
    rw [habs]; exact hb t ⟨hbd.1, hbd.2⟩
  have hσ : |(-1 : ℝ) ^ e| = 1 := by simp
  have hs := hsgn t ht
  set w := (delProd (chebNodes n) t).eval t
  set D := (derivative^[k] (delProd (chebNodes n) t)).eval y
  have hD : |D| = (-1 : ℝ) ^ e * D := by
    rw [← abs_of_nonneg hs, abs_mul, hσ, one_mul]
  calc |P.eval t / w * D| = |P.eval t| / |w| * ((-1 : ℝ) ^ e * D) := by
        rw [abs_mul, abs_div, hD]
    _ ≤ |(Chebyshev.T ℝ n).eval t| / |w| * ((-1 : ℝ) ^ e * D) := by gcongr
    _ = (Chebyshev.T ℝ n).eval t / w * ((-1 : ℝ) ^ e * D) := by
        rw [← abs_div, abs_of_pos hpos]
    _ = (-1 : ℝ) ^ e * ((Chebyshev.T ℝ n).eval t / w * D) := by ring

lemma main (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (P : ℝ[X]) (hP : P.natDegree ≤ n)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(derivative^[k] P).eval x| ≤ (derivative^[k] (Chebyshev.T ℝ n)).eval 1 := by
  have hn : 1 ≤ n := le_trans hk1 hkn
  obtain ⟨hm1, hp1, hbd⟩ := StrongConv.VM.chebNodes_bounds n hn
  obtain ⟨ξ, η, -, -, hξη, hηξ, hab, hξroot, hηroot, hsgn⟩ :=
    StrongConv.VM.interlace (chebNodes n) n k (StrongConv.VM.chebNodes_card n) hk1 hkn
      (-1) 1 hm1 hp1 hbd
  have hD : ∀ j : Fin (n - k + 1), ∀ y ∈ Set.Icc (chebLo (-1) η j) (chebHi 1 ξ j),
      |(derivative^[k] P).eval y| ≤
        (-1 : ℝ) ^ (n - k - j.val) * (derivative^[k] (Chebyshev.T ℝ n)).eval y :=
    fun j y hy => chebD n k hn P hP hb y _ (fun t ht => hsgn j y hy t ht)
  by_cases hin : ∃ j : Fin (n - k + 1), x ∈ Set.Icc (chebLo (-1) η j) (chebHi 1 ξ j)
  · obtain ⟨j, hj⟩ := hin
    refine (hD j x hj).trans ?_
    have := Chebyshev.abs_iterate_derivative_T_real_le (n : ℤ) k (abs_le.mpr hx)
    refine le_trans (le_abs_self _) ?_
    rw [abs_mul]
    simpa using this
  have hxgap : ∀ j, x < chebLo (-1) η j ∨ chebHi 1 ξ j < x := by
    intro j
    by_contra h
    push Not at h
    exact hin ⟨j, h.1, h.2⟩
  refine le_trans ?_ (StrongConv.VM.abs_r_le n k hk1 x hx)
  by_contra hlt
  push Not at hlt
  set p := derivative^[k] P with hpdef
  have hp0 : p.eval x ≠ 0 := by
    intro h; rw [h, abs_zero] at hlt; exact absurd hlt (not_lt.mpr (abs_nonneg _))
  set lam := (rPoly n k).eval x / p.eval x with hlamdef
  have hlam : |lam| ≤ 1 := by
    rw [hlamdef, abs_div, div_le_one (abs_pos.mpr hp0)]; exact hlt.le
  set H := rPoly n k - C lam * p with hHdef
  have hpdeg : p.natDegree ≤ n - k := (natDegree_iterate_derivative P k).trans (by omega)
  obtain ⟨hrdeg, hrc⟩ := StrongConv.VM.r_coeff n k hk1 hkn
  have hHc : H.coeff (n - k + 1) = (rPoly n k).coeff (n - k + 1) := by
    rw [hHdef, coeff_sub, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (show p.natDegree < n - k + 1 by omega), mul_zero, sub_zero]
  have hH0 : H ≠ 0 := by
    intro h; rw [h, coeff_zero] at hHc; exact hrc hHc.symm
  have hCp : (C lam * p).natDegree ≤ n - k + 1 :=
    (natDegree_C_mul_le _ _).trans (hpdeg.trans (Nat.le_succ _))
  have hHdeg : H.natDegree ≤ n - k + 1 := by
    rw [hHdef]; exact (natDegree_sub_le_of_le hrdeg hCp).trans (max_self _).le
  have hHx : H.eval x = 0 := by
    rw [hHdef, eval_sub, eval_mul, eval_C, hlamdef, div_mul_cancel₀ _ hp0, sub_self]
  -- endpoint values of `rPoly`
  have hrlo : ∀ j : Fin (n - k + 1), (rPoly n k).eval (chebLo (-1) η j) =
      -(derivative^[k] (Chebyshev.T ℝ n)).eval (chebLo (-1) η j) := by
    intro j
    apply StrongConv.VM.r_lo n k hk1 hkn
    unfold chebLo
    split_ifs with h
    · simp
    · rw [hηroot, mul_zero]
  have hrhi : ∀ j : Fin (n - k + 1), (rPoly n k).eval (chebHi 1 ξ j) =
      (derivative^[k] (Chebyshev.T ℝ n)).eval (chebHi 1 ξ j) := by
    intro j
    apply StrongConv.VM.r_hi n k hk1 hkn
    unfold chebHi
    split_ifs with h
    · rw [hξroot, mul_zero]
    · simp
  have hle : ∀ j : Fin (n - k + 1), chebLo (-1) η j ≤ chebHi 1 ξ j := by
    intro j
    unfold chebLo chebHi
    split_ifs with h1 h2 h2
    · exact (hab _).1.le
    · norm_num
    · exact (hηξ _ _ (by simp; omega)).le
    · exact (hab _).2.le
  have hsep : ∀ j j' : Fin (n - k + 1), j.val + 1 = j'.val →
      chebHi 1 ξ j < chebLo (-1) η j' := by
    intro j j' hjj
    have := j'.isLt
    have hj : j.val < n - k := by omega
    unfold chebLo chebHi
    rw [dif_pos hj, dif_neg (show j'.val ≠ 0 by omega)]
    have hfin : (⟨j'.val - 1, by omega⟩ : Fin (n - k)) = ⟨j.val, hj⟩ := Fin.ext (by simp; omega)
    rw [hfin]
    exact hξη _
  have hsignH : ∀ j : Fin (n - k + 1),
      H.eval (chebLo (-1) η j) * H.eval (chebHi 1 ξ j) ≤ 0 := by
    intro j
    set σ : ℝ := (-1 : ℝ) ^ (n - k - j.val) with hσdef
    have hσ : |σ| = 1 := by simp [hσdef]
    have hσσ : σ * σ = 1 := by rw [hσdef, ← pow_add, ← two_mul, pow_mul]; norm_num
    have key : ∀ y, -(lam * (σ * p.eval y)) ≤ |p.eval y| := by
      intro y
      refine le_trans (neg_le_abs _) ?_
      rw [abs_mul, abs_mul, hσ, one_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hlam
    have hlo := hD j (chebLo (-1) η j) ⟨le_refl _, hle j⟩
    have hhi := hD j (chebHi 1 ξ j) ⟨hle j, le_refl _⟩
    have hA : σ * H.eval (chebLo (-1) η j) ≤ 0 := by
      have e1 : σ * H.eval (chebLo (-1) η j) =
          -(σ * (derivative^[k] (Chebyshev.T ℝ n)).eval (chebLo (-1) η j)) -
            lam * (σ * p.eval (chebLo (-1) η j)) := by
        rw [hHdef, eval_sub, eval_mul, eval_C, hrlo j]; ring
      have := key (chebLo (-1) η j)
      rw [e1]; linarith
    have hB : 0 ≤ σ * H.eval (chebHi 1 ξ j) := by
      have e1 : σ * H.eval (chebHi 1 ξ j) =
          σ * (derivative^[k] (Chebyshev.T ℝ n)).eval (chebHi 1 ξ j) -
            lam * (σ * p.eval (chebHi 1 ξ j)) := by
        rw [hHdef, eval_sub, eval_mul, eval_C, hrhi j]; ring
      have := key (chebHi 1 ξ j)
      have h2 : -(lam * (σ * p.eval (chebHi 1 ξ j))) ≥ -|p.eval (chebHi 1 ξ j)| := by
        have : |lam * (σ * p.eval (chebHi 1 ξ j))| ≤ |p.eval (chebHi 1 ξ j)| := by
          rw [abs_mul, abs_mul, hσ, one_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) hlam
        have := le_abs_self (lam * (σ * p.eval (chebHi 1 ξ j)))
        linarith
      rw [e1]; linarith
    have hprod : H.eval (chebLo (-1) η j) * H.eval (chebHi 1 ξ j) =
        (σ * H.eval (chebLo (-1) η j)) * (σ * H.eval (chebHi 1 ξ j)) := by
      linear_combination (-(H.eval (chebLo (-1) η j) * H.eval (chebHi 1 ξ j))) * hσσ
    rw [hprod]
    exact mul_nonpos_of_nonpos_of_nonneg hA hB
  exact StrongConv.VM.no_root_in_gap (n - k) H hH0 hHdeg _ _ hle hsep hsignH x hxgap hHx

theorem vmarkov_normalized (n k : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(derivative^[k] P).eval x| ≤ (derivative^[k] (Chebyshev.T ℝ n)).eval 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simpa [Chebyshev.T_eval_one] using hb x hx
  by_cases hkn : n < k
  · rw [iterate_derivative_eq_zero (by omega : P.natDegree < k),
      iterate_derivative_eq_zero (p := Chebyshev.T ℝ n) (by simp; omega)]
    simp
  push Not at hkn
  exact main n k hk1 hkn P hP hb x hx

end StrongConv.VM.PartE
end

section
open Polynomial
namespace StrongConv.VM
alias vmarkov_normalized := StrongConv.VM.PartE.vmarkov_normalized

end StrongConv.VM
end

section
open Polynomial
namespace StrongConv.VM.PartS
open StrongConv.VM
lemma cN_eq (F : ℝ → ℝ) (a : ℝ) :
    StrongConv.cNorm 0 F 0 a = sSup ((fun x => |F x|) '' Set.Icc 0 a) := by
  simp [StrongConv.cNorm, StrongConv.supOn]

lemma cN_le {F : ℝ → ℝ} {a B : ℝ} (ha : 0 < a) (h : ∀ x ∈ Set.Icc 0 a, |F x| ≤ B) :
    StrongConv.cNorm 0 F 0 a ≤ B := by
  rw [cN_eq]
  apply csSup_le
  · exact ⟨_, Set.mem_image_of_mem _ (Set.left_mem_Icc.2 ha.le)⟩
  · rintro _ ⟨x, hx, rfl⟩; exact h x hx

lemma le_cN {F : ℝ → ℝ} {a x : ℝ} (hF : ContinuousOn F (Set.Icc 0 a)) (hx : x ∈ Set.Icc 0 a) :
    |F x| ≤ StrongConv.cNorm 0 F 0 a := by
  rw [cN_eq]
  apply le_csSup
  · exact (isCompact_Icc.image_of_continuousOn (hF.abs)).bddAbove
  · exact Set.mem_image_of_mem _ hx

lemma cN_nonneg (F : ℝ → ℝ) (a : ℝ) : 0 ≤ StrongConv.cNorm 0 F 0 a := by
  rw [cN_eq]; apply Real.sSup_nonneg; rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _

lemma iteratedDeriv_poly (h : ℝ[X]) (m : ℕ) :
    iteratedDeriv m (fun x => h.eval x) = fun x => (derivative^[m] h).eval x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [Polynomial.deriv, Function.iterate_succ_apply']

lemma iterate_derivative_comp_affine (h : ℝ[X]) (c d : ℝ) (j : ℕ) :
    derivative^[j] (h.comp (C c * X + C d)) =
      C (c ^ j) * (derivative^[j] h).comp (C c * X + C d) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp,
      Function.iterate_succ_apply']
    simp only [derivative_add, derivative_C_mul, derivative_X, derivative_C, mul_one, add_zero,
      pow_succ, C_mul]
    ring

theorem cNorm_iteratedDeriv_le (q m : ℕ) (h : ℝ[X]) (hh : h.natDegree ≤ q) (a : ℝ) (ha : 0 < a) :
    StrongConv.cNorm 0 (iteratedDeriv m (fun x => h.eval x)) 0 a ≤
      1 / ((2 * m - 1).doubleFactorial : ℝ) * (2 * (q : ℝ) ^ 2 / a) ^ m *
        StrongConv.cNorm 0 (fun x => h.eval x) 0 a := by
  set M := StrongConv.cNorm 0 (fun x => h.eval x) 0 a with hMdef
  have hcont : ContinuousOn (fun x => h.eval x) (Set.Icc 0 a) := h.continuous.continuousOn
  have hhM : ∀ x ∈ Set.Icc 0 a, |h.eval x| ≤ M := fun x hx => le_cN hcont hx
  have hM0 : 0 ≤ M := cN_nonneg _ _
  rw [iteratedDeriv_poly]
  apply cN_le ha
  intro x hx
  rcases hM0.eq_or_lt with hM | hMpos
  · have hz : h = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono (s := Set.Icc 0 a) ?_ (Set.Icc_infinite ha)
      intro y hy
      have := hhM y hy
      rw [← hM] at this
      exact abs_nonpos_iff.mp this
    rw [hz, ← hM]
    simp
  · set L : ℝ[X] := C (a / 2) * X + C (a / 2) with hL
    set P : ℝ[X] := C (1 / M) * h.comp L with hP
    have hLdeg : L.natDegree ≤ 1 := natDegree_linear_le
    have hPdeg : P.natDegree ≤ q := by
      refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
      calc h.natDegree * L.natDegree ≤ q * 1 := Nat.mul_le_mul hh hLdeg
        _ = q := mul_one q
    have hLeval : ∀ y, L.eval y = a / 2 * y + a / 2 := by
      intro y; simp [hL]
    have hPb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |P.eval y| ≤ 1 := by
      intro y hy
      rw [hP, eval_mul, eval_C, eval_comp, hLeval, abs_mul, abs_of_pos (by positivity),
        div_mul_eq_mul_div, one_mul, div_le_one hMpos]
      apply hhM
      constructor <;> nlinarith [hy.1, hy.2]
    set y := 2 * x / a - 1 with hy
    have hyI : y ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [hy]
      constructor
      · have : 0 ≤ 2 * x / a := by have := hx.1; positivity
        linarith
      · have : 2 * x / a ≤ 2 := by
          rw [div_le_iff₀ ha]; linarith [hx.2]
        linarith
    have hyx : a / 2 * y + a / 2 = x := by rw [hy]; field_simp; ring
    have key := StrongConv.VM.vmarkov_normalized q m P hPdeg hPb y hyI
    have hT := StrongConv.VM.T_iter_one_le q m
    have hev : (derivative^[m] P).eval y =
        1 / M * (a / 2) ^ m * (derivative^[m] h).eval x := by
      rw [hP, iterate_derivative_C_mul, hL, iterate_derivative_comp_affine, ← hL, eval_mul,
        eval_C, eval_mul, eval_C, eval_comp, hLeval, hyx]
      ring
    rw [hev] at key
    set u := |(derivative^[m] h).eval x|
    set D : ℝ := ((2 * m - 1).doubleFactorial : ℝ)
    have hD : 0 < D := Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
    set A : ℝ := (a / 2) ^ m
    have hA : 0 < A := by positivity
    have key' : A / M * u ≤ (q : ℝ) ^ (2 * m) / D := by
      have h1 : |1 / M * A * (derivative^[m] h).eval x| = A / M * u := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / M),
          abs_of_pos hA]
        ring
      rw [← h1]; exact key.trans hT
    have hu : u = (A / M * u) * (M / A) := by field_simp
    have hrhs : 1 / D * (2 * (q : ℝ) ^ 2 / a) ^ m * M = (q : ℝ) ^ (2 * m) / D * (M / A) := by
      simp only [A]
      rw [pow_mul, div_pow, mul_pow, div_pow]
      field_simp
    rw [hrhs, hu]
    exact mul_le_mul_of_nonneg_right key' (by positivity)

end StrongConv.VM.PartS
end

alias StrongConv.cNorm_iteratedDeriv_le_dev := StrongConv.VM.PartS.cNorm_iteratedDeriv_le

end
end

section
open Polynomial
open StrongConv

theorem solution (q m : ℕ) (h : ℝ[X]) (hh : h.natDegree ≤ q) (a : ℝ) (ha : 0 < a) :
    cNorm 0 (iteratedDeriv m (fun x => h.eval x)) 0 a ≤
      1 / ((2 * m - 1).doubleFactorial : ℝ) * (2 * (q : ℝ) ^ 2 / a) ^ m *
        cNorm 0 (fun x => h.eval x) 0 a := by
  apply StrongConv.cNorm_iteratedDeriv_le_dev <;> assumption

end
