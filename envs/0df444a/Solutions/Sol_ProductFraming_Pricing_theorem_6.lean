-- Prove2me | solution 1 for ProductFraming.Pricing.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T12:10:47.426027+00:00
-- url     : https://prove2.me/submissions/bfdf6328-74cc-47b8-ad1c-d2c7d40db0ba

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Pricing_Model

set_option autoImplicit false

open Finset

namespace PF6

noncomputable def W {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (a i - β * r i)

lemma W_pos {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (i : Fin n) : 0 < W a β r i :=
  Real.exp_pos _

lemma D_nonneg {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    0 ≤ ∑ i ∈ S, W a β r i :=
  Finset.sum_nonneg (fun i _ => (W_pos a β r i).le)

lemma den_pos {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    0 < 1 + ∑ i ∈ S, W a β r i := by
  have := D_nonneg a β r S; linarith

lemma rev_eq {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    ProductFraming.Pricing.revenue a β r S =
      (∑ i ∈ S, r i * W a β r i) / (1 + ∑ i ∈ S, W a β r i) := by
  unfold ProductFraming.Pricing.revenue ProductFraming.Pricing.mnl
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [if_pos hi]
  simp only [W]
  ring

lemma rev_mul {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    ProductFraming.Pricing.revenue a β r S * (1 + ∑ i ∈ S, W a β r i) =
      ∑ i ∈ S, r i * W a β r i := by
  rw [rev_eq]
  exact div_mul_cancel₀ _ (den_pos a β r S).ne'

lemma le_rev_iff {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) (t : ℝ) :
    t ≤ ProductFraming.Pricing.revenue a β r S ↔
      t * (1 + ∑ i ∈ S, W a β r i) ≤ ∑ i ∈ S, r i * W a β r i := by
  rw [rev_eq, le_div_iff₀ (den_pos a β r S)]

lemma rev_le_iff {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) (t : ℝ) :
    ProductFraming.Pricing.revenue a β r S ≤ t ↔
      ∑ i ∈ S, r i * W a β r i ≤ t * (1 + ∑ i ∈ S, W a β r i) := by
  rw [rev_eq, div_le_iff₀ (den_pos a β r S)]

/-- L1: adding products whose prices are at least the current revenue does not lower revenue. -/
lemma rev_le_of_subset {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) {S T : Finset (Fin n)}
    (hST : S ⊆ T) (h : ∀ j ∈ T \ S, ProductFraming.Pricing.revenue a β r S ≤ r j) :
    ProductFraming.Pricing.revenue a β r S ≤ ProductFraming.Pricing.revenue a β r T := by
  set R := ProductFraming.Pricing.revenue a β r S
  rw [le_rev_iff]
  have h1 := rev_mul a β r S
  have hN : ∑ i ∈ T, r i * W a β r i =
      ∑ i ∈ T \ S, r i * W a β r i + ∑ i ∈ S, r i * W a β r i := (Finset.sum_sdiff hST).symm
  have hD : ∑ i ∈ T, W a β r i = ∑ i ∈ T \ S, W a β r i + ∑ i ∈ S, W a β r i :=
    (Finset.sum_sdiff hST).symm
  have h2 : R * ∑ i ∈ T \ S, W a β r i ≤ ∑ i ∈ T \ S, r i * W a β r i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (h j hj) (W_pos a β r j).le)
  rw [hN, hD]
  nlinarith

/-- uniform revenue bound -/
noncomputable def Kb {n : ℕ} (a : Fin n → ℝ) (β : ℝ) : ℝ := ∑ i : Fin n, Real.exp (a i - 1) / β

lemma term_le {n : ℕ} (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (r : Fin n → ℝ) (i : Fin n) :
    r i * W a β r i ≤ Real.exp (a i - 1) / β := by
  rw [le_div_iff₀ hβ]
  have h1 : β * r i ≤ Real.exp (β * r i - 1) := by
    have := Real.add_one_le_exp (β * r i - 1); linarith
  have h2 : Real.exp (a i - 1) = Real.exp (β * r i - 1) * Real.exp (a i - β * r i) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2]
  have h3 : 0 < Real.exp (a i - β * r i) := Real.exp_pos _
  unfold W
  nlinarith

lemma Kb_nonneg {n : ℕ} (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) : 0 ≤ Kb a β :=
  Finset.sum_nonneg (fun i _ => div_nonneg (Real.exp_pos _).le hβ.le)

lemma rev_le_Kb {n : ℕ} (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (r : Fin n → ℝ)
    (S : Finset (Fin n)) : ProductFraming.Pricing.revenue a β r S ≤ Kb a β := by
  rw [rev_le_iff]
  have h1 : ∑ i ∈ S, r i * W a β r i ≤ ∑ i ∈ S, Real.exp (a i - 1) / β :=
    Finset.sum_le_sum (fun i _ => term_le a hβ r i)
  have h2 : ∑ i ∈ S, Real.exp (a i - 1) / β ≤ Kb a β :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => div_nonneg (Real.exp_pos _).le hβ.le)
  have h3 := D_nonneg a β r S
  have h4 := Kb_nonneg a hβ
  nlinarith

/-- L2: raising negative prices to zero does not lower revenue. -/
lemma rev_le_pos {n : ℕ} (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (r : Fin n → ℝ)
    (S : Finset (Fin n)) :
    ProductFraming.Pricing.revenue a β r S ≤
      ProductFraming.Pricing.revenue a β (fun i => max (r i) 0) S := by
  set r' : Fin n → ℝ := fun i => max (r i) 0
  have hW : ∀ i, W a β r' i ≤ W a β r i := by
    intro i; unfold W; apply Real.exp_le_exp.mpr
    have : r i ≤ r' i := le_max_left _ _
    nlinarith
  have hN : ∀ i, r i * W a β r i ≤ r' i * W a β r' i := by
    intro i
    by_cases h : 0 ≤ r i
    · have : r' i = r i := max_eq_left h
      simp only [W, this]
      rfl
    · have : r' i = 0 := max_eq_right (le_of_lt (not_le.mp h))
      rw [this, zero_mul]
      have := W_pos a β r i
      nlinarith [not_le.mp h]
  have hN0 : ∀ i, 0 ≤ r' i * W a β r' i :=
    fun i => mul_nonneg (le_max_right _ _) (W_pos a β r' i).le
  set N := ∑ i ∈ S, r i * W a β r i
  set N' := ∑ i ∈ S, r' i * W a β r' i
  set D := ∑ i ∈ S, W a β r i
  set D' := ∑ i ∈ S, W a β r' i
  have hNN : N ≤ N' := Finset.sum_le_sum (fun i _ => hN i)
  have hN'0 : 0 ≤ N' := Finset.sum_nonneg (fun i _ => hN0 i)
  have hDD : D' ≤ D := Finset.sum_le_sum (fun i _ => hW i)
  have hD'0 : 0 ≤ D' := D_nonneg a β r' S
  rw [rev_eq, rev_eq, div_le_div_iff₀ (den_pos a β r S) (den_pos a β r' S)]
  nlinarith

/-! ## First-order condition -/

/-- derivative of the revenue of `S` in the price of `j` -/
noncomputable def dterm {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n))
    (j : Fin n) : ℝ :=
  if j ∈ S then W a β r j / (1 + ∑ i ∈ S, W a β r i) *
    (1 + β * ProductFraming.Pricing.revenue a β r S - β * r j) else 0

lemma rev_update {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n))
    (j : Fin n) (hj : j ∈ S) (t : ℝ) :
    ProductFraming.Pricing.revenue a β (Function.update r j t) S =
      (∑ i ∈ S.erase j, r i * W a β r i + t * Real.exp (a j - β * t)) /
        (1 + ∑ i ∈ S.erase j, W a β r i + Real.exp (a j - β * t)) := by
  rw [rev_eq, ← Finset.sum_erase_add S _ hj, ← Finset.sum_erase_add S _ hj]
  have h1 : ∀ i ∈ S.erase j, Function.update r j t i * W a β (Function.update r j t) i =
      r i * W a β r i := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [W, Function.update_of_ne hij]
  have h2 : ∀ i ∈ S.erase j, W a β (Function.update r j t) i = W a β r i := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [W, Function.update_of_ne hij]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  have hWj : W a β (Function.update r j t) j = Real.exp (a j - β * t) := by
    simp only [W, Function.update_self]
  rw [hWj, Function.update_self]
  ring

lemma rev_hasDeriv {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n))
    (j : Fin n) :
    HasDerivAt (fun t => ProductFraming.Pricing.revenue a β (Function.update r j t) S)
      (dterm a β r S j) (r j) := by
  by_cases hj : j ∈ S
  · have hfun : (fun t => ProductFraming.Pricing.revenue a β (Function.update r j t) S) =
        fun t => (∑ i ∈ S.erase j, r i * W a β r i + t * Real.exp (a j - β * t)) /
          (1 + ∑ i ∈ S.erase j, W a β r i + Real.exp (a j - β * t)) :=
      funext (rev_update a β r S j hj)
    rw [hfun]
    set A := ∑ i ∈ S.erase j, r i * W a β r i
    set B := 1 + ∑ i ∈ S.erase j, W a β r i
    have he : HasDerivAt (fun t => Real.exp (a j - β * t)) (Real.exp (a j - β * r j) * (-β)) (r j) := by
      have h0 : HasDerivAt (fun t => a j - β * t) (-β) (r j) := by
        simpa using ((hasDerivAt_id (r j)).const_mul β).const_sub (a j)
      exact h0.exp
    have hc : HasDerivAt (fun t => A + t * Real.exp (a j - β * t))
        (1 * Real.exp (a j - β * r j) + r j * (Real.exp (a j - β * r j) * (-β))) (r j) :=
      ((hasDerivAt_id (r j)).mul he).const_add A
    have hd : HasDerivAt (fun t => B + Real.exp (a j - β * t))
        (Real.exp (a j - β * r j) * (-β)) (r j) := he.const_add B
    have hBpos : 0 < B := by
      have := D_nonneg a β r (S.erase j); simp only [B]; linarith
    have hne : B + Real.exp (a j - β * r j) ≠ 0 := by
      have := Real.exp_pos (a j - β * r j); linarith
    have hD : 1 + ∑ i ∈ S, W a β r i = B + Real.exp (a j - β * r j) := by
      rw [← Finset.sum_erase_add S _ hj]; simp only [B, W]; ring
    have hN : ∑ i ∈ S, r i * W a β r i = A + r j * Real.exp (a j - β * r j) := by
      rw [← Finset.sum_erase_add S _ hj]; simp only [A, W]
    have hval : dterm a β r S j =
        ((1 * Real.exp (a j - β * r j) + r j * (Real.exp (a j - β * r j) * (-β))) *
          (B + Real.exp (a j - β * r j)) -
          (A + r j * Real.exp (a j - β * r j)) * (Real.exp (a j - β * r j) * (-β))) /
          (B + Real.exp (a j - β * r j)) ^ 2 := by
      unfold dterm
      rw [if_pos hj, rev_eq, hD, hN]
      have hW : W a β r j = Real.exp (a j - β * r j) := rfl
      rw [hW]
      field_simp
      ring
    rw [hval]
    exact hc.div hd hne
  · have hfun : (fun t => ProductFraming.Pricing.revenue a β (Function.update r j t) S) =
        fun _ => ProductFraming.Pricing.revenue a β r S := by
      funext t
      rw [rev_eq, rev_eq]
      have h1 : ∀ i ∈ S, Function.update r j t i = r i := by
        intro i hi
        exact Function.update_of_ne (fun h => hj (by rw [← h]; exact hi)) _ _
      have h2 : ∀ i ∈ S, W a β (Function.update r j t) i = W a β r i := by
        intro i hi; simp only [W, h1 i hi]
      rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl (fun i hi => by rw [h1 i hi, h2 i hi])]
    rw [hfun]
    simp only [dterm, if_neg hj]
    exact hasDerivAt_const _ _

/-- FOC: at an optimal price vector for the framing `f`, the price derivative vanishes. -/
lemma foc {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ) (f : Fin n → ℕ)
    (r : Fin n → ℝ)
    (hopt : ∀ r' : Fin n → ℝ, ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f r) (j : Fin n) :
    ∑ x ∈ Icc 1 m, lam x * dterm a β r (ProductFraming.Nest.consideration f x) j = 0 := by
  have hd : HasDerivAt (fun t => ProductFraming.Pricing.totalRevenue m a β lam f
      (Function.update r j t))
      (∑ x ∈ Icc 1 m, lam x * dterm a β r (ProductFraming.Nest.consideration f x) j) (r j) := by
    unfold ProductFraming.Pricing.totalRevenue
    exact HasDerivAt.fun_sum (fun x _ =>
      (rev_hasDeriv a β r (ProductFraming.Nest.consideration f x) j).const_mul (lam x))
  have hmax : IsLocalMax (fun t => ProductFraming.Pricing.totalRevenue m a β lam f
      (Function.update r j t)) (r j) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [Function.update_eq_self]
    exact hopt _
  exact hmax.hasDerivAt_eq_zero hd

/-- L1': if the added products are priced at least at the revenue of the larger set. -/
lemma rev_le_of_subset' {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) {S T : Finset (Fin n)}
    (hST : S ⊆ T) (h : ∀ j ∈ T \ S, ProductFraming.Pricing.revenue a β r T ≤ r j) :
    ProductFraming.Pricing.revenue a β r S ≤ ProductFraming.Pricing.revenue a β r T := by
  set R := ProductFraming.Pricing.revenue a β r T
  rw [rev_le_iff]
  have h1 := rev_mul a β r T
  have hN : ∑ i ∈ T, r i * W a β r i =
      ∑ i ∈ T \ S, r i * W a β r i + ∑ i ∈ S, r i * W a β r i := (Finset.sum_sdiff hST).symm
  have hD : ∑ i ∈ T, W a β r i = ∑ i ∈ T \ S, W a β r i + ∑ i ∈ S, W a β r i :=
    (Finset.sum_sdiff hST).symm
  have h2 : R * ∑ i ∈ T \ S, W a β r i ≤ ∑ i ∈ T \ S, r i * W a β r i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (h j hj) (W_pos a β r j).le)
  rw [hN, hD] at h1
  nlinarith

/-! ## Consequences of the FOC -/

section FOC
variable {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ) (f : Fin n → ℕ) (r : Fin n → ℝ)

noncomputable def Rx (x : ℕ) : ℝ :=
  ProductFraming.Pricing.revenue a β r (ProductFraming.Nest.consideration f x)

noncomputable def gx (x : ℕ) : ℝ :=
  lam x / (1 + ∑ i ∈ ProductFraming.Nest.consideration f x, W a β r i)

lemma mem_cons (j : Fin n) (x : ℕ) :
    j ∈ ProductFraming.Nest.consideration f x ↔ 1 ≤ f j ∧ f j ≤ x := by
  simp [ProductFraming.Nest.consideration]

lemma cons_mono {x y : ℕ} (hxy : x ≤ y) :
    ProductFraming.Nest.consideration f x ⊆ ProductFraming.Nest.consideration f y := by
  intro j hj
  rw [mem_cons] at hj ⊢
  exact ⟨hj.1, hj.2.trans hxy⟩

lemma foc' (hopt : ∀ r' : Fin n → ℝ, ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f r) (j : Fin n) (hj : 1 ≤ f j) :
    ∑ x ∈ Ico (f j) (m + 1), gx a β lam f r x * (1 + β * Rx a β f r x - β * r j) = 0 := by
  have h := foc m a β lam f r hopt j
  have h2 : ∑ x ∈ Icc 1 m, lam x * dterm a β r (ProductFraming.Nest.consideration f x) j =
      ∑ x ∈ (Icc 1 m).filter (fun x => f j ≤ x),
        W a β r j * (gx a β lam f r x * (1 + β * Rx a β f r x - β * r j)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : f j ≤ x
    · have hm : j ∈ ProductFraming.Nest.consideration f x := (mem_cons f j x).mpr ⟨hj, hx⟩
      rw [if_pos hx]
      simp only [dterm, if_pos hm, gx, Rx]
      ring
    · have hm : j ∉ ProductFraming.Nest.consideration f x := fun h' =>
        hx ((mem_cons f j x).mp h').2
      rw [if_neg hx]
      simp only [dterm, if_neg hm, mul_zero]
  have h3 : (Icc 1 m).filter (fun x => f j ≤ x) = Ico (f j) (m + 1) := by
    ext x; simp only [mem_filter, mem_Icc, mem_Ico]; omega
  rw [h2, h3, ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left (W_pos a β r j).ne'

lemma gx_nonneg (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x) (x : ℕ) (hx : x ∈ Icc 1 m) :
    0 ≤ gx a β lam f r x :=
  div_nonneg (hlam x hx) (den_pos a β r _).le

lemma gx_pos (x : ℕ) (hx : 0 < lam x) : 0 < gx a β lam f r x :=
  div_pos hx (den_pos a β r _)

/-- Lemma A -/
lemma foc_lower (hβ : 0 < β) (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x)
    (hopt : ∀ r' : Fin n → ℝ, ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f r) (j : Fin n) (hj : 1 ≤ f j) (c : ℝ)
    (hc : ∀ x ∈ Ico (f j) (m + 1), 0 < lam x → c ≤ Rx a β f r x)
    (hex : ∃ x ∈ Ico (f j) (m + 1), 0 < lam x) : c + 1 / β ≤ r j := by
  by_contra hcon
  have hlt : β * r j < β * c + 1 := by
    have : r j < c + 1 / β := not_le.mp hcon
    have := mul_lt_mul_of_pos_left this hβ
    rw [mul_add, mul_one_div_cancel hβ.ne'] at this
    exact this
  have h := foc' m a β lam f r hopt j hj
  have hpos : 0 < ∑ x ∈ Ico (f j) (m + 1), gx a β lam f r x * (1 + β * Rx a β f r x - β * r j) := by
    apply Finset.sum_pos'
    · intro x hx
      have hx' : x ∈ Icc 1 m := by
        simp only [mem_Ico] at hx; simp only [mem_Icc]; omega
      rcases (hlam x hx').lt_or_eq with hl | hl
      · have := hc x hx hl
        have : 0 < 1 + β * Rx a β f r x - β * r j := by nlinarith
        exact (mul_pos (gx_pos a β lam f r x hl) this).le
      · simp [gx, ← hl]
    · obtain ⟨x, hx, hl⟩ := hex
      refine ⟨x, hx, ?_⟩
      have := hc x hx hl
      have : 0 < 1 + β * Rx a β f r x - β * r j := by nlinarith
      exact mul_pos (gx_pos a β lam f r x hl) this
  linarith

/-- Lemma B: revenues of relevant consideration sets are nondecreasing. -/
lemma R_mono (hβ : 0 < β) (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x)
    (hopt : ∀ r' : Fin n → ℝ, ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f r)
    (x₁ x₂ : ℕ) (h1 : 1 ≤ x₁) (h12 : x₁ ≤ x₂) (h2 : x₂ ≤ m) (hl2 : 0 < lam x₂) :
    Rx a β f r x₁ ≤ Rx a β f r x₂ := by
  set P := (Icc x₁ m).filter (fun x => 0 < lam x)
  have hP : P.Nonempty := ⟨x₂, by simp only [P, mem_filter, mem_Icc]; exact ⟨⟨h12, h2⟩, hl2⟩⟩
  obtain ⟨x', hx'P, hmin⟩ := Finset.exists_min_image P (fun x => Rx a β f r x) hP
  simp only [P, mem_filter, mem_Icc] at hx'P
  have hle : Rx a β f r x₁ ≤ Rx a β f r x' := by
    apply rev_le_of_subset' a β r (cons_mono f hx'P.1.1)
    intro j hj
    rw [mem_sdiff, mem_cons, mem_cons] at hj
    have hfj : x₁ < f j := by
      by_contra h; exact hj.2 ⟨hj.1.1, not_lt.mp h⟩
    have hR := foc_lower m a β lam f r hβ hlam hopt j hj.1.1 (Rx a β f r x')
      (fun x hx hl => hmin x (by
        simp only [P, mem_filter, mem_Icc]; simp only [mem_Ico] at hx
        exact ⟨⟨by omega, by omega⟩, hl⟩))
      ⟨x', by simp only [mem_Ico]; omega, hx'P.2⟩
    have : 0 < 1 / β := by positivity
    unfold Rx at hR
    linarith
  exact hle.trans (hmin x₂ (by simp only [P, mem_filter, mem_Icc]; exact ⟨⟨h12, h2⟩, hl2⟩))

/-- Lemma C -/
lemma price_ge (hβ : 0 < β) (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x)
    (hopt : ∀ r' : Fin n → ℝ, ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f r)
    (j : Fin n) (x : ℕ) (hx1 : 1 ≤ x) (hxj : x < f j)
    (hex : ∃ x' ∈ Ico (f j) (m + 1), 0 < lam x') :
    Rx a β f r x + 1 / β ≤ r j := by
  apply foc_lower m a β lam f r hβ hlam hopt j (by omega) _ _ hex
  intro y hy hl
  simp only [mem_Ico] at hy
  exact R_mono m a β lam f r hβ hlam hopt x y hx1 (by omega) (by omega) hl

/-- Lemma D: page prices are monotone. -/
lemma price_mono (hβ : 0 < β) (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x)
    (hopt : ∀ r' : Fin n → ℝ, ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f r)
    (i k : Fin n) (hi : 1 ≤ f i) (hik : f i < f k)
    (hex : ∃ x' ∈ Ico (f k) (m + 1), 0 < lam x') : r i ≤ r k := by
  by_contra hcon
  have hlt : r k < r i := not_le.mp hcon
  have hFi := foc' m a β lam f r hopt i hi
  have hFk := foc' m a β lam f r hopt k (by omega)
  obtain ⟨x', hx', hl'⟩ := hex
  have hkm : f k ≤ m + 1 := by simp only [mem_Ico] at hx'; omega
  rw [← Finset.sum_Ico_consecutive _ hik.le hkm] at hFi
  have hA : ∑ x ∈ Ico (f i) (f k), gx a β lam f r x * (1 + β * Rx a β f r x - β * r i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro x hx
    simp only [mem_Ico] at hx
    have hxI : x ∈ Icc 1 m := by simp only [mem_Icc]; simp only [mem_Ico] at hx'; omega
    rcases (hlam x hxI).lt_or_eq with hl | hl
    · have := price_ge m a β lam f r hβ hlam hopt k x (by omega) hx.2 ⟨x', hx', hl'⟩
      have h3 : β * (Rx a β f r x + 1 / β) ≤ β * r k := mul_le_mul_of_nonneg_left this hβ.le
      rw [mul_add, mul_one_div_cancel hβ.ne'] at h3
      have : 1 + β * Rx a β f r x - β * r i ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (gx_pos a β lam f r x hl).le this
    · simp [gx, ← hl]
  have hB : ∑ x ∈ Ico (f k) (m + 1), gx a β lam f r x * (1 + β * Rx a β f r x - β * r i) =
      ∑ x ∈ Ico (f k) (m + 1), gx a β lam f r x * (1 + β * Rx a β f r x - β * r k) -
        β * (r i - r k) * ∑ x ∈ Ico (f k) (m + 1), gx a β lam f r x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => by ring)
  have hgs : 0 < ∑ x ∈ Ico (f k) (m + 1), gx a β lam f r x := by
    apply Finset.sum_pos'
    · intro x hx
      simp only [mem_Ico] at hx
      exact gx_nonneg m a β lam f r hlam x (by simp only [mem_Icc]; omega)
    · exact ⟨x', hx', gx_pos a β lam f r x' hl'⟩
  have : 0 < β * (r i - r k) := mul_pos hβ (by linarith)
  rw [hB, hFk] at hFi
  nlinarith

end FOC

/-! ## Existence of optimal prices for a fixed framing -/

lemma rev_cont {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (S : Finset (Fin n)) :
    Continuous (fun r : Fin n → ℝ => ProductFraming.Pricing.revenue a β r S) := by
  have h : (fun r : Fin n → ℝ => ProductFraming.Pricing.revenue a β r S) =
      fun r => (∑ i ∈ S, r i * Real.exp (a i - β * r i)) /
        (1 + ∑ i ∈ S, Real.exp (a i - β * r i)) := by
    funext r; rw [rev_eq]; rfl
  rw [h]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro r; exact (den_pos a β r S).ne'

lemma tr_cont {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ) (f : Fin n → ℕ) :
    Continuous (fun r => ProductFraming.Pricing.totalRevenue m a β lam f r) := by
  unfold ProductFraming.Pricing.totalRevenue
  exact continuous_finsetSum _ (fun x _ => continuous_const.mul (rev_cont a β _))

lemma tr_le_of {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x) (f f' : Fin n → ℕ) (r r' : Fin n → ℝ)
    (h : ∀ x ∈ Icc 1 m, 0 < lam x →
      ProductFraming.Pricing.revenue a β r (ProductFraming.Nest.consideration f x) ≤
      ProductFraming.Pricing.revenue a β r' (ProductFraming.Nest.consideration f' x)) :
    ProductFraming.Pricing.totalRevenue m a β lam f r ≤
      ProductFraming.Pricing.totalRevenue m a β lam f' r' := by
  unfold ProductFraming.Pricing.totalRevenue
  apply Finset.sum_le_sum
  intro x hx
  rcases (hlam x hx).lt_or_eq with hl | hl
  · exact mul_le_mul_of_nonneg_left (h x hx hl) hl.le
  · rw [← hl, zero_mul, zero_mul]

lemma tr_hasDeriv {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ) (f : Fin n → ℕ)
    (r : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    HasDerivAt (fun s => ProductFraming.Pricing.totalRevenue m a β lam f (Function.update r j s))
      (∑ x ∈ Icc 1 m, lam x *
        dterm a β (Function.update r j t) (ProductFraming.Nest.consideration f x) j) t := by
  have key := fun x =>
    rev_hasDeriv a β (Function.update r j t) (ProductFraming.Nest.consideration f x) j
  simp only [Function.update_idem, Function.update_self] at key
  unfold ProductFraming.Pricing.totalRevenue
  exact HasDerivAt.fun_sum (fun x _ => (key x).const_mul (lam x))

lemma dterm_nonpos {n : ℕ} (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (r : Fin n → ℝ)
    (S : Finset (Fin n)) (j : Fin n) (hj : Kb a β + 1 / β ≤ r j) : dterm a β r S j ≤ 0 := by
  unfold dterm
  split_ifs
  · apply mul_nonpos_of_nonneg_of_nonpos
    · exact div_nonneg (W_pos a β r j).le (den_pos a β r S).le
    · have h1 := rev_le_Kb a hβ r S
      have h2 : β * (Kb a β + 1 / β) ≤ β * r j := mul_le_mul_of_nonneg_left hj hβ.le
      rw [mul_add, mul_one_div_cancel hβ.ne'] at h2
      nlinarith
  · exact le_refl 0

lemma tr_clamp1 {n : ℕ} (m : ℕ) (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x) (f : Fin n → ℕ) (r : Fin n → ℝ) (j : Fin n) :
    ProductFraming.Pricing.totalRevenue m a β lam f r ≤
      ProductFraming.Pricing.totalRevenue m a β lam f
        (Function.update r j (min (r j) (Kb a β + 1 / β))) := by
  by_cases hr : r j ≤ Kb a β + 1 / β
  · rw [min_eq_left hr, Function.update_eq_self]
  · rw [not_le] at hr
    rw [min_eq_right hr.le]
    have hanti : AntitoneOn
        (fun s => ProductFraming.Pricing.totalRevenue m a β lam f (Function.update r j s))
        (Set.Ici (Kb a β + 1 / β)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici _)
      · exact fun s _ => (tr_hasDeriv m a β lam f r j s).continuousAt.continuousWithinAt
      · exact fun s _ => (tr_hasDeriv m a β lam f r j s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        rw [(tr_hasDeriv m a β lam f r j s).deriv]
        apply Finset.sum_nonpos
        intro x hx
        apply mul_nonpos_of_nonneg_of_nonpos (hlam x hx)
        apply dterm_nonpos a hβ
        rw [Function.update_self]; exact le_of_lt hs
    have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr.le) hr.le
    simp only [Function.update_eq_self] at this
    exact this

lemma tr_clamp {n : ℕ} (m : ℕ) (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x) (f : Fin n → ℕ) (r : Fin n → ℝ) :
    ProductFraming.Pricing.totalRevenue m a β lam f r ≤
      ProductFraming.Pricing.totalRevenue m a β lam f (fun i => min (r i) (Kb a β + 1 / β)) := by
  classical
  have key : ∀ s : Finset (Fin n), ProductFraming.Pricing.totalRevenue m a β lam f r ≤
      ProductFraming.Pricing.totalRevenue m a β lam f
        (fun i => if i ∈ s then min (r i) (Kb a β + 1 / β) else r i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      refine ih.trans ?_
      have he : (fun i => if i ∈ insert j s then min (r i) (Kb a β + 1 / β) else r i) =
          Function.update (fun i => if i ∈ s then min (r i) (Kb a β + 1 / β) else r i) j
            (min ((fun i => if i ∈ s then min (r i) (Kb a β + 1 / β) else r i) j)
              (Kb a β + 1 / β)) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [Finset.mem_insert, hij]
      rw [he]
      exact tr_clamp1 m a hβ lam hlam f _ j
  simpa using key Finset.univ

lemma exists_opt {n : ℕ} (m : ℕ) (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x) (f : Fin n → ℕ) :
    ∃ r : Fin n → ℝ, ∀ r' : Fin n → ℝ, ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f r := by
  have hB : 0 ≤ Kb a β + 1 / β := by
    have := Kb_nonneg a hβ; have : 0 < 1 / β := by positivity
    linarith
  obtain ⟨r0, _, hmax⟩ :=
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc (a := (0:ℝ)) (b := Kb a β + 1 / β))).exists_isMaxOn
      ⟨fun _ => 0, fun i _ => ⟨le_refl 0, hB⟩⟩ (tr_cont m a β lam f).continuousOn
  refine ⟨r0, fun r' => ?_⟩
  have h1 : ProductFraming.Pricing.totalRevenue m a β lam f r' ≤
      ProductFraming.Pricing.totalRevenue m a β lam f (fun i => max (r' i) 0) :=
    tr_le_of m a β lam hlam f f r' _ (fun x _ _ => rev_le_pos a hβ r' _)
  have h2 := tr_clamp m a hβ lam hlam f (fun i => max (r' i) 0)
  have h3 : (fun i => min (max (r' i) 0) (Kb a β + 1 / β)) ∈
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) (Kb a β + 1 / β)) :=
    fun i _ => ⟨le_min (le_max_right _ _) hB, min_le_right _ _⟩
  exact h1.trans (h2.trans (isMaxOn_iff.mp hmax _ h3))

/-! ## Moves -/

lemma rev_update_notin {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ) (S : Finset (Fin n))
    (j : Fin n) (hj : j ∉ S) (t : ℝ) :
    ProductFraming.Pricing.revenue a β (Function.update r j t) S =
      ProductFraming.Pricing.revenue a β r S := by
  rw [rev_eq, rev_eq]
  have h1 : ∀ i ∈ S, Function.update r j t i = r i := by
    intro i hi
    exact Function.update_of_ne (fun h => hj (by rw [← h]; exact hi)) _ _
  have h2 : ∀ i ∈ S, W a β (Function.update r j t) i = W a β r i := by
    intro i hi; simp only [W, h1 i hi]
  rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl (fun i hi => by rw [h1 i hi, h2 i hi])]

lemma sum_two {n : ℕ} (S : Finset (Fin n)) (i k : Fin n) (hik : i ≠ k) (g : Fin n → ℝ)
    (hg : ∀ j, j ≠ i → j ≠ k → g j = 0) :
    ∑ j ∈ S, g j = (if i ∈ S then g i else 0) + (if k ∈ S then g k else 0) := by
  have h : ∀ j, g j = (if j = i then g j else 0) + (if j = k then g j else 0) := by
    intro j
    by_cases h1 : j = i
    · subst h1; simp [hik]
    · by_cases h2 : j = k
      · subst h2; simp [h1]
      · simp [h1, h2, hg j h1 h2]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

lemma sum_cons_swap {n : ℕ} (f : Fin n → ℕ) (i k : Fin n) (x : ℕ) (F : Fin n → ℝ) :
    ∑ j ∈ ProductFraming.Nest.consideration (fun j => f (Equiv.swap i k j)) x, F j =
      ∑ j ∈ ProductFraming.Nest.consideration f x, F (Equiv.swap i k j) := by
  apply Finset.sum_nbij' (Equiv.swap i k) (Equiv.swap i k)
  · intro j hj
    simp only [ProductFraming.Nest.consideration, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj ⊢
    exact hj
  · intro j hj
    simp only [ProductFraming.Nest.consideration, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj ⊢
    simpa [Equiv.swap_apply_self] using hj
  · intro j _; exact Equiv.swap_apply_self i k j
  · intro j _; exact Equiv.swap_apply_self i k j
  · intro j _; simp [Equiv.swap_apply_self]

lemma swap_diff {n : ℕ} (S : Finset (Fin n)) (i k : Fin n) (hik : i ≠ k) (h : Fin n → ℝ) :
    ∑ j ∈ S, h (Equiv.swap i k j) = ∑ j ∈ S, h j +
      ((if i ∈ S then h k - h i else 0) + (if k ∈ S then h i - h k else 0)) := by
  have := sum_two S i k hik (fun j => h (Equiv.swap i k j) - h j)
    (fun j h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2])
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Finset.sum_sub_distrib] at this
  linarith

noncomputable def pos (m : ℕ) (t : ℕ) : ℝ := if t = 0 then (m : ℝ) + 1 else (t : ℝ)

noncomputable def Cc {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑ j, |a j| + 1

noncomputable def Phi {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (f : Fin n → ℕ) : ℝ :=
  ∑ j, ((m : ℝ) + 1 - pos m (f j)) * (a j + Cc a)

lemma aC_pos {n : ℕ} (a : Fin n → ℝ) (j : Fin n) : 0 < a j + Cc a := by
  unfold Cc
  have h1 : |a j| ≤ ∑ l, |a l| :=
    Finset.single_le_sum (fun l _ => abs_nonneg (a l)) (Finset.mem_univ j)
  have h2 := neg_abs_le (a j)
  linarith

lemma phi_update {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (f : Fin n → ℕ) (i : Fin n) (y : ℕ)
    (hy1 : 1 ≤ y) (hym : y ≤ m) (hi : f i = 0 ∨ y < f i) :
    Phi m a f < Phi m a (Function.update f i y) := by
  unfold Phi
  rw [← sub_pos, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp only [Function.update_self]
    have hp : pos m y < pos m (f i) := by
      unfold pos
      rw [if_neg (by omega)]
      rcases hi with h | h
      · rw [if_pos h]
        have : (y : ℝ) ≤ m := by exact_mod_cast hym
        linarith
      · rw [if_neg (by omega)]; exact_mod_cast h
    have := aC_pos a i
    nlinarith
  · intro j _ hj; rw [Function.update_of_ne hj]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

lemma phi_swap {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (f : Fin n → ℕ) (i k : Fin n) (hik : i ≠ k)
    (hi : 1 ≤ f i) (him : f i ≤ m) (hk : f k = 0 ∨ f i < f k) (ha : a i < a k) :
    Phi m a f < Phi m a (fun j => f (Equiv.swap i k j)) := by
  unfold Phi
  rw [← sub_pos, ← Finset.sum_sub_distrib,
    sum_two univ i k hik _ (fun j h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2])]
  simp only [Finset.mem_univ, if_true, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hp : pos m (f i) < pos m (f k) := by
    unfold pos
    rw [if_neg (by omega)]
    rcases hk with h | h
    · rw [if_pos h]
      have : (f i : ℝ) ≤ m := by exact_mod_cast him
      linarith
    · rw [if_neg (by omega)]; exact_mod_cast h
  nlinarith [mul_pos (sub_pos.mpr hp) (sub_pos.mpr ha)]

lemma feas_update {n : ℕ} (m p : ℕ) (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f)
    (y : ℕ) (hy : y ∈ Icc 1 m) (hc : (univ.filter (fun j => f j = y)).card < p) (i : Fin n) :
    ProductFraming.Trunc.Feasible m p (Function.update f i y) := by
  unfold ProductFraming.Trunc.Feasible ProductFraming.Nest.IsFeasibleFraming at hf ⊢
  obtain ⟨hf1, hf2⟩ := hf
  refine ⟨fun j => ?_, fun z hz => ?_⟩
  · by_cases hj : j = i
    · rw [hj, Function.update_self]; exact (Finset.mem_Icc.mp hy).2
    · rw [Function.update_of_ne hj]; exact hf1 j
  · by_cases hzy : z = y
    · rw [hzy]
      calc (univ.filter (fun j => Function.update f i y j = y)).card
          ≤ (insert i (univ.filter (fun j => f j = y))).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
            by_cases hji : j = i
            · left; exact hji
            · right; rwa [Function.update_of_ne hji] at hj
        _ ≤ (univ.filter (fun j => f j = y)).card + 1 := Finset.card_insert_le _ _
        _ ≤ p := Nat.succ_le_of_lt hc
    · calc (univ.filter (fun j => Function.update f i y j = z)).card
          ≤ (univ.filter (fun j => f j = z)).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            by_cases hji : j = i
            · rw [hji, Function.update_self] at hj; exact absurd hj.symm hzy
            · rwa [Function.update_of_ne hji] at hj
        _ ≤ p := hf2 z hz

lemma feas_swap {n : ℕ} (m p : ℕ) (f : Fin n → ℕ) (hf : ProductFraming.Trunc.Feasible m p f)
    (i k : Fin n) : ProductFraming.Trunc.Feasible m p (fun j => f (Equiv.swap i k j)) := by
  unfold ProductFraming.Trunc.Feasible ProductFraming.Nest.IsFeasibleFraming at hf ⊢
  refine ⟨fun j => hf.1 _, fun z hz => ?_⟩
  calc _ = (univ.filter (fun j => f j = z)).card := by
        apply Finset.card_nbij' (Equiv.swap i k) (Equiv.swap i k)
        · intro j hj; simpa using hj
        · intro j hj; simpa [Equiv.swap_apply_self] using hj
        · intro j _; exact Equiv.swap_apply_self i k j
        · intro j _; exact Equiv.swap_apply_self i k j
    _ ≤ p := hf.2 z hz

section Moves
open ProductFraming.Pricing

lemma rev_move1 {n : ℕ} (m : ℕ) (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x) (f : Fin n → ℕ) (r : Fin n → ℝ)
    (hopt : ∀ r' : Fin n → ℝ, totalRevenue m a β lam f r' ≤ totalRevenue m a β lam f r)
    (y : ℕ) (hy1 : 1 ≤ y) (i : Fin n) (hi : f i = 0 ∨ y < f i) :
    ∃ r' : Fin n → ℝ, totalRevenue m a β lam f r ≤
      totalRevenue m a β lam (Function.update f i y) r' := by
  have hcons : ∀ x, ProductFraming.Nest.consideration (Function.update f i y) x =
      if y ≤ x then insert i (ProductFraming.Nest.consideration f x)
      else ProductFraming.Nest.consideration f x := by
    intro x
    ext j
    split_ifs with hx
    · rw [Finset.mem_insert, mem_cons, mem_cons]
      by_cases hji : j = i
      · rw [hji, Function.update_self]; simp [hy1, hx]
      · rw [Function.update_of_ne hji]; simp [hji]
    · rw [mem_cons, mem_cons]
      by_cases hji : j = i
      · rw [hji, Function.update_self]
        constructor <;> rintro ⟨h1, h2⟩ <;> omega
      · rw [Function.update_of_ne hji]
  by_cases hrel : 1 ≤ f i ∧ ∃ x' ∈ Ico (f i) (m + 1), 0 < lam x'
  · refine ⟨r, tr_le_of m a β lam hlam f _ r r (fun x hx hl => ?_)⟩
    have hx' := Finset.mem_Icc.mp hx
    rw [hcons x]
    split_ifs with hyx
    · by_cases hix : i ∈ ProductFraming.Nest.consideration f x
      · rw [Finset.insert_eq_of_mem hix]
      · have hxf : x < f i := by rw [mem_cons] at hix; omega
        apply rev_le_of_subset a β r (Finset.subset_insert _ _)
        intro j hj
        rw [Finset.mem_sdiff, Finset.mem_insert] at hj
        rcases hj.1 with h | h
        · rw [h]
          have := price_ge m a β lam f r hβ hlam hopt i x hx'.1 hxf hrel.2
          have : 0 < 1 / β := by positivity
          unfold Rx at *
          linarith
        · exact absurd h hj.2
    · exact le_rfl
  · refine ⟨Function.update r i (Kb a β), tr_le_of m a β lam hlam f _ r _ (fun x hx hl => ?_)⟩
    have hx' := Finset.mem_Icc.mp hx
    have hix : i ∉ ProductFraming.Nest.consideration f x := by
      intro h; rw [mem_cons] at h
      exact hrel ⟨h.1, x, Finset.mem_Ico.mpr ⟨h.2, by omega⟩, hl⟩
    have heq := rev_update_notin a β r _ i hix (Kb a β)
    rw [hcons x]
    split_ifs with hyx
    · rw [← heq]
      apply rev_le_of_subset a β _ (Finset.subset_insert _ _)
      intro j hj
      rw [Finset.mem_sdiff, Finset.mem_insert] at hj
      rcases hj.1 with h | h
      · rw [h, Function.update_self]; exact rev_le_Kb a hβ _ _
      · exact absurd h hj.2
    · exact heq.ge

lemma rev_move2 {n : ℕ} (m : ℕ) (a : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ x ∈ Icc 1 m, 0 ≤ lam x) (f : Fin n → ℕ) (r : Fin n → ℝ)
    (hopt : ∀ r' : Fin n → ℝ, totalRevenue m a β lam f r' ≤ totalRevenue m a β lam f r)
    (i k : Fin n) (hik : i ≠ k) (hi : 1 ≤ f i) (hk : f k = 0 ∨ f i < f k) (ha : a i < a k) :
    ∃ r' : Fin n → ℝ, totalRevenue m a β lam f r ≤
      totalRevenue m a β lam (fun j => f (Equiv.swap i k j)) r' := by
  have hki : ∀ x, k ∈ ProductFraming.Nest.consideration f x →
      i ∈ ProductFraming.Nest.consideration f x := by
    intro x hx; rw [mem_cons] at hx ⊢; omega
  have hWi := W_pos a β r i
  have hWk := W_pos a β r k
  by_cases hB : (¬ (1 ≤ f k ∧ ∃ x' ∈ Ico (f k) (m + 1), 0 < lam x')) ∨ W a β r k ≤ W a β r i
  · obtain ⟨r', hr'⟩ : ∃ r' : Fin n → ℝ,
        ∀ j, r' j = r (Equiv.swap i k j) + (a j - a (Equiv.swap i k j)) / β := ⟨_, fun j => rfl⟩
    have hr : ∀ j, r' (Equiv.swap i k j) = r j + (a (Equiv.swap i k j) - a j) / β := by
      intro j; rw [hr', Equiv.swap_apply_self]
    have hW : ∀ j, W a β r' (Equiv.swap i k j) = W a β r j := by
      intro j; unfold W; rw [hr j]; congr 1; field_simp; ring
    refine ⟨r', tr_le_of m a β lam hlam f _ r r' (fun x hx hl => ?_)⟩
    have s1 : ∑ j ∈ ProductFraming.Nest.consideration (fun j => f (Equiv.swap i k j)) x,
        W a β r' j = ∑ j ∈ ProductFraming.Nest.consideration f x, W a β r j := by
      rw [sum_cons_swap f i k x (fun j => W a β r' j)]
      exact Finset.sum_congr rfl (fun j _ => hW j)
    have s2 : ∑ j ∈ ProductFraming.Nest.consideration (fun j => f (Equiv.swap i k j)) x,
        r' j * W a β r' j = ∑ j ∈ ProductFraming.Nest.consideration f x, r j * W a β r j +
          ∑ j ∈ ProductFraming.Nest.consideration f x,
            (a (Equiv.swap i k j) - a j) / β * W a β r j := by
      rw [sum_cons_swap f i k x (fun j => r' j * W a β r' j), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hr j, hW j]; ring
    have s3 := sum_two (ProductFraming.Nest.consideration f x) i k hik
      (fun j => (a (Equiv.swap i k j) - a j) / β * W a β r j)
      (fun j h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2])
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at s3
    have h1 := rev_mul a β r (ProductFraming.Nest.consideration f x)
    have hc : 0 < (a k - a i) / β := div_pos (by linarith) hβ
    have hcorr : 0 ≤ (if i ∈ ProductFraming.Nest.consideration f x then
          (a k - a i) / β * W a β r i else 0) +
        (if k ∈ ProductFraming.Nest.consideration f x then
          (a i - a k) / β * W a β r k else 0) := by
      by_cases hkS : k ∈ ProductFraming.Nest.consideration f x
      · have hiS := hki x hkS
        rw [if_pos hiS, if_pos hkS]
        have hWW : W a β r k ≤ W a β r i := by
          rcases hB with hB | hB
          · exfalso; apply hB
            have hkS' := (mem_cons f k x).mp hkS
            have := Finset.mem_Icc.mp hx
            exact ⟨hkS'.1, x, Finset.mem_Ico.mpr ⟨hkS'.2, by omega⟩, hl⟩
          · exact hB
        have : (a i - a k) / β = -((a k - a i) / β) := by ring
        rw [this]; nlinarith
      · rw [if_neg hkS, add_zero]
        split_ifs
        · exact (mul_pos hc hWi).le
        · exact le_rfl
    rw [le_rev_iff, s1, s2]
    linarith
  · rw [not_or, not_not, not_le] at hB
    obtain ⟨hrel, hWlt⟩ := hB
    refine ⟨r, tr_le_of m a β lam hlam f _ r r (fun x hx hl => ?_)⟩
    have hx1 := (Finset.mem_Icc.mp hx).1
    have s1 : ∑ j ∈ ProductFraming.Nest.consideration (fun j => f (Equiv.swap i k j)) x,
        W a β r j = ∑ j ∈ ProductFraming.Nest.consideration f x, W a β r j +
          ((if i ∈ ProductFraming.Nest.consideration f x then W a β r k - W a β r i else 0) +
           (if k ∈ ProductFraming.Nest.consideration f x then W a β r i - W a β r k else 0)) := by
      rw [sum_cons_swap f i k x (fun j => W a β r j)]
      exact swap_diff _ i k hik (fun j => W a β r j)
    have s2 : ∑ j ∈ ProductFraming.Nest.consideration (fun j => f (Equiv.swap i k j)) x,
        r j * W a β r j = ∑ j ∈ ProductFraming.Nest.consideration f x, r j * W a β r j +
          ((if i ∈ ProductFraming.Nest.consideration f x then
              r k * W a β r k - r i * W a β r i else 0) +
           (if k ∈ ProductFraming.Nest.consideration f x then
              r i * W a β r i - r k * W a β r k else 0)) := by
      rw [sum_cons_swap f i k x (fun j => r j * W a β r j)]
      exact swap_diff _ i k hik (fun j => r j * W a β r j)
    have h1 := rev_mul a β r (ProductFraming.Nest.consideration f x)
    rw [le_rev_iff, s1, s2]
    by_cases hkS : k ∈ ProductFraming.Nest.consideration f x
    · simp only [if_pos (hki x hkS), if_pos hkS]
      nlinarith
    · simp only [if_neg hkS, add_zero]
      by_cases hiS : i ∈ ProductFraming.Nest.consideration f x
      · simp only [if_pos hiS]
        have hxk : x < f k := by rw [mem_cons] at hkS; omega
        have hC := price_ge m a β lam f r hβ hlam hopt k x hx1 hxk hrel.2
        have hD := price_mono m a β lam f r hβ hlam hopt i k hi (by omega) hrel.2
        unfold Rx at hC
        have hb : 0 < 1 / β := by positivity
        nlinarith [mul_pos (sub_pos.mpr hWlt) (show 0 < r k -
            ProductFraming.Pricing.revenue a β r (ProductFraming.Nest.consideration f x) by linarith),
          mul_nonneg hWi.le (sub_nonneg.mpr hD)]
      · simp only [if_neg hiS, add_zero]
        linarith

end Moves

lemma card_fill {n : ℕ} (m p : ℕ) (hp : 1 ≤ p) (f : Fin n → ℕ)
    (hf : ProductFraming.Trunc.Feasible m p f)
    (hno : ∀ y ∈ Icc 1 m, (univ.filter (fun j => f j = y)).card < p →
      ∀ i, 1 ≤ f i ∧ f i ≤ y) :
    ∀ x, x ≤ m → (ProductFraming.Nest.consideration f x).card = min n (x * p) := by
  unfold ProductFraming.Trunc.Feasible ProductFraming.Nest.IsFeasibleFraming at hf
  intro x
  induction x with
  | zero =>
    intro _
    have h0 : ProductFraming.Nest.consideration f 0 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj; rw [mem_cons] at hj; omega
    rw [h0]; simp
  | succ x ih =>
    intro hx
    have ih' := ih (by omega)
    have hU : ProductFraming.Nest.consideration f (x + 1) =
        ProductFraming.Nest.consideration f x ∪ univ.filter (fun j => f j = x + 1) := by
      ext j
      rw [Finset.mem_union, mem_cons, mem_cons, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      omega
    have hD : Disjoint (ProductFraming.Nest.consideration f x)
        (univ.filter (fun j => f j = x + 1)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      rw [mem_cons] at h1
      rw [Finset.mem_filter] at h2
      omega
    have hcard := Finset.card_union_of_disjoint hD
    rw [← hU] at hcard
    have hle := Finset.card_le_univ (ProductFraming.Nest.consideration f (x + 1))
    rw [Fintype.card_fin] at hle
    have hpage := hf.2 (x + 1) (by simp only [Finset.mem_Icc]; omega)
    have hmul : (x + 1) * p = x * p + p := by ring
    rw [hmul]
    rcases Nat.lt_or_ge (univ.filter (fun j => f j = x + 1)).card p with hc | hc
    · have hall := hno (x + 1) (by simp only [Finset.mem_Icc]; omega) hc
      have huniv : ProductFraming.Nest.consideration f (x + 1) = univ := by
        ext j
        simp only [Finset.mem_univ, iff_true]
        rw [mem_cons]
        exact hall j
      have hn : (ProductFraming.Nest.consideration f (x + 1)).card = n := by
        rw [huniv, Finset.card_univ, Fintype.card_fin]
      generalize x * p = q at *
      omega
    · generalize x * p = q at *
      omega

end PF6

open ProductFraming.Pricing Finset in
theorem solution {n m p : ℕ} (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (hβ : 0 < β) (hm : 1 ≤ m) (hp : 1 ≤ p) (hlam : ProductFraming.Nest.IsPageLaw m lam) :
    ∃ f : Fin n → ℕ, ∃ r : Fin n → ℝ, ProductFraming.Trunc.Feasible m p f ∧
      (∀ (f' : Fin n → ℕ) (r' : Fin n → ℝ), ProductFraming.Trunc.Feasible m p f' →
        totalRevenue m a β lam f' r' ≤ totalRevenue m a β lam f r) ∧
      (∀ x ∈ Icc 1 m, (ProductFraming.Nest.consideration f x).card = min n (x * p)) ∧
      (∀ i k : Fin n, 1 ≤ f i → (f k = 0 ∨ f i < f k) → a k ≤ a i) := by
  classical
  have hl0 := hlam.1
  choose ro hro using fun f => PF6.exists_opt m a hβ lam hl0 f
  let FF : Finset (Fin n → ℕ) :=
    (Finset.univ.image (fun g : Fin n → Fin (m + 1) => fun i => (g i : ℕ))).filter
      (fun f => ProductFraming.Trunc.Feasible m p f)
  have hFF : ∀ f, f ∈ FF ↔ ProductFraming.Trunc.Feasible m p f := by
    intro f
    simp only [FF, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨fun i => ⟨f i, Nat.lt_succ_of_le (h.1 i)⟩, rfl⟩, h⟩
  have hzero : ProductFraming.Trunc.Feasible m p (fun _ : Fin n => 0) := by
    unfold ProductFraming.Trunc.Feasible ProductFraming.Nest.IsFeasibleFraming
    refine ⟨fun _ => Nat.zero_le _, fun x hx => ?_⟩
    refine le_trans (le_of_eq (Finset.card_eq_zero.mpr ?_)) (Nat.zero_le p)
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ h
    have h' : (0 : ℕ) = x := h
    have := (Finset.mem_Icc.mp hx).1
    omega
  have hne : FF.Nonempty := ⟨fun _ => 0, (hFF _).mpr hzero⟩
  obtain ⟨f1, hf1, hmax1⟩ := FF.exists_max_image (fun f => totalRevenue m a β lam f (ro f)) hne
  let GG := FF.filter (fun f => totalRevenue m a β lam f1 (ro f1) ≤ totalRevenue m a β lam f (ro f))
  have hGG : ∀ f, f ∈ GG ↔ f ∈ FF ∧
      totalRevenue m a β lam f1 (ro f1) ≤ totalRevenue m a β lam f (ro f) := by
    intro f; simp only [GG, Finset.mem_filter]
  have hGne : GG.Nonempty := ⟨f1, (hGG f1).mpr ⟨hf1, le_rfl⟩⟩
  obtain ⟨f0, hf0, hmax0⟩ := GG.exists_max_image (fun f => PF6.Phi m a f) hGne
  rw [hGG] at hf0
  have hf0F : ProductFraming.Trunc.Feasible m p f0 := (hFF f0).mp hf0.1
  have hopt0 := hro f0
  have hglob : ∀ (f' : Fin n → ℕ) (r' : Fin n → ℝ), ProductFraming.Trunc.Feasible m p f' →
      totalRevenue m a β lam f' r' ≤ totalRevenue m a β lam f0 (ro f0) := by
    intro f' r' hf'
    exact (hro f' r').trans ((hmax1 f' ((hFF f').mpr hf')).trans hf0.2)
  have hnomove : ∀ (f' : Fin n → ℕ) (r' : Fin n → ℝ), ProductFraming.Trunc.Feasible m p f' →
      totalRevenue m a β lam f0 (ro f0) ≤ totalRevenue m a β lam f' r' →
      PF6.Phi m a f' ≤ PF6.Phi m a f0 := by
    intro f' r' hf' hle
    apply hmax0
    rw [hGG]
    exact ⟨(hFF f').mpr hf', hf0.2.trans (hle.trans (hro f' r'))⟩
  refine ⟨f0, ro f0, hf0F, hglob, ?_, ?_⟩
  · have hno : ∀ y ∈ Icc 1 m, (univ.filter (fun j => f0 j = y)).card < p →
        ∀ i, 1 ≤ f0 i ∧ f0 i ≤ y := by
      intro y hy hc i
      by_contra hcon
      have hi : f0 i = 0 ∨ y < f0 i := by omega
      have hy' := Finset.mem_Icc.mp hy
      obtain ⟨r', hr'⟩ := PF6.rev_move1 m a hβ lam hl0 f0 (ro f0) hopt0 y hy'.1 i hi
      have h1 := hnomove _ r' (PF6.feas_update m p f0 hf0F y hy hc i) hr'
      have h2 := PF6.phi_update m a f0 i y hy'.1 hy'.2 hi
      linarith
    intro x hx
    exact PF6.card_fill m p hp f0 hf0F hno x (Finset.mem_Icc.mp hx).2
  · intro i k hi hk
    by_contra hcon
    rw [not_le] at hcon
    have hik : i ≠ k := by
      rintro rfl; omega
    obtain ⟨r', hr'⟩ := PF6.rev_move2 m a hβ lam hl0 f0 (ro f0) hopt0 i k hik hi hk hcon
    have h1 := hnomove _ r' (PF6.feas_swap m p f0 hf0F i k) hr'
    have h2 := PF6.phi_swap m a f0 i k hik hi (hf0F.1 i) hk hcon
    linarith
