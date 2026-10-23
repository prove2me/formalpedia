-- Prove2me | solution 1 for StaticReusable.Guarantee.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:24:34.701389+00:00
-- url     : https://prove2.me/submissions/653b0c77-ed99-4794-adeb-526802efed26

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace SolSRGL1
open StaticReusable.Guarantee

lemma sum_range_split (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

lemma a_succ (C k : ℕ) (hk : k ≤ C) : a C (k + 1) = ((C : ℝ) - k) * a C k := by
  unfold a
  rw [Nat.descFactorial_succ]
  push_cast [Nat.cast_sub hk]
  ring

lemma weight_eq (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) (k : ℕ) :
    weight C μ lam k = a C k * ∏ j ∈ Finset.Icc (k + 1) C, lam j / μ := rfl

/-- auxiliary weight: the coefficient of `ℓ` in the weight of a state `k < i` after
replacing `λ_i` by `ℓ`. -/
noncomputable def uu (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) (i k : ℕ) : ℝ :=
  a C k * (∏ j ∈ (Finset.Icc (k + 1) C).erase i, lam j / μ) / μ

lemma weight_update_lt {C : ℕ} {μ : ℝ} (lam : ℕ → ℝ) {i k : ℕ} (ℓ : ℝ) (hk : k < i)
    (hi : i ≤ C) : weight C μ (Function.update lam i ℓ) k = ℓ * uu C μ lam i k := by
  rw [weight_eq]
  have hmem : i ∈ Finset.Icc (k + 1) C := by simp only [Finset.mem_Icc]; omega
  rw [← Finset.mul_prod_erase _ _ hmem, Function.update_self]
  have : ∏ j ∈ (Finset.Icc (k + 1) C).erase i, Function.update lam i ℓ j / μ =
      ∏ j ∈ (Finset.Icc (k + 1) C).erase i, lam j / μ := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this]
  unfold uu
  ring

lemma weight_update_ge {C : ℕ} {μ : ℝ} (lam : ℕ → ℝ) {i k : ℕ} (ℓ : ℝ) (hk : i ≤ k) :
    weight C μ (Function.update lam i ℓ) k = weight C μ lam k := by
  rw [weight_eq, weight_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  rw [Function.update_of_ne (by omega)]

lemma weight_succ {C : ℕ} {μ : ℝ} (hμ : 0 < μ) (lam : ℕ → ℝ) (i : ℕ) (hi : i < C) :
    lam (i + 1) * weight C μ lam (i + 1) = μ * ((C : ℝ) - i) * weight C μ lam i := by
  rw [weight_eq, weight_eq, a_succ C i hi.le]
  have hI : Finset.Icc (i + 1) C = insert (i + 1) (Finset.Icc (i + 1 + 1) C) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnm : (i + 1) ∉ Finset.Icc (i + 1 + 1) C := by simp
  rw [hI, Finset.prod_insert hnm]
  field_simp

lemma weight_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (i : ℕ) : 0 ≤ weight C μ lam i := by
  unfold weight
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have := (hlam j (by simp only [Finset.mem_Icc]; omega)).1
  positivity

lemma weight_C_pos {C : ℕ} {μ : ℝ} (lam : ℕ → ℝ) : 0 < weight C μ lam C := by
  unfold weight
  have : Finset.Icc (C + 1) C = ∅ := by ext; simp
  rw [this, Finset.prod_empty, mul_one]
  exact_mod_cast Nat.descFactorial_self C ▸ Nat.factorial_pos C

lemma total_pos {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ) :
    0 < ∑ k ∈ Finset.range (C + 1), weight C μ lam k := by
  have h := Finset.single_le_sum (f := fun k => weight C μ lam k)
    (fun k _ => weight_nonneg hμ hlam k) (Finset.self_mem_range_succ C)
  linarith [weight_C_pos (C := C) (μ := μ) lam]

lemma uu_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (i k : ℕ) : 0 ≤ uu C μ lam i k := by
  unfold uu
  apply div_nonneg _ hμ.le
  apply mul_nonneg (by unfold a; positivity)
  apply Finset.prod_nonneg
  intro j hj
  have hj' := Finset.mem_of_mem_erase hj
  simp only [Finset.mem_Icc] at hj'
  have := (hlam j (by simp only [Finset.mem_Icc]; omega)).1
  positivity

/-- value times total weight = weighted reward. -/
lemma value_mul_total {C : ℕ} {μ Λ c α₁ α₂ α₃ : ℝ} {p : ℝ → ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ}
    (hlam : lam ∈ Policies C Λ) :
    value C μ p c α₁ α₂ α₃ lam * ∑ k ∈ Finset.range (C + 1), weight C μ lam k =
      ∑ k ∈ Finset.Icc 1 C, weight C μ lam k * (myopic p c α₁ α₂ (lam k) + α₃) := by
  have hT := total_pos hμ hlam
  have hv : value C μ p c α₁ α₂ α₃ lam =
      (∑ k ∈ Finset.Icc 1 C, weight C μ lam k * (myopic p c α₁ α₂ (lam k) + α₃)) /
        ∑ k ∈ Finset.range (C + 1), weight C μ lam k := by
    unfold value profit marketShare serviceLevel prob myopic
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  rw [hv]
  field_simp

lemma update_mem {C : ℕ} {Λ : ℝ} {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ) (i : ℕ) {ℓ : ℝ}
    (hℓ : ℓ ∈ Set.Icc 0 Λ) : Function.update lam i ℓ ∈ Policies C Λ := by
  intro j hj
  by_cases h : j = i
  · subst h; rw [Function.update_self]; exact hℓ
  · rw [Function.update_of_ne h]; exact hlam j hj

/-- comparative statics for a strictly concave objective with a linear penalty. -/
lemma comp_statics {Λ : ℝ} {F : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc 0 Λ, ∀ y ∈ Set.Icc 0 Λ, x ≠ y → (F x + F y) / 2 < F ((x + y) / 2))
    {l1 l2 d1 d2 : ℝ} (hl1 : l1 ∈ Set.Icc 0 Λ) (hl2 : l2 ∈ Set.Icc 0 Λ)
    (h1 : ∀ l ∈ Set.Icc 0 Λ, F l - l * d1 ≤ F l1 - l1 * d1)
    (h2 : ∀ l ∈ Set.Icc 0 Λ, F l - l * d2 ≤ F l2 - l2 * d2) (hd : d2 ≤ d1) : l1 ≤ l2 := by
  by_contra hlt
  push Not at hlt
  have e1 := h1 l2 hl2
  have e2 := h2 l1 hl1
  have hdeq : d1 = d2 := by nlinarith
  subst hdeq
  have hm : (l1 + l2) / 2 ∈ Set.Icc 0 Λ := by
    constructor <;> [linarith [hl1.1, hl2.1]; linarith [hl1.2, hl2.2]]
  have := hF l1 hl1 l2 hl2 (ne_of_gt hlt)
  have e3 := h1 _ hm
  nlinarith


/-- The descending-chain argument on the "bias differences" `Δ`. -/
lemma chain {C b : ℕ} (hbC : b ≤ C) {μ G : ℝ} (hμ : 0 < μ) (Δ φ lam : ℕ → ℝ)
    (hR : ∀ i, b ≤ i → i ≤ C → G = φ i + μ * ((C : ℝ) - i) * Δ (i + 1))
    (hX : ∀ i j, b ≤ i → i ≤ C → b ≤ j → j ≤ C → φ i + lam i * (Δ i - Δ j) ≤ φ j)
    (hpos : ∀ i, b < i → i ≤ C → 0 < lam i) (hnn : ∀ i, b ≤ i → i ≤ C → 0 ≤ lam i)
    (hbot : 0 ≤ Δ b) :
    0 ≤ Δ C ∧ ∀ i j, b ≤ i → i ≤ j → j ≤ C → Δ j ≤ Δ i := by
  -- coefficient fact
  have hcoef : ∀ i, i < C → 0 ≤ (C : ℝ) - ((i : ℝ) + 1) := by
    intro i hi
    have : ((i : ℝ) + 1) ≤ C := by exact_mod_cast hi
    linarith
  -- step identity: φ i - φ (i+1) = μ (C-i-1) (Δ(i+2) - Δ(i+1)) - μ Δ(i+1)
  have hstep : ∀ i, b ≤ i → i < C →
      φ i - φ (i + 1) = μ * ((C : ℝ) - ((i : ℝ) + 1)) * (Δ (i + 1 + 1) - Δ (i + 1)) - μ * Δ (i + 1) := by
    intro i hbi hiC
    have h1 := hR i hbi hiC.le
    have h2 := hR (i + 1) (by omega) hiC
    push_cast at h2
    linarith
  -- (1) Δ C ≥ 0
  have hC0 : 0 ≤ Δ C := by
    by_contra hneg
    push Not at hneg
    have key : ∀ d, ∀ i, i + d = C → b ≤ i → Δ i < 0 ∧ (i < C → Δ i ≤ Δ (i + 1)) := by
      intro d
      induction d with
      | zero =>
        intro i hi _
        simp at hi
        subst hi
        exact ⟨hneg, fun h => absurd h (lt_irrefl _)⟩
      | succ d ih =>
        intro i hi hbi
        have hiC : i < C := by omega
        obtain ⟨hn1, hm1⟩ := ih (i + 1) (by omega) (by omega)
        have hs := hstep i hbi hiC
        have hc : 0 ≤ μ * ((C : ℝ) - ((i : ℝ) + 1)) * (Δ (i + 1 + 1) - Δ (i + 1)) := by
          rcases Nat.lt_or_ge (i + 1) C with h | h
          · have := hm1 h
            have := hcoef i hiC
            apply mul_nonneg (mul_nonneg hμ.le this); linarith
          · have : (C : ℝ) - ((i : ℝ) + 1) = 0 := by
              have : (i : ℝ) + 1 = C := by exact_mod_cast (show i + 1 = C by omega)
              linarith
            rw [this]; simp
        have hx := hX i (i + 1) hbi hiC.le (by omega) (by omega)
        have hgt : 0 < φ i - φ (i + 1) := by nlinarith
        have hlam : 0 < lam i * (Δ (i + 1) - Δ i) := by linarith
        have hd : 0 < Δ (i + 1) - Δ i := by
          by_contra hle
          push Not at hle
          nlinarith [hnn i hbi hiC.le]
        exact ⟨by linarith, fun _ => by linarith⟩
    have := (key (C - b) b (by omega) le_rfl).1
    linarith
  -- (2) Δ non-increasing
  have key2 : ∀ d, ∀ i, i + d = C → b ≤ i → 0 ≤ Δ i ∧ (i < C → Δ (i + 1) ≤ Δ i) := by
    intro d
    induction d with
    | zero =>
      intro i hi _
      simp at hi
      subst hi
      exact ⟨hC0, fun h => absurd h (lt_irrefl _)⟩
    | succ d ih =>
      intro i hi hbi
      have hiC : i < C := by omega
      obtain ⟨hn1, hm1⟩ := ih (i + 1) (by omega) (by omega)
      have hs := hstep i hbi hiC
      have hle : Δ (i + 1) ≤ Δ i := by
        by_contra hlt
        push Not at hlt
        have hc : μ * ((C : ℝ) - ((i : ℝ) + 1)) * (Δ (i + 1 + 1) - Δ (i + 1)) ≤ 0 := by
          rcases Nat.lt_or_ge (i + 1) C with h | h
          · have := hm1 h
            have := hcoef i hiC
            apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hμ.le this); linarith
          · have : (C : ℝ) - ((i : ℝ) + 1) = 0 := by
              have : (i : ℝ) + 1 = C := by exact_mod_cast (show i + 1 = C by omega)
              linarith
            rw [this]; simp
        have hx := hX (i + 1) i (by omega) hiC (by omega) hiC.le
        have hp := hpos (i + 1) (by omega) hiC
        have : 0 < lam (i + 1) * (Δ (i + 1) - Δ i) := mul_pos hp (by linarith)
        nlinarith
      exact ⟨by linarith, fun _ => hle⟩
  refine ⟨hC0, ?_⟩
  intro i j hbi hij hjC
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := (key2 (C - j) j (by omega) (by omega)).2 (by omega)
    linarith [ih (by omega)]

end SolSRGL1

open SolSRGL1 StaticReusable.Guarantee in
theorem solution {C : ℕ} {μ Λ c α₁ α₂ α₃ : ℝ} {p : ℝ → ℝ}
    (hS : StaticReusable.Guarantee.Standing C μ Λ c p α₁ α₂ α₃) (hα₁ : 0 < α₁)
    (hstrict : StrictConcaveOn ℝ (Set.Icc 0 Λ) (fun l => l * (p l - c)))
    (lbar : ℝ) (hlbar : lbar ∈ Set.Icc 0 Λ)
    (hmyopic : IsMaxOn (StaticReusable.Guarantee.myopic p c α₁ α₂) (Set.Icc 0 Λ) lbar)
    (lamStar : ℕ → ℝ) (hpol : lamStar ∈ StaticReusable.Guarantee.Policies C Λ)
    (hopt : IsMaxOn (StaticReusable.Guarantee.value C μ p c α₁ α₂ α₃)
      (StaticReusable.Guarantee.Policies C Λ) lamStar) :
    lamStar C ≤ lbar ∧
      ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ C →
        0 < StaticReusable.Guarantee.prob C μ lamStar i → lamStar i ≤ lamStar j := by
  have hμ := hS.μ_pos
  have hC := hS.one_le_C
  have hα₃ := hS.α₃_nonneg
  set lam := lamStar with hlamdef
  set M := myopic p c α₁ α₂ with hMdef
  set g := value C μ p c α₁ α₂ α₃ lam with hgdef
  set w : ℕ → ℝ := fun k => weight C μ lam k with hwdef
  have hw0 : ∀ k, 0 ≤ w k := fun k => weight_nonneg hμ hpol k
  -- rewards
  let ρ : (ℕ → ℝ) → ℕ → ℝ := fun l k => if k = 0 then 0 else M (l k) + α₃
  let Γ : (ℕ → ℝ) → ℝ := fun l => ∑ k ∈ Finset.range (C + 1), weight C μ l k * (g - ρ l k)
  have hΓ : ∀ l ∈ Policies C Λ, Γ l = g * (∑ k ∈ Finset.range (C + 1), weight C μ l k) -
      value C μ p c α₁ α₂ α₃ l * (∑ k ∈ Finset.range (C + 1), weight C μ l k) := by
    intro l hl
    rw [value_mul_total hμ hl]
    simp only [Γ]
    rw [sum_range_split, sum_range_split, mul_add, Finset.mul_sum]
    simp only [ρ, if_true]
    rw [mul_sub, mul_zero, sub_zero]
    have : ∑ k ∈ Finset.Icc 1 C, weight C μ l k * (g - (if k = 0 then 0 else M (l k) + α₃)) =
        ∑ k ∈ Finset.Icc 1 C, (g * weight C μ l k - weight C μ l k * (myopic p c α₁ α₂ (l k) + α₃)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have : k ≠ 0 := by simp only [Finset.mem_Icc] at hk; omega
      simp only [this, if_false, hMdef]
      ring
    rw [this, Finset.sum_sub_distrib]
    ring
  have hΓnn : ∀ l ∈ Policies C Λ, 0 ≤ Γ l := by
    intro l hl
    rw [hΓ l hl]
    have := hopt hl
    have hT := total_pos hμ hl
    simp only [Set.mem_setOf_eq] at this
    nlinarith
  have hΓ0 : Γ lam = 0 := by rw [hΓ lam hpol]; ring
  -- g ≥ α₃ (zero policy)
  have hgα : α₃ ≤ g := by
    have hz : (fun _ : ℕ => (0 : ℝ)) ∈ Policies C Λ := fun _ _ => ⟨le_rfl, hS.Λ_pos.le⟩
    have hv := value_mul_total (c := c) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) (p := p) hμ hz
    have hT := total_pos hμ hz
    have hw00 : weight C μ (fun _ => (0 : ℝ)) 0 = 0 := by
      rw [weight_eq]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (i := 1) (by simp only [Finset.mem_Icc]; omega)
      simp
    have hM0 : myopic p c α₁ α₂ 0 = 0 := by simp [myopic]
    simp only [hM0, zero_add] at hv
    rw [← Finset.sum_mul] at hv
    have hsplit := sum_range_split (fun k => weight C μ (fun _ => (0 : ℝ)) k) C
    simp only [hw00, zero_add] at hsplit
    rw [← hsplit] at hv
    have hval : value C μ p c α₁ α₂ α₃ (fun _ => 0) = α₃ := by
      have := mul_right_cancel₀ hT.ne' (hv.trans (mul_comm _ _))
      exact this
    have := hopt hz
    simp only [Set.mem_setOf_eq] at this
    linarith
  have hg0 : 0 ≤ g := le_trans hα₃ hgα
  -- coordinate decomposition
  let L : ℕ → ℝ := fun i => ∑ k ∈ Finset.range i, uu C μ lam i k * (g - ρ lam k)
  let H : ℕ → ℝ := fun i => ∑ k ∈ Finset.Ico (i + 1) (C + 1), w k * (g - ρ lam k)
  let T : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, w k * (g - ρ lam k)
  have hρupd : ∀ i k ℓ, k ≠ i → ρ (Function.update lam i ℓ) k = ρ lam k := by
    intro i k ℓ hki
    simp only [ρ]
    rw [Function.update_of_ne hki]
  have hdec : ∀ i, 1 ≤ i → i ≤ C → ∀ ℓ, Γ (Function.update lam i ℓ) =
      ℓ * L i + w i * (g - (M ℓ + α₃)) + H i := by
    intro i hi1 hiC ℓ
    simp only [Γ]
    rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ C + 1 by omega), Finset.sum_range_succ]
    have e1 : ∑ k ∈ Finset.range i, weight C μ (Function.update lam i ℓ) k *
        (g - ρ (Function.update lam i ℓ) k) = ℓ * L i := by
      simp only [L]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < i := Finset.mem_range.1 hk
      rw [weight_update_lt lam ℓ hk' hiC, hρupd i k ℓ (by omega)]
      ring
    have e2 : weight C μ (Function.update lam i ℓ) i * (g - ρ (Function.update lam i ℓ) i) =
        w i * (g - (M ℓ + α₃)) := by
      rw [weight_update_ge lam ℓ le_rfl]
      simp only [ρ, hwdef]
      rw [if_neg (by omega), Function.update_self]
    have e3 : ∑ k ∈ Finset.Ico (i + 1) (C + 1), weight C μ (Function.update lam i ℓ) k *
        (g - ρ (Function.update lam i ℓ) k) = H i := by
      simp only [H]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := (Finset.mem_Ico.1 hk).1
      rw [weight_update_ge lam ℓ (by omega), hρupd i k ℓ (by omega)]
    rw [e1, e2, e3]
  have hdec0 : ∀ i, 1 ≤ i → i ≤ C → 0 = lam i * L i + w i * (g - (M (lam i) + α₃)) + H i := by
    intro i hi1 hiC
    have := hdec i hi1 hiC (lam i)
    rw [Function.update_eq_self] at this
    rw [← this, hΓ0]
  have hTL : ∀ i, i ≤ C → T i = lam i * L i := by
    intro i hiC
    simp only [T, L]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < i := Finset.mem_range.1 hk
    have := weight_update_lt (μ := μ) lam (lam i) hk' hiC
    rw [Function.update_eq_self] at this
    simp only [hwdef]
    rw [this]
    ring
  have hTsucc : ∀ i, 1 ≤ i → T (i + 1) = T i + w i * (g - (M (lam i) + α₃)) := by
    intro i hi
    simp only [T]
    rw [Finset.sum_range_succ]
    simp only [ρ]
    rw [if_neg (by omega)]
  have hTend : T (C + 1) = 0 := hΓ0
  -- per-state optimality
  let Δ : ℕ → ℝ := fun i => L i / w i
  have hopti : ∀ i, 1 ≤ i → i ≤ C → 0 < w i → ∀ ℓ ∈ Set.Icc 0 Λ,
      M ℓ - ℓ * Δ i ≤ M (lam i) - lam i * Δ i := by
    intro i hi1 hiC hwi ℓ hℓ
    have h1 := hΓnn _ (update_mem hpol i hℓ)
    rw [hdec i hi1 hiC ℓ] at h1
    have h0 := hdec0 i hi1 hiC
    have hL : L i = Δ i * w i := by simp only [Δ]; field_simp
    rw [hL] at h1 h0
    have : w i * (M ℓ - ℓ * Δ i) ≤ w i * (M (lam i) - lam i * Δ i) := by nlinarith
    exact le_of_mul_le_mul_left this hwi
  -- weights recursion
  have hws : ∀ i, i < C → lam (i + 1) * w (i + 1) = μ * ((C : ℝ) - i) * w i :=
    fun i hi => weight_succ hμ lam i hi
  have hpos_of_mul : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 < x * y → 0 < x ∧ 0 < y := by
    intro x y hx hy hxy
    refine ⟨lt_of_le_of_ne hx ?_, lt_of_le_of_ne hy ?_⟩
    · intro h; rw [← h, zero_mul] at hxy; exact lt_irrefl _ hxy
    · intro h; rw [← h, mul_zero] at hxy; exact lt_irrefl _ hxy
  have hlamnn : ∀ i, 1 ≤ i → i ≤ C → 0 ≤ lam i := fun i h1 h2 =>
    (hpol i (by simp only [Finset.mem_Icc]; omega)).1
  -- the recursion (R_i)
  have hR : ∀ i, 1 ≤ i → i ≤ C → 0 < w i →
      g - α₃ = (M (lam i) - lam i * Δ i) + μ * ((C : ℝ) - i) * Δ (i + 1) := by
    intro i hi1 hiC hwi
    have hLi : L i = Δ i * w i := by simp only [Δ]; field_simp
    have E1 := hTsucc i hi1
    rw [hTL i hiC, hLi] at E1
    have key : w i * (g - α₃ - ((M (lam i) - lam i * Δ i) + μ * ((C : ℝ) - i) * Δ (i + 1))) = 0 := by
      rcases Nat.lt_or_ge i C with h | h
      · have E3 := hws i h
        have hCi : (0 : ℝ) < (C : ℝ) - i := by
          have : (i : ℝ) < C := by exact_mod_cast h
          linarith
        have hp : 0 < lam (i + 1) * w (i + 1) := by rw [E3]; positivity
        have hwi1 := (hpos_of_mul _ _ (hlamnn (i + 1) (by omega) h) (hw0 _) hp).2
        have hL1 : L (i + 1) = Δ (i + 1) * w (i + 1) := by simp only [Δ]; field_simp
        have E2 := hTL (i + 1) h
        rw [hL1] at E2
        linear_combination (-1 : ℝ) * E1 + E2 + Δ (i + 1) * E3
      · have hiC' : i = C := le_antisymm hiC h
        subst hiC'
        have E2 := hTend
        simp only [sub_self, mul_zero, zero_mul, add_zero]
        linear_combination (-1 : ℝ) * E1 + E2
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h hwi.ne'
    · linarith
  -- good states
  let Gd : ℕ → Prop := fun i => 1 ≤ i ∧ i ≤ C ∧ 0 < w (i - 1)
  have hGd : ∀ i, Gd i → 0 < lam i ∧ 0 < w i := by
    intro i ⟨hi1, hiC, hwi⟩
    have E := hws (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at E
    have hCi : (0 : ℝ) < (C : ℝ) - ((i - 1 : ℕ) : ℝ) := by
      have : ((i - 1 : ℕ) : ℝ) < C := by exact_mod_cast (show i - 1 < C by omega)
      linarith
    have hp : 0 < lam i * w i := by rw [E]; positivity
    exact hpos_of_mul _ _ (hlamnn i hi1 hiC) (hw0 _) hp
  have hGd_up : ∀ i, Gd i → ∀ j, i ≤ j → j ≤ C → Gd j := by
    intro i hi j hij hjC
    induction j, hij using Nat.le_induction with
    | base => exact hi
    | succ j hij ih =>
      have h := hGd j (ih (by omega))
      refine ⟨by omega, hjC, ?_⟩
      simp only [Nat.add_sub_cancel]
      exact h.2
  -- bottom fact
  have hbot : ∀ b, Gd b → (b = 1 ∨ ¬ Gd (b - 1)) → 0 ≤ Δ b := by
    intro b hb hmin
    obtain ⟨hb1, hbC, hwb⟩ := hb
    obtain ⟨hlb, hwbb⟩ := hGd b ⟨hb1, hbC, hwb⟩
    have hTb : 0 ≤ T b := by
      have hsplit : T b = T (b - 1) + w (b - 1) * (g - ρ lam (b - 1)) := by
        simp only [T]
        conv_lhs => rw [show b = (b - 1) + 1 by omega]
        rw [Finset.sum_range_succ]
      rw [hsplit]
      by_cases hb1' : b = 1
      · subst hb1'
        simp only [T, ρ]
        simp
        exact mul_nonneg (hw0 0) hg0
      · have h := hmin.resolve_left hb1'
        have hb2 : 2 ≤ b := by omega
        have hw2 : w (b - 1 - 1) = 0 := by
          by_contra hne
          apply h
          exact ⟨by omega, by omega, lt_of_le_of_ne (hw0 _) (Ne.symm hne)⟩
        have E := hws (b - 1 - 1) (by omega)
        rw [show b - 1 - 1 + 1 = b - 1 by omega, hw2, mul_zero] at E
        have hwb1 : 0 < w (b - 1) := hwb
        have hl0 : lam (b - 1) = 0 := by
          rcases mul_eq_zero.1 E with h' | h'
          · exact h'
          · exact absurd h' hwb1.ne'
        rw [hTL (b - 1) (by omega), hl0]
        simp only [ρ]
        rw [if_neg (by omega), hl0]
        have hM0 : M 0 = 0 := by simp [hMdef, myopic]
        rw [hM0]
        have : 0 ≤ w (b - 1) * (g - (0 + α₃)) := mul_nonneg (hw0 _) (by linarith)
        linarith
    have hTb' : T b = (lam b * w b) * Δ b := by
      rw [hTL b hbC]
      simp only [Δ]
      field_simp
    rw [hTb'] at hTb
    exact (mul_nonneg_iff_of_pos_left (mul_pos hlb hwbb)).mp hTb
  -- the chain from the lowest good state
  classical
  have hchain : ∀ i0, Gd i0 → ∃ b, b ≤ i0 ∧ Gd b ∧
      (0 ≤ Δ C ∧ ∀ i j, b ≤ i → i ≤ j → j ≤ C → Δ j ≤ Δ i) := by
    intro i0 hi0
    have hex : ∃ i, Gd i := ⟨i0, hi0⟩
    refine ⟨Nat.find hex, Nat.find_min' hex hi0, Nat.find_spec hex, ?_⟩
    set b := Nat.find hex with hbdef
    have hb : Gd b := Nat.find_spec hex
    have hbC : b ≤ C := hb.2.1
    have hb1 : 1 ≤ b := hb.1
    have hmin : b = 1 ∨ ¬ Gd (b - 1) := by
      by_cases h : b = 1
      · exact Or.inl h
      · exact Or.inr (Nat.find_min hex (by omega))
    apply chain hbC hμ Δ (fun k => M (lam k) - lam k * Δ k) lam
    · intro i hbi hiC
      exact hR i (by omega) hiC (hGd i (hGd_up b hb i hbi hiC)).2
    · intro i j hbi hiC hbj hjC
      have hwj := (hGd j (hGd_up b hb j hbj hjC)).2
      have := hopti j (by omega) hjC hwj (lam i) (hpol i (by simp only [Finset.mem_Icc]; omega))
      linarith
    · intro i hbi hiC
      exact (hGd i (hGd_up b hb i hbi.le hiC)).1
    · intro i hbi hiC
      exact hlamnn i (by omega) hiC
    · exact hbot b hb hmin
  -- strict midpoint concavity of the myopic objective
  have hF : ∀ x ∈ Set.Icc 0 Λ, ∀ y ∈ Set.Icc 0 Λ, x ≠ y → (M x + M y) / 2 < M ((x + y) / 2) := by
    intro x hx y hy hxy
    have := hstrict.2 hx hy hxy (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at this
    have hmid : (1 / 2 : ℝ) * x + 1 / 2 * y = (x + y) / 2 := by ring
    rw [hmid] at this
    simp only [hMdef, myopic]
    nlinarith
  have hmy : ∀ l ∈ Set.Icc 0 Λ, M l - l * 0 ≤ M lbar - lbar * 0 := by
    intro l hl
    have := isMaxOn_iff.mp hmyopic l hl
    simp only [mul_zero, sub_zero]
    exact this
  refine ⟨?_, ?_⟩
  · -- λ*_C ≤ λ̄
    by_cases hGC : 0 < w (C - 1)
    · have hgC : Gd C := ⟨hC, le_rfl, hGC⟩
      obtain ⟨b, -, -, hΔC, -⟩ := hchain C hgC
      have hwC := (hGd C hgC).2
      exact comp_statics hF (hpol C (by simp only [Finset.mem_Icc]; omega)) hlbar
        (hopti C hC le_rfl hwC) hmy hΔC
    · have hw1 : w (C - 1) = 0 := le_antisymm (not_lt.1 hGC) (hw0 _)
      have E := hws (C - 1) (by omega)
      rw [Nat.sub_add_cancel hC, hw1, mul_zero] at E
      have hwC : 0 < w C := weight_C_pos lam
      have hl0 : lam C = 0 := by
        rcases mul_eq_zero.1 E with h | h
        · exact h
        · exact absurd h hwC.ne'
      rw [hl0]
      exact hlbar.1
  · intro i j hi1 hij hjC hprob
    have hiC : i ≤ C := le_trans hij hjC
    have hwi : 0 < w i := by
      unfold prob at hprob
      have hT := total_pos hμ hpol
      exact (div_pos_iff_of_pos_right hT).mp hprob
    by_cases hli : lam i = 0
    · rw [hli]; exact (hpol j (by simp only [Finset.mem_Icc]; omega)).1
    · have hlpos : 0 < lam i := lt_of_le_of_ne (hlamnn i hi1 hiC) (Ne.symm hli)
      have hgi : Gd i := by
        refine ⟨hi1, hiC, ?_⟩
        have E := hws (i - 1) (by omega)
        rw [Nat.sub_add_cancel hi1] at E
        have hp : 0 < lam i * w i := mul_pos hlpos hwi
        rw [E] at hp
        have hCi : (0 : ℝ) ≤ (C : ℝ) - ((i - 1 : ℕ) : ℝ) := by
          have : ((i - 1 : ℕ) : ℝ) ≤ C := by exact_mod_cast (show i - 1 ≤ C by omega)
          linarith
        rcases lt_or_eq_of_le (hw0 (i - 1)) with h | h
        · exact h
        · rw [← h, mul_zero] at hp; exact absurd hp (lt_irrefl _)
      obtain ⟨b, hbi, hb, -, hmono⟩ := hchain i hgi
      have hgj : Gd j := hGd_up i hgi j hij hjC
      have hwj := (hGd j hgj).2
      exact comp_statics hF (hpol i (by simp only [Finset.mem_Icc]; omega))
        (hpol j (by simp only [Finset.mem_Icc]; omega))
        (hopti i hi1 hiC hwi) (hopti j (by omega) hjC hwj) (hmono i j hbi hij hjC)
