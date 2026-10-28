-- Prove2me | solution 2 for WiesemannRMDP.AffineSDP.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:35:14.63484+00:00
-- url     : https://prove2.me/submissions/e0ef6f1d-d1a5-4ea2-8e40-0a3511f5f7f8

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_AffineSDP_ParamSet
import Definitions.Def_WiesemannRMDP_AffineSDP_Model
import Definitions.Def_WiesemannRMDP_AffineSDP_Programs
import Theorems.Thm_Lagrange_exists_multiplier

-- carved verbatim out of submission 1ff76dcc-a042-4b5a-a216-4caf8b895579, lines 3156-3235

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma aux1_linear_pi {α : Type*} [Fintype α] [DecidableEq α] (L : (α → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) :
    L p = ∑ i, p i * L (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ L p]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

private lemma aux2_qf_smul {n : Type*} [Fintype n] (A : Matrix n n ℝ) (c : ℝ) (v : n → ℝ) :
    (c • v) ⬝ᵥ A *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

private lemma aux2_roots (bx by' kb : ℝ) (hx : 0 < bx) (hy : by' < 0) :
    ∃ s₁ s₂ : ℝ, s₁ < 0 ∧ 0 < s₂ ∧ bx + s₁ * kb + s₁ ^ 2 * by' = 0 ∧
      bx + s₂ * kb + s₂ ^ 2 * by' = 0 := by
  have hD : 0 ≤ kb ^ 2 - 4 * bx * by' := by nlinarith
  set r := Real.sqrt (kb ^ 2 - 4 * bx * by') with hr_def
  have hr2 : r ^ 2 = kb ^ 2 - 4 * bx * by' := Real.sq_sqrt hD
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrk1 : kb < r := by nlinarith
  have hrk2 : -kb < r := by nlinarith
  have hy2 : (2 * by') ≠ 0 := by linarith
  have hy4 : (4 * by') ≠ 0 := by linarith
  refine ⟨(-kb + r) / (2 * by'), (-kb - r) / (2 * by'), ?_, ?_, ?_, ?_⟩
  · exact div_neg_of_pos_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · set s := (-kb + r) / (2 * by')
    have hs : 2 * by' * s = -kb + r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb + r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h
  · set s := (-kb - r) / (2 * by')
    have hs : 2 * by' * s = -kb - r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb - r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h

private lemma aux2_pair_real (ax bx ay by' ka kb s₁ s₂ : ℝ) (hx : 0 < bx) (hs₁ : s₁ < 0) (hs₂ : 0 < s₂)
    (hb₁ : bx + s₁ * kb + s₁ ^ 2 * by' = 0) (hb₂ : bx + s₂ * kb + s₂ ^ 2 * by' = 0)
    (ha₁ : 0 ≤ ax + s₁ * ka + s₁ ^ 2 * ay) (ha₂ : 0 ≤ ax + s₂ * ka + s₂ ^ 2 * ay) :
    0 ≤ ay * bx - ax * by' := by
  by_contra hC
  push Not at hC
  set C := ay * bx - ax * by'
  set γ := ka * bx - ax * kb
  -- h(s) = (a-part)·bx - ax·(b-part) = s γ + s² C
  have e₁ : (ax + s₁ * ka + s₁ ^ 2 * ay) * bx - ax * (bx + s₁ * kb + s₁ ^ 2 * by') =
      s₁ * (γ + s₁ * C) := by simp only [γ, C]; ring
  have e₂ : (ax + s₂ * ka + s₂ ^ 2 * ay) * bx - ax * (bx + s₂ * kb + s₂ ^ 2 * by') =
      s₂ * (γ + s₂ * C) := by simp only [γ, C]; ring
  rw [hb₁, mul_zero, sub_zero] at e₁
  rw [hb₂, mul_zero, sub_zero] at e₂
  have h₁ : 0 ≤ s₁ * (γ + s₁ * C) := e₁ ▸ mul_nonneg ha₁ hx.le
  have h₂ : 0 ≤ s₂ * (γ + s₂ * C) := e₂ ▸ mul_nonneg ha₂ hx.le
  have h₁' : γ + s₁ * C ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have h₂' : 0 ≤ γ + s₂ * C := by
    by_contra h; push Not at h; nlinarith
  nlinarith

private lemma aux2_core {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V → ℝ)
    (ha : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, a (x + s • y) = a x + s * k + s ^ 2 * a y)
    (hb : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, b (x + s • y) = b x + s * k + s ^ 2 * b y)
    (hslater : ∃ x₀, 0 < b x₀) (H : ∀ x, 0 ≤ b x → 0 ≤ a x) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ a x - τ * b x := by
  -- pair inequality
  have hpair : ∀ x y, 0 < b x → b y < 0 → 0 ≤ a y * b x - a x * b y := by
    intro x y hx hy
    obtain ⟨ka, hka⟩ := ha x y
    obtain ⟨kb, hkb⟩ := hb x y
    obtain ⟨s₁, s₂, hs₁, hs₂, h₁, h₂⟩ := aux2_roots (b x) (b y) kb hx hy
    refine aux2_pair_real (a x) (b x) (a y) (b y) ka kb s₁ s₂ hx hs₁ hs₂ h₁ h₂ ?_ ?_
    · rw [← hka]; exact H _ (by rw [hkb, h₁])
    · rw [← hka]; exact H _ (by rw [hkb, h₂])
  obtain ⟨x₀, hx₀⟩ := hslater
  let S : Set ℝ := {q | ∃ x, 0 < b x ∧ q = a x / b x}
  have hSne : S.Nonempty := ⟨_, x₀, hx₀, rfl⟩
  have hS0 : ∀ q ∈ S, 0 ≤ q := by
    rintro q ⟨x, hx, rfl⟩; exact div_nonneg (H x hx.le) hx.le
  have hSbdd : BddBelow S := ⟨0, hS0⟩
  refine ⟨sInf S, le_csInf hSne hS0, fun x => ?_⟩
  rcases lt_trichotomy (b x) 0 with hneg | hzero | hpos
  · have hle : a x / b x ≤ sInf S := by
      refine le_csInf hSne ?_
      rintro q ⟨z, hz, rfl⟩
      rw [div_le_iff_of_neg hneg, div_mul_eq_mul_div, div_le_iff₀ hz]
      linarith [hpair z x hz hneg]
    rw [div_le_iff_of_neg hneg] at hle
    linarith
  · rw [hzero, mul_zero, sub_zero]; exact H x hzero.ge
  · have hle : sInf S ≤ a x / b x := csInf_le hSbdd ⟨x, hpos, rfl⟩
    rw [le_div_iff₀ hpos] at hle
    linarith

private lemma aux2_qexp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x y : n → ℝ) (s : ℝ) :
    (x + s • y) ⬝ᵥ A *ᵥ (x + s • y) =
      x ⬝ᵥ A *ᵥ x + s * (x ⬝ᵥ A *ᵥ y + y ⬝ᵥ A *ᵥ x) + s ^ 2 * (y ⬝ᵥ A *ᵥ y) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

private def aux2_Q {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (p : (n → ℝ) × ℝ) : ℝ :=
  p.1 ⬝ᵥ A *ᵥ p.1 + 2 * p.2 * (b ⬝ᵥ p.1) + c * p.2 ^ 2

private lemma aux2_Q_exp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (p q : (n → ℝ) × ℝ) (s : ℝ) :
    aux2_Q A b c (p + s • q) = aux2_Q A b c p + s * (p.1 ⬝ᵥ A *ᵥ q.1 + q.1 ⬝ᵥ A *ᵥ p.1 +
      2 * (p.2 * (b ⬝ᵥ q.1) + q.2 * (b ⬝ᵥ p.1)) + 2 * c * p.2 * q.2) + s ^ 2 * aux2_Q A b c q := by
  simp only [aux2_Q, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [aux2_qexp]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

private lemma aux2_Q_one {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ) (x : n → ℝ) :
    aux2_Q A b c (x, 1) = x ⬝ᵥ A *ᵥ x + 2 * b ⬝ᵥ x + c := by
  simp only [aux2_Q]; ring

private lemma aux2_Q_scale {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (u : n → ℝ) (t : ℝ) : aux2_Q A b c (t • u, t) = t ^ 2 * aux2_Q A b c (u, 1) := by
  simp only [aux2_Q, aux2_qf_smul, dotProduct_smul, smul_eq_mul]; ring

private lemma aux2_big (f₀ k q : ℝ) (hq : q < 0) : ∃ S : ℝ, 0 ≤ S ∧ f₀ + S * k + S ^ 2 * q < 0 := by
  set M := |f₀| + |k| + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M / (-q) + 1, ?_⟩
  set S := M / (-q) + 1 with hS
  have hS1 : 1 ≤ S := by have : 0 ≤ M / (-q) := div_nonneg hM0.le (by linarith); linarith
  have hSq : S * q = -M + q := by
    rw [hS, add_mul, div_mul_eq_mul_div, one_mul]
    rw [div_neg, mul_div_assoc, div_self hq.ne, mul_one]
  have h1 : f₀ ≤ S * |f₀| := by nlinarith [le_abs_self f₀, abs_nonneg f₀]
  have h2 : S * k ≤ S * |k| := by nlinarith [le_abs_self k]
  have h3 : S ^ 2 * q = S * (-M + q) := by rw [← hSq]; ring
  refine ⟨by linarith, ?_⟩
  nlinarith

private lemma aux2_t0 {V : Type*} [AddCommGroup V] [Module ℝ V] (Q₁ Q₂ : V → ℝ) (P d : V)
    (h1 : ∃ k, ∀ s : ℝ, Q₁ (P + s • d) = Q₁ P + s * k + s ^ 2 * Q₁ d)
    (h2 : ∃ k, ∀ s : ℝ, Q₂ (P + s • d) = Q₂ P + s * k + s ^ 2 * Q₂ d)
    (hP : Q₂ P < 0) (hd : Q₂ d ≤ 0) (H : ∀ s : ℝ, Q₂ (P + s • d) ≤ 0 → 0 ≤ Q₁ (P + s • d)) :
    0 ≤ Q₁ d := by
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨k₂, hk₂⟩ := h2
  by_contra hneg
  push Not at hneg
  have key : ∀ s : ℝ, s * k₂ ≤ 0 → 0 ≤ Q₁ P + s * k₁ + s ^ 2 * Q₁ d := by
    intro s hs
    rw [← hk₁]
    apply H
    rw [hk₂]
    nlinarith [sq_nonneg s]
  rcases le_total k₂ 0 with hk | hk
  · obtain ⟨S, hS0, hS⟩ := aux2_big (Q₁ P) k₁ (Q₁ d) hneg
    linarith [key S (mul_nonpos_of_nonneg_of_nonpos hS0 hk)]
  · obtain ⟨S, hS0, hS⟩ := aux2_big (Q₁ P) (-k₁) (Q₁ d) hneg
    have := key (-S) (by nlinarith)
    nlinarith

theorem sLemma_inhom {n : Type*} [Fintype n] (A₁ A₂ : Matrix n n ℝ) (b₁ b₂ : n → ℝ) (c₁ c₂ : ℝ)
    (hslater : ∃ x₀, x₀ ⬝ᵥ A₂ *ᵥ x₀ + 2 * b₂ ⬝ᵥ x₀ + c₂ < 0) :
    (∀ x, x ⬝ᵥ A₂ *ᵥ x + 2 * b₂ ⬝ᵥ x + c₂ ≤ 0 → 0 ≤ x ⬝ᵥ A₁ *ᵥ x + 2 * b₁ ⬝ᵥ x + c₁) ↔
      ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ (x ⬝ᵥ A₁ *ᵥ x + 2 * b₁ ⬝ᵥ x + c₁) + τ * (x ⬝ᵥ A₂ *ᵥ x + 2 * b₂ ⬝ᵥ x + c₂) := by
  constructor
  · intro H
    obtain ⟨x₀, hx₀⟩ := hslater
    have H1 : ∀ u, aux2_Q A₂ b₂ c₂ (u, 1) ≤ 0 → 0 ≤ aux2_Q A₁ b₁ c₁ (u, 1) := by
      intro u hu
      rw [aux2_Q_one] at hu ⊢
      exact H u hu
    have hP0 : aux2_Q A₂ b₂ c₂ (x₀, 1) < 0 := by rw [aux2_Q_one]; exact hx₀
    have hHom : ∀ p : (n → ℝ) × ℝ, 0 ≤ -aux2_Q A₂ b₂ c₂ p → 0 ≤ aux2_Q A₁ b₁ c₁ p := by
      rintro ⟨w, t⟩ hp
      by_cases ht : t = 0
      · subst ht
        have hline : ∀ s : ℝ, ((x₀, (1 : ℝ)) + s • (w, (0 : ℝ))) = (x₀ + s • w, 1) := by
          intro s; ext <;> simp
        refine aux2_t0 (aux2_Q A₁ b₁ c₁) (aux2_Q A₂ b₂ c₂) (x₀, 1) (w, 0)
          ⟨_, aux2_Q_exp A₁ b₁ c₁ (x₀, 1) (w, 0)⟩ ⟨_, aux2_Q_exp A₂ b₂ c₂ (x₀, 1) (w, 0)⟩
          hP0 (by linarith) fun s hs => ?_
        rw [hline] at hs ⊢
        exact H1 _ hs
      · obtain ⟨u, rfl⟩ : ∃ u, w = t • u := ⟨t⁻¹ • w, by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]⟩
        rw [aux2_Q_scale] at hp ⊢
        have ht2 : 0 < t ^ 2 := by positivity
        have h2 : aux2_Q A₂ b₂ c₂ (u, 1) ≤ 0 := by nlinarith
        have := H1 u h2
        positivity
    obtain ⟨τ, hτ, h⟩ := aux2_core (aux2_Q A₁ b₁ c₁) (fun p => -aux2_Q A₂ b₂ c₂ p)
      (fun p q => ⟨_, aux2_Q_exp A₁ b₁ c₁ p q⟩)
      (fun p q => ⟨-(p.1 ⬝ᵥ A₂ *ᵥ q.1 + q.1 ⬝ᵥ A₂ *ᵥ p.1 +
          2 * (p.2 * (b₂ ⬝ᵥ q.1) + q.2 * (b₂ ⬝ᵥ p.1)) + 2 * c₂ * p.2 * q.2), fun s => by
        show -aux2_Q A₂ b₂ c₂ (p + s • q) = _
        rw [aux2_Q_exp A₂ b₂ c₂ p q s]
        ring⟩)
      ⟨(x₀, 1), by linarith⟩ hHom
    refine ⟨τ, hτ, fun x => ?_⟩
    have := h (x, 1)
    rw [aux2_Q_one, aux2_Q_one] at this
    linarith
  · rintro ⟨τ, hτ, h⟩ x hx
    have := h x
    nlinarith

end

noncomputable section
open WiesemannRMDP.AffineSDP FoundationsML.ReinforcementLearning Matrix
set_option linter.unusedSectionVars false

def qv {q : ℕ} (t : ℝ) (ξ : Fin q → ℝ) : Unit ⊕ Fin q → ℝ := Sum.elim (fun _ => t) ξ

lemma qv_eta {q : ℕ} (x : Unit ⊕ Fin q → ℝ) :
    x = qv (x (Sum.inl ())) (fun i => x (Sum.inr i)) := by
  funext i; rcases i with ⟨⟩ | i <;> rfl

lemma Q1 {q : ℕ} (σ : ℝ) (s : Fin q → ℝ) (S : Matrix (Fin q) (Fin q) ℝ) (t : ℝ)
    (ξ : Fin q → ℝ) :
    qv t ξ ⬝ᵥ (quadBlock σ s S *ᵥ qv t ξ) = σ * t ^ 2 + t * (s ⬝ᵥ ξ) + ξ ⬝ᵥ (S *ᵥ ξ) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, quadBlock, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, qv, Sum.elim_inl,
    Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
  have e1 : ∀ i, ξ i * (s i / 2 * t + ∑ j, S i j * ξ j) =
      t * (s i * ξ i) / 2 + ξ i * ∑ j, S i j * ξ j := fun i => by ring
  simp only [e1, Finset.sum_add_distrib]
  have e2 : ∑ j, s j / 2 * ξ j = (∑ j, s j * ξ j) / 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ i, t * (s i * ξ i) / 2 = t * (∑ j, s j * ξ j) / 2 := by
    rw [Finset.mul_sum, Finset.sum_div]
  rw [e2, e3]; ring

lemma Q1' {q : ℕ} (σ : ℝ) (s : Fin q → ℝ) (S : Matrix (Fin q) (Fin q) ℝ) (ξ : Fin q → ℝ) :
    qv 1 ξ ⬝ᵥ (quadBlock σ s S *ᵥ qv 1 ξ) = σ + s ⬝ᵥ ξ + ξ ⬝ᵥ (S *ᵥ ξ) := by
  rw [Q1]; ring

lemma Qf_sub {n : Type*} [Fintype n] (A B : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((A - B) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - x ⬝ᵥ (B *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub]

lemma Qf_smul {n : Type*} [Fintype n] (c : ℝ) (A : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((c • A) *ᵥ x) = c * x ⬝ᵥ (A *ᵥ x) := by
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma Qf_sum {n ι : Type*} [Fintype n] [Fintype ι] (A : ι → Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((∑ i, A i) *ᵥ x) = ∑ i, x ⬝ᵥ (A i *ᵥ x) := by
  rw [sum_mulVec, dotProduct_sum]

lemma qB_sub {q : ℕ} (σ σ' : ℝ) (s s' : Fin q → ℝ) (S S' : Matrix (Fin q) (Fin q) ℝ) :
    quadBlock σ s S - quadBlock σ' s' S' = quadBlock (σ - σ') (s - s') (S - S') := by
  ext i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;> simp [quadBlock, sub_div]

lemma qB_smul {q : ℕ} (c σ : ℝ) (s : Fin q → ℝ) (S : Matrix (Fin q) (Fin q) ℝ) :
    c • quadBlock σ s S = quadBlock (c * σ) (c • s) (c • S) := by
  ext i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;> simp [quadBlock, mul_div_assoc]

lemma qB_sum {q : ℕ} {ι : Type*} [Fintype ι] (σ : ι → ℝ) (s : ι → Fin q → ℝ)
    (S : ι → Matrix (Fin q) (Fin q) ℝ) :
    ∑ i, quadBlock (σ i) (s i) (S i) = quadBlock (∑ i, σ i) (∑ i, s i) (∑ i, S i) := by
  ext i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
    simp [quadBlock, Matrix.sum_apply, Finset.sum_apply, Finset.sum_div]

lemma lim0 (a b c : ℝ) (h : ∀ ε : ℝ, 0 < ε → 0 ≤ a * ε ^ 2 + b * ε + c) : 0 ≤ c := by
  by_contra hc
  push Not at hc
  have hKpos : 0 < |a| + |b| + 1 := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min 1 (-c / (2 * (|a| + |b| + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ lt_min one_pos (div_pos (by linarith) (by positivity))
  have hε1 : ε ≤ 1 := hε ▸ min_le_left _ _
  have hε2 : ε ≤ -c / (2 * (|a| + |b| + 1)) := hε ▸ min_le_right _ _
  have h1 := h ε hε0
  have h3 : ε * (2 * (|a| + |b| + 1)) ≤ -c := (le_div_iff₀ (by positivity)).mp hε2
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have h4 : a * ε ^ 2 ≤ |a| * ε :=
    (mul_le_mul_of_nonneg_right (le_abs_self a) (sq_nonneg ε)).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg a))
  have h5 : b * ε ≤ |b| * ε := mul_le_mul_of_nonneg_right (le_abs_self b) hε0.le
  nlinarith

lemma homog {q : ℕ} {A : Matrix (Unit ⊕ Fin q) (Unit ⊕ Fin q) ℝ}
    (hA : ∃ σ s S, A = quadBlock σ s S) (h1 : ∀ ξ, 0 ≤ qv 1 ξ ⬝ᵥ (A *ᵥ qv 1 ξ)) :
    IsPSDForm A := by
  obtain ⟨σ, s, S, rfl⟩ := hA
  have h1' : ∀ ξ, 0 ≤ σ + s ⬝ᵥ ξ + ξ ⬝ᵥ (S *ᵥ ξ) := fun ξ => by
    have := h1 ξ; rw [Q1'] at this; exact this
  have hsc : ∀ (t : ℝ) (ξ : Fin q → ℝ), t ≠ 0 → σ * t ^ 2 + t * (s ⬝ᵥ ξ) + ξ ⬝ᵥ (S *ᵥ ξ) =
      t ^ 2 * (σ + s ⬝ᵥ (t⁻¹ • ξ) + (t⁻¹ • ξ) ⬝ᵥ (S *ᵥ (t⁻¹ • ξ))) := by
    intro t ξ ht
    simp only [dotProduct_smul, smul_dotProduct, mulVec_smul, smul_eq_mul]
    field_simp
  have hnn : ∀ (t : ℝ) (ξ : Fin q → ℝ), t ≠ 0 →
      0 ≤ σ * t ^ 2 + t * (s ⬝ᵥ ξ) + ξ ⬝ᵥ (S *ᵥ ξ) := fun t ξ ht => by
    rw [hsc t ξ ht]; exact mul_nonneg (sq_nonneg t) (h1' _)
  intro x
  rw [qv_eta x, Q1]
  by_cases ht : x (Sum.inl ()) = 0
  · rw [ht]
    have := lim0 σ (s ⬝ᵥ fun i => x (Sum.inr i)) ((fun i => x (Sum.inr i)) ⬝ᵥ
      (S *ᵥ fun i => x (Sum.inr i))) (fun ε hε => by have := hnn ε (fun i => x (Sum.inr i)) hε.ne'; linarith)
    linarith
  · exact hnn _ _ ht

def gq {q : ℕ} (O : Matrix (Fin q) (Fin q) ℝ) (o : Fin q → ℝ) (ω : ℝ) (ξ : Fin q → ℝ) : ℝ :=
  ω + o ⬝ᵥ ξ + ξ ⬝ᵥ (O *ᵥ ξ)

end

noncomputable section
open WiesemannRMDP.AffineSDP FoundationsML.ReinforcementLearning Matrix
set_option linter.unusedSectionVars false
variable {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act] {q L : ℕ}

lemma gq_nonneg (M : Model St Act q L) {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) (l : Fin L) :
    0 ≤ gq (M.O l) (M.o l) (M.ω l) ξ := by
  have := hξ l
  unfold gq; linarith

lemma blk_eval (M : Model St Act q L) (s : St) (a : Act) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) (ξ : Fin q → ℝ) :
    qv 1 ξ ⬝ᵥ (M.block20c s a w W *ᵥ qv 1 ξ) =
      (M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • (w + W *ᵥ ξ)) := by
  rw [Model.block20c, Q1']
  have h1 : (M.rvec s a ᵥ* M.K s a) ⬝ᵥ ξ = M.rvec s a ⬝ᵥ (M.K s a *ᵥ ξ) :=
    (dotProduct_mulVec _ _ _).symm
  have h2 : (M.k s a ᵥ* W) ⬝ᵥ ξ = M.k s a ⬝ᵥ (W *ᵥ ξ) := (dotProduct_mulVec _ _ _).symm
  have h3 : (w ᵥ* M.K s a) ⬝ᵥ ξ = w ⬝ᵥ (M.K s a *ᵥ ξ) := (dotProduct_mulVec _ _ _).symm
  have h4 : ξ ⬝ᵥ (((M.K s a)ᵀ * W) *ᵥ ξ) = (M.K s a *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hc1 : (M.K s a *ᵥ ξ) ⬝ᵥ M.rvec s a = M.rvec s a ⬝ᵥ (M.K s a *ᵥ ξ) := dotProduct_comm _ _
  have hc2 : (M.K s a *ᵥ ξ) ⬝ᵥ w = w ⬝ᵥ (M.K s a *ᵥ ξ) := dotProduct_comm _ _
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Matrix.smul_mulVec, h1, h2, h3, h4, hc1, hc2]
  ring

lemma rhs_eq (M : Model St Act q L) (π : St → Act → ℝ) (ξ : Fin q → ℝ) (v : St → ℝ) (s : St) :
    M.rhat π ξ s + M.lam * ∑ s', M.Phat π ξ s s' * v s' =
      ∑ a, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • v)) := by
  have e1 : M.rhat π ξ s = ∑ a, ∑ s', π s a * (M.pXi ξ s a s' * M.r s a s') := by
    simp only [Model.rhat, InducedReward, Model.expReward, Finset.mul_sum]
  have e2 : M.lam * ∑ s', M.Phat π ξ s s' * v s' =
      ∑ a, ∑ s', π s a * (M.pXi ξ s a s' * (M.lam * v s')) := by
    simp only [Model.Phat, InducedTransition, of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ a, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • v)) =
      ∑ a, ∑ s', (π s a * (M.pXi ξ s a s' * M.r s a s') +
        π s a * (M.pXi ξ s a s' * (M.lam * v s'))) := by
    simp only [dotProduct, Model.pXi, Model.rvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by rw [← Finset.sum_add_distrib]

lemma feas19_of (M : Model St Act q L) (π : St → Act → ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ)
    (h : ∀ ξ ∈ M.Xi, ∀ s, w s + W s ⬝ᵥ ξ ≤
      ∑ a, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • (w + W *ᵥ ξ)))) :
    M.Feas19 π w W := by
  intro ξ hξ s
  have := h ξ hξ s
  rw [← rhs_eq] at this
  exact this

lemma feas19_to (M : Model St Act q L) (π : St → Act → ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ)
    (hF : M.Feas19 π w W) : ∀ ξ ∈ M.Xi, ∀ s, w s + W s ⬝ᵥ ξ ≤
      ∑ a, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • (w + W *ᵥ ξ))) := by
  intro ξ hξ s
  have h : w s + W s ⬝ᵥ ξ ≤ M.rhat π ξ s + M.lam * ∑ s', M.Phat π ξ s s' * (w + W *ᵥ ξ) s' :=
    hF ξ hξ s
  rwa [rhs_eq] at h

lemma f20b (M : Model St Act q L) (τ : ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ)
    (γ : Fin L → ℝ) (ξ : Fin q → ℝ) :
    qv 1 ξ ⬝ᵥ ((M.lhs20b τ w W - ∑ l, γ l • Qblock M.O M.o M.ω l) *ᵥ qv 1 ξ) =
      M.p0 ⬝ᵥ (w + W *ᵥ ξ) - τ - ∑ l, γ l * gq (M.O l) (M.o l) (M.ω l) ξ := by
  rw [Qf_sub, Qf_sum]
  simp only [Qf_smul, Model.lhs20b, Qblock, Q1', gq, zero_mulVec, dotProduct_zero]
  rw [dotProduct_add, dotProduct_mulVec M.p0 W ξ]
  ring

lemma rep20b (M : Model St Act q L) (τ : ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ)
    (γ : Fin L → ℝ) : ∃ σ s S, M.lhs20b τ w W - ∑ l, γ l • Qblock M.O M.o M.ω l =
      quadBlock σ s S := by
  refine ⟨M.p0 ⬝ᵥ w - τ - ∑ l, γ l * M.ω l, M.p0 ᵥ* W - ∑ l, γ l • M.o l,
    0 - ∑ l, γ l • M.O l, ?_⟩
  simp only [Model.lhs20b, Qblock, qB_smul]
  rw [qB_sum, qB_sub]

lemma f20c (M : Model St Act q L) (π : St → Act → ℝ) (s : St) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) (Γ : St → Fin L → ℝ) (ξ : Fin q → ℝ) :
    qv 1 ξ ⬝ᵥ (M.lhs20c π s w W Γ *ᵥ qv 1 ξ) =
      ∑ a, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • (w + W *ᵥ ξ))) -
        (w s + W s ⬝ᵥ ξ) - ∑ l, Γ s l * gq (M.O l) (M.o l) (M.ω l) ξ := by
  rw [Model.lhs20c, Qf_sub, Qf_sub, Qf_sum, Qf_sum]
  simp only [Qf_smul, blk_eval, Qblock, Q1', gq, zero_mulVec, dotProduct_zero]
  ring

lemma rep20c (M : Model St Act q L) (π : St → Act → ℝ) (s : St) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) (Γ : St → Fin L → ℝ) :
    ∃ σ sv S, M.lhs20c π s w W Γ = quadBlock σ sv S := by
  refine ⟨∑ a, π s a * (M.k s a ⬝ᵥ (M.rvec s a + M.lam • w)) - w s - ∑ l, Γ s l * M.ω l,
    ∑ a, π s a • (M.rvec s a ᵥ* M.K s a + M.lam • (M.k s a ᵥ* W + w ᵥ* M.K s a)) - W s -
      ∑ l, Γ s l • M.o l,
    ∑ a, π s a • (M.lam • ((M.K s a)ᵀ * W)) - 0 - ∑ l, Γ s l • M.O l, ?_⟩
  simp only [Model.lhs20c, Model.block20c, Qblock, qB_smul]
  rw [qB_sum, qB_sum, qB_sub, qB_sub]

lemma rep20c_head (M : Model St Act q L) (π : St → Act → ℝ) (s : St) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) :
    ∃ σ sv S, ∀ ξ, ∑ a, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ
      (M.rvec s a + M.lam • (w + W *ᵥ ξ))) - (w s + W s ⬝ᵥ ξ) = σ + sv ⬝ᵥ ξ + ξ ⬝ᵥ (S *ᵥ ξ) := by
  obtain ⟨σ, sv, S, hrep⟩ : ∃ σ sv S, (∑ a, π s a • M.block20c s a w W) -
      quadBlock (w s) (W s) 0 = quadBlock σ sv S := by
    refine ⟨∑ a, π s a * (M.k s a ⬝ᵥ (M.rvec s a + M.lam • w)) - w s,
      ∑ a, π s a • (M.rvec s a ᵥ* M.K s a + M.lam • (M.k s a ᵥ* W + w ᵥ* M.K s a)) - W s,
      ∑ a, π s a • (M.lam • ((M.K s a)ᵀ * W)) - 0, ?_⟩
    simp only [Model.block20c, qB_smul]
    rw [qB_sum, qB_sub]
  refine ⟨σ, sv, S, fun ξ => ?_⟩
  rw [← Q1', ← hrep, Qf_sub, Qf_sum]
  simp only [Qf_smul, blk_eval, Q1', zero_mulVec, dotProduct_zero]
  ring

lemma Xi_compact (M : Model St Act q L) (hM : M.Standing) : IsCompact M.Xi := by
  apply Metric.isCompact_of_isClosed_isBounded _ hM.1.2.1
  show IsClosed {ξ : Fin q → ℝ | ∀ l : Fin L, 0 ≤ ξ ⬝ᵥ (M.O l *ᵥ ξ) + M.o l ⬝ᵥ ξ + M.ω l}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun l => isClosed_le continuous_const ?_
  exact ((continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)).add
    (continuous_const.dotProduct continuous_id)).add continuous_const

lemma Xi_nonempty (M : Model St Act q L) (hM : M.Standing) : Nonempty M.Xi := by
  obtain ⟨ξ, hξ⟩ := hM.1.2.2
  exact ⟨⟨ξ, fun l => (hξ l).le⟩⟩

lemma val_bdd (M : Model St Act q L) (hM : M.Standing) (w : St → ℝ) (W : Matrix St (Fin q) ℝ) :
    BddBelow (Set.range fun ξ : M.Xi => M.p0 ⬝ᵥ (w + W *ᵥ (ξ : Fin q → ℝ))) := by
  have hc : Continuous fun ξ : Fin q → ℝ => M.p0 ⬝ᵥ (w + W *ᵥ ξ) :=
    continuous_const.dotProduct (continuous_const.add (continuous_const.matrix_mulVec
      continuous_id))
  obtain ⟨b, hb⟩ := ((Xi_compact M hM).image hc).bddBelow
  exact ⟨b, by rintro _ ⟨ξ, rfl⟩; exact hb ⟨ξ.1, ξ.2, rfl⟩⟩

lemma concave_id (O : Matrix (Fin q) (Fin q) ℝ) (o : Fin q → ℝ) (ω t : ℝ) (x y : Fin q → ℝ) :
    gq O o ω (t • x + (1 - t) • y) - (t * gq O o ω x + (1 - t) * gq O o ω y) =
      -(t * (1 - t)) * ((x - y) ⬝ᵥ (O *ᵥ (x - y))) := by
  simp only [gq, mulVec_add, mulVec_smul, mulVec_sub, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_sub, sub_dotProduct, smul_eq_mul]
  ring

lemma gamma_exists (M : Model St Act q L) (hM : M.Standing) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) :
    ∃ γ : Fin L → ℝ, (∀ l, 0 ≤ γ l) ∧ ∀ ξ, ∑ l, γ l * gq (M.O l) (M.o l) (M.ω l) ξ ≤
      M.p0 ⬝ᵥ (w + W *ᵥ ξ) - M.val19 w W := by
  haveI := Xi_nonempty M hM
  let G : (Fin q → ℝ) → (Fin L → ℝ) := fun ξ l => gq (M.O l) (M.o l) (M.ω l) ξ
  let f : (Fin q → ℝ) → ℝ := fun ξ => -(M.p0 ⬝ᵥ (w + W *ᵥ ξ))
  have hmemK : ∀ u : Fin L → ℝ, u ∈ PointedCone.positive ℝ (Fin L → ℝ) ↔ ∀ l, 0 ≤ u l :=
    fun u => by rw [PointedCone.mem_positive, Pi.le_def]; rfl
  have hGX : ∀ ξ, G ξ ∈ PointedCone.positive ℝ (Fin L → ℝ) → ξ ∈ M.Xi := by
    intro ξ h l
    have := (hmemK _).mp h l
    simp only [G, gq] at this
    linarith
  have hcvx : ∀ x₁ ∈ (Set.univ : Set (Fin q → ℝ)), ∀ x₂ ∈ (Set.univ : Set (Fin q → ℝ)),
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x ∈ (Set.univ : Set (Fin q → ℝ)),
        G x - (t • G x₁ + (1 - t) • G x₂) ∈ PointedCone.positive ℝ (Fin L → ℝ) ∧
          t * f x₁ + (1 - t) * f x₂ ≤ f x := by
    intro x₁ _ x₂ _ t ht0 ht1
    refine ⟨t • x₁ + (1 - t) • x₂, trivial, (hmemK _).mpr fun l => ?_, ?_⟩
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, G]
      rw [concave_id]
      have hpsd := (hM.1.1 l).dotProduct_mulVec_nonneg (x₁ - x₂)
      simp only [star_trivial, neg_mulVec, dotProduct_neg] at hpsd
      have : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
      nlinarith
    · simp only [f, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
      apply le_of_eq
      ring
  have hslater : (0 : Fin L → ℝ) ∈ interior {u | ∃ x ∈ (Set.univ : Set (Fin q → ℝ)),
      G x - u ∈ PointedCone.positive ℝ (Fin L → ℝ)} := by
    obtain ⟨ξb, hξb⟩ := hM.1.2.2
    let U : Set (Fin L → ℝ) := {u | ∀ l, u l < G ξb l}
    have hUo : IsOpen U := by
      show IsOpen {u : Fin L → ℝ | ∀ l, u l < G ξb l}
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun l => isOpen_lt (continuous_apply l) continuous_const
    refine mem_interior.mpr ⟨U, fun u hu => ⟨ξb, trivial, (hmemK _).mpr fun l => ?_⟩, hUo,
      fun l => ?_⟩
    · have := hu l
      simp only [Pi.sub_apply]
      linarith
    · have := hξb l
      simp only [Pi.zero_apply, G, gq]
      linarith
  have hp : ∀ x ∈ (Set.univ : Set (Fin q → ℝ)), G x ∈ PointedCone.positive ℝ (Fin L → ℝ) →
      f x ≤ -M.val19 w W := by
    intro x _ hx
    have := ciInf_le (val_bdd M hM w W) ⟨x, hGX x hx⟩
    simp only [f]
    unfold Model.val19
    linarith
  obtain ⟨y, hy, hyle⟩ := Lagrange.exists_multiplier Set.univ f G
    (PointedCone.positive ℝ (Fin L → ℝ)) hcvx hslater (-M.val19 w W) hp
  refine ⟨fun l => y (Pi.single l 1), fun l => hy _ ((hmemK _).mpr fun j => ?_), fun ξ => ?_⟩
  · by_cases h : j = l
    · subst h; simp
    · simp [Pi.single_apply, h]
  · have h1 : -(M.p0 ⬝ᵥ (w + W *ᵥ ξ)) + y (G ξ) ≤ -M.val19 w W := hyle ξ trivial
    have h2 := aux1_linear_pi y (G ξ)
    have h3 : ∑ l, y (Pi.single l 1) * gq (M.O l) (M.o l) (M.ω l) ξ = y (G ξ) := by
      rw [h2]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    show ∑ l, y (Pi.single l 1) * gq (M.O l) (M.o l) (M.ω l) ξ ≤ _
    linarith

end

noncomputable section

open FoundationsML.ReinforcementLearning Matrix in
open WiesemannRMDP.AffineSDP in
theorem solution {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) (τ : ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ)
    (γ : Fin L → ℝ) (Γ : St → Fin L → ℝ) (hopt : M.IsOpt20 π τ w W γ Γ) :
    (L = 1 →
        IsGreatest (M.values19 π) τ ∧ M.Feas19 π w W ∧ M.val19 w W = τ) ∧
      (1 < L →
        τ ∈ lowerBounds (upperBounds (M.values19 π)) ∧ M.Feas19 π w W ∧
          M.val19 w W = τ) := by
  haveI := Xi_nonempty M hM
  obtain ⟨⟨hγ, hΓ, h20b, h20c⟩, hmax⟩ := hopt
  -- (20b) at (1, ξ) gives (22b)
  have h22b : ∀ ξ ∈ M.Xi, τ ≤ M.p0 ⬝ᵥ (w + W *ᵥ ξ) := by
    intro ξ hξ
    have h := h20b (qv 1 ξ)
    rw [f20b] at h
    have : 0 ≤ ∑ l, γ l * gq (M.O l) (M.o l) (M.ω l) ξ :=
      Finset.sum_nonneg fun l _ => mul_nonneg (hγ l) (gq_nonneg M hξ l)
    linarith
  -- (20c) at (1, ξ) gives (19)
  have hF : M.Feas19 π w W := by
    refine feas19_of M π w W fun ξ hξ s => ?_
    have h := h20c s (qv 1 ξ)
    rw [f20c] at h
    have : 0 ≤ ∑ l, Γ s l * gq (M.O l) (M.o l) (M.ω l) ξ :=
      Finset.sum_nonneg fun l _ => mul_nonneg (hΓ s l) (gq_nonneg M hξ l)
    linarith
  -- any (w', W') with (20c) for some Γ' reaches val19 w' W' ≤ τ
  have hup : ∀ (w' : St → ℝ) (W' : Matrix St (Fin q) ℝ) (Γ' : St → Fin L → ℝ),
      (∀ s l, 0 ≤ Γ' s l) → (∀ s, IsPSDForm (M.lhs20c π s w' W' Γ')) → M.val19 w' W' ≤ τ := by
    intro w' W' Γ' hΓ' h20c'
    obtain ⟨γ', hγ', hγle⟩ := gamma_exists M hM w' W'
    refine hmax _ w' W' γ' Γ' ⟨hγ', hΓ', homog (rep20b M _ w' W' γ') fun ξ => ?_, h20c'⟩
    rw [f20b]
    linarith [hγle ξ]
  have hval : M.val19 w W = τ := le_antisymm (hup w W Γ hΓ h20c)
    (le_ciInf fun ξ => h22b ξ.1 ξ.2)
  have hmem : τ ∈ M.values19 π := ⟨w, W, hF, hval⟩
  refine ⟨fun hL => ⟨⟨hmem, ?_⟩, hF, hval⟩, fun _ => ⟨fun u hu => hu hmem, hF, hval⟩⟩
  rintro t ⟨w', W', hF', rfl⟩
  subst hL
  have h22c := feas19_to M π w' W' hF'
  have hS : ∀ s, ∃ Γs : ℝ, 0 ≤ Γs ∧ ∀ ξ, 0 ≤
      ∑ a, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • (w' + W' *ᵥ ξ))) -
        (w' s + W' s ⬝ᵥ ξ) - Γs * gq (M.O 0) (M.o 0) (M.ω 0) ξ := by
    intro s
    obtain ⟨σ, sv, S, hrep⟩ := rep20c_head M π s w' W'
    obtain ⟨ξb, hξb⟩ := hM.1.2.2
    have key := (sLemma_inhom S (-M.O 0) ((1 / 2 : ℝ) • sv) (-((1 / 2 : ℝ) • M.o 0)) σ
      (-M.ω 0) ⟨ξb, by
        have := hξb 0
        simp only [neg_mulVec, dotProduct_neg, neg_dotProduct, smul_dotProduct, smul_eq_mul]
        linarith⟩).mp (fun x hx => by
          have hxX : x ∈ M.Xi := by
            intro l
            have hl : l = 0 := Subsingleton.elim l 0
            subst hl
            simp only [neg_mulVec, dotProduct_neg, neg_dotProduct, smul_dotProduct,
              smul_eq_mul] at hx
            linarith
          have := h22c x hxX s
          rw [← sub_nonneg, hrep x] at this
          simp only [smul_dotProduct, smul_eq_mul]
          linarith)
    obtain ⟨Γs, hΓs, hall⟩ := key
    refine ⟨Γs, hΓs, fun ξ => ?_⟩
    have h1 := hall ξ
    have h2 := hrep ξ
    simp only [neg_mulVec, dotProduct_neg, neg_dotProduct, smul_dotProduct, smul_eq_mul] at h1
    unfold gq
    linarith
  choose Γs hΓs0 hΓsall using hS
  refine hup w' W' (fun s _ => Γs s) (fun s _ => hΓs0 s) fun s => ?_
  refine homog (rep20c M π s w' W' _) fun ξ => ?_
  rw [f20c, Fin.sum_univ_one]
  exact hΓsall s ξ

end
