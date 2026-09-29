-- Prove2me | solution 1 for RobustLS.Structured.s_procedure_step_eq29
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:56:18.551968+00:00
-- url     : https://prove2.me/submissions/5853bf63-8f9b-4a46-b37a-7af067731442

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

lemma aux_s29_expand {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (u v : ι → ℝ) (s : ℝ) :
    (u + s • v) ⬝ᵥ (M *ᵥ (u + s • v)) =
      u ⬝ᵥ (M *ᵥ u) + s * (u ⬝ᵥ (M *ᵥ v) + v ⬝ᵥ (M *ᵥ u)) + s ^ 2 * (v ⬝ᵥ (M *ᵥ v)) := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

lemma aux_s29_smul {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (w : ι → ℝ) (c : ℝ) :
    (c • w) ⬝ᵥ (M *ᵥ (c • w)) = c ^ 2 * (w ⬝ᵥ (M *ᵥ w)) := by
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma aux_s29_real (c0 c1 c2 p0 p1 p2 : ℝ) (hc0 : 0 < c0) (hc2 : c2 < 0)
    (hroot : ∀ s : ℝ, c0 + s * c1 + s ^ 2 * c2 = 0 → 0 ≤ p0 + s * p1 + s ^ 2 * p2) :
    p0 * c2 ≤ p2 * c0 := by
  have hdisc : 0 ≤ c1 ^ 2 - 4 * c0 * c2 := by nlinarith [sq_nonneg c1]
  obtain ⟨D, hD0, hD2⟩ : ∃ D : ℝ, 0 ≤ D ∧ D ^ 2 = c1 ^ 2 - 4 * c0 * c2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt hdisc⟩
  have hDc1 : c1 < D := by nlinarith [sq_nonneg (c1 - D), sq_nonneg (c1 + D)]
  have hDc2 : -c1 < D := by nlinarith [sq_nonneg (c1 - D), sq_nonneg (c1 + D)]
  have h2c2 : 2 * c2 ≠ 0 := by linarith
  set s1 := (-c1 + D) / (2 * c2) with hs1def
  set s2 := (-c1 - D) / (2 * c2) with hs2def
  have hs1 : s1 < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
  have hs2 : 0 < s2 := div_pos_of_neg_of_neg (by linarith) (by linarith)
  have hs1e : s1 * (2 * c2) = -c1 + D := by rw [hs1def]; exact div_mul_cancel₀ _ h2c2
  have hs2e : s2 * (2 * c2) = -c1 - D := by rw [hs2def]; exact div_mul_cancel₀ _ h2c2
  have r1 : c0 + s1 * c1 + s1 ^ 2 * c2 = 0 := by
    have : 4 * c2 * (c0 + s1 * c1 + s1 ^ 2 * c2) = 0 := by
      have e : 4 * c2 * (c0 + s1 * c1 + s1 ^ 2 * c2)
          = (s1 * (2 * c2)) ^ 2 + 2 * c1 * (s1 * (2 * c2)) + 4 * c0 * c2 := by ring
      rw [e, hs1e]; nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; linarith
    · exact h
  have r2 : c0 + s2 * c1 + s2 ^ 2 * c2 = 0 := by
    have : 4 * c2 * (c0 + s2 * c1 + s2 ^ 2 * c2) = 0 := by
      have e : 4 * c2 * (c0 + s2 * c1 + s2 ^ 2 * c2)
          = (s2 * (2 * c2)) ^ 2 + 2 * c1 * (s2 * (2 * c2)) + 4 * c0 * c2 := by ring
      rw [e, hs2e]; nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; linarith
    · exact h
  have g1 := hroot s1 r1
  have g2 := hroot s2 r2
  have G1 : 0 ≤ s1 * ((c0 * p1 - p0 * c1) + s1 * (c0 * p2 - p0 * c2)) := by
    have e : s1 * ((c0 * p1 - p0 * c1) + s1 * (c0 * p2 - p0 * c2))
        = c0 * (p0 + s1 * p1 + s1 ^ 2 * p2) - p0 * (c0 + s1 * c1 + s1 ^ 2 * c2) := by ring
    rw [e, r1, mul_zero, sub_zero]; exact mul_nonneg hc0.le g1
  have G2 : 0 ≤ s2 * ((c0 * p1 - p0 * c1) + s2 * (c0 * p2 - p0 * c2)) := by
    have e : s2 * ((c0 * p1 - p0 * c1) + s2 * (c0 * p2 - p0 * c2))
        = c0 * (p0 + s2 * p1 + s2 ^ 2 * p2) - p0 * (c0 + s2 * c1 + s2 ^ 2 * c2) := by ring
    rw [e, r2, mul_zero, sub_zero]; exact mul_nonneg hc0.le g2
  have e1 : (c0 * p1 - p0 * c1) + s1 * (c0 * p2 - p0 * c2) ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have e2 : 0 ≤ (c0 * p1 - p0 * c1) + s2 * (c0 * p2 - p0 * c2) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hb : 0 ≤ (s2 - s1) * (c0 * p2 - p0 * c2) := by nlinarith
  have hb' : 0 ≤ c0 * p2 - p0 * c2 := by
    by_contra hcon
    push Not at hcon
    have : (s2 - s1) * (c0 * p2 - p0 * c2) < 0 := mul_neg_of_pos_of_neg (by linarith) hcon
    linarith
  linarith

lemma aux_s29_pair {ι : Type*} [Fintype ι] (P C : Matrix ι ι ℝ)
    (h : ∀ w, 0 ≤ w ⬝ᵥ (C *ᵥ w) → 0 ≤ w ⬝ᵥ (P *ᵥ w)) (u v : ι → ℝ)
    (hu : 0 < u ⬝ᵥ (C *ᵥ u)) (hv : v ⬝ᵥ (C *ᵥ v) < 0) :
    (u ⬝ᵥ (P *ᵥ u)) * (v ⬝ᵥ (C *ᵥ v)) ≤ (v ⬝ᵥ (P *ᵥ v)) * (u ⬝ᵥ (C *ᵥ u)) := by
  refine aux_s29_real _ (u ⬝ᵥ (C *ᵥ v) + v ⬝ᵥ (C *ᵥ u)) _ _
    (u ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ u)) _ hu hv ?_
  intro s hs
  have := h (u + s • v) (by rw [aux_s29_expand]; exact hs.ge)
  rwa [aux_s29_expand] at this

lemma aux_s29_slemma {ι : Type*} [Fintype ι] (P C : Matrix ι ι ℝ)
    (h : ∀ w, 0 ≤ w ⬝ᵥ (C *ᵥ w) → 0 ≤ w ⬝ᵥ (P *ᵥ w)) (u0 : ι → ℝ)
    (hu0 : 0 < u0 ⬝ᵥ (C *ᵥ u0)) :
    ∃ τ : ℝ, ∀ w, τ * (w ⬝ᵥ (C *ᵥ w)) ≤ w ⬝ᵥ (P *ᵥ w) := by
  let S : Set ℝ := {r | ∃ u, 0 < u ⬝ᵥ (C *ᵥ u) ∧ r = u ⬝ᵥ (P *ᵥ u) / u ⬝ᵥ (C *ᵥ u)}
  have hne : S.Nonempty := ⟨_, u0, hu0, rfl⟩
  have hbdd : BddBelow S := ⟨0, by
    rintro r ⟨u, hu, rfl⟩
    exact div_nonneg (h u hu.le) hu.le⟩
  refine ⟨sInf S, fun w => ?_⟩
  rcases lt_trichotomy (w ⬝ᵥ (C *ᵥ w)) 0 with hw | hw | hw
  · have key : w ⬝ᵥ (P *ᵥ w) / w ⬝ᵥ (C *ᵥ w) ≤ sInf S := by
      apply le_csInf hne
      rintro r ⟨u, hu, rfl⟩
      rw [div_le_iff_of_neg hw, div_mul_eq_mul_div, div_le_iff₀ hu]
      exact aux_s29_pair P C h u w hu hw
    rwa [div_le_iff_of_neg hw] at key
  · rw [hw, mul_zero]; exact h w hw.ge
  · have key : sInf S ≤ w ⬝ᵥ (P *ᵥ w) / w ⬝ᵥ (C *ᵥ w) := csInf_le hbdd ⟨w, hw, rfl⟩
    rwa [le_div_iff₀ hw] at key

noncomputable def aux_s29_E0 (p : ℕ) : Matrix (Unit ⊕ Fin p) (Unit ⊕ Fin p) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => 0))

noncomputable def aux_s29_J (p : ℕ) : Matrix (Unit ⊕ Fin p) (Unit ⊕ Fin p) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

lemma aux_s29_E0form {p : ℕ} (w : Unit ⊕ Fin p → ℝ) :
    w ⬝ᵥ (aux_s29_E0 p *ᵥ w) = w (Sum.inl ()) ^ 2 := by
  simp [aux_s29_E0, dotProduct, mulVec_diagonal, Fintype.sum_sum_type]
  ring

lemma aux_s29_Jform {p : ℕ} (w : Unit ⊕ Fin p → ℝ) :
    w ⬝ᵥ (aux_s29_J p *ᵥ w) = w (Sum.inl ()) ^ 2 - ∑ i, w (Sum.inr i) ^ 2 := by
  simp [aux_s29_J, dotProduct, mulVec_diagonal, Fintype.sum_sum_type]
  ring_nf

lemma aux_s29_calF_eq {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam τ : ℝ) :
    calF A0 A b0 b x lam τ = (lam • aux_s29_E0 p - hgFBlock A0 A b0 b x) - τ • aux_s29_J p := by
  ext i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
    simp [calF, hgFBlock, aux_s29_E0, aux_s29_J, diagonal_apply, one_apply]
  · ring
  · split_ifs <;> ring

end RobustLS.Structured

open RobustLS.Structured

theorem solution {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 → oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) ≤ lam) ↔
      ∃ τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef := by
  set H := hgFBlock A0 A b0 b x with hH
  have hPform : ∀ w : Unit ⊕ Fin p → ℝ,
      w ⬝ᵥ ((lam • aux_s29_E0 p - H) *ᵥ w) = lam * w (Sum.inl ()) ^ 2 - w ⬝ᵥ (H *ᵥ w) := by
    intro w
    rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, aux_s29_E0form, smul_eq_mul]
  have hFform : ∀ (τ : ℝ) (w : Unit ⊕ Fin p → ℝ),
      w ⬝ᵥ (calF A0 A b0 b x lam τ *ᵥ w)
        = w ⬝ᵥ ((lam • aux_s29_E0 p - H) *ᵥ w) - τ * (w ⬝ᵥ (aux_s29_J p *ᵥ w)) := by
    intro τ w
    rw [aux_s29_calF_eq, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hstack : ∀ δ : Fin p → ℝ, oneStack δ ⬝ᵥ (aux_s29_J p *ᵥ oneStack δ) = 1 - δ ⬝ᵥ δ := by
    intro δ
    rw [aux_s29_Jform]
    simp [oneStack, dotProduct, sq]
  have hherm : ∀ τ : ℝ, (calF A0 A b0 b x lam τ).IsHermitian := by
    intro τ
    refine Matrix.IsHermitian.ext ?_
    intro i j
    rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
      simp [calF, Fmat, mul_apply, one_apply, mul_comm, eq_comm]
  constructor
  · intro hδ
    have hcond : ∀ w : Unit ⊕ Fin p → ℝ, 0 ≤ w ⬝ᵥ (aux_s29_J p *ᵥ w) →
        0 ≤ w ⬝ᵥ ((lam • aux_s29_E0 p - H) *ᵥ w) := by
      intro w hw
      by_cases ht : w (Sum.inl ()) = 0
      · rw [aux_s29_Jform, ht] at hw
        have hsum : ∑ i, w (Sum.inr i) ^ 2 = 0 := by
          have : 0 ≤ ∑ i, w (Sum.inr i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
          linarith
        have hz : ∀ i, w (Sum.inr i) = 0 := by
          intro i
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w (Sum.inr i)))).mp
            hsum i (Finset.mem_univ _)
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        have hw0 : w = 0 := by
          funext k
          rcases k with ⟨⟩ | k
          · exact ht
          · exact hz k
        rw [hw0]; simp
      · set t := w (Sum.inl ()) with htdef
        set δ : Fin p → ℝ := t⁻¹ • (fun i => w (Sum.inr i)) with hδdef
        have hwe : w = t • oneStack δ := by
          funext k
          rcases k with ⟨⟩ | k
          · simp [oneStack, htdef]
          · simp [oneStack, hδdef]
            field_simp
        have ht2 : 0 < t ^ 2 := by positivity
        rw [hwe, aux_s29_smul] at hw ⊢
        rw [hstack] at hw
        have hδ1 : δ ⬝ᵥ δ ≤ 1 := by
          by_contra hcon
          push Not at hcon
          have : t ^ 2 * (1 - δ ⬝ᵥ δ) < 0 := mul_neg_of_pos_of_neg ht2 (by linarith)
          linarith
        have := hδ δ hδ1
        rw [hPform]
        have h1 : oneStack δ (Sum.inl ()) = 1 := rfl
        rw [h1]
        apply mul_nonneg ht2.le
        linarith
    have hpos : 0 < (Sum.elim (fun _ => 1) (fun _ => 0) : Unit ⊕ Fin p → ℝ) ⬝ᵥ
        (aux_s29_J p *ᵥ Sum.elim (fun _ => 1) (fun _ => 0)) := by
      rw [aux_s29_Jform]
      simp
    obtain ⟨τ, hτ⟩ := aux_s29_slemma (lam • aux_s29_E0 p - H) (aux_s29_J p) hcond _ hpos
    refine ⟨τ, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hherm τ) ?_⟩
    intro w
    rw [star_trivial, hFform]
    linarith [hτ w]
  · rintro ⟨τ, hτ⟩ δ hδ
    have hτ0 : 0 ≤ τ := by
      have hd := hτ.diag_nonneg (i := Sum.inr ⟨0, hp⟩)
      have hF : 0 ≤ Fmat A b x ⟨0, hp⟩ ⟨0, hp⟩ := by
        simp only [Fmat, mul_apply, transpose_apply]
        exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
      simp [calF] at hd
      linarith
    have h1 := hτ.dotProduct_mulVec_nonneg (oneStack δ)
    rw [star_trivial, hFform, hPform, hstack] at h1
    have h2 : oneStack δ (Sum.inl ()) = 1 := rfl
    rw [h2] at h1
    have h3 : 0 ≤ τ * (1 - δ ⬝ᵥ δ) := mul_nonneg hτ0 (by linarith)
    nlinarith
