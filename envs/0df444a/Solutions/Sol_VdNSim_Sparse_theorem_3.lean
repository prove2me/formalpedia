-- Prove2me | solution 1 for VdNSim.Sparse.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T21:47:53.888008+00:00
-- url     : https://prove2.me/submissions/a51b3948-a9a6-4212-b1da-02bea0e65294

import Definitions.Def_VdNSim_Sparse_Model
import Theorems.Thm_VdNSim_Sparse_eq_5
import Theorems.Thm_VdNSim_Sparse_eqs_6_8
import Theorems.Thm_VdNSim_Sparse_F_bound
import Theorems.Thm_VdNSim_Sparse_claim_2
import Theorems.Thm_VdNSim_Sparse_complex_hoeffding

noncomputable section

open VdNSim.Sparse

namespace AuxThm3

lemma double_sum_marginalize {I J : Type*} [Fintype I] [Fintype J]
    (wI : I → ℝ) (wJ : J → ℝ) (hI : ∑ i, wI i = 1) (hJ : ∑ j, wJ j = 1)
    (A : I → ℝ) (B : J → ℝ) :
    ∑ i, ∑ j, wI i * wJ j * (A i + B j) =
      (∑ i, wI i * A i) + (∑ j, wJ j * B j) := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  · calc ∑ i, ∑ j, wI i * wJ j * A i
      _ = ∑ i, (wI i * A i) * ∑ j, wJ j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ i, wI i * A i := by simp [hJ]
  · calc ∑ i, ∑ j, wI i * wJ j * B j
      _ = ∑ j, ∑ i, wI i * wJ j * B j := Finset.sum_comm
      _ = ∑ j, (wJ j * B j) * ∑ i, wI i := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ j, wJ j * B j := by simp [hI]

lemma double_sum_exchange {I J S : Type*} [Fintype I] [Fintype J] [Fintype S]
    (wI : I → ℝ) (wJ : J → ℝ) (hI : ∑ i, wI i = 1) (hJ : ∑ j, wJ j = 1)
    (A : S → I → ℝ) (B : S → J → ℝ) :
    ∑ i, ∑ j, (wI i * wJ j * ∑ s, (A s i + B s j)) =
      ∑ s, ((∑ i, wI i * A s i) + (∑ j, wJ j * B s j)) := by
  calc ∑ i, ∑ j, (wI i * wJ j * ∑ s, (A s i + B s j))
    _ = ∑ i, ∑ s, ∑ j, wI i * wJ j * (A s i + B s j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ j, wI i * wJ j * (A s i + B s j) := Finset.sum_comm
    _ = ∑ s, ((∑ i, wI i * A s i) + (∑ j, wJ j * B s j)) :=
        Finset.sum_congr rfl (fun s _ => double_sum_marginalize wI wJ hI hJ (A s) (B s))

lemma sum_prob_prod_eq_one {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : ∑ x, p x = 1) (K : ℕ) :
    ∑ xs : Fin K → X, ∏ k, p (xs k) = 1 := by
  have h := (Fintype.prod_sum (fun (_ : Fin K) (x : X) => p x)).symm
  rw [h]
  simp [hp]

lemma indicator_sum_bound {s : ℕ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε)
    (A B : Fin s → ℂ) (hAB : ‖∑ i, (A i + B i)‖ ≤ ∑ i, (‖A i‖ + ‖B i‖)) :
    (if ε < ‖∑ i, (A i + B i)‖ then (1 : ℝ) else 0) ≤
      ∑ i : Fin s, ((if ε / (2 * (s : ℝ)) < ‖A i‖ then (1 : ℝ) else 0) +
                    (if ε / (2 * (s : ℝ)) < ‖B i‖ then (1 : ℝ) else 0)) := by
  let term : Fin s → ℝ := fun j =>
    (if ε / (2 * (s : ℝ)) < ‖A j‖ then (1 : ℝ) else 0) +
    (if ε / (2 * (s : ℝ)) < ‖B j‖ then (1 : ℝ) else 0)
  have hterm_nonneg : ∀ j : Fin s, 0 ≤ term j := by
    intro j
    dsimp [term]
    refine add_nonneg ?_ ?_ <;> (split_ifs <;> norm_num)
  change (if ε < ‖∑ i, (A i + B i)‖ then (1 : ℝ) else 0) ≤ ∑ i : Fin s, term i
  split_ifs with h
  · have hsR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs
    have hcontra : ∃ i : Fin s, ε / (2 * (s : ℝ)) < ‖A i‖ ∨ ε / (2 * (s : ℝ)) < ‖B i‖ := by
      by_contra hall
      push_neg at hall
      have hsum : ∑ i : Fin s, (‖A i‖ + ‖B i‖) ≤ ε := by
        calc ∑ i : Fin s, (‖A i‖ + ‖B i‖)
          _ ≤ ∑ i : Fin s, (ε / (2 * (s : ℝ)) + ε / (2 * (s : ℝ))) :=
              Finset.sum_le_sum (fun i _ => add_le_add (hall i).1 (hall i).2)
          _ = ∑ i : Fin s, (ε / (s : ℝ)) :=
              Finset.sum_congr rfl (fun i _ => by ring)
          _ = (s : ℝ) * (ε / (s : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = ε := mul_div_cancel₀ ε (ne_of_gt hsR)
      exact lt_irrefl ε (lt_of_lt_of_le h (hAB.trans hsum))
    rcases hcontra with ⟨i, hiA | hiB⟩
    · have hi_term : (1 : ℝ) ≤ term i := by
        dsimp [term]
        rw [if_pos hiA]
        have : 0 ≤ (if ε / (2 * (s : ℝ)) < ‖B i‖ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        linarith
      exact hi_term.trans (Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i))
    · have hi_term : (1 : ℝ) ≤ term i := by
        dsimp [term]
        rw [if_pos hiB]
        have : 0 ≤ (if ε / (2 * (s : ℝ)) < ‖A i‖ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        linarith
      exact hi_term.trans (Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i))
  · exact Finset.sum_nonneg (fun j _ => hterm_nonneg j)

lemma estimate_sub_matElem {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (ψ ϕ : X → ℂ) {K : ℕ}
    (xs ys : Fin K → X) :
    estimate ψ ϕ D xs ys - matElem ϕ A ψ =
      ∑ i : Fin s,
        (((K : ℂ)⁻¹ * ∑ k, F ψ ϕ D i (xs k) - expect (prob ψ) (F ψ ϕ D i)) +
         ((K : ℂ)⁻¹ * ∑ k, G ψ ϕ D i (ys k) - expect (prob ϕ) (G ψ ϕ D i))) := by
  unfold estimate
  rw [eq_5 D ψ ϕ]
  have h_elem : (∑ i : Fin s, ∑ x, D.α i x * star (ϕ (D.r i x)) * ψ x) =
      ∑ i : Fin s, (expect (prob ψ) (F ψ ϕ D i) + expect (prob ϕ) (G ψ ϕ D i)) := by
    refine Finset.sum_congr rfl (fun i _ => eqs_6_8 D ψ ϕ i)
  rw [h_elem, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => by ring)

lemma F_exp_le {s K : ℕ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    4 * Real.exp (-((K : ℝ) * (ε / (2 * (s : ℝ))) ^ 2) / 8) ≤
      4 * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by
  have _ := hε
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have heq : -((K : ℝ) * (ε / (2 * (s : ℝ))) ^ 2) / 8 = -((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 2) := by
    ring
  rw [heq, neg_div, neg_div, neg_le_neg_iff]
  have hpow : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ 4 := pow_le_pow_right₀ hs1 (by omega)
  have hden : 32 * (s : ℝ) ^ 2 ≤ 32 * (s : ℝ) ^ 4 := by linarith
  have hnum : 0 ≤ (K : ℝ) * ε ^ 2 := by positivity
  have hden_pos : 0 < 32 * (s : ℝ) ^ 2 := by positivity
  exact div_le_div_of_nonneg_left hnum hden_pos hden

lemma expect_smul {X : Type*} [Fintype X] (p : X → ℝ) (c : ℂ) (f : X → ℂ) :
    expect p (fun x => c * f x) = c * expect p f := by
  unfold expect
  simp_rw [mul_left_comm (p _ : ℂ) c (f _)]
  rw [← Finset.mul_sum]

lemma mean_smul {X : Type*} [Fintype X] {K : ℕ} (p : X → ℝ) (c : ℂ) (f : X → ℂ) (ys : Fin K → X) :
    (K : ℂ)⁻¹ * ∑ k, c * f (ys k) - expect p (fun y => c * f y) =
      c * ((K : ℂ)⁻¹ * ∑ k, f (ys k) - expect p f) := by
  rw [expect_smul, ← Finset.mul_sum]
  ring

lemma norm_natCast_inv {s : ℕ} (hs : 0 < s) :
    ‖(s : ℂ)⁻¹‖ = (s : ℝ)⁻¹ := by
  have _ := hs
  rw [norm_inv, Complex.norm_natCast]

lemma lt_iff_rescaled {s : ℕ} (hs : 0 < s) {ε : ℝ} (Z : ℝ) :
    (ε / (2 * (s : ℝ)) < Z) ↔ (ε / (2 * (s : ℝ) ^ 2) < (s : ℝ)⁻¹ * Z) := by
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
  constructor <;> intro h
  · calc ε / (2 * (s : ℝ) ^ 2)
      _ = (s : ℝ)⁻¹ * (ε / (2 * (s : ℝ))) := by field_simp
      _ < (s : ℝ)⁻¹ * Z := mul_lt_mul_of_pos_left h (inv_pos.mpr hs_pos)
  · calc ε / (2 * (s : ℝ))
      _ = (s : ℝ) * (ε / (2 * (s : ℝ) ^ 2)) := by field_simp
      _ < (s : ℝ) * ((s : ℝ)⁻¹ * Z) := mul_lt_mul_of_pos_left h hs_pos
      _ = Z := by rw [← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]

lemma G_tail_bound {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s K : ℕ} (hs : 0 < s) (hK : 0 < K)
    (hsp : IsSparse s A) (hA : QAlgorithms.specNorm A ≤ 1)
    (D : ColumnData A s) (ψ ϕ : X → ℂ) (hϕ : ∑ y, prob ϕ y = 1)
    (i : Fin s) {ε : ℝ} (hε : 0 < ε) :
    sampleProb (prob ϕ) K (fun ys =>
      ε / (2 * (s : ℝ)) < ‖(K : ℂ)⁻¹ * ∑ k, G ψ ϕ D i (ys k) - expect (prob ϕ) (G ψ ϕ D i)‖) ≤
      4 * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by
  let g : X → ℂ := fun y => (s : ℂ)⁻¹ * G ψ ϕ D i y
  let ε' : ℝ := ε / (2 * (s : ℝ) ^ 2)
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs
  have hε' : 0 < ε' := by positivity
  have hg_norm : ∀ y, ‖g y‖ ≤ 1 := by
    intro y
    dsimp [g]
    rw [norm_mul, norm_natCast_inv hs]
    have hg := claim_2 hsp hA D ψ ϕ i y
    have h1 : (s : ℝ)⁻¹ * ‖G ψ ϕ D i y‖ ≤ (s : ℝ)⁻¹ * (s : ℝ) :=
      mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr (le_of_lt hs_pos))
    rw [inv_mul_cancel₀ (ne_of_gt hs_pos)] at h1
    exact h1
  have hprob0 : ∀ y, 0 ≤ prob ϕ y := fun y => by unfold prob; positivity
  have hH := complex_hoeffding (prob ϕ) hprob0 hϕ g hg_norm hK hε'
  have hequiv : ∀ ys : Fin K → X,
      (ε / (2 * (s : ℝ)) < ‖(K : ℂ)⁻¹ * ∑ k, G ψ ϕ D i (ys k) - expect (prob ϕ) (G ψ ϕ D i)‖) ↔
      (ε' < ‖(K : ℂ)⁻¹ * ∑ k, g (ys k) - expect (prob ϕ) g‖) := by
    intro ys
    have hsmul := mean_smul (prob ϕ) (s : ℂ)⁻¹ (G ψ ϕ D i) ys
    have hnorm : ‖(K : ℂ)⁻¹ * ∑ k, g (ys k) - expect (prob ϕ) g‖ =
        (s : ℝ)⁻¹ * ‖(K : ℂ)⁻¹ * ∑ k, G ψ ϕ D i (ys k) - expect (prob ϕ) (G ψ ϕ D i)‖ := by
      rw [hsmul, norm_mul, norm_natCast_inv hs]
    rw [hnorm]
    exact lt_iff_rescaled hs _
  have hcong : (fun ys : Fin K → X =>
      ε / (2 * (s : ℝ)) < ‖(K : ℂ)⁻¹ * ∑ k, G ψ ϕ D i (ys k) - expect (prob ϕ) (G ψ ϕ D i)‖) =
      (fun ys : Fin K → X => ε' < ‖(K : ℂ)⁻¹ * ∑ k, g (ys k) - expect (prob ϕ) g‖) :=
    funext (fun ys => propext (hequiv ys))
  rw [hcong]
  refine hH.trans ?_
  have heq : -((K : ℝ) * ε' ^ 2) / 8 = -((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4) := by
    dsimp [ε']
    ring
  rw [heq]

lemma F_tail_bound {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s K : ℕ} (hs : 0 < s) (hK : 0 < K)
    (hA : QAlgorithms.specNorm A ≤ 1)
    (D : ColumnData A s) (ψ ϕ : X → ℂ) (hψ : ∑ x, prob ψ x = 1)
    (i : Fin s) {ε : ℝ} (hε : 0 < ε) :
    sampleProb (prob ψ) K (fun xs =>
      ε / (2 * (s : ℝ)) < ‖(K : ℂ)⁻¹ * ∑ k, F ψ ϕ D i (xs k) - expect (prob ψ) (F ψ ϕ D i)‖) ≤
      4 * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs
  have hε_div : 0 < ε / (2 * (s : ℝ)) := by positivity
  have hprob0 : ∀ x, 0 ≤ prob ψ x := fun x => by unfold prob; positivity
  have hH := complex_hoeffding (prob ψ) hprob0 hψ (F ψ ϕ D i) (F_bound hA D ψ ϕ i) hK hε_div
  exact hH.trans (F_exp_le hs hε)

end AuxThm3

open VdNSim.Sparse AuxThm3 in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    {s K : ℕ} (hK : 0 < K)
    (ψ ϕ : X → ℂ) (hψ : ∑ x, prob ψ x = 1) (hϕ : ∑ y, prob ϕ y = 1)
    (A : Matrix X X ℂ) (hsp : IsSparse s A)
    (hA : QAlgorithms.specNorm A ≤ 1) (D : ColumnData A s)
    {ε : ℝ} (hε : 0 < ε) :
    failProb ψ ϕ D K (matElem ϕ A ψ) ε ≤
      8 * (s : ℝ) * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- s = 0
    have hest : ∀ xs ys : Fin K → X, estimate ψ ϕ D xs ys = 0 := by
      intro xs ys
      unfold estimate
      simp only [IsEmpty.forall_iff, Finset.univ_eq_empty, Finset.sum_empty]
    have hmat : matElem ϕ A ψ = 0 := by
      rw [eq_5 D ψ ϕ]
      simp only [IsEmpty.forall_iff, Finset.univ_eq_empty, Finset.sum_empty]
    have hfail : failProb ψ ϕ D K (matElem ϕ A ψ) ε = 0 := by
      unfold failProb
      refine Finset.sum_eq_zero (fun xs _ => ?_)
      refine Finset.sum_eq_zero (fun ys _ => ?_)
      rw [hest xs ys, hmat, sub_zero, norm_zero]
      have : ¬(ε < 0) := not_lt_of_gt hε
      rw [if_neg this, mul_zero]
    rw [hfail]
    ring_nf
    rfl
  · -- s > 0
    let ΔF : Fin s → (Fin K → X) → ℂ := fun i xs =>
      (K : ℂ)⁻¹ * ∑ k, F ψ ϕ D i (xs k) - expect (prob ψ) (F ψ ϕ D i)
    let ΔG : Fin s → (Fin K → X) → ℂ := fun i ys =>
      (K : ℂ)⁻¹ * ∑ k, G ψ ϕ D i (ys k) - expect (prob ϕ) (G ψ ϕ D i)
    have hind : ∀ (xs ys : Fin K → X),
        (if ε < ‖estimate ψ ϕ D xs ys - matElem ϕ A ψ‖ then (1 : ℝ) else 0) ≤
          ∑ i : Fin s, ((if ε / (2 * (s : ℝ)) < ‖ΔF i xs‖ then (1 : ℝ) else 0) +
                        (if ε / (2 * (s : ℝ)) < ‖ΔG i ys‖ then (1 : ℝ) else 0)) := by
      intro xs ys
      rw [estimate_sub_matElem D ψ ϕ xs ys]
      have hAB : ‖∑ i : Fin s, (ΔF i xs + ΔG i ys)‖ ≤ ∑ i : Fin s, (‖ΔF i xs‖ + ‖ΔG i ys‖) := by
        calc ‖∑ i : Fin s, (ΔF i xs + ΔG i ys)‖
          _ ≤ ∑ i : Fin s, ‖ΔF i xs + ΔG i ys‖ := norm_sum_le _ _
          _ ≤ ∑ i : Fin s, (‖ΔF i xs‖ + ‖ΔG i ys‖) := Finset.sum_le_sum (fun i _ => norm_add_le _ _)
      exact indicator_sum_bound hs hε (fun i => ΔF i xs) (fun i => ΔG i ys) hAB
    have hw_nonneg : ∀ (xs ys : Fin K → X), 0 ≤ (∏ k, prob ψ (xs k)) * (∏ k, prob ϕ (ys k)) := by
      intro xs ys
      refine mul_nonneg ?_ ?_
      · exact Finset.prod_nonneg (fun k _ => by unfold prob; positivity)
      · exact Finset.prod_nonneg (fun k _ => by unfold prob; positivity)
    have hle_double : failProb ψ ϕ D K (matElem ϕ A ψ) ε ≤
        ∑ xs : Fin K → X, ∑ ys : Fin K → X,
          (∏ k, prob ψ (xs k)) * (∏ k, prob ϕ (ys k)) *
            ∑ i : Fin s, ((if ε / (2 * (s : ℝ)) < ‖ΔF i xs‖ then (1 : ℝ) else 0) +
                          (if ε / (2 * (s : ℝ)) < ‖ΔG i ys‖ then (1 : ℝ) else 0)) := by
      unfold failProb
      refine Finset.sum_le_sum (fun xs _ => ?_)
      refine Finset.sum_le_sum (fun ys _ => ?_)
      exact mul_le_mul_of_nonneg_left (hind xs ys) (hw_nonneg xs ys)
    have hone_ψ := sum_prob_prod_eq_one (prob ψ) hψ K
    have hone_ϕ := sum_prob_prod_eq_one (prob ϕ) hϕ K
    have hexch := double_sum_exchange
      (fun xs : Fin K → X => ∏ k, prob ψ (xs k))
      (fun ys : Fin K → X => ∏ k, prob ϕ (ys k))
      hone_ψ hone_ϕ
      (fun (i : Fin s) (xs : Fin K → X) => if ε / (2 * (s : ℝ)) < ‖ΔF i xs‖ then (1 : ℝ) else 0)
      (fun (i : Fin s) (ys : Fin K → X) => if ε / (2 * (s : ℝ)) < ‖ΔG i ys‖ then (1 : ℝ) else 0)
    have hle_sum : failProb ψ ϕ D K (matElem ϕ A ψ) ε ≤
        ∑ i : Fin s, (sampleProb (prob ψ) K (fun xs => ε / (2 * (s : ℝ)) < ‖ΔF i xs‖) +
                     sampleProb (prob ϕ) K (fun ys => ε / (2 * (s : ℝ)) < ‖ΔG i ys‖)) := by
      unfold sampleProb
      exact hle_double.trans (le_of_eq hexch)
    have h_bound_i : ∀ i : Fin s,
        sampleProb (prob ψ) K (fun xs => ε / (2 * (s : ℝ)) < ‖ΔF i xs‖) +
        sampleProb (prob ϕ) K (fun ys => ε / (2 * (s : ℝ)) < ‖ΔG i ys‖) ≤
        8 * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by
      intro i
      have hF := F_tail_bound hs hK hA D ψ ϕ hψ i hε
      have hG := G_tail_bound hs hK hsp hA D ψ ϕ hϕ i hε
      linarith
    have h_total : ∑ i : Fin s,
        (sampleProb (prob ψ) K (fun xs => ε / (2 * (s : ℝ)) < ‖ΔF i xs‖) +
         sampleProb (prob ϕ) K (fun ys => ε / (2 * (s : ℝ)) < ‖ΔG i ys‖)) ≤
        8 * (s : ℝ) * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by
      calc ∑ i : Fin s, (sampleProb (prob ψ) K (fun xs => ε / (2 * (s : ℝ)) < ‖ΔF i xs‖) +
                        sampleProb (prob ϕ) K (fun ys => ε / (2 * (s : ℝ)) < ‖ΔG i ys‖))
        _ ≤ ∑ i : Fin s, 8 * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) :=
            Finset.sum_le_sum (fun i _ => h_bound_i i)
        _ = (s : ℝ) * (8 * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = 8 * (s : ℝ) * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by ring
    exact hle_sum.trans h_total
