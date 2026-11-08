-- Prove2me | solution 1 for PSDPolyApprox.noise_qy
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:49:36.161343+00:00
-- url     : https://prove2.me/submissions/9b8c9a21-8a63-4845-8d92-bad46cd74513

import Mathlib
import Definitions.Def_PSDPolyApprox_noise
import Definitions.Def_PSDPolyApprox_qy

namespace Aux_PSDnoiseqy

open PSDPolyApprox

theorem sum_units (h : ℤˣ → ℝ) : ∑ u : ℤˣ, h u = h 1 + h (-1) := by
  rw [Fintype.sum_eq_add 1 (-1) (by decide)]
  intro u hu
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact absurd rfl hu.1
  · exact absurd rfl hu.2

theorem sq_one (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem expect_prod {n : ℕ} (g : Fin n → ℤˣ → ℝ) :
    expect (fun x : Cube n => ∏ k, g k (x k)) = ∏ k, ((g k 1 + g k (-1)) / 2) := by
  unfold expect
  rw [← Fintype.prod_sum]
  simp_rw [sum_units]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem ortho {n : ℕ} (S T : Finset (Fin n)) :
    expect (fun x => chi T x * chi S x) = if S = T then 1 else 0 := by
  have hfun : (fun x : Cube n => chi T x * chi S x) = fun x => ∏ k,
      ((if k ∈ T then ((x k : ℤ) : ℝ) else 1) * (if k ∈ S then ((x k : ℤ) : ℝ) else 1)) := by
    funext x
    unfold chi
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.univ_inter]
  rw [hfun, expect_prod (fun k u =>
    (if k ∈ T then ((u : ℤ) : ℝ) else 1) * (if k ∈ S then ((u : ℤ) : ℝ) else 1))]
  by_cases h : S = T
  · subst h
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro k _
    split_ifs <;> norm_num
  · rw [if_neg h]
    have : ∃ k, ¬ (k ∈ S ↔ k ∈ T) := by
      by_contra hc
      push_neg at hc
      exact h (Finset.ext hc)
    obtain ⟨k, hk⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases h1 : k ∈ S <;> by_cases h2 : k ∈ T <;> simp_all

theorem noise_chi {n : ℕ} (ρ : ℝ) (T : Finset (Fin n)) (x : Cube n) :
    noise ρ (chi T) x = ρ ^ T.card * chi T x := by
  unfold noise PSDPolyApprox.fourierCoeff
  simp_rw [ortho]
  rw [Finset.sum_eq_single T]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ T) h

theorem fc_lin {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → Cube n → ℝ) (c : ι → ℝ)
    (S : Finset (Fin n)) :
    PSDPolyApprox.fourierCoeff (fun x => ∑ i, c i * f i x) S = ∑ i, c i * PSDPolyApprox.fourierCoeff (f i) S := by
  unfold PSDPolyApprox.fourierCoeff expect
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem noise_lin {n : ℕ} {ι : Type*} [Fintype ι] (ρ : ℝ) (f : ι → Cube n → ℝ) (c : ι → ℝ)
    (x : Cube n) :
    noise ρ (fun x => ∑ i, c i * f i x) x = ∑ i, c i * noise ρ (f i) x := by
  unfold noise
  simp_rw [fc_lin]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro S _
  ring

def P {n : ℕ} (p : Fin n × Fin n) : Finset (Fin n) := if p.1 = p.2 then ∅ else {p.1, p.2}

theorem chi_P {n : ℕ} (p : Fin n × Fin n) (x : Cube n) :
    chi (P p) x = ((x p.1 : ℤ) : ℝ) * ((x p.2 : ℤ) : ℝ) := by
  unfold P chi
  by_cases h : p.1 = p.2
  · rw [if_pos h, Finset.prod_empty, ← h, sq_one]
  · rw [if_neg h, Finset.prod_pair h]

end Aux_PSDnoiseqy

open PSDPolyApprox Aux_PSDnoiseqy in
theorem solution (n : ℕ) (hn : 1 ≤ n) (y : Cube n) (ρ : ℝ) :
    noise ρ (qy n y) = fun x => 1 + ρ ^ 2 * (qy n y x - 1) := by
  set c : Fin n × Fin n → ℝ := fun p => (n : ℝ)⁻¹ * ((y p.1 : ℤ) : ℝ) * ((y p.2 : ℤ) : ℝ)
    with hc
  have hq : qy n y = fun x => ∑ p : Fin n × Fin n, c p * chi (P p) x := by
    funext x
    unfold qy
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [chi_P]
    simp only [hc]
    ring
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  funext x
  have hd : ∀ i : Fin n, c (i, i) * chi (P (i, i)) x = (n : ℝ)⁻¹ := by
    intro i
    rw [chi_P]
    simp only [hc]
    have h1 := sq_one (y i)
    have h2 := sq_one (x i)
    calc (n : ℝ)⁻¹ * ((y i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) * (((x i : ℤ) : ℝ) * ((x i : ℤ) : ℝ))
        = (n : ℝ)⁻¹ * (((y i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) * (((x i : ℤ) : ℝ) * ((x i : ℤ) : ℝ)) := by
          ring
      _ = (n : ℝ)⁻¹ := by rw [h1, h2]; ring
  have hdiag : ∑ p : Fin n × Fin n, (if p.1 = p.2 then c p * chi (P p) x else 0) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [hd]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn0
  have e1 : ∀ p : Fin n × Fin n, c p * (ρ ^ (P p).card * chi (P p) x) =
      (if p.1 = p.2 then c p * chi (P p) x else 0) +
        ρ ^ 2 * (if p.1 = p.2 then 0 else c p * chi (P p) x) := by
    intro p
    by_cases h : p.1 = p.2
    · rw [show P p = ∅ from if_pos h, Finset.card_empty, if_pos h, if_pos h]; ring
    · rw [show P p = {p.1, p.2} from if_neg h, Finset.card_pair h, if_neg h, if_neg h]; ring
  have e2 : ∀ p : Fin n × Fin n, c p * chi (P p) x =
      (if p.1 = p.2 then c p * chi (P p) x else 0) +
        (if p.1 = p.2 then 0 else c p * chi (P p) x) := by
    intro p
    by_cases h : p.1 = p.2
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [hq, noise_lin ρ (fun p => chi (P p)) c x]
  simp only [noise_chi]
  rw [Finset.sum_congr rfl (fun p _ => e1 p), Finset.sum_add_distrib, ← Finset.mul_sum, hdiag,
    Finset.sum_congr rfl (fun p _ => e2 p), Finset.sum_add_distrib, hdiag]
  ring
