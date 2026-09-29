-- Prove2me | solution 1 for SmaleNinth.khachiyan_nonempty_imp
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T02:30:23.324713+00:00
-- url     : https://prove2.me/submissions/d5f0cda4-a106-4016-86e6-b2f277f66547

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_Khachiyan
import Theorems.Thm_SmaleNinth_exists_integral_farkas_certificate

open Matrix LinearOptimization

namespace KhachAux

/-- Row `i < m` of the perturbed system is row `i` of `A` with right-hand side `bᵢ − ε`. -/
lemma orig_row {m n : ℕ} (U : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℝ)
    (hx : x ∈ polyhedron (SmaleNinth.khachiyanSystemA A) (SmaleNinth.khachiyanSystemb n U b))
    (i : Fin m) :
    (b i : ℝ) - SmaleNinth.khachiyanEps n U ≤ ∑ j, (A i j : ℝ) * x j := by
  have hlt : (i : ℕ) < m + n + n := by omega
  have h := hx ⟨(i : ℕ), hlt⟩
  have hb : SmaleNinth.khachiyanSystemb n U b ⟨(i : ℕ), hlt⟩
      = (b i : ℝ) - SmaleNinth.khachiyanEps n U := by
    simp only [SmaleNinth.khachiyanSystemb, dif_pos i.isLt, Fin.eta]
  have ha : (SmaleNinth.khachiyanSystemA A).mulVec x ⟨(i : ℕ), hlt⟩
      = ∑ j, (A i j : ℝ) * x j := by
    simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA,
      dif_pos i.isLt, Fin.eta]
  rw [hb, ha] at h
  exact h

end KhachAux

open KhachAux

theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U) (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    (polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty →
      (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty := by
  rintro ⟨x, hx⟩
  by_contra hcon
  have hempty : polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hcon
  obtain ⟨y, hy0, hyA, hyb, hyS⟩ :=
    SmaleNinth.exists_integral_farkas_certificate U hU hn A b hA hb hempty
  set ε : ℝ := SmaleNinth.khachiyanEps n U with hε
  set S : ℝ := ∑ i, (y i : ℝ) with hS
  -- positivity facts about the constants
  have hUR : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have hUpos : (0 : ℝ) < (U : ℝ) := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hden : (0 : ℝ) < 2 * ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) * (U : ℝ) ^ (n + 1) := by
    have : (0 : ℝ) < (U : ℝ) ^ (n + 1) := pow_pos hUpos _
    positivity
  have hεpos : 0 < ε := by
    rw [hε, SmaleNinth.khachiyanEps]
    exact div_pos one_pos hden
  -- the dual certificate is nonnegative, so the ℓ¹ norm is its sum
  have hy0R : ∀ i, (0 : ℝ) ≤ (y i : ℝ) := fun i => by exact_mod_cast hy0 i
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ => hy0R i
  -- `ε · S ≤ 1/2`, the whole point of the constant `ε`
  have hSle : S ≤ ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) * (U : ℝ) ^ (n + 1) := by
    have : ((∑ i, y i : ℤ) : ℝ)
        ≤ (((n + 1) * (n + 1).factorial * U ^ (n + 1) : ℤ) : ℝ) := by exact_mod_cast hyS
    push_cast at this
    rw [hS]; push_cast; linarith
  have hεS : ε * S ≤ 1 / 2 := by
    rw [hε, SmaleNinth.khachiyanEps]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
    nlinarith [hSle, hSnn, hfac]
  -- multiply the relaxed system by the certificate
  have hkey : (0 : ℝ) ≤ ∑ i, (y i : ℝ) * (∑ j, (A i j : ℝ) * x j) -
      (∑ i, (y i : ℝ) * ((b i : ℝ) - ε)) := by
    have : ∀ i ∈ Finset.univ, (y i : ℝ) * ((b i : ℝ) - ε)
        ≤ (y i : ℝ) * (∑ j, (A i j : ℝ) * x j) := fun i _ =>
      mul_le_mul_of_nonneg_left (orig_row U A b x hx i) (hy0R i)
    have := Finset.sum_le_sum this
    linarith
  -- `yᵀA = 0` collapses the left-hand sum to zero
  have hzero : ∑ i, (y i : ℝ) * (∑ j, (A i j : ℝ) * x j) = 0 := by
    have hswap : ∑ i, (y i : ℝ) * (∑ j, (A i j : ℝ) * x j)
        = ∑ j, (∑ i, (y i : ℝ) * (A i j : ℝ)) * x j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hswap]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∑ i, (y i : ℝ) * (A i j : ℝ) = 0 := by
      have h0 := hyA j
      have hc : ((∑ i, y i * A i j : ℤ) : ℝ) = 0 := by rw [h0]; norm_num
      push_cast at hc
      exact hc
    rw [this, zero_mul]
  -- and `yᵀb ≥ 1` on the right
  have hrhs : ∑ i, (y i : ℝ) * ((b i : ℝ) - ε) = (∑ i, (y i : ℝ) * (b i : ℝ)) - ε * S := by
    rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hyb1 : (1 : ℝ) ≤ ∑ i, (y i : ℝ) * (b i : ℝ) := by
    have : ((1 : ℤ) : ℝ) ≤ ((∑ i, y i * b i : ℤ) : ℝ) := by exact_mod_cast hyb
    push_cast at this
    exact this
  rw [hzero, hrhs] at hkey
  linarith
