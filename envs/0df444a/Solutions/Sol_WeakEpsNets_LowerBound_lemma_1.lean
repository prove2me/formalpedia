-- Prove2me | solution 1 for WeakEpsNets.LowerBound.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:01:33.397446+00:00
-- url     : https://prove2.me/submissions/cd401e51-6721-4ac1-b7ed-f9f15a7fc388

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Parameters

section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace WeakEpsNets.Dev.L1
open Polynomial

def M1 {R : Type} [CommRing R] (a1 a2 a3 t : R) : R := (t - a2) * (t - a3) * (a3 - a2)
def M2 {R : Type} [CommRing R] (a1 a2 a3 t : R) : R := -((t - a1) * (t - a3) * (a3 - a1))
def M3 {R : Type} [CommRing R] (a1 a2 a3 t : R) : R := (t - a1) * (t - a2) * (a2 - a1)
def NN {R : Type} [CommRing R] (a1 a2 a3 : R) : R := (a2 - a1) * (a3 - a1) * (a3 - a2)

lemma abs3 (q : ℤ) (x y z : ℤ) (hx : |x| ≤ q) (hy : |y| ≤ q) (hz : |z| ≤ q) :
    |x * y * z| ≤ q ^ 3 := by
  have h0 : 0 ≤ q := le_trans (abs_nonneg _) hx
  rw [abs_mul, abs_mul]
  calc |x| * |y| * |z| ≤ q * q * q := by gcongr
    _ = q ^ 3 := by ring

lemma absd (q x y : ℤ) (hx1 : 1 ≤ x) (hx2 : x ≤ q) (hy1 : 1 ≤ y) (hy2 : y ≤ q) : |x - y| ≤ q := by
  rw [abs_le]; constructor <;> omega

lemma key (q : ℕ) (a1 a2 a3 a b1 b2 b3 b : ℕ) (G : ℝ[X]) (hG : G.natDegree = 2)
    (ha1 : 1 ≤ a1 ∧ a1 ≤ q) (ha2 : 1 ≤ a2 ∧ a2 ≤ q) (ha3 : 1 ≤ a3 ∧ a3 ≤ q)
    (ha : 1 ≤ a ∧ a ≤ q)
    (hb1 : b1 ≤ q ^ 2) (hb2 : b2 ≤ q ^ 2) (hb3 : b3 ≤ q ^ 2) (hb : b ≤ q ^ 2)
    (τ : ℝ) (hτ : τ = 1 / (9 * (q : ℝ) ^ 5))
    (h1 : G.eval (a1 : ℝ) = ((b1 : ℝ) + τ) ^ 2)
    (h2 : G.eval (a2 : ℝ) = ((b2 : ℝ) + τ) ^ 2)
    (h3 : G.eval (a3 : ℝ) = ((b3 : ℝ) + τ) ^ 2)
    (h : G.eval (a : ℝ) = ((b : ℝ) + τ) ^ 2) :
    (b1 : ℝ) * M1 (a1 : ℝ) a2 a3 a + b2 * M2 (a1 : ℝ) a2 a3 a + b3 * M3 (a1 : ℝ) a2 a3 a
      = NN (a1 : ℝ) a2 a3 * b := by
  have hev : ∀ t : ℝ, G.eval t = G.coeff 2 * t ^ 2 + G.coeff 1 * t + G.coeff 0 := by
    intro t
    rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
    simp [Finset.sum_range_succ]; ring
  have E : NN (a1 : ℝ) a2 a3 * ((b : ℝ) + τ) ^ 2 =
      ((b1 : ℝ) + τ) ^ 2 * M1 (a1 : ℝ) a2 a3 a + ((b2 : ℝ) + τ) ^ 2 * M2 (a1 : ℝ) a2 a3 a
        + ((b3 : ℝ) + τ) ^ 2 * M3 (a1 : ℝ) a2 a3 a := by
    rw [← h, ← h1, ← h2, ← h3, hev, hev, hev, hev]
    simp only [M1, M2, M3, NN]; ring
  -- integers
  set Q : ℤ := (q : ℤ) with hQ
  have hq1 : (1 : ℤ) ≤ Q := by omega
  have hb1' : (b1 : ℤ) ≤ Q ^ 2 := by rw [hQ]; exact_mod_cast hb1
  have hb2' : (b2 : ℤ) ≤ Q ^ 2 := by rw [hQ]; exact_mod_cast hb2
  have hb3' : (b3 : ℤ) ≤ Q ^ 2 := by rw [hQ]; exact_mod_cast hb3
  have hb' : (b : ℤ) ≤ Q ^ 2 := by rw [hQ]; exact_mod_cast hb
  have hd12 := absd Q a1 a2 (by omega) (by omega) (by omega) (by omega)
  have hd13 := absd Q a1 a3 (by omega) (by omega) (by omega) (by omega)
  have hd23 := absd Q a2 a3 (by omega) (by omega) (by omega) (by omega)
  have hd21 := absd Q a2 a1 (by omega) (by omega) (by omega) (by omega)
  have hd31 := absd Q a3 a1 (by omega) (by omega) (by omega) (by omega)
  have hd32 := absd Q a3 a2 (by omega) (by omega) (by omega) (by omega)
  have hda1 := absd Q a a1 (by omega) (by omega) (by omega) (by omega)
  have hda2 := absd Q a a2 (by omega) (by omega) (by omega) (by omega)
  have hda3 := absd Q a a3 (by omega) (by omega) (by omega) (by omega)
  have hN : |NN (a1 : ℤ) a2 a3| ≤ Q ^ 3 := abs3 _ _ _ _ hd21 hd31 hd32
  have hm1 : |M1 (a1 : ℤ) a2 a3 a| ≤ Q ^ 3 := abs3 _ _ _ _ hda2 hda3 hd32
  have hm2 : |M2 (a1 : ℤ) a2 a3 a| ≤ Q ^ 3 := by
    simp only [M2]; rw [abs_neg]; exact abs3 _ _ _ _ hda1 hda3 hd31
  have hm3 : |M3 (a1 : ℤ) a2 a3 a| ≤ Q ^ 3 := abs3 _ _ _ _ hda1 hda2 hd21
  set J : ℤ := b1 * M1 (a1 : ℤ) a2 a3 a + b2 * M2 (a1 : ℤ) a2 a3 a + b3 * M3 (a1 : ℤ) a2 a3 a
      - NN (a1 : ℤ) a2 a3 * b with hJ
  set I : ℤ := NN (a1 : ℤ) a2 a3 * b ^ 2 - (b1 ^ 2 * M1 (a1 : ℤ) a2 a3 a
      + b2 ^ 2 * M2 (a1 : ℤ) a2 a3 a + b3 ^ 2 * M3 (a1 : ℤ) a2 a3 a) with hI
  have hbd : ∀ (m : ℤ) (c : ℕ), c ≤ Q ^ 2 → |m| ≤ Q ^ 3 → |(c : ℤ) * m| ≤ Q ^ 5 := by
    intro m c hc hm
    rw [abs_mul, Nat.abs_cast]
    calc (c : ℤ) * |m| ≤ Q ^ 2 * Q ^ 3 := by
          apply mul_le_mul (by exact_mod_cast hc) hm (abs_nonneg _) (by positivity)
      _ = Q ^ 5 := by ring
  have hJb : |J| ≤ 4 * Q ^ 5 := by
    have e1 := hbd _ _ hb1' hm1
    have e2 := hbd _ _ hb2' hm2
    have e3 := hbd _ _ hb3' hm3
    have e4 := hbd _ _ hb' hN
    have : J = b1 * M1 (a1 : ℤ) a2 a3 a + b2 * M2 (a1 : ℤ) a2 a3 a + b3 * M3 (a1 : ℤ) a2 a3 a
      + (-(b * NN (a1 : ℤ) a2 a3)) := by rw [hJ]; ring
    rw [this]
    have := abs_add_three (↑b1 * M1 (a1 : ℤ) a2 a3 a + ↑b2 * M2 (a1 : ℤ) a2 a3 a)
      (↑b3 * M3 (a1 : ℤ) a2 a3 a) (-(b * NN (a1 : ℤ) a2 a3))
    have h5 := abs_add_le (↑b1 * M1 (a1 : ℤ) a2 a3 a) (↑b2 * M2 (a1 : ℤ) a2 a3 a)
    rw [abs_neg] at this
    linarith
  have hQpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hIJ : (I : ℝ) = 2 * τ * J := by
    rw [hI, hJ]; push_cast [M1, M2, M3, NN]
    simp only [M1, M2, M3, NN] at E
    linear_combination E
  have hJr : |(J : ℝ)| ≤ 4 * (q : ℝ) ^ 5 := by
    have := (Int.cast_le (R := ℝ)).mpr hJb
    rw [hQ] at this; push_cast at this; exact this
  have hI1 : |(I : ℝ)| < 1 := by
    rw [hIJ, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * τ)]
    have : 2 * τ * (4 * (q : ℝ) ^ 5) = 8 / 9 := by rw [hτ]; field_simp; ring
    calc 2 * τ * |(J : ℝ)| ≤ 2 * τ * (4 * (q : ℝ) ^ 5) := by gcongr
      _ < 1 := by rw [this]; norm_num
  have hI0 : I = 0 := by
    have : |I| < 1 := by exact_mod_cast hI1
    rw [abs_lt] at this; omega
  have hJ0 : (J : ℝ) = 0 := by
    have h0 : (I : ℝ) = 0 := by exact_mod_cast hI0
    rw [hIJ] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact h
  have : (J : ℝ) = (b1 : ℝ) * M1 (a1 : ℝ) a2 a3 a + b2 * M2 (a1 : ℝ) a2 a3 a
      + b3 * M3 (a1 : ℝ) a2 a3 a - NN (a1 : ℝ) a2 a3 * b := by
    rw [hJ]; push_cast [M1, M2, M3, NN]; ring
  linarith


lemma fst_inj (q : ℕ) (G : ℝ[X]) (τ : ℝ) (hτ : 0 < τ) (pairs : Finset (ℕ × ℕ))
    (hv : ∀ ab ∈ pairs, G.eval (ab.1 : ℝ) = ((ab.2 : ℝ) + τ) ^ 2) :
    Set.InjOn Prod.fst (pairs : Set (ℕ × ℕ)) := by
  intro p hp r hr hfst
  have h1 := hv p hp
  have h2 := hv r hr
  rw [hfst] at h1
  have h3 : ((p.2 : ℝ) + τ) ^ 2 = ((r.2 : ℝ) + τ) ^ 2 := by rw [← h1, ← h2]
  have h4 : (p.2 : ℝ) + τ = (r.2 : ℝ) + τ := by
    have := (sq_eq_sq₀ (by positivity) (by positivity)).mp h3
    exact this
  have : p.2 = r.2 := by exact_mod_cast (add_right_cancel h4)
  exact Prod.ext hfst this

end WeakEpsNets.Dev.L1
namespace WeakEpsNets.LowerBound
open Polynomial
open WeakEpsNets.Dev.L1 in
theorem chk_lemma_1 (q : ℕ) (hq : 2 ≤ q) (heven : Even q)
    (G : Polynomial ℝ) (hdegree : G.natDegree = 2)
    (pairs : Finset (ℕ × ℕ))
    (hgrid : pairs ⊆ (positiveInterval q).product (positiveInterval (q ^ 2)))
    (hfive : 5 ≤ pairs.card)
    (hvalues : ∀ ab ∈ pairs, G.eval (ab.1 : ℝ) = ((ab.2 : ℝ) + tau q) ^ 2) :
    ∃ α t₀ : ℝ, G = Polynomial.C α * (Polynomial.X - Polynomial.C t₀) ^ 2 := by
  have hτpos : 0 < tau q := by unfold tau; have : (0:ℝ) < q := by positivity
                               positivity
  have hinj := fst_inj q G (tau q) hτpos pairs hvalues
  have hmem : ∀ p ∈ pairs, (1 ≤ p.1 ∧ p.1 ≤ q) ∧ p.2 ≤ q ^ 2 := by
    intro p hp
    have h : p ∈ positiveInterval q ×ˢ positiveInterval (q ^ 2) := hgrid hp
    rw [Finset.mem_product] at h
    simp only [positiveInterval, Finset.mem_Icc] at h
    exact ⟨h.1, h.2.2⟩
  obtain ⟨p1, hp1, p2, hp2, p3, hp3, h12, h13, h23⟩ := Finset.two_lt_card.mp (by omega : 2 < pairs.card)
  have n12 : p1.1 ≠ p2.1 := fun h => h12 (hinj hp1 hp2 h)
  have n13 : p1.1 ≠ p3.1 := fun h => h13 (hinj hp1 hp3 h)
  have n23 : p2.1 ≠ p3.1 := fun h => h23 (hinj hp2 hp3 h)
  have hN : NN (p1.1 : ℝ) p2.1 p3.1 ≠ 0 := by
    unfold NN
    have e12 : (p2.1 : ℝ) - p1.1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast n12.symm)
    have e13 : (p3.1 : ℝ) - p1.1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast n13.symm)
    have e23 : (p3.1 : ℝ) - p2.1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast n23.symm)
    exact mul_ne_zero (mul_ne_zero e12 e13) e23
  set a1 : ℝ := ((p1.1 : ℕ) : ℝ)
  set a2 : ℝ := ((p2.1 : ℕ) : ℝ)
  set a3 : ℝ := ((p3.1 : ℕ) : ℝ)
  set R : ℝ[X] := C (p1.2 : ℝ) * ((X - C a2) * (X - C a3) * C (a3 - a2))
    + C (p2.2 : ℝ) * (-((X - C a1) * (X - C a3) * C (a3 - a1)))
    + C (p3.2 : ℝ) * ((X - C a1) * (X - C a2) * C (a2 - a1)) with hR
  have hReval : ∀ t : ℝ, R.eval t = (p1.2 : ℝ) * M1 a1 a2 a3 t + p2.2 * M2 a1 a2 a3 t
      + p3.2 * M3 a1 a2 a3 t := by
    intro t; simp [hR, M1, M2, M3]
  set U : ℝ[X] := R + C (NN a1 a2 a3 * tau q) with hU
  have hUdeg : U.natDegree ≤ 2 := by
    rw [hU, hR]; compute_degree
  have hGdeg : (C (NN a1 a2 a3 ^ 2) * G).natDegree ≤ 2 :=
    (natDegree_C_mul_le _ _).trans hdegree.le
  have hP : C (NN a1 a2 a3 ^ 2) * G - U ^ 2 = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      _ (pairs.image (fun p : ℕ × ℕ => (p.1 : ℝ)))
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨⟨hpa1, hpa2⟩, hpb⟩ := hmem p hp
      obtain ⟨⟨h11, h12'⟩, h1b⟩ := hmem p1 hp1
      obtain ⟨⟨h21, h22'⟩, h2b⟩ := hmem p2 hp2
      obtain ⟨⟨h31, h32'⟩, h3b⟩ := hmem p3 hp3
      have := key q p1.1 p2.1 p3.1 p.1 p1.2 p2.2 p3.2 p.2 G hdegree ⟨h11, h12'⟩ ⟨h21, h22'⟩
        ⟨h31, h32'⟩ ⟨hpa1, hpa2⟩ h1b h2b h3b hpb (tau q) rfl (hvalues p1 hp1) (hvalues p2 hp2)
        (hvalues p3 hp3) (hvalues p hp)
      simp only [eval_sub, eval_mul, eval_C, eval_pow, hU, eval_add, hReval, hvalues p hp]
      rw [this]; ring
    · rw [Finset.card_image_of_injOn]
      · have : (C (NN a1 a2 a3 ^ 2) * G - U ^ 2).natDegree ≤ 4 :=
          (natDegree_sub_le _ _).trans (max_le (hGdeg.trans (by norm_num))
            ((natDegree_pow_le).trans (by omega)))
        omega
      · intro x hx y hy hxy
        exact hinj hx hy (Nat.cast_injective (R := ℝ) hxy)
  have hGS : G = (C (1 / NN a1 a2 a3) * U) ^ 2 := by
    have e : U ^ 2 = C (NN a1 a2 a3 ^ 2) * G := by linear_combination -hP
    have h1 : (C (1 / NN a1 a2 a3) * U) ^ 2 = C ((1 / NN a1 a2 a3) ^ 2 * NN a1 a2 a3 ^ 2) * G := by
      rw [mul_pow, e, ← C_pow, ← mul_assoc, ← C_mul]
    have h2 : (1 / NN a1 a2 a3) ^ 2 * NN a1 a2 a3 ^ 2 = 1 := by field_simp
    rw [h1, h2]; simp
  set S : ℝ[X] := C (1 / NN a1 a2 a3) * U with hS
  have hSdeg : S.natDegree ≤ 2 := (natDegree_C_mul_le _ _).trans hUdeg
  have hS1 : S.natDegree = 1 := by
    have : G.natDegree = 2 * S.natDegree := by rw [hGS, natDegree_pow]
    omega
  have hform : S = C (S.coeff 1) * X + C (S.coeff 0) := eq_X_add_C_of_natDegree_le_one hS1.le
  have hc : S.coeff 1 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr (show S ≠ 0 by intro h; rw [h] at hS1; simp at hS1)
    rwa [leadingCoeff, hS1] at this
  refine ⟨S.coeff 1 ^ 2, -(S.coeff 0 / S.coeff 1), ?_⟩
  have h3 : S = C (S.coeff 1) * (X - C (-(S.coeff 0 / S.coeff 1))) := by
    rw [mul_sub, ← C_mul]
    have : S.coeff 1 * -(S.coeff 0 / S.coeff 1) = -S.coeff 0 := by field_simp
    rw [this, C_neg]
    conv_lhs => rw [hform]
    ring
  rw [hGS]
  nth_rewrite 1 [h3]
  rw [mul_pow, ← C_pow]

end WeakEpsNets.LowerBound
end

theorem solution : type_of% @WeakEpsNets.LowerBound.chk_lemma_1 := @WeakEpsNets.LowerBound.chk_lemma_1
