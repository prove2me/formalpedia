-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P31.parityBias_controls_stringLawL2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:31:59.51289+00:00
-- url     : https://prove2.me/submissions/e615632c-c9f8-4e25-9671-ac1ae790d45d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P31
open QAlgorithms.Papers.Independent.Renew46.P31

def g64j_sg (x : Bool) : ℝ := if x then -1 else 1

lemma g64j_sg_add (x y : Bool) : g64j_sg (x + y) = g64j_sg x * g64j_sg y := by
  cases x <;> cases y <;> simp [g64j_sg] <;> decide

lemma g64j_sg_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    g64j_sg (∑ m ∈ s, f m) = ∏ m ∈ s, g64j_sg (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g64j_sg]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, g64j_sg_add, ih]

lemma g64j_orth (n : ℕ) (a b : QAlgorithms.Qubits n) :
    ∑ X : QAlgorithms.Qubits n, g64j_sg (QAlgorithms.dotBits X a) * g64j_sg (QAlgorithms.dotBits X b)
      = if a = b then 2 ^ n else 0 := by
  have e1 : ∀ X : QAlgorithms.Qubits n,
      g64j_sg (QAlgorithms.dotBits X a) * g64j_sg (QAlgorithms.dotBits X b) =
      ∏ m, (g64j_sg (X m && a m) * g64j_sg (X m && b m)) := by
    intro X
    simp only [QAlgorithms.dotBits, g64j_sg_sum, Finset.prod_mul_distrib]
  simp only [e1]
  rw [← Fintype.prod_sum (fun m x => g64j_sg (x && a m) * g64j_sg (x && b m))]
  have e2 : ∀ m, ∑ x : Bool, g64j_sg (x && a m) * g64j_sg (x && b m) =
      if a m = b m then 2 else 0 := by
    intro m
    cases h1 : a m <;> cases h2 : b m <;> simp [g64j_sg] <;> norm_num
  simp only [e2]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab]
    obtain ⟨m, hm⟩ : ∃ m, a m ≠ b m := by
      by_contra h; exact hab (funext fun m => by by_contra h'; exact h ⟨m, h'⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ m) (by simp [hm])

lemma g64j_map_toReal {m : ℕ} (P : PMF (QAlgorithms.Qubits m)) (X : QAlgorithms.Qubits m) :
    (P.map (QAlgorithms.dotBits X) false).toReal =
      ∑ z, (if QAlgorithms.dotBits X z = false then (P z).toReal else 0) := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases h : QAlgorithms.dotBits X z = false
    · simp [h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]; simp
  · intro z _
    split_ifs
    · exact PMF.apply_ne_top P z
    · simp

lemma g64j_sum_one {m : ℕ} (P : PMF (QAlgorithms.Qubits m)) :
    ∑ z, (P z).toReal = 1 := by
  have h := P.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun z _ => PMF.apply_ne_top P z), h]
  simp

theorem solution
    (m : ℕ) (P Pideal : PMF (QAlgorithms.Qubits m))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hparity : ∀ X : QAlgorithms.Qubits m,
      |(P.map (QAlgorithms.dotBits X) false).toReal -
        (Pideal.map (QAlgorithms.dotBits X) false).toReal| ≤ epsilon) :
    ‖(WithLp.toLp 2 (fun z : QAlgorithms.Qubits m =>
      (P z).toReal - (Pideal z).toReal) :
        EuclideanSpace ℝ (QAlgorithms.Qubits m))‖ ≤ 2 * epsilon := by
  set d : QAlgorithms.Qubits m → ℝ := fun z => (P z).toReal - (Pideal z).toReal with hd
  have hsum0 : ∑ z, d z = 0 := by
    simp only [hd, Finset.sum_sub_distrib, g64j_sum_one, sub_self]
  -- Fourier coefficient
  set F : QAlgorithms.Qubits m → ℝ := fun X => ∑ z, g64j_sg (QAlgorithms.dotBits X z) * d z with hF
  have hdiff : ∀ X, (P.map (QAlgorithms.dotBits X) false).toReal -
      (Pideal.map (QAlgorithms.dotBits X) false).toReal = F X / 2 := by
    intro X
    rw [g64j_map_toReal, g64j_map_toReal, ← Finset.sum_sub_distrib]
    have : ∀ z, ((if QAlgorithms.dotBits X z = false then (P z).toReal else 0) -
        (if QAlgorithms.dotBits X z = false then (Pideal z).toReal else 0)) =
        (d z + g64j_sg (QAlgorithms.dotBits X z) * d z) / 2 := by
      intro z
      cases h : QAlgorithms.dotBits X z <;> simp [g64j_sg, hd]
    simp only [this, ← Finset.sum_div, Finset.sum_add_distrib, hsum0, zero_add, hF]
  have hF2 : ∀ X, F X ^ 2 ≤ (2 * epsilon) ^ 2 := by
    intro X
    have h1 := hparity X
    rw [hdiff] at h1
    have : |F X| ≤ 2 * epsilon := by
      rw [abs_div] at h1; norm_num at h1; linarith
    exact sq_le_sq' (by linarith [neg_abs_le (F X)]) (le_trans (le_abs_self _) this)
  have parseval : ∑ X, F X ^ 2 = 2 ^ m * ∑ z, d z ^ 2 := by
    have : ∀ X, F X ^ 2 = ∑ z, ∑ w, d z * d w *
        (g64j_sg (QAlgorithms.dotBits X z) * g64j_sg (QAlgorithms.dotBits X w)) := by
      intro X
      rw [hF, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))
      ring
    simp only [this]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, g64j_orth]
    rw [Finset.sum_eq_single z]
    · simp; ring
    · intro w _ hw; simp [Ne.symm hw]
    · simp
  have hcard : (Fintype.card (QAlgorithms.Qubits m) : ℝ) = 2 ^ m := by simp
  have hbound : ∑ X, F X ^ 2 ≤ 2 ^ m * (2 * epsilon) ^ 2 := by
    calc ∑ X, F X ^ 2 ≤ ∑ _X : QAlgorithms.Qubits m, (2 * epsilon) ^ 2 :=
          Finset.sum_le_sum (fun X _ => hF2 X)
      _ = 2 ^ m * (2 * epsilon) ^ 2 := by rw [Finset.sum_const, Finset.card_univ]; simp
  have hd2 : ∑ z, d z ^ 2 ≤ (2 * epsilon) ^ 2 := by
    rw [parseval] at hbound
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    exact le_of_mul_le_mul_left hbound hp
  rw [EuclideanSpace.norm_eq]
  rw [Real.sqrt_le_left (by positivity)]
  simpa [hd, Real.norm_eq_abs, sq_abs] using hd2
