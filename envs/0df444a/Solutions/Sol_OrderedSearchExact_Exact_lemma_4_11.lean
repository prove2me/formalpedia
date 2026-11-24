-- Prove2me | solution 1 for OrderedSearchExact.Exact.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:07:47.230705+00:00
-- url     : https://prove2.me/submissions/4b5896be-930a-4fe3-b1bf-831f18a9ea07

import Definitions.Def_OrderedSearchExact_Exact_Laurent

open OrderedSearchExact.Exact

lemma osx_int_cos (m : ℕ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos (((m + 1 : ℕ) : ℝ) * θ) = 0 := by
  have hc : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
  have : ((m + 1 : ℕ) : ℝ) * (2 * Real.pi) = ((2 * (m + 1) : ℕ) : ℝ) * Real.pi := by
    push_cast; ring
  rw [this, Real.sin_nat_mul_pi]
  simp

lemma osx_int_circle {n : ℕ} (a : Coeff n) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), circle a θ = 2 * Real.pi := by
  unfold circle
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_eq_zero (fun i _ => by
      rw [intervalIntegral.integral_const_mul, osx_int_cos, mul_zero])]
    simp
  · intro i _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma osx_circle_ge {n : ℕ} (a : Coeff n) (θ : ℝ) : 1 - mass a ≤ circle a θ := by
  unfold circle mass
  have : -(∑ i, |a i|) ≤ ∑ i, a i * Real.cos (((i.val + 1 : ℕ) : ℝ) * θ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h1 := Real.abs_cos_le_one (((i.val + 1 : ℕ) : ℝ) * θ)
    have h2 : |a i * Real.cos (((i.val + 1 : ℕ) : ℝ) * θ)| ≤ |a i| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h1
    linarith [neg_abs_le (a i * Real.cos (((i.val + 1 : ℕ) : ℝ) * θ))]
  linarith

lemma osx_sum_rev {n : ℕ} (f : Fin (n - 1) → ℝ) : ∑ i : Fin (n - 1), f (Fin.rev i) = ∑ i, f i :=
  Fintype.sum_equiv Fin.revPerm (fun i : Fin (n - 1) => f i.rev) f (fun _ => by simp)

lemma osx_mass_proj {n : ℕ} (a b : Coeff n) (h : ∀ i, |b i| ≤ (|a i| + |a i.rev|) / 2) :
    mass b ≤ mass a := by
  unfold mass
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  have hr := osx_sum_rev (fun i => |a i|)
  rw [← Finset.sum_div, Finset.sum_add_distrib, hr] at hs
  linarith

lemma osx_mass_plus {n : ℕ} (a : Coeff n) : mass (projectPlus a) ≤ mass a := by
  apply osx_mass_proj
  intro i
  simp only [projectPlus, reversal, Pi.div_apply, Pi.add_apply, Pi.ofNat_apply]
  rw [abs_div, abs_two]
  have := abs_add_le (a i) (a i.rev)
  linarith

lemma osx_mass_minus {n : ℕ} (a : Coeff n) : mass (projectMinus a) ≤ mass a := by
  apply osx_mass_proj
  intro i
  simp only [projectMinus, reversal, Pi.div_apply, Pi.sub_apply, Pi.ofNat_apply]
  rw [abs_div, abs_two]
  have := abs_add_le (a i) (-a i.rev)
  rw [abs_neg, ← sub_eq_add_neg] at this
  linarith

theorem solution (n k : ℕ) (hn : 1 ≤ n) (p : ℕ → Coeff n)
    (hp : FeasiblePrefix n k p) (hm : mass (p k) < 1) :
    FeasiblePath n (k + 2) (exactify p k) ∧
      (∀ t, t ≤ k → exactify p k t = p t) := by
  obtain ⟨h0, hnn, hpar⟩ := hp
  have hle : ∀ t, t ≤ k → exactify p k t = p t := fun t ht => by
    unfold exactify; rw [if_pos ht]
  have h1 : exactify p k (k + 1) = exactifierMiddle k (p k) := by
    unfold exactify; rw [if_neg (by omega), if_pos rfl]
  have h2 : exactify p k (k + 2) = 0 := by
    unfold exactify; rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨⟨⟨?_, ?_, ?_⟩, h2⟩, hle⟩
  · rw [hle 0 (Nat.zero_le _), h0]
  · intro t ht
    refine ⟨?_, osx_int_circle _⟩
    rcases (show t ≤ k ∨ t = k + 1 ∨ t = k + 2 by omega) with h | h | h
    · rw [hle t h]; exact (hnn t h).1
    · subst h
      rw [h1]
      intro θ
      have hmm : mass (exactifierMiddle k (p k)) ≤ mass (p k) := by
        unfold exactifierMiddle
        split_ifs
        · exact osx_mass_minus _
        · exact osx_mass_plus _
      linarith [osx_circle_ge (exactifierMiddle k (p k)) θ]
    · subst h
      rw [h2]
      intro θ
      simp [circle]
  · intro t ht1 ht2
    rcases (show t ≤ k ∨ t = k + 1 ∨ t = k + 2 by omega) with h | h | h
    · rw [hle t h, hle (t - 1) (by omega)]; exact hpar t ht1 h
    · subst h
      rw [h1, show k + 1 - 1 = k by omega, hle k le_rfl]
      unfold ParityStep exactifierMiddle
      by_cases h3 : Odd (k + 1)
      · rw [if_pos h3, if_pos h3]
        funext i
        simp [reversal, projectMinus, Fin.rev_rev] <;> ring
      · rw [if_neg h3, if_neg h3]
        funext i
        simp [reversal, projectPlus, Fin.rev_rev] <;> ring
    · subst h
      rw [h2, show k + 2 - 1 = k + 1 by omega, h1]
      unfold ParityStep exactifierMiddle
      by_cases h3 : Odd (k + 1)
      · have h4 : ¬ Odd (k + 2) := by rw [Nat.odd_iff] at h3 ⊢; omega
        rw [if_pos h3, if_neg h4]
        funext i
        simp [reversal, projectMinus, Fin.rev_rev] <;> ring
      · have h4 : Odd (k + 2) := by rw [Nat.odd_iff] at h3 ⊢; omega
        rw [if_neg h3, if_pos h4]
        funext i
        simp [reversal, projectPlus, Fin.rev_rev] <;> ring
