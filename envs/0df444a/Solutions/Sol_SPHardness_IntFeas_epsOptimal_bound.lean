-- Prove2me | solution 1 for SPHardness.IntFeas.epsOptimal_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:03:39.474195+00:00
-- url     : https://prove2.me/submissions/00d28316-a7f7-4997-a67e-497a89c67b24

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model
import Theorems.Thm_SPHardness_IntFeas_lemma_4
import Theorems.Thm_SPHardness_IntFeas_secondStage_solution

open MeasureTheory
open SPHardness.IntFeas

namespace IFT4C

variable {m n : ℕ}

noncomputable def fval (ξ : Fin n → ℝ) : ℝ := ∑ i, max (ξ i) (1 - ξ i)

lemma polytope_cube (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (ξ : Fin n → ℝ) (h : InPolytope A b ξ) :
    ξ ∈ SPHardness.FixedRecourse.cube n := by
  intro j _
  exact hinst ξ h j

lemma fval_le (ξ : Fin n → ℝ) (h : ξ ∈ SPHardness.FixedRecourse.cube n) :
    fval ξ ≤ n := by
  unfold fval
  have : ∀ i ∈ Finset.univ, max (ξ i) (1 - ξ i) ≤ (1 : ℝ) := by
    intro i _
    have := h i (Set.mem_univ _)
    simp only [Set.mem_Icc] at this
    exact max_le this.2 (by linarith [this.1])
  calc ∑ i, max (ξ i) (1 - ξ i) ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum this
    _ = n := by simp

lemma fval_nonneg (ξ : Fin n → ℝ) : 0 ≤ fval ξ := by
  unfold fval
  apply Finset.sum_nonneg
  intro i _
  rcases le_total (ξ i) (1 - ξ i) with h | h
  · exact le_trans (by linarith) (le_max_right _ _)
  · exact le_trans (by linarith) (le_max_left _ _)

lemma bdd (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hinst : IsIFPInstance A b) :
    BddAbove {v | ∃ ξ : Fin n → ℝ, InPolytope A b ξ ∧ v = ∑ i, max (ξ i) (1 - ξ i)} := by
  refine ⟨n, ?_⟩
  rintro v ⟨ξ, hξ, rfl⟩
  exact fval_le ξ (polytope_cube A b hinst ξ hξ)

lemma le_xStar (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hinst : IsIFPInstance A b)
    (ξ : Fin n → ℝ) (h : InPolytope A b ξ) : fval ξ ≤ xStar A b :=
  le_csSup (bdd A b hinst) ⟨ξ, h, rfl⟩

lemma xStar_le_iff (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hinst : IsIFPInstance A b)
    (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) (x : ℝ) :
    xStar A b ≤ x ↔ ∀ ξ, InPolytope A b ξ → fval ξ ≤ x := by
  obtain ⟨ξ0, h0⟩ := hne
  unfold xStar
  rw [csSup_le_iff (bdd A b hinst) ⟨_, ξ0, h0, rfl⟩]
  constructor
  · intro H ξ hξ; exact H _ ⟨ξ, hξ, rfl⟩
  · rintro H v ⟨ξ, hξ, rfl⟩; exact H ξ hξ

lemma xStar_le_n (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hinst : IsIFPInstance A b)
    (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) : xStar A b ≤ n :=
  (xStar_le_iff A b hinst hne n).2 fun ξ h => fval_le ξ (polytope_cube A b hinst ξ h)

lemma xStar_nonneg (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hinst : IsIFPInstance A b)
    (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) : 0 ≤ xStar A b := by
  obtain ⟨ξ0, h0⟩ := hne
  exact le_trans (fval_nonneg ξ0) (le_xStar A b hinst ξ0 h0)

lemma isClosed_polytope (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    IsClosed {ξ : Fin n → ℝ | InPolytope A b ξ} := by
  have : {ξ : Fin n → ℝ | InPolytope A b ξ} =
      ⋂ i, {ξ : Fin n → ℝ | ∑ j, (A i j : ℝ) * ξ j ≤ (b i : ℝ)} := by
    ext ξ; simp [InPolytope]
  rw [this]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le (by fun_prop) continuous_const

lemma isCompact_polytope (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) : IsCompact {ξ : Fin n → ℝ | InPolytope A b ξ} := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))))
    (isClosed_polytope A b) ?_
  intro ξ h
  exact polytope_cube A b hinst ξ h

lemma xStar_attained (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) :
    ∃ ξ, InPolytope A b ξ ∧ fval ξ = xStar A b := by
  have hc := isCompact_polytope A b hinst
  have hcont : Continuous (fun ξ : Fin n → ℝ => fval ξ) := by
    unfold fval; fun_prop
  have hne' : ({ξ : Fin n → ℝ | InPolytope A b ξ}).Nonempty := hne
  obtain ⟨ξ, hξ, hmax⟩ := hc.exists_isMaxOn hne' hcont.continuousOn
  refine ⟨ξ, hξ, le_antisymm (le_xStar A b hinst ξ hξ) ?_⟩
  rw [xStar_le_iff A b hinst hne]
  intro η hη
  exact hmax hη

/-! ### Dichotomy -/

theorem dichotomy (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ)
    (ε' : ℝ) (hε'0 : 0 ≤ ε') (hε'half : ε' < 1 / 2)
    (hε'row : ∀ i, ε' * ∑ j, |(A i j : ℝ)| < 1) :
    (IFPAnswer A b ↔ xStar A b = n) ∧ (¬ IFPAnswer A b ↔ xStar A b < n - ε') := by
  have hle := xStar_le_n A b hinst hne
  have yes : IFPAnswer A b → xStar A b = n := by
    rintro ⟨y, hy, hP⟩
    refine le_antisymm hle ?_
    have : fval y = n := by
      unfold fval
      have : ∀ i ∈ Finset.univ, max (y i) (1 - y i) = (1 : ℝ) := by
        intro i _
        rcases hy i with h | h <;> rw [h] <;> norm_num
      rw [Finset.sum_congr rfl this]; simp
    rw [← this]; exact le_xStar A b hinst y hP
  have no : ¬ IFPAnswer A b → xStar A b < n - ε' := by
    intro hno
    obtain ⟨ξ, hξ, hfx⟩ := xStar_attained A b hinst hne
    rw [← hfx]
    have hl4 := lemma_4 A b hinst ε' hε'0 hε'half hε'row
    have hnot : ¬ ∀ j, (0 ≤ ξ j ∧ ξ j ≤ ε') ∨ (1 - ε' ≤ ξ j ∧ ξ j ≤ 1) := by
      intro H; exact hno (hl4.2 ⟨ξ, H, hξ⟩)
    push Not at hnot
    obtain ⟨j, hj1, hj2⟩ := hnot
    have hc := polytope_cube A b hinst ξ hξ
    have hcj := hc j (Set.mem_univ _)
    simp only [Set.mem_Icc] at hcj
    have hj1' : ε' < ξ j := by
      by_contra h; push Not at h; exact absurd (hj1 hcj.1) (not_lt.mpr h)
    have hj2' : ξ j < 1 - ε' := by
      by_contra h; push Not at h; exact absurd (hj2 h) (not_lt.mpr hcj.2)
    have hmj : max (ξ j) (1 - ξ j) < 1 - ε' := max_lt hj2' (by linarith)
    unfold fval
    have hrest : ∀ i ∈ Finset.univ, max (ξ i) (1 - ξ i) ≤ (1 : ℝ) := by
      intro i _
      have := hc i (Set.mem_univ _)
      simp only [Set.mem_Icc] at this
      exact max_le this.2 (by linarith [this.1])
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hs : ∑ i ∈ Finset.univ.erase j, max (ξ i) (1 - ξ i) ≤ ((n : ℝ) - 1) := by
      calc ∑ i ∈ Finset.univ.erase j, max (ξ i) (1 - ξ i)
          ≤ ∑ _i ∈ Finset.univ.erase j, (1 : ℝ) :=
            Finset.sum_le_sum fun i hi => hrest i (Finset.mem_univ i)
        _ = (n : ℝ) - 1 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
            simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            have : 1 ≤ n := by
              rcases Nat.eq_zero_or_pos n with h | h
              · subst h; exact j.elim0
              · exact h
            push_cast [this]; ring
    linarith
  refine ⟨⟨yes, fun h => ?_⟩, ⟨no, fun h hy => ?_⟩⟩
  · by_contra hno
    have := no hno
    linarith
  · have := yes hy
    linarith

end IFT4C

open MeasureTheory
open SPHardness.IntFeas

namespace IFT4C

variable {m n : ℕ}

open Classical in
noncomputable def gval (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (ξ : Fin n → ℝ) : ℝ :=
  if InPolytope A b ξ then fval ξ else 0

lemma feasible_iff (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) (x : ℝ) :
    FirstStageFeasible A b x ↔ xStar A b ≤ x := by
  rw [xStar_le_iff A b hinst hne]
  constructor
  · intro H ξ hξ
    have hc := polytope_cube A b hinst ξ hξ
    exact ((secondStage_solution A b x ξ hc).1 hξ).1.mp (H ξ hc)
  · intro H ξ hc
    by_cases hξ : InPolytope A b ξ
    · exact ((secondStage_solution A b x ξ hc).1 hξ).1.mpr (H ξ hξ)
    · obtain ⟨ξ0, h0⟩ := hne
      have : 0 ≤ x := le_trans (fval_nonneg ξ0) (H ξ0 h0)
      exact ((secondStage_solution A b x ξ hc).2 hξ).1.mpr this

lemma value_eq (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : ℝ)
    (hx : FirstStageFeasible A b x) (ξ : Fin n → ℝ) (hc : ξ ∈ SPHardness.FixedRecourse.cube n) :
    secondStageValue A b x ξ = gval A b ξ := by
  by_cases hξ : InPolytope A b ξ
  · simp only [gval, hξ, if_true]; exact ((secondStage_solution A b x ξ hc).1 hξ).2.1 (hx ξ hc)
  · simp only [gval, hξ, if_false]; exact ((secondStage_solution A b x ξ hc).2 hξ).2.1 (hx ξ hc)

lemma measurableSet_cube : MeasurableSet (SPHardness.FixedRecourse.cube n) := by
  unfold SPHardness.FixedRecourse.cube
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma objective_eq (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : ℝ)
    (hx : FirstStageFeasible A b x) :
    objective A b x = x + ∫ ξ in SPHardness.FixedRecourse.cube n, gval A b ξ := by
  unfold objective
  congr 1
  exact setIntegral_congr_fun measurableSet_cube (fun ξ hc => value_eq A b x hx ξ hc)

lemma volume_cube : volume (SPHardness.FixedRecourse.cube n) = 1 := by
  unfold SPHardness.FixedRecourse.cube
  rw [volume_pi_pi]
  simp

lemma integral_bounds (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    0 ≤ ∫ ξ in SPHardness.FixedRecourse.cube n, gval A b ξ ∧
    ∫ ξ in SPHardness.FixedRecourse.cube n, gval A b ξ ≤ n := by
  have hg0 : ∀ ξ ∈ SPHardness.FixedRecourse.cube n, 0 ≤ gval A b ξ := by
    intro ξ _
    by_cases hξ : InPolytope A b ξ
    · simp only [gval, hξ, if_true]; exact fval_nonneg ξ
    · simp only [gval, hξ, if_false]; exact le_rfl
  have hgn : ∀ ξ ∈ SPHardness.FixedRecourse.cube n, ‖gval A b ξ‖ ≤ (n : ℝ) := by
    intro ξ hc
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ξ hc)]
    by_cases hξ : InPolytope A b ξ
    · simp only [gval, hξ, if_true]; exact fval_le ξ hc
    · simp only [gval, hξ, if_false]; positivity
  refine ⟨setIntegral_nonneg measurableSet_cube hg0, ?_⟩
  have := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (by rw [volume_cube]; simp) hgn
  rw [measureReal_def, volume_cube] at this
  simp only [ENNReal.toReal_one, mul_one] at this
  exact le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at this)

theorem optimal (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) :
    (∀ x, FirstStageFeasible A b x ↔ xStar A b ≤ x) ∧
    objective A b (xStar A b) = optValue A b ∧
    ∀ x, FirstStageFeasible A b x → objective A b x = optValue A b → x = xStar A b := by
  have hfe := feasible_iff A b hinst hne
  have hsf : FirstStageFeasible A b (xStar A b) := (hfe _).2 le_rfl
  have hopt : objective A b (xStar A b) = optValue A b := by
    unfold optValue
    symm
    apply IsLeast.csInf_eq
    refine ⟨⟨_, hsf, rfl⟩, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    rw [objective_eq A b x hx, objective_eq A b _ hsf]
    have := (hfe x).1 hx
    linarith
  refine ⟨hfe, hopt, ?_⟩
  intro x hx h
  rw [← hopt, objective_eq A b x hx, objective_eq A b _ hsf] at h
  linarith

theorem bound (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) (hn : 1 ≤ n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (x : ℝ) (hx : IsEpsOptimal A b ε x) :
    |xStar A b - x| ≤ 2 * n * ε := by
  obtain ⟨_, hopt, _⟩ := optimal A b hinst hne
  obtain ⟨hxf, hrel⟩ := hx
  have hsf : FirstStageFeasible A b (xStar A b) := (feasible_iff A b hinst hne _).2 le_rfl
  rw [← hopt, objective_eq A b x hxf, objective_eq A b _ hsf] at hrel
  obtain ⟨hI0, hIn⟩ := integral_bounds A b
  set I := ∫ ξ in SPHardness.FixedRecourse.cube n, gval A b ξ
  have h0 := xStar_nonneg A b hinst hne
  have hle := xStar_le_n A b hinst hne
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : max |xStar A b + I| 1 ≤ 2 * n := by
    rw [abs_of_nonneg (by linarith)]
    exact max_le (by linarith) (by linarith)
  have hMpos : 0 < max |xStar A b + I| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [div_le_iff₀ hMpos] at hrel
  have heq : xStar A b + I - (x + I) = xStar A b - x := by ring
  rw [heq] at hrel
  calc |xStar A b - x| ≤ ε * max |xStar A b + I| 1 := hrel
    _ ≤ ε * (2 * n) := mul_le_mul_of_nonneg_left hM hε0
    _ = 2 * n * ε := by ring

end IFT4C

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) (hn : 1 ≤ n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (x : ℝ) (hx : IsEpsOptimal A b ε x) :
    |xStar A b - x| ≤ 2 * n * ε :=
  IFT4C.bound A b hinst hne hn ε hε0 x hx
