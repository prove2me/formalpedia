-- Prove2me | solution 1 for RossQC.Sufficient.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:58:06.705986+00:00
-- url     : https://prove2.me/submissions/f81980b5-67dc-4706-b724-f5c326cac04f

import Mathlib
import Definitions.Def_RossQC_Sufficient_Model

open RossQC.Sufficient Filter Topology

private theorem update_mem (M : Model) (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    {P : ℝ} (hP : P ∈ Set.Icc (0 : ℝ) 1) : M.T P ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [Model.T]
  obtain ⟨hP0, hP1⟩ := hP
  constructor <;> nlinarith [mul_nonneg hπ0 (sub_nonneg.mpr hP1),
    mul_nonneg (sub_nonneg.mpr hπ1) (sub_nonneg.mpr hP1)]

private theorem operator_le (M : Model) (hβ : 0 ≤ M.β)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (f g : ℝ → ℝ)
    (hfg : ∀ P ∈ Set.Icc (0 : ℝ) 1, f P ≤ g P)
    {P : ℝ} (hP : P ∈ Set.Icc (0 : ℝ) 1) :
    min (M.rhs3 f P .produce) (min (M.rhs3 f P .inspect) (M.rhs3 f P .revise)) ≤
      min (M.rhs3 g P .produce) (min (M.rhs3 g P .inspect) (M.rhs3 g P .revise)) := by
  apply min_le_min
  · dsimp [Model.rhs3]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (hfg _ (update_mem M hπ0 hπ1 hP)) hβ) _
  · apply min_le_min
    · dsimp [Model.rhs3]
      have h1 := mul_le_mul_of_nonneg_left (hfg 1 (by simp)) (mul_nonneg hβ hP.1)
      have h2 := mul_le_mul_of_nonneg_left (hfg M.π ⟨hπ0, hπ1⟩)
        (mul_nonneg hβ (sub_nonneg.mpr hP.2))
      linarith
    · dsimp [Model.rhs3]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (hfg M.π ⟨hπ0, hπ1⟩) hβ) _

private theorem iter_bounds (M : Model) (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (hC0 : 0 < M.C)
    (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ n P, P ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ M.valueIter n P ∧ M.valueIter n P ≤ M.C / (1 - M.β) := by
  have hden : 0 < 1 - M.β := by linarith
  have hB : 0 ≤ M.C / (1 - M.β) := le_of_lt (div_pos hC0 hden)
  have heq : M.C + M.β * (M.C / (1 - M.β)) = M.C / (1 - M.β) := by
    field_simp
    <;> ring
  intro n
  induction n with
  | zero => intro P hP; exact ⟨le_refl 0, hB⟩
  | succ n ih =>
    intro P hP
    have ht := ih _ (update_mem M hπ0 hπ1 hP)
    have h1 := ih 1 (by simp)
    have hπ := ih M.π ⟨hπ0, hπ1⟩
    have ht0 := ht.1
    have h10 := h1.1
    have hπn := hπ.1
    have hP0 := hP.1
    constructor
    · dsimp [Model.valueIter, Model.rhs3]
      apply le_min
      · positivity
      · apply le_min
        · have hI : 0 ≤ M.I := by linarith
          have hp : 0 ≤ 1 - P := by linarith [hP.2]
          positivity
        · have hR : 0 ≤ M.R := by linarith
          positivity
    · apply le_trans (min_le_left _ _)
      dsimp [Model.rhs3]
      have hc := mul_le_mul_of_nonneg_left hP.2 hC0.le
      have ht' := mul_le_mul_of_nonneg_left ht.2 hβ0.le
      linarith

private theorem iter_time_mono (M : Model) (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (hC0 : 0 < M.C)
    (hCI : M.C < M.I) (hIR : M.I < M.R) (P : ℝ) (hP : P ∈ Set.Icc (0 : ℝ) 1) :
    Monotone (fun n => M.valueIter n P) := by
  apply monotone_nat_of_le_succ
  have hstep : ∀ n P, P ∈ Set.Icc (0 : ℝ) 1 → M.valueIter n P ≤ M.valueIter (n+1) P := by
    intro n
    induction n with
    | zero => intro P hP; exact (iter_bounds M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR 1 P hP).1
    | succ n ih =>
      intro P hP
      exact operator_le M hβ0.le hπ0 hπ1 _ _ ih hP
  exact fun n => hstep n P hP

private theorem value_tendsto (M : Model) (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (hC0 : 0 < M.C)
    (hCI : M.C < M.I) (hIR : M.I < M.R) (P : ℝ) (hP : P ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => M.valueIter n P) atTop (𝓝 (M.value P)) := by
  apply tendsto_nhds_limUnder
  refine ⟨_, tendsto_atTop_ciSup (iter_time_mono M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR P hP) ?_⟩
  refine ⟨M.C / (1 - M.β), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (iter_bounds M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR n P hP).2


private theorem iter_concave (M : Model) (hβ0 : 0 < M.β)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) :
    ∀ n, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (M.valueIter n) := by
  intro n
  induction n with
  | zero => exact concaveOn_const 0 (convex_Icc _ _)
  | succ n ih =>
    refine ⟨convex_Icc _ _, ?_⟩
    intro P hP Q hQ a b ha hb hab
    simp only [smul_eq_mul]
    have htP := update_mem M hπ0 hπ1 hP
    have htQ := update_mem M hπ0 hπ1 hQ
    have ht := ih.2 htP htQ ha hb hab
    simp only [smul_eq_mul] at ht
    have hT : M.T (a * P + b * Q) = a * M.T P + b * M.T Q := by
      dsimp [Model.T]
      nlinarith [hab]
    let V := M.valueIter n
    have hprod (X : ℝ) : M.valueIter (n+1) X ≤ M.rhs3 V X .produce := min_le_left _ _
    have hins (X : ℝ) : M.valueIter (n+1) X ≤ M.rhs3 V X .inspect :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hrev (X : ℝ) : M.valueIter (n+1) X ≤ M.rhs3 V X .revise :=
      (min_le_right _ _).trans (min_le_right _ _)
    change a * M.valueIter (n+1) P + b * M.valueIter (n+1) Q ≤
      min (M.rhs3 V (a * P + b * Q) .produce)
        (min (M.rhs3 V (a * P + b * Q) .inspect) (M.rhs3 V (a * P + b * Q) .revise))
    apply le_min
    · have hP' := mul_le_mul_of_nonneg_left (hprod P) ha
      have hQ' := mul_le_mul_of_nonneg_left (hprod Q) hb
      dsimp [Model.rhs3, V] at hP' hQ' ⊢
      rw [hT]
      nlinarith
    · apply le_min
      · have hP' := mul_le_mul_of_nonneg_left (hins P) ha
        have hQ' := mul_le_mul_of_nonneg_left (hins Q) hb
        dsimp [Model.rhs3] at hP' hQ' ⊢
        have he : M.I + M.β * (a * P + b * Q) * V 1 +
            M.β * (1 - (a * P + b * Q)) * V M.π =
            a * (M.I + M.β * P * V 1 + M.β * (1-P) * V M.π) +
            b * (M.I + M.β * Q * V 1 + M.β * (1-Q) * V M.π) := by
          linear_combination -(M.I + M.β * V M.π) * hab
        rw [he]
        exact add_le_add hP' hQ'
      · have hP' := mul_le_mul_of_nonneg_left (hrev P) ha
        have hQ' := mul_le_mul_of_nonneg_left (hrev Q) hb
        dsimp [Model.rhs3] at hP' hQ' ⊢
        calc
          _ ≤ a * (M.R + M.β * V M.π) + b * (M.R + M.β * V M.π) := add_le_add hP' hQ'
          _ = _ := by rw [← add_mul, hab, one_mul]

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) M.value := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro P hP Q hQ a b ha hb hab
  have hcombo := (convex_Icc (0 : ℝ) 1) hP hQ ha hb hab
  simp only [smul_eq_mul] at hcombo ⊢
  have hP' := value_tendsto M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR P hP
  have hQ' := value_tendsto M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR Q hQ
  have hcombo' := value_tendsto M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR _ hcombo
  apply le_of_tendsto_of_tendsto ((hP'.const_mul a).add (hQ'.const_mul b)) hcombo'
  apply Filter.Eventually.of_forall
  intro n
  simpa only [smul_eq_mul] using (iter_concave M hβ0 hπ0 hπ1 n).2 hP hQ ha hb hab

#print axioms solution
