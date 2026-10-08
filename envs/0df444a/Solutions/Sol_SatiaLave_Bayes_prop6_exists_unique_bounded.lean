-- Prove2me | solution 1 for SatiaLave.Bayes.prop6_exists_unique_bounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:23:10.177994+00:00
-- url     : https://prove2.me/submissions/abc57db1-59d3-4c53-b89c-d00668c40f00

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory


namespace SatiaLave.Bayes

open scoped BoundedContinuousFunction

structure SLDom (S : Type*) (D : S → Type*) where
  i : S
  g : Measure (Mat S D)

instance (S : Type*) (D : S → Type*) : TopologicalSpace (SLDom S D) := ⊥
instance (S : Type*) (D : S → Type*) : DiscreteTopology (SLDom S D) := ⟨rfl⟩

section
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]

theorem sl6_ae_stoch {g : Measure (Mat S D)} (hg : IsPrior g) : ∀ᵐ P ∂g, IsStoch P := by
  rw [ae_iff]; exact hg.2

theorem sl6_meas (i : S) (k : D i) (j : S) : Measurable fun P : Mat S D => P i k j := by fun_prop

theorem sl6_entry_le {P : Mat S D} (hP : IsStoch P) (i : S) (k : D i) (j : S) :
    0 ≤ P i k j ∧ P i k j ≤ 1 := by
  refine ⟨(hP i k).1 j, ?_⟩
  have := (hP i k).2
  rw [← this]
  exact Finset.single_le_sum (f := fun x => P i k x) (fun x _ => (hP i k).1 x) (Finset.mem_univ j)

theorem sl6_integrable {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (j : S) :
    Integrable (fun P : Mat S D => P i k j) g := by
  haveI := hg.1
  refine Integrable.mono' (integrable_const (1:ℝ)) (sl6_meas i k j).aestronglyMeasurable ?_
  filter_upwards [sl6_ae_stoch hg] with P hP
  have h := sl6_entry_le hP i k j
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2]

theorem sl6_pbar_nonneg {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (j : S) :
    0 ≤ pbar g i k j := by
  unfold pbar
  apply integral_nonneg_of_ae
  filter_upwards [sl6_ae_stoch hg] with P hP
  exact (hP i k).1 j

theorem sl6_pbar_sum {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) :
    ∑ j, pbar g i k j = 1 := by
  haveI := hg.1
  unfold pbar
  rw [← integral_finset_sum _ (fun j _ => sl6_integrable hg i k j)]
  rw [integral_congr_ae (g := fun _ => (1:ℝ))]
  · simp
  filter_upwards [sl6_ae_stoch hg] with P hP
  exact (hP i k).2

theorem sl6_bayes_prior {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (j : S) :
    IsPrior (bayes g i k j) := by
  unfold bayes
  split_ifs with h
  · exact hg
  have hpos : 0 < pbar g i k j := lt_of_le_of_ne (sl6_pbar_nonneg hg i k j) (Ne.symm h)
  haveI := hg.1
  have hlin : ∫⁻ P, ENNReal.ofReal (P i k j) ∂g = ENNReal.ofReal (pbar g i k j) := by
    unfold pbar
    rw [ofReal_integral_eq_lintegral_ofReal (sl6_integrable hg i k j)]
    filter_upwards [sl6_ae_stoch hg] with P hP
    exact (hP i k).1 j
  refine ⟨⟨?_⟩, ?_⟩
  · rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hlin,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using hpos) ENNReal.ofReal_ne_top
  · rw [Measure.smul_apply, withDensity_absolutelyContinuous _ _ hg.2, smul_zero]

theorem sl6_wavg_le {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (v : S → ℝ)
    (c : ℝ) (hv : ∀ j, v j ≤ c) : ∑ j, pbar g i k j * v j ≤ c := by
  calc ∑ j, pbar g i k j * v j ≤ ∑ j, pbar g i k j * c :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (sl6_pbar_nonneg hg i k j)
    _ = c := by rw [← Finset.sum_mul, sl6_pbar_sum hg, one_mul]

theorem sl6_wavg_ge {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (v : S → ℝ)
    (c : ℝ) (hv : ∀ j, c ≤ v j) : c ≤ ∑ j, pbar g i k j * v j := by
  calc c = ∑ j, pbar g i k j * c := by rw [← Finset.sum_mul, sl6_pbar_sum hg, one_mul]
    _ ≤ ∑ j, pbar g i k j * v j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (sl6_pbar_nonneg hg i k j)

theorem sl6_wavg_abs {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (v : S → ℝ)
    (c : ℝ) (hv : ∀ j, |v j| ≤ c) : |∑ j, pbar g i k j * v j| ≤ c := by
  rw [abs_le]
  constructor
  · have := sl6_wavg_ge hg i k v (-c) (fun j => (abs_le.1 (hv j)).1)
    linarith
  · exact sl6_wavg_le hg i k v c (fun j => (abs_le.1 (hv j)).2)

/-- The term inside the max of Eq. (10). -/
noncomputable def sl6_a (M : UncertainMDP S D) (F : S → Measure (Mat S D) → ℝ) (i : S)
    (g : Measure (Mat S D)) (k : D i) : ℝ :=
  ∑ j, pbar g i k j * M.r i k j + M.β * ∑ j, pbar g i k j * F j (bayes g i k j)

theorem sl6_a_sub (M : UncertainMDP S D) (F G : S → Measure (Mat S D) → ℝ) (i : S)
    (g : Measure (Mat S D)) (k : D i) :
    sl6_a M F i g k - sl6_a M G i g k =
      M.β * ∑ j, pbar g i k j * (F j (bayes g i k j) - G j (bayes g i k j)) := by
  unfold sl6_a
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem sl6_eq (M : UncertainMDP S D) (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    (i : S) (g : Measure (Mat S D)) (hg : IsPrior g) :
    f i g = Finset.univ.sup' Finset.univ_nonempty (sl6_a M f i g) := hf i g hg

theorem sl6_lim (M : UncertainMDP S D) (x C : ℝ) (h : ∀ n : ℕ, x ≤ M.β ^ n * C) : x ≤ 0 := by
  have hlim : Filter.Tendsto (fun n : ℕ => M.β ^ n * C) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one).mul_const C
    simpa using this
  exact ge_of_tendsto' hlim h

/-- Comparison: a bounded supersolution dominates the solution. -/
theorem sl6_comp_le (M : UncertainMDP S D) (f h : S → Measure (Mat S D) → ℝ)
    (hf : SolvesEq10 M f) (C : ℝ) (hfC : ∀ i g, IsPrior g → |f i g| ≤ C)
    (hhC : ∀ i g, IsPrior g → |h i g| ≤ C)
    (hsup : ∀ i g, IsPrior g → ∀ k, sl6_a M h i g k ≤ h i g) :
    ∀ i g, IsPrior g → f i g ≤ h i g := by
  have key : ∀ n : ℕ, ∀ i g, IsPrior g → f i g - h i g ≤ M.β ^ n * (2 * C) := by
    intro n
    induction n with
    | zero =>
      intro i g hg
      have h1 := hfC i g hg
      have h2 := hhC i g hg
      rw [abs_le] at h1 h2
      simp only [pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro i g hg
      have : f i g ≤ h i g + M.β ^ (n+1) * (2 * C) := by
        rw [sl6_eq M f hf i g hg]
        apply Finset.sup'_le
        intro k _
        have e := sl6_a_sub M f h i g k
        have w : ∑ j, pbar g i k j * (f j (bayes g i k j) - h j (bayes g i k j)) ≤
            M.β ^ n * (2 * C) :=
          sl6_wavg_le hg i k (fun j => f j (bayes g i k j) - h j (bayes g i k j)) _
            (fun j => ih j _ (sl6_bayes_prior hg i k j))
        have hs := hsup i g hg k
        have w2 : M.β * ∑ j, pbar g i k j * (f j (bayes g i k j) - h j (bayes g i k j)) ≤
            M.β * (M.β ^ n * (2 * C)) := mul_le_mul_of_nonneg_left w M.β_nonneg
        rw [pow_succ]
        linarith
      linarith
  intro i g hg
  have := sl6_lim M _ _ (fun n => key n i g hg)
  linarith

/-- Comparison: a bounded subsolution is dominated by the solution. -/
theorem sl6_comp_ge (M : UncertainMDP S D) (f h : S → Measure (Mat S D) → ℝ)
    (hf : SolvesEq10 M f) (C : ℝ) (hfC : ∀ i g, IsPrior g → |f i g| ≤ C)
    (hhC : ∀ i g, IsPrior g → |h i g| ≤ C)
    (hsub : ∀ i g, IsPrior g → ∃ k, h i g ≤ sl6_a M h i g k) :
    ∀ i g, IsPrior g → h i g ≤ f i g := by
  have key : ∀ n : ℕ, ∀ i g, IsPrior g → h i g - f i g ≤ M.β ^ n * (2 * C) := by
    intro n
    induction n with
    | zero =>
      intro i g hg
      have h1 := hfC i g hg
      have h2 := hhC i g hg
      rw [abs_le] at h1 h2
      simp only [pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro i g hg
      obtain ⟨k, hk⟩ := hsub i g hg
      have hfk : sl6_a M f i g k ≤ f i g := by
        rw [sl6_eq M f hf i g hg]
        exact Finset.le_sup' (sl6_a M f i g) (Finset.mem_univ k)
      have e := sl6_a_sub M h f i g k
      have w : ∑ j, pbar g i k j * (h j (bayes g i k j) - f j (bayes g i k j)) ≤
          M.β ^ n * (2 * C) :=
        sl6_wavg_le hg i k (fun j => h j (bayes g i k j) - f j (bayes g i k j)) _
          (fun j => ih j _ (sl6_bayes_prior hg i k j))
      have w2 : M.β * ∑ j, pbar g i k j * (h j (bayes g i k j) - f j (bayes g i k j)) ≤
          M.β * (M.β ^ n * (2 * C)) := mul_le_mul_of_nonneg_left w M.β_nonneg
      rw [pow_succ]
      linarith
  intro i g hg
  have := sl6_lim M _ _ (fun n => key n i g hg)
  linarith

theorem sl6_unique (M : UncertainMDP S D) :
    ∀ f₁ f₂ : S → Measure (Mat S D) → ℝ,
      SolvesEq10 M f₁ → IsBoundedOnPriors f₁ →
      SolvesEq10 M f₂ → IsBoundedOnPriors f₂ →
      ∀ i g, IsPrior g → f₁ i g = f₂ i g := by
  intro f₁ f₂ h1 ⟨C1, hC1⟩ h2 ⟨C2, hC2⟩ i g hg
  have b1 : ∀ i g, IsPrior g → |f₁ i g| ≤ max C1 C2 :=
    fun i g hg => le_trans (hC1 i g hg) (le_max_left _ _)
  have b2 : ∀ i g, IsPrior g → |f₂ i g| ≤ max C1 C2 :=
    fun i g hg => le_trans (hC2 i g hg) (le_max_right _ _)
  have s1 : ∀ i g, IsPrior g → ∀ k, sl6_a M f₁ i g k ≤ f₁ i g := by
    intro i g hg k; rw [sl6_eq M f₁ h1 i g hg]; exact Finset.le_sup' _ (Finset.mem_univ k)
  have s2 : ∀ i g, IsPrior g → ∀ k, sl6_a M f₂ i g k ≤ f₂ i g := by
    intro i g hg k; rw [sl6_eq M f₂ h2 i g hg]; exact Finset.le_sup' _ (Finset.mem_univ k)
  exact le_antisymm (sl6_comp_le M f₁ f₂ h1 _ b1 b2 s2 i g hg)
    (sl6_comp_le M f₂ f₁ h2 _ b2 b1 s1 i g hg)

/-! Existence via Banach's fixed point theorem. -/

noncomputable def sl6_R (M : UncertainMDP S D) : ℝ := ∑ i, ∑ k : D i, ∑ j, |M.r i k j|

theorem sl6_R_nonneg (M : UncertainMDP S D) : 0 ≤ sl6_R M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sl6_r_le (M : UncertainMDP S D) (i : S) (k : D i) (j : S) : |M.r i k j| ≤ sl6_R M := by
  unfold sl6_R
  calc |M.r i k j| ≤ ∑ j', |M.r i k j'| :=
        Finset.single_le_sum (f := fun j' => |M.r i k j'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ k' : D i, ∑ j', |M.r i k' j'| :=
        Finset.single_le_sum (f := fun k' => ∑ j', |M.r i k' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ k' : D i', ∑ j', |M.r i' k' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)

theorem sl6_a_abs (M : UncertainMDP S D) (F : S → Measure (Mat S D) → ℝ) (B : ℝ)
    (hF : ∀ j g', IsPrior g' → |F j g'| ≤ B) {g : Measure (Mat S D)} (hg : IsPrior g) (i : S)
    (k : D i) : |sl6_a M F i g k| ≤ sl6_R M + M.β * B := by
  unfold sl6_a
  have h1 := sl6_wavg_abs hg i k (fun j => M.r i k j) (sl6_R M) (fun j => sl6_r_le M i k j)
  have h2 := sl6_wavg_abs hg i k (fun j => F j (bayes g i k j)) B
    (fun j => hF _ _ (sl6_bayes_prior hg i k j))
  calc _ ≤ |∑ j, pbar g i k j * M.r i k j| + |M.β * ∑ j, pbar g i k j * F j (bayes g i k j)| :=
        abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg M.β_nonneg]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 M.β_nonneg)

theorem sl6_abs_sup' {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (B : ℝ)
    (h : ∀ k, |a k| ≤ B) : |Finset.univ.sup' Finset.univ_nonempty a| ≤ B := by
  rw [abs_le]
  constructor
  · have := (abs_le.1 (h (Classical.arbitrary ι))).1
    exact le_trans this (Finset.le_sup' a (Finset.mem_univ _))
  · exact Finset.sup'_le _ _ fun k _ => (abs_le.1 (h k)).2

theorem sl6_sup'_sub {ι : Type*} [Fintype ι] [Nonempty ι] (a b : ι → ℝ) (c : ℝ)
    (h : ∀ k, |a k - b k| ≤ c) :
    |Finset.univ.sup' Finset.univ_nonempty a - Finset.univ.sup' Finset.univ_nonempty b| ≤ c := by
  rw [abs_sub_le_iff]
  constructor
  · have : Finset.univ.sup' Finset.univ_nonempty a ≤ Finset.univ.sup' Finset.univ_nonempty b + c :=
      Finset.sup'_le _ _ fun k _ => by
        have := (abs_le.1 (h k)).2
        have := Finset.le_sup' b (Finset.mem_univ k)
        linarith
    linarith
  · have : Finset.univ.sup' Finset.univ_nonempty b ≤ Finset.univ.sup' Finset.univ_nonempty a + c :=
      Finset.sup'_le _ _ fun k _ => by
        have := (abs_le.1 (h k)).1
        have := Finset.le_sup' a (Finset.mem_univ k)
        linarith
    linarith

open Classical in
noncomputable def sl6_Phi0 (M : UncertainMDP S D) (F : SLDom S D → ℝ) (x : SLDom S D) : ℝ :=
  if IsPrior x.g then
    Finset.univ.sup' Finset.univ_nonempty (sl6_a M (fun j g => F ⟨j, g⟩) x.i x.g)
  else 0

theorem sl6_Phi0_abs (M : UncertainMDP S D) (F : SLDom S D →ᵇ ℝ) (x : SLDom S D) :
    |sl6_Phi0 M F x| ≤ sl6_R M + M.β * ‖F‖ := by
  unfold sl6_Phi0
  split_ifs with hx
  · apply sl6_abs_sup'
    intro k
    apply sl6_a_abs M _ _ _ hx
    intro j g' _
    rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm _
  · simp only [abs_zero]
    exact add_nonneg (sl6_R_nonneg M) (mul_nonneg M.β_nonneg (norm_nonneg _))

noncomputable def sl6_Phi (M : UncertainMDP S D) (F : SLDom S D →ᵇ ℝ) : SLDom S D →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfDiscrete (sl6_Phi0 M F) (2 * (sl6_R M + M.β * ‖F‖)) (by
    intro x y
    have hx := sl6_Phi0_abs M F x
    have hy := sl6_Phi0_abs M F y
    rw [Real.dist_eq]
    rw [abs_le] at hx hy ⊢
    constructor <;> linarith)

theorem sl6_Phi_apply (M : UncertainMDP S D) (F : SLDom S D →ᵇ ℝ) (x : SLDom S D) :
    sl6_Phi M F x = sl6_Phi0 M F x := rfl

theorem sl6_Phi_lip (M : UncertainMDP S D) (F G : SLDom S D →ᵇ ℝ) :
    dist (sl6_Phi M F) (sl6_Phi M G) ≤ M.β * dist F G := by
  rw [BoundedContinuousFunction.dist_le (mul_nonneg M.β_nonneg dist_nonneg)]
  intro x
  rw [sl6_Phi_apply, sl6_Phi_apply]
  unfold sl6_Phi0
  split_ifs with hx
  · rw [Real.dist_eq]
    apply sl6_sup'_sub
    intro k
    rw [sl6_a_sub, abs_mul, abs_of_nonneg M.β_nonneg]
    apply mul_le_mul_of_nonneg_left _ M.β_nonneg
    apply sl6_wavg_abs hx
    intro j
    rw [← Real.dist_eq]; exact BoundedContinuousFunction.dist_coe_le_dist _
  · simp only [dist_self]; exact mul_nonneg M.β_nonneg dist_nonneg

theorem sl6_exists (M : UncertainMDP S D) :
    ∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f := by
  let K : NNReal := ⟨M.β, M.β_nonneg⟩
  have hK : ContractingWith K (sl6_Phi M) :=
    ⟨by rw [← NNReal.coe_lt_coe]; exact M.β_lt_one,
     LipschitzWith.of_dist_le_mul fun F G => sl6_Phi_lip M F G⟩
  have hF : sl6_Phi M (ContractingWith.fixedPoint _ hK) = ContractingWith.fixedPoint _ hK :=
    ContractingWith.fixedPoint_isFixedPt hK
  set F := ContractingWith.fixedPoint _ hK
  refine ⟨fun i g => F ⟨i, g⟩, ?_, ‖F‖, fun i g _ => ?_⟩
  · intro i g hg
    have := congrArg (fun H : SLDom S D →ᵇ ℝ => H ⟨i, g⟩) hF
    simp only [sl6_Phi_apply] at this
    show F ⟨i, g⟩ = _
    rw [← this]
    unfold sl6_Phi0
    rw [if_pos hg]
    rfl
  · rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm _

theorem prop6_core (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    ∀ f₁ f₂ : S → Measure (Mat S D) → ℝ,
      SolvesEq10 M f₁ → IsBoundedOnPriors f₁ →
      SolvesEq10 M f₂ → IsBoundedOnPriors f₂ →
      ∀ i g, IsPrior g → f₁ i g = f₂ i g :=
  ⟨sl6_exists M, sl6_unique M⟩

end

end SatiaLave.Bayes

open SatiaLave.Bayes


theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    ∀ f₁ f₂ : S → Measure (Mat S D) → ℝ,
      SolvesEq10 M f₁ → IsBoundedOnPriors f₁ →
      SolvesEq10 M f₂ → IsBoundedOnPriors f₂ →
      ∀ i g, IsPrior g → f₁ i g = f₂ i g := by
  exact prop6_core M
