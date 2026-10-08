-- Prove2me | solution 1 for SatiaLave.Bayes.bayes_return_bounded_by_maxmax_maxmin
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:33:50.042267+00:00
-- url     : https://prove2.me/submissions/fbd1a174-ec39-4e63-9d72-1f01b4ff8b3c

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

/-! Shared tools for integrals against priors and posteriors. -/

theorem sl_row_abs {P : Mat S D} (hP : IsStoch P) (i : S) (k : D i) (v : S → ℝ) (c : ℝ)
    (hv : ∀ j, |v j| ≤ c) : |∑ j, P i k j * v j| ≤ c := by
  rw [abs_le]; constructor
  · calc -c = ∑ j, P i k j * (-c) := by rw [← Finset.sum_mul, (hP i k).2]; ring
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_le.1 (hv j)).1 ((hP i k).1 j)
  · calc _ ≤ ∑ j, P i k j * c := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_le.1 (hv j)).2 ((hP i k).1 j)
      _ = c := by rw [← Finset.sum_mul, (hP i k).2, one_mul]

theorem sl_post {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (j : S)
    (φ : Mat S D → ℝ) :
    pbar g i k j * ∫ P, φ P ∂(bayes g i k j) = ∫ P, P i k j * φ P ∂g := by
  by_cases h : pbar g i k j = 0
  · rw [h, zero_mul]
    have hz : (fun P : Mat S D => P i k j) =ᵐ[g] 0 := by
      rw [← integral_eq_zero_iff_of_nonneg_ae _ (sl6_integrable hg i k j)]
      · exact h
      · filter_upwards [sl6_ae_stoch hg] with P hP; exact (hP i k).1 j
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with P hP
    simp only [Pi.zero_apply] at hP ⊢
    rw [hP, zero_mul]
  · unfold bayes; rw [if_neg h]
    rw [integral_smul_measure]
    have : (fun P : Mat S D => ENNReal.ofReal (P i k j)) =
        fun P => ((Real.toNNReal (P i k j) : NNReal) : ENNReal) := rfl
    rw [this, integral_withDensity_eq_integral_smul (sl6_meas i k j).real_toNNReal φ]
    have hpos : 0 < pbar g i k j := lt_of_le_of_ne (sl6_pbar_nonneg hg i k j) (Ne.symm h)
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hpos.le, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ h, one_mul]
    apply integral_congr_ae
    filter_upwards [sl6_ae_stoch hg] with P hP
    rw [NNReal.smul_def, Real.coe_toNNReal _ ((hP i k).1 j), smul_eq_mul]

theorem sl_int_bdd {g : Measure (Mat S D)} (hg : IsPrior g) (φ : Mat S D → ℝ)
    (hm : AEStronglyMeasurable φ g) (B : ℝ) (hb : ∀ P, IsStoch P → |φ P| ≤ B) :
    Integrable φ g := by
  haveI := hg.1
  refine Integrable.mono' (integrable_const B) hm ?_
  filter_upwards [sl6_ae_stoch hg] with P hP
  rw [Real.norm_eq_abs]; exact hb P hP

theorem sl_int_mul {g : Measure (Mat S D)} (hg : IsPrior g) (i : S) (k : D i) (j : S)
    (φ : Mat S D → ℝ) (hm : AEStronglyMeasurable φ g) (B : ℝ)
    (hb : ∀ P, IsStoch P → |φ P| ≤ B) :
    Integrable (fun P => P i k j * φ P) g := by
  refine sl_int_bdd hg _ ((sl6_meas i k j).aestronglyMeasurable.mul hm) B ?_
  intro P hP
  have h1 := sl6_entry_le hP i k j
  have h2 := hb P hP
  rw [abs_mul, abs_of_nonneg h1.1]
  calc P i k j * |φ P| ≤ 1 * |φ P| := mul_le_mul_of_nonneg_right h1.2 (abs_nonneg _)
    _ ≤ B := by rw [one_mul]; exact h2

theorem sl_int_abs {g : Measure (Mat S D)} (hg : IsPrior g) (φ : Mat S D → ℝ) (B : ℝ)
    (hb : ∀ P, IsStoch P → |φ P| ≤ B) : |∫ P, φ P ∂g| ≤ B := by
  haveI := hg.1
  have := norm_integral_le_of_norm_le_const (μ := g) (f := φ) (C := B)
    (by filter_upwards [sl6_ae_stoch hg] with P hP; rw [Real.norm_eq_abs]; exact hb P hP)
  simpa using this

theorem sl_expand (M : UncertainMDP S D) {g : Measure (Mat S D)} (hg : IsPrior g) (i : S)
    (k : D i) (φ : S → Mat S D → ℝ) (hφ : ∀ j, Integrable (fun P => P i k j * φ j P) g) :
    ∫ P, ∑ j, P i k j * (M.r i k j + M.β * φ j P) ∂g =
      sl6_a M (fun j g' => ∫ P, φ j P ∂g') i g k := by
  have e : ∀ j, (fun P : Mat S D => P i k j * (M.r i k j + M.β * φ j P)) =
      fun P => P i k j * M.r i k j + M.β * (P i k j * φ j P) := by
    intro j; funext P; ring
  have hI : ∀ j, Integrable (fun P : Mat S D => P i k j * (M.r i k j + M.β * φ j P)) g := by
    intro j
    rw [e j]
    exact ((sl6_integrable hg i k j).mul_const (M.r i k j)).add ((hφ j).const_mul M.β)
  rw [integral_finset_sum _ (fun j _ => hI j)]
  unfold sl6_a
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sl_post hg i k j (φ j), e j,
    integral_add ((sl6_integrable hg i k j).mul_const _) ((hφ j).const_mul _),
    integral_mul_const, integral_const_mul]
  rfl

/-! Stationary policies. -/

noncomputable def sl_u (M : UncertainMDP S D) (A : (i : S) → D i) (n : ℕ) (P : Mat S D) :
    S → ℝ := ((policyMatrix P A) ^ n).mulVec (policyReward M P A)

theorem sl_u_succ (M : UncertainMDP S D) (A : (i : S) → D i) (n : ℕ) (P : Mat S D) (i : S) :
    sl_u M A (n+1) P i = ∑ j, P i (A i) j * sl_u M A n P j := by
  unfold sl_u
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

theorem sl_u_zero (M : UncertainMDP S D) (A : (i : S) → D i) (P : Mat S D) (i : S) :
    sl_u M A 0 P i = ∑ j, P i (A i) j * M.r i (A i) j := by
  unfold sl_u
  rw [pow_zero, Matrix.one_mulVec]
  rfl

theorem sl_u_meas (M : UncertainMDP S D) (A : (i : S) → D i) (n : ℕ) (i : S) :
    Measurable fun P => sl_u M A n P i := by
  induction n generalizing i with
  | zero =>
    simp only [sl_u_zero]
    exact Finset.measurable_sum _ fun j _ => (sl6_meas i (A i) j).mul_const _
  | succ n ih =>
    simp only [sl_u_succ]
    exact Finset.measurable_sum _ fun j _ => (sl6_meas i (A i) j).mul (ih j)

theorem sl_u_bd (M : UncertainMDP S D) (A : (i : S) → D i) {P : Mat S D} (hP : IsStoch P)
    (n : ℕ) (i : S) : |sl_u M A n P i| ≤ sl6_R M := by
  induction n generalizing i with
  | zero =>
    rw [sl_u_zero]
    exact sl_row_abs hP i (A i) _ _ fun j => sl6_r_le M i (A i) j
  | succ n ih =>
    rw [sl_u_succ]
    exact sl_row_abs hP i (A i) _ _ ih

theorem sl_pv_eq (M : UncertainMDP S D) (A : (i : S) → D i) (P : Mat S D) (i : S) :
    policyValue M A P i = ∑' n : ℕ, M.β ^ n * sl_u M A n P i := rfl

theorem sl_pv_summable (M : UncertainMDP S D) (A : (i : S) → D i) {P : Mat S D}
    (hP : IsStoch P) (i : S) : Summable fun n : ℕ => M.β ^ n * sl_u M A n P i := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one M.β_nonneg M.β_lt_one).mul_right (sl6_R M)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg M.β_nonneg n)]
  exact mul_le_mul_of_nonneg_left (sl_u_bd M A hP n i) (pow_nonneg M.β_nonneg n)

theorem sl_pv_bd (M : UncertainMDP S D) (A : (i : S) → D i) {P : Mat S D}
    (hP : IsStoch P) (i : S) : |policyValue M A P i| ≤ (1 - M.β)⁻¹ * sl6_R M := by
  rw [sl_pv_eq, ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one M.β_nonneg M.β_lt_one).mul_right (sl6_R M)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg M.β_nonneg n)]
  exact mul_le_mul_of_nonneg_left (sl_u_bd M A hP n i) (pow_nonneg M.β_nonneg n)

theorem sl_pv_meas (M : UncertainMDP S D) (A : (i : S) → D i) (i : S) :
    Measurable fun P => policyValue M A P i := by
  simp only [sl_pv_eq]
  exact Measurable.tsum fun n => (sl_u_meas M A n i).const_mul _

theorem sl_pv_bell (M : UncertainMDP S D) (A : (i : S) → D i) {P : Mat S D}
    (hP : IsStoch P) (i : S) :
    policyValue M A P i =
      ∑ j, P i (A i) j * (M.r i (A i) j + M.β * policyValue M A P j) := by
  rw [sl_pv_eq, (sl_pv_summable M A hP i).tsum_eq_zero_add]
  have e1 : ∀ n : ℕ, M.β ^ (n+1) * sl_u M A (n+1) P i =
      M.β * ∑ j, P i (A i) j * (M.β ^ n * sl_u M A n P j) := by
    intro n
    rw [sl_u_succ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [e1]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun j _ => (sl_pv_summable M A hP j).mul_left _)]
  simp only [tsum_mul_left, pow_zero, one_mul, sl_u_zero, ← sl_pv_eq]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem policy_core (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g : Measure (Mat S D)) (hg : IsPrior g) (A : (i : S) → D i) (i : S) :
    Integrable (fun P => policyValue M A P i) g ∧
      ∫ P, policyValue M A P i ∂g ≤ f i g := by
  obtain ⟨C, hC⟩ := hb
  have hbd := fun j P (hP : IsStoch P) => sl_pv_bd M A hP j
  refine ⟨sl_int_bdd hg _ (sl_pv_meas M A i).aestronglyMeasurable _ (hbd i), ?_⟩
  refine sl6_comp_ge M f (fun j g' => ∫ P, policyValue M A P j ∂g') hf
    (max C ((1 - M.β)⁻¹ * sl6_R M))
    (fun j g' hg' => le_trans (hC j g' hg') (le_max_left _ _))
    (fun j g' hg' => le_trans (sl_int_abs hg' _ _ (hbd j)) (le_max_right _ _)) ?_ i g hg
  intro j g' hg'
  refine ⟨A j, le_of_eq ?_⟩
  rw [← sl_expand M hg' j (A j) (fun l P => policyValue M A P l)
    (fun l => sl_int_mul hg' j (A j) l _ (sl_pv_meas M A l).aestronglyMeasurable _ (hbd l))]
  apply integral_congr_ae
  filter_upwards [sl6_ae_stoch hg'] with P hP
  exact sl_pv_bell M A hP j

/-! Point-mass priors and Jensen. -/

theorem sl_pbar_dirac (P : Mat S D) (l : S) (m : D l) (j : S) :
    pbar (Measure.dirac P) l m j = P l m j := by
  unfold pbar
  exact integral_dirac' _ _
    (by fun_prop : Measurable fun Q : Mat S D => Q l m j).stronglyMeasurable

theorem sl_bayes_dirac (P : Mat S D) (hP : ∀ i k j, 0 ≤ P i k j) (l : S) (m : D l) (j : S) :
    bayes (Measure.dirac P) l m j = Measure.dirac P := by
  unfold bayes
  rw [sl_pbar_dirac]
  split_ifs with h
  · rfl
  · rw [dirac_withDensity' (by fun_prop : Measurable fun Q : Mat S D => ENNReal.ofReal (Q l m j)),
      smul_smul]
    have hpos : 0 < P l m j := lt_of_le_of_ne (hP l m j) (Ne.symm h)
    rw [ENNReal.inv_mul_cancel (by simpa using hpos) ENNReal.ofReal_ne_top, one_smul]

theorem sl_dirac_prior {P : Mat S D} (hP : IsStoch P) : IsPrior (Measure.dirac P) := by
  refine ⟨inferInstance, ?_⟩
  rw [Measure.dirac_apply]
  simp [hP]

theorem sl_V_eq (M : UncertainMDP S D) (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    {P : Mat S D} (hP : IsStoch P) (i : S) :
    f i (Measure.dirac P) = Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
      ∑ j, P i k j * (M.r i k j + M.β * f j (Measure.dirac P))) := by
  have hnn : ∀ i k j, 0 ≤ P i k j := fun i k j => (hP i k).1 j
  rw [hf i _ (sl_dirac_prior hP)]
  congr 1
  funext k
  simp only [sl_pbar_dirac, sl_bayes_dirac P hnn]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

noncomputable def sl_v (M : UncertainMDP S D) : ℕ → Mat S D → S → ℝ
  | 0 => fun _ _ => 0
  | n+1 => fun P i => Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
      ∑ j, P i k j * (M.r i k j + M.β * sl_v M n P j))

theorem sl_v_meas (M : UncertainMDP S D) (n : ℕ) (i : S) : Measurable fun P => sl_v M n P i := by
  induction n generalizing i with
  | zero => exact measurable_const
  | succ n ih =>
    have : (fun P => sl_v M (n+1) P i) = Finset.univ.sup' Finset.univ_nonempty
        (fun (k : D i) (P : Mat S D) => ∑ j, P i k j * (M.r i k j + M.β * sl_v M n P j)) := by
      funext P; rw [Finset.sup'_apply]; rfl
    rw [this]
    exact Finset.measurable_sup' _ fun k _ => Finset.measurable_sum _ fun j _ =>
      (sl6_meas i k j).mul (measurable_const.add (measurable_const.mul (ih j)))

theorem sl_v_close (M : UncertainMDP S D) (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    (C : ℝ) (hC : ∀ i g, IsPrior g → |f i g| ≤ C) {P : Mat S D} (hP : IsStoch P) (n : ℕ)
    (i : S) : |sl_v M n P i - f i (Measure.dirac P)| ≤ M.β ^ n * C := by
  induction n generalizing i with
  | zero =>
    simp only [sl_v, zero_sub, abs_neg, pow_zero, one_mul]
    exact hC i _ (sl_dirac_prior hP)
  | succ n ih =>
    rw [sl_V_eq M f hf hP i]
    simp only [sl_v]
    apply sl6_sup'_sub
    intro k
    have : (∑ j, P i k j * (M.r i k j + M.β * sl_v M n P j)) -
        ∑ j, P i k j * (M.r i k j + M.β * f j (Measure.dirac P)) =
        M.β * ∑ j, P i k j * (sl_v M n P j - f j (Measure.dirac P)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, abs_mul, abs_of_nonneg M.β_nonneg, pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left (sl_row_abs hP i k _ _ ih) M.β_nonneg

theorem jensen_core (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g : Measure (Mat S D)) (hg : IsPrior g) (i : S) :
    Integrable (fun P => f i (Measure.dirac P)) g ∧
      f i g ≤ ∫ P, f i (Measure.dirac P) ∂g := by
  obtain ⟨C, hC⟩ := hb
  have hbd : ∀ j P, IsStoch P → |f j (Measure.dirac P)| ≤ C :=
    fun j P hP => hC j _ (sl_dirac_prior hP)
  have hm : ∀ j (g' : Measure (Mat S D)), IsPrior g' →
      AEStronglyMeasurable (fun P => f j (Measure.dirac P)) g' := by
    intro j g' hg'
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop (f := fun n P => sl_v M n P j)
      (fun n => (sl_v_meas M n j).aestronglyMeasurable) ?_
    filter_upwards [sl6_ae_stoch hg'] with P hP
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ => M.β ^ n * C) (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact sl_v_close M f hf C hC hP n j) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one).mul_const C
  refine ⟨sl_int_bdd hg _ (hm i g hg) C (hbd i), ?_⟩
  refine sl6_comp_le M f (fun j g' => ∫ P, f j (Measure.dirac P) ∂g') hf C hC
    (fun j g' hg' => sl_int_abs hg' _ _ (hbd j)) ?_ i g hg
  intro j g' hg' k
  have hφ : ∀ l, Integrable (fun P => P j k l * f l (Measure.dirac P)) g' :=
    fun l => sl_int_mul hg' j k l _ (hm l g' hg') C (hbd l)
  rw [← sl_expand M hg' j k (fun l P => f l (Measure.dirac P)) hφ]
  apply integral_mono_ae
  · refine integrable_finsetSum _ fun l _ => ?_
    have e : (fun P : Mat S D => P j k l * (M.r j k l + M.β * f l (Measure.dirac P))) =
        fun P => P j k l * M.r j k l + M.β * (P j k l * f l (Measure.dirac P)) := by
      funext P; ring
    rw [e]; exact ((sl6_integrable hg' j k l).mul_const _).add ((hφ l).const_mul _)
  · exact sl_int_bdd hg' _ (hm j g' hg') C (hbd j)
  · filter_upwards [sl6_ae_stoch hg'] with P hP
    rw [sl_V_eq M f hf hP j]
    exact Finset.le_sup' (fun k => ∑ l, P j k l * (M.r j k l + M.β * f l (Measure.dirac P)))
      (Finset.mem_univ k)

/-! Max-max and max-min equations. -/

theorem sl_simplex_le {p : S → ℝ} (hp : p ∈ stdSimplex ℝ S) (v : S → ℝ) (c : ℝ)
    (hv : ∀ j, v j ≤ c) : ∑ j, p j * v j ≤ c := by
  calc _ ≤ ∑ j, p j * c := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hp.1 j)
    _ = c := by rw [← Finset.sum_mul, hp.2, one_mul]

theorem sl_simplex_ge {p : S → ℝ} (hp : p ∈ stdSimplex ℝ S) (v : S → ℝ) (c : ℝ)
    (hv : ∀ j, c ≤ v j) : c ≤ ∑ j, p j * v j := by
  calc c = ∑ j, p j * c := by rw [← Finset.sum_mul, hp.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hp.1 j)

theorem sl_simplex_abs {p : S → ℝ} (hp : p ∈ stdSimplex ℝ S) (v : S → ℝ) (c : ℝ)
    (hv : ∀ j, |v j| ≤ c) : |∑ j, p j * v j| ≤ c := by
  rw [abs_le]
  exact ⟨by linarith [sl_simplex_ge hp v (-c) fun j => (abs_le.1 (hv j)).1],
    sl_simplex_le hp v c fun j => (abs_le.1 (hv j)).2⟩

noncomputable def sl_cB (M : UncertainMDP S D) (V : S → ℝ) (i : S) (k : D i) : ℝ :=
  ∑ j, |M.r i k j + M.β * V j|

theorem sl_simp_bd (M : UncertainMDP S D) (V : S → ℝ) (i : S) (k : D i) {p : S → ℝ}
    (hp : p ∈ stdSimplex ℝ S) : |∑ j, p j * (M.r i k j + M.β * V j)| ≤ sl_cB M V i k :=
  sl_simplex_abs hp _ _ fun j => Finset.single_le_sum
    (f := fun j => |M.r i k j + M.β * V j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem sl_simp_diff (M : UncertainMDP S D) (V W : S → ℝ) (i : S) (k : D i) {p : S → ℝ}
    (hp : p ∈ stdSimplex ℝ S) :
    |∑ j, p j * (M.r i k j + M.β * V j) - ∑ j, p j * (M.r i k j + M.β * W j)| ≤
      M.β * dist V W := by
  have e : ∑ j, p j * (M.r i k j + M.β * V j) - ∑ j, p j * (M.r i k j + M.β * W j) =
      M.β * ∑ j, p j * (V j - W j) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, abs_mul, abs_of_nonneg M.β_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.β_nonneg
  apply sl_simplex_abs hp
  intro j
  rw [← Real.dist_eq]; exact dist_le_pi_dist V W j

theorem sl_bddA (M : UncertainMDP S D) (V : S → ℝ) (i : S) (k : D i) :
    BddAbove (Set.range fun p : M.U i k => ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * V j)) :=
  ⟨sl_cB M V i k, by
    rintro _ ⟨p, rfl⟩
    exact (abs_le.1 (sl_simp_bd M V i k (M.U_subset i k p.2))).2⟩

theorem sl_bddB (M : UncertainMDP S D) (V : S → ℝ) (i : S) (k : D i) :
    BddBelow (Set.range fun p : M.U i k => ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * V j)) :=
  ⟨-sl_cB M V i k, by
    rintro _ ⟨p, rfl⟩
    exact (abs_le.1 (sl_simp_bd M V i k (M.U_subset i k p.2))).1⟩

theorem sl_ciSup_sub {ι : Type*} [Nonempty ι] (F G : ι → ℝ) (c : ℝ)
    (bF : BddAbove (Set.range F)) (bG : BddAbove (Set.range G)) (h : ∀ p, |F p - G p| ≤ c) :
    |(⨆ p, F p) - ⨆ p, G p| ≤ c := by
  rw [abs_sub_le_iff]; constructor
  · have : (⨆ p, F p) ≤ (⨆ p, G p) + c := ciSup_le fun p => by
      have := (abs_le.1 (h p)).2; have := le_ciSup bG p; linarith
    linarith
  · have : (⨆ p, G p) ≤ (⨆ p, F p) + c := ciSup_le fun p => by
      have := (abs_le.1 (h p)).1; have := le_ciSup bF p; linarith
    linarith

theorem sl_ciInf_sub {ι : Type*} [Nonempty ι] (F G : ι → ℝ) (c : ℝ)
    (bF : BddBelow (Set.range F)) (bG : BddBelow (Set.range G)) (h : ∀ p, |F p - G p| ≤ c) :
    |(⨅ p, F p) - ⨅ p, G p| ≤ c := by
  rw [abs_sub_le_iff]; constructor
  · have : (⨅ p, F p) - c ≤ (⨅ p, G p) := le_ciInf fun p => by
      have := (abs_le.1 (h p)).2; have := ciInf_le bF p; linarith
    linarith
  · have : (⨅ p, G p) - c ≤ (⨅ p, F p) := le_ciInf fun p => by
      have := (abs_le.1 (h p)).1; have := ciInf_le bG p; linarith
    linarith

noncomputable def sl_Tp (M : UncertainMDP S D) (V : S → ℝ) : S → ℝ := fun i =>
  Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
    ⨆ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * V j))

noncomputable def sl_Tm (M : UncertainMDP S D) (V : S → ℝ) : S → ℝ := fun i =>
  Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
    ⨅ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * V j))

theorem sl_Tp_lip (M : UncertainMDP S D) (V W : S → ℝ) :
    dist (sl_Tp M V) (sl_Tp M W) ≤ M.β * dist V W := by
  rw [dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)]
  intro i
  rw [Real.dist_eq]
  apply sl6_sup'_sub
  intro k
  haveI := (M.U_nonempty i k).to_subtype
  exact sl_ciSup_sub _ _ _ (sl_bddA M V i k) (sl_bddA M W i k)
    fun p => sl_simp_diff M V W i k (M.U_subset i k p.2)

theorem sl_Tm_lip (M : UncertainMDP S D) (V W : S → ℝ) :
    dist (sl_Tm M V) (sl_Tm M W) ≤ M.β * dist V W := by
  rw [dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)]
  intro i
  rw [Real.dist_eq]
  apply sl6_sup'_sub
  intro k
  haveI := (M.U_nonempty i k).to_subtype
  exact sl_ciInf_sub _ _ _ (sl_bddB M V i k) (sl_bddB M W i k)
    fun p => sl_simp_diff M V W i k (M.U_subset i k p.2)

theorem sl_Vp_exists (M : UncertainMDP S D) : ∃ V : S → ℝ, SolvesVplus M V := by
  let K : NNReal := ⟨M.β, M.β_nonneg⟩
  have hK : ContractingWith K (sl_Tp M) :=
    ⟨by rw [← NNReal.coe_lt_coe]; exact M.β_lt_one,
     LipschitzWith.of_dist_le_mul fun V W => sl_Tp_lip M V W⟩
  have h : sl_Tp M (ContractingWith.fixedPoint _ hK) = ContractingWith.fixedPoint _ hK :=
    ContractingWith.fixedPoint_isFixedPt hK
  exact ⟨_, fun i => (congrFun h i).symm⟩

theorem sl_Vm_exists (M : UncertainMDP S D) : ∃ V : S → ℝ, SolvesVminus M V := by
  let K : NNReal := ⟨M.β, M.β_nonneg⟩
  have hK : ContractingWith K (sl_Tm M) :=
    ⟨by rw [← NNReal.coe_lt_coe]; exact M.β_lt_one,
     LipschitzWith.of_dist_le_mul fun V W => sl_Tm_lip M V W⟩
  have h : sl_Tm M (ContractingWith.fixedPoint _ hK) = ContractingWith.fixedPoint _ hK :=
    ContractingWith.fixedPoint_isFixedPt hK
  exact ⟨_, fun i => (congrFun h i).symm⟩

/-! Comparisons for a known matrix. -/

theorem sl_geo (M : UncertainMDP S D) (x : S → ℝ)
    (hstep : ∀ c, (∀ j, x j ≤ c) → ∀ i, x i ≤ M.β * c) : ∀ i, x i ≤ 0 := by
  have key : ∀ n : ℕ, ∀ i, x i ≤ M.β ^ n * Finset.univ.sup' Finset.univ_nonempty x := by
    intro n
    induction n with
    | zero => intro i; simp only [pow_zero, one_mul]; exact Finset.le_sup' x (Finset.mem_univ i)
    | succ n ih => intro i; rw [pow_succ', mul_assoc]; exact hstep _ ih i
  intro i
  exact sl6_lim M _ _ fun n => key n i

theorem sl_r_le_rmax (M : UncertainMDP S D) (i : S) (k : D i) (j : S) :
    M.r i k j ≤ (1 - M.β) * rmax M := by
  have h : M.r i k j / (1 - M.β) ≤ rmax M :=
    Finset.le_sup' (fun x : (Σ i, D i) × S => M.r x.1.1 x.1.2 x.2 / (1 - M.β))
      (Finset.mem_univ ((⟨i, k⟩ : Σ i, D i), j))
  have hb : 0 < 1 - M.β := by linarith [M.β_lt_one]
  rw [div_le_iff₀ hb] at h; linarith

theorem sl_rmin_le_r (M : UncertainMDP S D) (i : S) (k : D i) (j : S) :
    (1 - M.β) * rmin M ≤ M.r i k j := by
  have h : rmin M ≤ M.r i k j / (1 - M.β) :=
    Finset.inf'_le (fun x : (Σ i, D i) × S => M.r x.1.1 x.1.2 x.2 / (1 - M.β))
      (Finset.mem_univ ((⟨i, k⟩ : Σ i, D i), j))
  have hb : 0 < 1 - M.β := by linarith [M.β_lt_one]
  rw [le_div_iff₀ hb] at h; linarith

theorem sl_VP_le_Vp (M : UncertainMDP S D) (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    {P : Mat S D} (hP : IsStoch P) (hc : P ∈ consistentSet M) (Vp : S → ℝ)
    (hVp : SolvesVplus M Vp) (i : S) : f i (Measure.dirac P) ≤ Vp i := by
  have := sl_geo M (fun i => f i (Measure.dirac P) - Vp i) ?_ i
  · try simp only at this
    linarith
  intro c hc' i
  try simp only at hc' ⊢
  have hVi : f i (Measure.dirac P) ≤ Vp i + M.β * c := by
    rw [sl_V_eq M f hf hP i]
    apply Finset.sup'_le; intro k _
    have e : ∑ j, P i k j * (M.r i k j + M.β * f j (Measure.dirac P)) -
        ∑ j, P i k j * (M.r i k j + M.β * Vp j) =
        M.β * ∑ j, P i k j * (f j (Measure.dirac P) - Vp j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h2 := sl_simplex_le (hP i k) _ c hc'
    have h3 := mul_le_mul_of_nonneg_left h2 M.β_nonneg
    have h4 : ∑ j, P i k j * (M.r i k j + M.β * Vp j) ≤
        ⨆ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * Vp j) :=
      le_ciSup (f := fun p : M.U i k => ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * Vp j))
        (sl_bddA M Vp i k) ⟨P i k, hc i k⟩
    have h5 : (⨆ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * Vp j)) ≤ Vp i := by
      rw [hVp i]
      exact Finset.le_sup' (fun k : D i =>
        ⨆ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * Vp j)) (Finset.mem_univ k)
    linarith
  linarith

theorem sl_VP_le_rmax (M : UncertainMDP S D) (f : S → Measure (Mat S D) → ℝ)
    (hf : SolvesEq10 M f) {P : Mat S D} (hP : IsStoch P) (i : S) :
    f i (Measure.dirac P) ≤ rmax M := by
  have := sl_geo M (fun i => f i (Measure.dirac P) - rmax M) ?_ i
  · try simp only at this
    linarith
  intro c hc' i
  try simp only at hc' ⊢
  have hVi : f i (Measure.dirac P) ≤ rmax M + M.β * c := by
    rw [sl_V_eq M f hf hP i]
    apply Finset.sup'_le; intro k _
    apply sl_simplex_le (hP i k)
    intro j
    have h1 := sl_r_le_rmax M i k j
    have h2 : M.β * f j (Measure.dirac P) ≤ M.β * (rmax M + c) :=
      mul_le_mul_of_nonneg_left (by linarith [hc' j]) M.β_nonneg
    linarith
  linarith

theorem sl_Vm_le_W (M : UncertainMDP S D) {P : Mat S D} (hP : IsStoch P)
    (hc : P ∈ consistentSet M) (Vm : S → ℝ) (A : (i : S) → D i)
    (hA : ∀ i, Vm i = ⨅ p : M.U i (A i), ∑ j, (p : S → ℝ) j * (M.r i (A i) j + M.β * Vm j))
    (i : S) : Vm i ≤ policyValue M A P i := by
  have := sl_geo M (fun i => Vm i - policyValue M A P i) ?_ i
  · try simp only at this
    linarith
  intro c hc' i
  try simp only at hc' ⊢
  have h1 : Vm i ≤ ∑ j, P i (A i) j * (M.r i (A i) j + M.β * Vm j) := by
    rw [hA i]
    exact ciInf_le (f := fun p : M.U i (A i) =>
      ∑ j, (p : S → ℝ) j * (M.r i (A i) j + M.β * Vm j)) (sl_bddB M Vm i (A i))
      ⟨P i (A i), hc i (A i)⟩
  have h2 := sl_pv_bell M A hP i
  have e : ∑ j, P i (A i) j * (M.r i (A i) j + M.β * Vm j) -
      ∑ j, P i (A i) j * (M.r i (A i) j + M.β * policyValue M A P j) =
      M.β * ∑ j, P i (A i) j * (Vm j - policyValue M A P j) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 := sl_simplex_le (hP i (A i)) _ c hc'
  have h4 := mul_le_mul_of_nonneg_left h3 M.β_nonneg
  linarith

theorem sl_rmin_le_W (M : UncertainMDP S D) {P : Mat S D} (hP : IsStoch P)
    (A : (i : S) → D i) (i : S) : rmin M ≤ policyValue M A P i := by
  have := sl_geo M (fun i => rmin M - policyValue M A P i) ?_ i
  · try simp only at this
    linarith
  intro c hc' i
  try simp only at hc' ⊢
  have h2 := sl_pv_bell M A hP i
  have h3 : rmin M - M.β * c ≤
      ∑ j, P i (A i) j * (M.r i (A i) j + M.β * policyValue M A P j) := by
    apply sl_simplex_ge (hP i (A i))
    intro j
    have h1 := sl_rmin_le_r M i (A i) j
    have h2 : M.β * (rmin M - c) ≤ M.β * policyValue M A P j :=
      mul_le_mul_of_nonneg_left (by linarith [hc' j]) M.β_nonneg
    linarith
  linarith

theorem sl_cons_meas (M : UncertainMDP S D) : MeasurableSet (consistentSet M) := by
  have : consistentSet M = ⋂ i, ⋂ k, (fun P : Mat S D => P i k) ⁻¹' M.U i k := by
    ext P; simp [consistentSet]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
    (M.U_closed i k).measurableSet.preimage (by fun_prop)

theorem goal_core (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    (∃ V : S → ℝ, SolvesVplus M V) ∧ (∃ V : S → ℝ, SolvesVminus M V) ∧
    ∀ (f : S → Measure (Mat S D) → ℝ), SolvesEq10 M f → IsBoundedOnPriors f →
    ∀ (Vp Vm : S → ℝ), SolvesVplus M Vp → SolvesVminus M Vm →
    ∀ (g : Measure (Mat S D)), IsPrior g → ∀ i : S,
      alpha M g * Vm i + (1 - alpha M g) * rmin M ≤ f i g ∧
        f i g ≤ alpha M g * Vp i + (1 - alpha M g) * rmax M := by
  refine ⟨sl6_exists M, sl_Vp_exists M, sl_Vm_exists M, ?_⟩
  intro f hf hb Vp Vm hVp hVm g hg i
  haveI := hg.1
  have hcm := sl_cons_meas M
  have hind_int : Integrable ((consistentSet M).indicator (fun _ => (1:ℝ))) g :=
    (integrable_const (1:ℝ)).indicator hcm
  have hint : ∀ a b : ℝ,
      ∫ P, a + (b - a) * (consistentSet M).indicator (fun _ => (1:ℝ)) P ∂g =
        alpha M g * b + (1 - alpha M g) * a := by
    intro a b
    rw [integral_add (integrable_const _) (hind_int.const_mul _), integral_const,
      integral_const_mul, integral_indicator_const _ hcm]
    have hα : alpha M g = g.real (consistentSet M) := rfl
    simp only [probReal_univ, one_smul, smul_eq_mul, mul_one]
    rw [hα]; ring
  have hψ : ∀ a b : ℝ,
      Integrable (fun P => a + (b - a) * (consistentSet M).indicator (fun _ => (1:ℝ)) P) g :=
    fun a b => (integrable_const _).add (hind_int.const_mul _)
  constructor
  · choose A hA using fun i => Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k : D i => ⨅ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * Vm j))
    have hA' : ∀ i, Vm i =
        ⨅ p : M.U i (A i), ∑ j, (p : S → ℝ) j * (M.r i (A i) j + M.β * Vm j) :=
      fun i => (hVm i).trans (hA i).2
    obtain ⟨hWint, hWle⟩ := policy_core M f hf hb g hg A i
    rw [← hint]
    refine le_trans (integral_mono_ae (hψ _ _) hWint ?_) hWle
    filter_upwards [sl6_ae_stoch hg] with P hP
    by_cases hc : P ∈ consistentSet M
    · rw [Set.indicator_of_mem hc]
      have := sl_Vm_le_W M hP hc Vm A hA' i
      linarith
    · rw [Set.indicator_of_notMem hc]
      have := sl_rmin_le_W M hP A i
      linarith
  · obtain ⟨hVint, hVle⟩ := jensen_core M f hf hb g hg i
    rw [← hint]
    refine le_trans hVle (integral_mono_ae hVint (hψ _ _) ?_)
    filter_upwards [sl6_ae_stoch hg] with P hP
    by_cases hc : P ∈ consistentSet M
    · rw [Set.indicator_of_mem hc]
      have := sl_VP_le_Vp M f hf hP hc Vp hVp i
      linarith
    · rw [Set.indicator_of_notMem hc]
      have := sl_VP_le_rmax M f hf hP i
      linarith

end

end SatiaLave.Bayes

open SatiaLave.Bayes


theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    (∃ V : S → ℝ, SolvesVplus M V) ∧ (∃ V : S → ℝ, SolvesVminus M V) ∧
    ∀ (f : S → Measure (Mat S D) → ℝ), SolvesEq10 M f → IsBoundedOnPriors f →
    ∀ (Vp Vm : S → ℝ), SolvesVplus M Vp → SolvesVminus M Vm →
    ∀ (g : Measure (Mat S D)), IsPrior g → ∀ i : S,
      alpha M g * Vm i + (1 - alpha M g) * rmin M ≤ f i g ∧
        f i g ≤ alpha M g * Vp i + (1 - alpha M g) * rmax M := by
  exact goal_core M
