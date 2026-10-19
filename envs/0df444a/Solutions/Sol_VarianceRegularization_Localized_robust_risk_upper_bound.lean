-- Prove2me | solution 1 for VarianceRegularization.Localized.robust_risk_upper_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T13:54:06.770491+00:00
-- url     : https://prove2.me/submissions/89b1657c-e624-4070-a3da-695263e18d13

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory



namespace Cex853

/-- `ω₁` as a type: uncountable, every initial segment countable. -/
def Y : Type := (Cardinal.aleph.{0} 1).ord.ToType

noncomputable instance : LinearOrder Y :=
  inferInstanceAs (LinearOrder (Cardinal.aleph.{0} 1).ord.ToType)

set_option linter.deprecated false in
theorem Y_Iio_countable (y : Y) : (Set.Iio y).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one]
  exact Cardinal.mk_Iio_toType_ord_lt (c := Cardinal.aleph.{0} 1) y

theorem Y_not_countable : ¬ (Set.univ : Set Y).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, Cardinal.mk_univ]
  have : Cardinal.mk Y = Cardinal.aleph.{0} 1 := by
    show Cardinal.mk (Cardinal.aleph.{0} 1).ord.ToType = _
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  rw [this]
  exact lt_irrefl _

theorem Y_bound (S : Set Y) (hS : S.Countable) : ∃ z, ∀ y ∈ S, y < z := by
  have hU : (⋃ y ∈ S, Set.Iic y).Countable := by
    refine hS.biUnion fun y _ => ?_
    rw [← Set.Iio_union_right]
    exact (Y_Iio_countable y).union (Set.countable_singleton y)
  obtain ⟨z, hz⟩ : ∃ z, z ∉ ⋃ y ∈ S, Set.Iic y := by
    by_contra h
    push_neg at h
    exact Y_not_countable (hU.mono fun x _ => h x)
  refine ⟨z, fun y hy => ?_⟩
  by_contra hle
  exact hz (Set.mem_biUnion hy (not_lt.mp hle))

/-- The countable–cocountable σ-algebra. -/
instance : MeasurableSpace Y where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl Set.countable_empty
  measurableSet_compl s h := by
    rcases h with h | h
    · right; simpa using h
    · left; exact h
  measurableSet_iUnion f hf := by
    by_cases h : ∀ i, (f i).Countable
    · exact Or.inl (Set.countable_iUnion h)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      right
      refine ((hf i).resolve_left hi).mono ?_
      exact Set.compl_subset_compl.mpr (Set.subset_iUnion f i)

theorem Y_meas_iff (s : Set Y) : MeasurableSet s ↔ s.Countable ∨ sᶜ.Countable := Iff.rfl

theorem not_both (s t : Set Y) (hs : sᶜ.Countable) (ht : tᶜ.Countable) : ¬ Disjoint s t := by
  intro hd
  apply Y_not_countable
  refine (hs.union ht).mono ?_
  intro x _
  by_contra hx
  simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hx
  exact Set.disjoint_left.mp hd hx.1 hx.2

open Classical in
/-- The `0`–`1` measure: countable sets get `0`, cocountable sets get `1`. -/
noncomputable def muY : Measure Y :=
  Measure.ofMeasurable (fun s _ => if s.Countable then 0 else 1) (by simp)
    (by
      intro f hf hdisj
      by_cases h : ∀ i, (f i).Countable
      · rw [if_pos (Set.countable_iUnion h)]
        simp [h]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        have hU : ¬ (⋃ j, f j).Countable := fun hc => hi (hc.mono (Set.subset_iUnion f i))
        rw [if_neg hU]
        have hco : (f i)ᶜ.Countable := (hf i).resolve_left hi
        have hother : ∀ j, j ≠ i → (f j).Countable := by
          intro j hj
          exact hco.mono (fun x hx => Set.disjoint_left.mp (hdisj hj) hx)
        rw [tsum_eq_single i]
        · simp [hi]
        · intro j hj
          simp [hother j hj])

theorem muY_apply_countable (s : Set Y) (hs : s.Countable) : muY s = 0 := by
  have hm : MeasurableSet s := Or.inl hs
  rw [muY, Measure.ofMeasurable_apply s hm, if_pos hs]

instance : IsProbabilityMeasure muY := by
  constructor
  rw [muY, Measure.ofMeasurable_apply Set.univ MeasurableSet.univ, if_neg Y_not_countable]

abbrev X := Y × unitInterval

noncomputable def P : Measure X := muY.prod (volume : Measure unitInterval)

instance : IsProbabilityMeasure P := by unfold P; infer_instance

/-- Lexicographic initial segments. -/
def C (q : X) : Set X := {x | toLex x < toLex q}

theorem C_eq (q : X) : C q = (Set.Iio q.1 ×ˢ Set.univ) ∪ ({q.1} ×ˢ Set.Iio q.2) := by
  ext x
  simp only [C, Set.mem_setOf_eq, Prod.Lex.toLex_lt_toLex, Set.mem_union, Set.mem_prod,
    Set.mem_Iio, Set.mem_univ, and_true, Set.mem_singleton_iff]

theorem C_meas (q : X) : MeasurableSet (C q) := by
  rw [C_eq]
  have h1 : MeasurableSet (Set.Iio q.1) := Or.inl (Y_Iio_countable q.1)
  have h2 : MeasurableSet ({q.1} : Set Y) := Or.inl (Set.countable_singleton q.1)
  exact (h1.prod MeasurableSet.univ).union (h2.prod measurableSet_Iio)

theorem C_null (q : X) : P (C q) = 0 := by
  rw [C_eq]
  refine measure_union_null ?_ ?_
  · rw [P, Measure.prod_prod, muY_apply_countable _ (Y_Iio_countable q.1), zero_mul]
  · rw [P, Measure.prod_prod, muY_apply_countable _ (Set.countable_singleton q.1), zero_mul]

end Cex853




namespace Cex853R
open MeasureTheory

open UnderstandingML

theorem iSup_img {α γ : Type*} (g : α → γ) (A : Set α) (h : γ → ℝ) :
    (⨆ a : (g '' A), h a) = ⨆ w : A, h (g w) := by
  rw [← sSup_image', Set.image_image, sSup_image']

theorem rad_comp_perm {n : ℕ} (A : Set (Fin n → ℝ)) (τ : Equiv.Perm (Fin n)) :
    rademacher ((fun w => w ∘ τ) '' A) = rademacher A := by
  unfold rademacher
  have key : ∀ σ : Fin n → Bool,
      (⨆ a : ((fun w => w ∘ τ) '' A), ∑ i, signVec σ i * (a : Fin n → ℝ) i)
        = ⨆ w : A, ∑ i, signVec (σ ∘ τ.symm) i * (w : Fin n → ℝ) i := by
    intro σ
    refine (iSup_img (fun w : Fin n → ℝ => w ∘ τ) A
      (fun a => ∑ i, signVec σ i * a i)).trans ?_
    congr 1
    funext w
    rw [← Equiv.sum_comp τ (fun i => signVec (σ ∘ τ.symm) i * (w : Fin n → ℝ) i)]
    simp [signVec, Function.comp]
  simp_rw [key]
  rw [Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl Bool))
    (fun x => ⨆ w : A, ∑ i, signVec (x ∘ τ.symm) i * (w : Fin n → ℝ) i)
    (fun σ => ⨆ w : A, ∑ i, signVec σ i * (w : Fin n → ℝ) i) (fun σ => rfl)]

/-- Suffix indicators, scaled by `c ∈ [0,1]` with `c² ≤ r`. -/
def E1 (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ c ∈ Set.Icc (0:ℝ) 1, c ^ 2 ≤ r ∧ ∃ k : ℕ, v = fun j => c * if k ≤ j.val then 1 else 0}

/-- Suffix sums of signs. -/
noncomputable def T {n : ℕ} (k : ℕ) (σ : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, if k ≤ j.val then signVec σ j else 0

theorem T_n {n : ℕ} (σ : Fin n → Bool) : T n σ = 0 := by
  unfold T
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg (not_le.mpr j.isLt)]

theorem T_min {n : ℕ} (k : ℕ) (σ : Fin n → Bool) : T k σ = T (min k n) σ := by
  unfold T
  refine Finset.sum_congr rfl fun j _ => ?_
  have : k ≤ j.val ↔ min k n ≤ j.val := by
    constructor
    · intro h; exact le_trans (min_le_left _ _) h
    · intro h
      rcases min_choice k n with h' | h'
      · rw [h'] at h; exact h
      · rw [h'] at h; exact absurd j.isLt (not_lt.mpr h)
  simp only [this]

theorem iSup_E1_le {n : ℕ} (σ : Fin n → Bool) (r : ℝ) (hr : 0 ≤ r) (l : ℝ) (hl : 0 < l) :
    (⨆ w : E1 n r, ∑ j, signVec σ j * (w : Fin n → ℝ) j)
      ≤ Real.sqrt r * ((1 / l) * Real.log (∑ k ∈ Finset.range (n + 1), Real.exp (l * T k σ))) := by
  set Z := ∑ k ∈ Finset.range (n + 1), Real.exp (l * T k σ) with hZ
  have hTle : ∀ k ∈ Finset.range (n + 1), Real.exp (l * T k σ) ≤ Z := fun k hk =>
    Finset.single_le_sum (f := fun k => Real.exp (l * T k σ)) (fun k _ => (Real.exp_pos _).le) hk
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) (hTle 0 (by simp))
  have hL : ∀ k : ℕ, T k σ ≤ (1 / l) * Real.log Z := by
    intro k
    rw [T_min]
    have h1 := hTle (min k n) (Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _)))
    have h2 : l * T (min k n) σ ≤ Real.log Z := by
      rw [Real.le_log_iff_exp_le hZpos]; exact h1
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hl]
    linarith
  have hL0 : 0 ≤ (1 / l) * Real.log Z := by
    have := hL n
    rw [T_n] at this
    exact this
  have hne : Nonempty (E1 n r) :=
    ⟨⟨fun _ => 0, 0, ⟨le_refl _, zero_le_one⟩, by simpa using hr, 0, by simp⟩⟩
  refine ciSup_le fun w => ?_
  obtain ⟨_, c, hc, hcr, k, rfl⟩ := w
  have hsum : (∑ j, signVec σ j * (c * if k ≤ j.val then (1:ℝ) else 0)) = c * T k σ := by
    unfold T
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  simp only
  rw [hsum]
  have hcs : c ≤ Real.sqrt r := by
    have := Real.abs_le_sqrt hcr
    rwa [abs_of_nonneg hc.1] at this
  have h1 : c * T k σ ≤ c * ((1 / l) * Real.log Z) := mul_le_mul_of_nonneg_left (hL k) hc.1
  have h2 : c * ((1 / l) * Real.log Z) ≤ Real.sqrt r * ((1 / l) * Real.log Z) :=
    mul_le_mul_of_nonneg_right hcs hL0
  linarith

theorem sum_exp_T {n : ℕ} (k : ℕ) (l : ℝ) :
    ∑ σ : Fin n → Bool, Real.exp (l * T k σ) ≤ (2 * Real.exp (l ^ 2 / 2)) ^ n := by
  have hrw : ∀ σ : Fin n → Bool, Real.exp (l * T k σ)
      = ∏ j : Fin n, (fun (j : Fin n) (b : Bool) =>
          Real.exp (l * if k ≤ j.val then (if b then 1 else -1) else 0)) j (σ j) := by
    intro σ
    unfold T
    rw [Finset.mul_sum, Real.exp_sum]
    rfl
  simp_rw [hrw]
  rw [← Fintype.prod_sum (fun (j : Fin n) (b : Bool) =>
    Real.exp (l * if k ≤ j.val then (if b then 1 else -1) else 0))]
  calc ∏ j : Fin n, ∑ b : Bool, Real.exp (l * if k ≤ j.val then (if b then 1 else -1) else 0)
      ≤ ∏ _j : Fin n, (2 * Real.exp (l ^ 2 / 2)) := by
        refine Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun b _ => (Real.exp_pos _).le)
          fun j _ => ?_
        have hc := Real.cosh_le_exp_half_sq l
        rw [Real.cosh_eq] at hc
        have h1 : 1 ≤ Real.exp (l ^ 2 / 2) := Real.one_le_exp (by positivity)
        rw [Fintype.sum_bool]
        by_cases h : k ≤ j.val
        · simp [h] <;> linarith
        · simp [h] <;> linarith
    _ = (2 * Real.exp (l ^ 2 / 2)) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem rad_E1_le (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) (l : ℝ) (hl : 0 < l) :
    rademacher (E1 n r) ≤
      Real.sqrt r * ((1 / n) * ((1 / l) * (Real.log (n + 1) + n * (l ^ 2 / 2)))) := by
  unfold rademacher
  set A : ℝ := (n + 1) * Real.exp (l ^ 2 / 2) ^ n with hA
  have hApos : 0 < A := by positivity
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  set Z : (Fin n → Bool) → ℝ := fun σ => ∑ k ∈ Finset.range (n + 1), Real.exp (l * T k σ) with hZ
  have hZpos : ∀ σ, 0 < Z σ := fun σ =>
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨0, by simp⟩
  have havg : (1 / 2 ^ n) * ∑ σ, Z σ ≤ A := by
    rw [hZ]
    simp only
    rw [Finset.sum_comm]
    have : ∀ k ∈ Finset.range (n + 1),
        ∑ σ : Fin n → Bool, Real.exp (l * T k σ) ≤ 2 ^ n * Real.exp (l ^ 2 / 2) ^ n := by
      intro k _
      have := sum_exp_T (n := n) k l
      rwa [mul_pow] at this
    have hs := Finset.sum_le_sum this
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    rw [hA, one_div, inv_mul_le_iff₀ h2n]
    push_cast at hs ⊢
    nlinarith [hs]
  have htan : ∀ σ, Real.log (Z σ) ≤ Real.log A + Z σ / A - 1 := by
    intro σ
    have := Real.log_le_sub_one_of_pos (div_pos (hZpos σ) hApos)
    rw [Real.log_div (hZpos σ).ne' hApos.ne'] at this
    linarith
  have hlogsum : (1 / 2 ^ n) * ∑ σ : Fin n → Bool, Real.log (Z σ) ≤ Real.log A := by
    have h1 : ∑ σ : Fin n → Bool, Real.log (Z σ)
        ≤ ∑ σ : Fin n → Bool, (Real.log A - 1 + Z σ / A) :=
      Finset.sum_le_sum fun σ _ => by linarith [htan σ]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.sum_div] at h1
    have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
    rw [nsmul_eq_mul, hcard] at h1
    have h3 : (1 / 2 ^ n) * (∑ σ, Z σ) / A ≤ 1 := by
      rw [div_le_one hApos]; exact havg
    calc (1 / 2 ^ n) * ∑ σ : Fin n → Bool, Real.log (Z σ)
        ≤ (1 / 2 ^ n) * (2 ^ n * (Real.log A - 1) + (∑ σ, Z σ) / A) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Real.log A - 1) + (1 / 2 ^ n) * (∑ σ, Z σ) / A := by
          field_simp
      _ ≤ Real.log A := by linarith
  have hlogA : Real.log A = Real.log (n + 1) + n * (l ^ 2 / 2) := by
    rw [hA, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp]
  have hsup : ∀ σ : Fin n → Bool, (⨆ w : E1 n r, ∑ j, signVec σ j * (w : Fin n → ℝ) j)
      ≤ Real.sqrt r * ((1 / l) * Real.log (Z σ)) := fun σ => iSup_E1_le σ r hr l hl
  have hstep : (1 / 2 ^ n) * ∑ σ : Fin n → Bool, (⨆ w : E1 n r, ∑ j, signVec σ j * (w : Fin n → ℝ) j)
      ≤ Real.sqrt r * ((1 / l) * Real.log A) := by
    calc (1 / 2 ^ n) * ∑ σ : Fin n → Bool, (⨆ w : E1 n r, ∑ j, signVec σ j * (w : Fin n → ℝ) j)
        ≤ (1 / 2 ^ n) * ∑ σ : Fin n → Bool, Real.sqrt r * ((1 / l) * Real.log (Z σ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hsup σ) (by positivity)
      _ = Real.sqrt r * ((1 / l) * ((1 / 2 ^ n) * ∑ σ : Fin n → Bool, Real.log (Z σ))) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
      _ ≤ Real.sqrt r * ((1 / l) * Real.log A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogsum (by positivity))
            (Real.sqrt_nonneg _)
  rw [← hlogA]
  calc (1 / (n:ℝ)) * ((1 / 2 ^ n) * ∑ σ : Fin n → Bool,
        (⨆ w : E1 n r, ∑ j, signVec σ j * (w : Fin n → ℝ) j))
      ≤ (1 / n) * (Real.sqrt r * ((1 / l) * Real.log A)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = _ := by ring

theorem log_big_lt : Real.log 1048577 < 14 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : (2.7:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (1048577:ℝ) < 2.7 ^ 14 := by norm_num
    _ < Real.exp 1 ^ 14 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)

theorem rad_E1_big (r : ℝ) (hr : 0 ≤ r) : rademacher (E1 1048576 r) ≤ (1 / 100) * Real.sqrt r := by
  have h := rad_E1_le 1048576 (by norm_num) r hr (1 / 100) (by norm_num)
  have hl := log_big_lt
  push_cast at h
  have : Real.log (1048576 + 1) = Real.log 1048577 := by norm_num
  rw [this] at h
  have hB : (1 / (1048576:ℝ)) * ((1 / (1 / 100)) * (Real.log 1048577 + 1048576 * ((1 / 100) ^ 2 / 2)))
      ≤ 1 / 100 := by nlinarith
  calc rademacher (E1 1048576 r) ≤ _ := h
    _ ≤ Real.sqrt r * (1 / 100) := mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)
    _ = _ := by ring

end Cex853R

namespace Cex853

open UnderstandingML VarianceRegularization.Localized Cex853R

/-- The class: indicators of the complements of the lexicographic initial segments. -/
def G : Set (X → ℝ) := {f | ∃ q : X, f = (C q)ᶜ.indicator (fun _ => (1:ℝ))}

theorem G_meas : ∀ f ∈ G, Measurable f := by
  rintro f ⟨q, rfl⟩
  exact measurable_const.indicator (C_meas q).compl

theorem G_range : ∀ f ∈ G, ∀ x, f x ∈ Set.Icc (0:ℝ) 1 := by
  rintro f ⟨q, rfl⟩ x
  by_cases h : x ∈ (C q)ᶜ <;> simp [Set.indicator, h]

theorem ae_one (q : X) (c : ℝ) (p : ℕ) :
    (fun x => (c * (C q)ᶜ.indicator (fun _ => (1:ℝ)) x) ^ p) =ᵐ[P] fun _ => (c * 1) ^ p := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ (C_null q)
  intro x hx
  by_contra h
  apply hx
  have : x ∈ (C q)ᶜ := h
  simp [Set.indicator_of_mem this]

theorem int_sq (q : X) (c : ℝ) :
    ∫ x, (c * (C q)ᶜ.indicator (fun _ => (1:ℝ)) x) ^ 2 ∂P = c ^ 2 := by
  rw [integral_congr_ae (ae_one q c 2)]
  simp

theorem int_one (q : X) : ∫ x, (C q)ᶜ.indicator (fun _ => (1:ℝ)) x ∂P = 1 := by
  have h := ae_one q 1 1
  simp only [one_mul, pow_one] at h
  rw [integral_congr_ae h]
  simp

/-- Sorted order of an injective sample. -/
noncomputable def key {n : ℕ} (s : Fin n → X) : Fin n → Lex X := fun i => toLex (s i)

theorem trace {n : ℕ} (s : Fin n → X) (q : X) :
    ∃ k : ℕ, ∀ i, (s i ∈ C q ↔ ((Tuple.sort (key s)).symm i).val < k) := by
  classical
  set σ := Tuple.sort (key s) with hσ
  have hmono : Monotone (key s ∘ σ) := Tuple.monotone_sort _
  let p : ℕ → Prop := fun m => m = n ∨ ∃ h : m < n, toLex q ≤ key s (σ ⟨m, h⟩)
  have hex : ∃ m, p m := ⟨n, Or.inl rfl⟩
  refine ⟨Nat.find hex, fun i => ?_⟩
  have hi : s i = s (σ (σ.symm i)) := by simp
  rw [hi]
  set j := σ.symm i
  show key s (σ j) < toLex q ↔ j.val < Nat.find hex
  constructor
  · intro hlt
    by_contra hge
    push_neg at hge
    rcases Nat.find_spec hex with h | ⟨h, hq⟩
    · have := j.isLt; omega
    · have hle : (⟨Nat.find hex, h⟩ : Fin n) ≤ j := hge
      have := hmono hle
      exact absurd hlt (not_lt.mpr (le_trans hq this))
  · intro hlt
    have hmin := Nat.find_min hex hlt
    simp only [p, not_or, not_exists] at hmin
    exact lt_of_not_ge (hmin.2 j.isLt)

theorem exists_q {n : ℕ} (s : Fin n → X) (hinj : Function.Injective (key s)) (k : ℕ) :
    ∃ q : X, ∀ i, (s i ∈ C q ↔ ((Tuple.sort (key s)).symm i).val < k) := by
  set σ := Tuple.sort (key s) with hσ
  have hsm : StrictMono (key s ∘ σ) :=
    (Tuple.monotone_sort _).strictMono_of_injective (hinj.comp σ.injective)
  by_cases hk : k < n
  · refine ⟨s (σ ⟨k, hk⟩), fun i => ?_⟩
    have hi : s i = s (σ (σ.symm i)) := by simp
    rw [hi]
    set j := σ.symm i
    show key s (σ j) < key s (σ ⟨k, hk⟩) ↔ j.val < k
    rw [show key s (σ j) < key s (σ ⟨k, hk⟩) ↔ (key s ∘ σ) j < (key s ∘ σ) ⟨k, hk⟩ from Iff.rfl,
      hsm.lt_iff_lt]
    rfl
  · obtain ⟨z, hz⟩ := Y_bound (Set.range fun i => (s i).1) (Set.finite_range _).countable
    refine ⟨(z, 0), fun i => ?_⟩
    have h1 : s i ∈ C (z, 0) := by
      show toLex (s i) < toLex (z, (0 : unitInterval))
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (hz _ ⟨i, rfl⟩)
    have h2 : (σ.symm i).val < k := lt_of_lt_of_le (σ.symm i).isLt (not_lt.mp hk)
    exact ⟨fun _ => h2, fun _ => h1⟩

theorem loc_eq (r : ℝ) :
    localizedClass P G r = {g | ∃ q : X, ∃ c ∈ Set.Icc (0:ℝ) 1, c ^ 2 ≤ r ∧
      g = fun x => c * (C q)ᶜ.indicator (fun _ => (1:ℝ)) x} := by
  ext g
  constructor
  · rintro ⟨f, ⟨q, rfl⟩, c, hc, rfl, hint⟩
    rw [int_sq] at hint
    exact ⟨q, c, hc, hint, rfl⟩
  · rintro ⟨q, c, hc, hcr, rfl⟩
    refine ⟨_, ⟨q, rfl⟩, c, hc, rfl, ?_⟩
    rw [int_sq]
    exact hcr

theorem compl_iff {n : ℕ} (s : Fin n → X) (q : X) (k : ℕ)
    (hk : ∀ i, (s i ∈ C q ↔ ((Tuple.sort (key s)).symm i).val < k)) (c : ℝ) (i : Fin n) :
    c * (C q)ᶜ.indicator (fun _ => (1:ℝ)) (s i)
      = c * if k ≤ ((Tuple.sort (key s)).symm i).val then 1 else 0 := by
  by_cases h : s i ∈ C q
  · have h' : s i ∉ (C q)ᶜ := fun h2 => h2 h
    rw [Set.indicator_of_notMem h', if_neg (not_le.mpr ((hk i).mp h))]
  · have h' : s i ∈ (C q)ᶜ := h
    rw [Set.indicator_of_mem h', if_pos (not_lt.mp (fun h2 => h ((hk i).mpr h2)))]

theorem evalSet_eq {n : ℕ} (r : ℝ) (s : Fin n → X)
    (hinj : Function.Injective (key s)) :
    evalSet (localizedClass P G r) s = (fun w => w ∘ (Tuple.sort (key s)).symm) '' E1 n r := by
  rw [loc_eq r]
  ext v
  constructor
  · rintro ⟨g, ⟨q, c, hc, hcr, rfl⟩, rfl⟩
    obtain ⟨k, hk⟩ := trace s q
    refine ⟨fun j => c * if k ≤ j.val then 1 else 0, ⟨c, hc, hcr, k, rfl⟩, ?_⟩
    funext i
    simp only [Function.comp]
    exact (compl_iff s q k hk c i).symm
  · rintro ⟨w, ⟨c, hc, hcr, k, rfl⟩, rfl⟩
    obtain ⟨q, hq⟩ := exists_q s hinj k
    refine ⟨fun x => c * (C q)ᶜ.indicator (fun _ => (1:ℝ)) x, ⟨q, c, hc, hcr, rfl⟩, ?_⟩
    funext i
    simp only [Function.comp]
    exact (compl_iff s q k hq c i).symm

theorem rad_const {n : ℕ} (r : ℝ) (s : Fin n → X)
    (hinj : Function.Injective fun i => (s i).2) :
    empRademacher (localizedClass P G r) s = rademacher (E1 n r) := by
  have hk : Function.Injective (key s) := by
    intro i j hij
    apply hinj
    have : s i = s j := toLex.injective hij
    simp [this]
  unfold empRademacher
  rw [evalSet_eq r s hk, rad_comp_perm]

theorem diag_null : ((volume : Measure unitInterval).prod volume) {p | p.1 = p.2} = 0 := by
  have hD : MeasurableSet {p : unitInterval × unitInterval | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  rw [Measure.prod_apply hD]
  have : ∀ x : unitInterval, (volume : Measure unitInterval) (Prod.mk x ⁻¹' {p | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : unitInterval × unitInterval | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [this, measure_singleton]
  simp [this]

theorem ties_null (n : ℕ) :
    (Measure.pi fun _ : Fin n => P) {s | ¬ Function.Injective fun i => (s i).2} = 0 := by
  set μ := Measure.pi fun _ : Fin n => P with hμ
  have hsub : {s : Fin n → X | ¬ Function.Injective fun i => (s i).2}
      ⊆ ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {s : Fin n → X | (s i).2 = (s j).2} := by
    intro s hs
    simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, hne, hij⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  have hind : iIndepFun (fun k (s : Fin n → X) => (s k).2) μ :=
    iIndepFun_pi (X := fun _ (x : X) => x.2) (fun _ => measurable_snd.aemeasurable)
  have hpair := (hind.indepFun hij).map_prod_eq_prod_map_map
    ((measurable_pi_apply i).snd.aemeasurable) ((measurable_pi_apply j).snd.aemeasurable)
  have hmarg : ∀ k : Fin n, μ.map (fun s : Fin n → X => (s k).2) = volume := by
    intro k
    have : (fun s : Fin n → X => (s k).2) = Prod.snd ∘ (fun s : Fin n → X => s k) := rfl
    rw [this, ← Measure.map_map measurable_snd (measurable_pi_apply k),
      (measurePreserving_eval (fun _ : Fin n => P) k).map_eq, P, Measure.map_snd_prod,
      measure_univ, one_smul]
  rw [hmarg i, hmarg j] at hpair
  have hφ : Measurable fun s : Fin n → X => ((s i).2, (s j).2) :=
    (measurable_pi_apply i).snd.prodMk (measurable_pi_apply j).snd
  have hD : MeasurableSet {p : unitInterval × unitInterval | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have : {s : Fin n → X | (s i).2 = (s j).2}
      = (fun s : Fin n → X => ((s i).2, (s j).2)) ⁻¹' {p | p.1 = p.2} := rfl
  rw [this, ← Measure.map_apply hφ hD, hpair]
  exact diag_null

/-- The sub-root function `r ↦ √r / 100`. -/
noncomputable def psi : ℝ → ℝ := fun r => (1 / 100) * Real.sqrt r

theorem subroot : IsSubRoot psi := by
  refine ⟨fun r _ => by unfold psi; positivity, fun a _ b _ hab => ?_, ?_⟩
  · unfold psi
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) (by norm_num)
  · intro a ha b hb hab
    have ha' : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    have hb' : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    simp only [psi]
    rw [mul_div_assoc, mul_div_assoc, div_self ha'.ne', div_self hb'.ne']

theorem loc : LocalizationBound P 1048576 G psi := by
  intro r hr
  have hae : (fun s : Fin 1048576 → X => empRademacher (localizedClass P G r) s)
      =ᵐ[Measure.pi fun _ : Fin 1048576 => P] fun _ => rademacher (E1 1048576 r) := by
    have : ∀ᵐ s ∂(Measure.pi fun _ : Fin 1048576 => P), Function.Injective fun i => (s i).2 :=
      ae_iff.mpr (ties_null 1048576)
    filter_upwards [this] with s hs
    exact rad_const r s hs
  refine ⟨(integrable_const _).congr hae.symm, ?_⟩
  unfold expRademacher
  rw [integral_congr_ae hae]
  simp only [integral_const, probReal_univ, one_smul]
  exact rad_E1_big r hr

theorem fix : psi (1 / 10000) ≤ 1 / 10000 := by
  unfold psi
  rw [show (1 / 10000 : ℝ) = (1 / 100) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem robustRisk_zero {n : ℕ} (ρ : ℝ) (s : Fin n → X) (f : X → ℝ) (hf : ∀ i, f (s i) = 0) :
    robustRisk ρ s f = 0 := by
  unfold robustRisk VarianceRegularization.Expansion.robustSup
  simp only [hf, mul_zero, Finset.sum_const_zero]
  rcases (VarianceRegularization.Expansion.chiSqBall n ρ).eq_empty_or_nonempty with h | h
  · rw [h, Set.image_empty, Real.sSup_empty]
  · rw [h.image_const, csSup_singleton]

theorem event (s : Fin 1048576 → X) (a b : ℝ) (hb : b < 1) :
    ∃ f ∈ G, a * robustRisk (131072 / 5) s f + b < ∫ x, f x ∂P := by
  obtain ⟨z, hz⟩ := Y_bound (Set.range fun i => (s i).1) (Set.finite_range _).countable
  refine ⟨(C (z, 0))ᶜ.indicator (fun _ => (1:ℝ)), ⟨(z, 0), rfl⟩, ?_⟩
  have hmem : ∀ i, s i ∈ C (z, 0) := by
    intro i
    show toLex (s i) < toLex (z, (0 : unitInterval))
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (hz _ ⟨i, rfl⟩)
  have h0 : ∀ i, (C (z, 0))ᶜ.indicator (fun _ => (1:ℝ)) (s i) = 0 := fun i =>
    Set.indicator_of_notMem (fun h => absurd (hmem i) h) _
  rw [robustRisk_zero _ s _ h0, int_one, mul_zero, zero_add]
  exact hb

theorem numeric_hyp :
    8 * (45 * 1 / ((1048576 : ℕ) : ℝ) * (1 + Real.log (⌈Real.log (((1048576 : ℕ) : ℝ) / 1)⌉ : ℝ))
      + 18 * (1 / 10000)) ≤ (131072 / 5 : ℝ) / ((1048576 : ℕ) : ℝ) := by
  have hl : Real.log (((1048576 : ℕ) : ℝ) / 1) < 14 := by
    have : (((1048576 : ℕ) : ℝ) / 1) = 1048576 := by norm_num
    rw [this]
    calc Real.log 1048576 < Real.log 1048577 := Real.log_lt_log (by norm_num) (by norm_num)
      _ < 14 := log_big_lt
  have hpos : 0 < Real.log (((1048576 : ℕ) : ℝ) / 1) := Real.log_pos (by norm_num)
  have hc1 : (⌈Real.log (((1048576 : ℕ) : ℝ) / 1)⌉ : ℝ) ≤ 14 := by
    have : ⌈Real.log (((1048576 : ℕ) : ℝ) / 1)⌉ ≤ 14 := Int.ceil_le.mpr (by exact_mod_cast hl.le)
    exact_mod_cast this
  have hc0 : 0 < (⌈Real.log (((1048576 : ℕ) : ℝ) / 1)⌉ : ℝ) :=
    lt_of_lt_of_le hpos (Int.le_ceil _)
  have hlog := Real.log_le_sub_one_of_pos hc0
  have : ((1048576 : ℕ) : ℝ) = 1048576 := by norm_num
  rw [this]
  nlinarith

theorem numeric_concl :
    (13 + 4 * Real.sqrt (2 * (131072 / 5 : ℝ) / ((1048576 : ℕ) : ℝ)))
      * (1 * (131072 / 5 : ℝ) / ((1048576 : ℕ) : ℝ)) < 1 := by
  have : ((1048576 : ℕ) : ℝ) = 1048576 := by norm_num
  rw [this]
  have hs : Real.sqrt (2 * (131072 / 5 : ℝ) / 1048576) ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  have hs0 := Real.sqrt_nonneg (2 * (131072 / 5 : ℝ) / 1048576)
  nlinarith

theorem two_exp_lt : ENNReal.ofReal (2 * Real.exp (-1)) < 1 := by
  rw [ENNReal.ofReal_lt_one, Real.exp_neg]
  have h := Real.exp_one_gt_d9
  have hp : 0 < Real.exp 1 := Real.exp_pos 1
  rw [← div_eq_mul_inv, div_lt_one hp]
  linarith

end Cex853

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (M t ρ rstar : ℝ)
    (ψ : ℝ → ℝ) (hM : 1 ≤ M) (ht : 0 < t) (htn : t < n)
    (hmeas : ∀ f ∈ F, Measurable f) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc 0 M)
    (hψ : IsSubRoot ψ) (hloc : LocalizationBound P n F ψ)
    (hrstar : 0 < rstar) (hfix : ψ rstar ≤ rstar)
    (hρ : 8 * (45 * M / n * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ)) + 18 * rstar) ≤ ρ / n),
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, (1 + 2 * Real.sqrt (2 * ρ / n)) * robustRisk ρ s f
            + (13 + 4 * Real.sqrt (2 * ρ / n)) * (M * ρ / n) < ∫ x, f x ∂P}
        ≤ ENNReal.ofReal (2 * Real.exp (-t))) := by
  intro h
  have h2 := h (X := Cex853.X) Cex853.P 1048576 (by norm_num) Cex853.G 1 1 (131072 / 5) (1 / 10000)
    Cex853.psi (le_refl _) (by norm_num) (by norm_num) Cex853.G_meas Cex853.G_range Cex853.subroot
    Cex853.loc (by norm_num) Cex853.fix Cex853.numeric_hyp
  have h3 : (Measure.pi fun _ : Fin 1048576 => Cex853.P) Set.univ
      ≤ ENNReal.ofReal (2 * Real.exp (-1)) := by
    refine le_trans (measure_mono ?_) h2
    intro s _
    exact Cex853.event s _ _ Cex853.numeric_concl
  rw [measure_univ] at h3
  exact absurd h3 (not_le.mpr Cex853.two_exp_lt)
