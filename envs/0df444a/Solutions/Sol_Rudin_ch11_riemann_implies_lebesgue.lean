-- Prove2me | solution 1 for Rudin.ch11_riemann_implies_lebesgue
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T05:01:41.412548+00:00
-- url     : https://prove2.me/submissions/179a0c56-bea2-4ca8-a594-8d6ccefd89b3

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Rudin

/-!
# Riemann implies Lebesgue (Rudin 11.33(a))

Mathlib has no Riemann integral; Rudin's Darboux definition is bridged here to the Lebesgue
integral, in a private namespace, by sandwiching the integrand between the step functions of
near-optimal partitions.
-/

namespace RiemLeb


variable {a b : ℝ} {f : ℝ → ℝ}

theorem pmono (P : Partition a b) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j
  induction j with
  | zero =>
      intro hij _
      have : i = 0 := Nat.le_zero.1 hij
      subst this; exact le_rfl
  | succ kk ih =>
      intro hij hj
      rcases Nat.lt_or_ge i (kk + 1) with h | h
      · exact le_trans (ih (by omega) (by omega)) (P.mono kk (by omega))
      · have hik : i = kk + 1 := by omega
        subst hik; exact le_rfl

theorem pmem (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · have h := pmono P (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := pmono P hi (le_refl P.n)
    rwa [P.last] at h

theorem psum (P : Partition a b) : ∑ i ∈ Finset.range P.n, (P.x (i + 1) - P.x i) = b - a := by
  rw [Finset.sum_range_sub (fun i => P.x i), P.first, P.last]

/-! ## Bounds on the suprema and infima over subintervals -/

section Bounds

variable {K : ℝ} (hK : ∀ x ∈ Set.Icc a b, |f x| ≤ K)

include hK

theorem bddAbove_image {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b) :
    BddAbove (f '' Set.Icc u v) := by
  refine ⟨K, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact (abs_le.1 (hK t (hsub ht))).2

theorem bddBelow_image {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b) :
    BddBelow (f '' Set.Icc u v) := by
  refine ⟨-K, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact (abs_le.1 (hK t (hsub ht))).1

omit hK in
theorem nonempty_image {u v : ℝ} (huv : u ≤ v) : (f '' Set.Icc u v).Nonempty :=
  ⟨f u, u, ⟨le_rfl, huv⟩, rfl⟩

theorem le_sSup_image {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b)
    {t : ℝ} (ht : t ∈ Set.Icc u v) : f t ≤ sSup (f '' Set.Icc u v) :=
  le_csSup (bddAbove_image hK huv hsub) ⟨t, ht, rfl⟩

theorem sInf_image_le {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b)
    {t : ℝ} (ht : t ∈ Set.Icc u v) : sInf (f '' Set.Icc u v) ≤ f t :=
  csInf_le (bddBelow_image hK huv hsub) ⟨t, ht, rfl⟩

theorem sSup_image_le_K {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b) :
    sSup (f '' Set.Icc u v) ≤ K := by
  refine csSup_le (nonempty_image (f := f) huv) ?_
  rintro y ⟨t, ht, rfl⟩
  exact (abs_le.1 (hK t (hsub ht))).2

theorem neg_K_le_sInf {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b) :
    -K ≤ sInf (f '' Set.Icc u v) := by
  refine le_csInf (nonempty_image (f := f) huv) ?_
  rintro y ⟨t, ht, rfl⟩
  exact (abs_le.1 (hK t (hsub ht))).1

theorem neg_K_le_sSup {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b) :
    -K ≤ sSup (f '' Set.Icc u v) :=
  le_trans (neg_K_le_sInf hK huv hsub)
    (le_trans (sInf_image_le hK huv hsub ⟨le_rfl, huv⟩) (le_sSup_image hK huv hsub ⟨le_rfl, huv⟩))

theorem sInf_le_K {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ Set.Icc a b) :
    sInf (f '' Set.Icc u v) ≤ K :=
  le_trans (sInf_image_le hK huv hsub ⟨le_rfl, huv⟩)
    ((abs_le.1 (hK u (hsub ⟨le_rfl, huv⟩))).2)

end Bounds

/-! ## Step functions attached to a partition -/

section Step

variable (f)

/-- The upper step function of a partition. -/
noncomputable def upStep (P : Partition a b) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    Set.indicator (Set.Ioc (P.x i) (P.x (i + 1)))
      (fun _ => sSup (f '' Set.Icc (P.x i) (P.x (i + 1)))) t

/-- The lower step function of a partition. -/
noncomputable def loStep (P : Partition a b) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    Set.indicator (Set.Ioc (P.x i) (P.x (i + 1)))
      (fun _ => sInf (f '' Set.Icc (P.x i) (P.x (i + 1)))) t

variable {f}

theorem measurable_upStep (P : Partition a b) : Measurable (upStep f P) := by
  refine Finset.measurable_sum _ fun i _ => ?_
  exact measurable_const.indicator measurableSet_Ioc

theorem measurable_loStep (P : Partition a b) : Measurable (loStep f P) := by
  refine Finset.measurable_sum _ fun i _ => ?_
  exact measurable_const.indicator measurableSet_Ioc

/-- The subintervals of a partition are pairwise disjoint. -/
theorem notMem_of_ne (P : Partition a b) {i j : ℕ} (hi : i < P.n) (hj : j < P.n) (hij : j ≠ i)
    {t : ℝ} (ht : t ∈ Set.Ioc (P.x i) (P.x (i + 1))) :
    t ∉ Set.Ioc (P.x j) (P.x (j + 1)) := by
  rintro ⟨h1, h2⟩
  rcases lt_or_gt_of_ne hij with h | h
  · have : P.x (j + 1) ≤ P.x i := pmono P (by omega) (by omega)
    linarith [ht.1]
  · have : P.x (i + 1) ≤ P.x j := pmono P (by omega) (by omega)
    linarith [ht.2]

theorem upStep_apply (P : Partition a b) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Set.Ioc (P.x i) (P.x (i + 1))) :
    upStep f P t = sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) := by
  rw [upStep, Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem ht]
  · intro j hj hji
    exact Set.indicator_of_notMem (notMem_of_ne P hi (Finset.mem_range.1 hj) hji ht) _
  · intro hmem
    exact absurd (Finset.mem_range.2 hi) hmem

theorem loStep_apply (P : Partition a b) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Set.Ioc (P.x i) (P.x (i + 1))) :
    loStep f P t = sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) := by
  rw [loStep, Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem ht]
  · intro j hj hji
    exact Set.indicator_of_notMem (notMem_of_ne P hi (Finset.mem_range.1 hj) hji ht) _
  · intro hmem
    exact absurd (Finset.mem_range.2 hi) hmem

/-- Every point of `(a, b]` lies in one of the subintervals of a partition. -/
theorem exists_index (P : Partition a b) {t : ℝ} (ht : t ∈ Set.Ioc a b) :
    ∃ i < P.n, t ∈ Set.Ioc (P.x i) (P.x (i + 1)) := by
  classical
  have hex : ∃ i, t ≤ P.x i := ⟨P.n, by rw [P.last]; exact ht.2⟩
  set i := Nat.find hex with hi
  have hfi : t ≤ P.x i := Nat.find_spec hex
  have hipos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exfalso
      rw [h, P.first] at hfi
      linarith [ht.1]
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hnotk : ¬ t ≤ P.x k := Nat.find_min hex (by omega)
  have hile : i ≤ P.n := Nat.find_le (by rw [P.last]; exact ht.2)
  have hkn : k < P.n := by omega
  exact ⟨k, hkn, ⟨by linarith [not_le.1 hnotk], by rw [← hk]; exact hfi⟩⟩

theorem sub_Icc (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    Set.Icc (P.x i) (P.x (i + 1)) ⊆ Set.Icc a b :=
  Set.Icc_subset_Icc (pmem P (by omega)).1 (pmem P (by omega)).2

theorem sub_Ioc (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    Set.Ioc (P.x i) (P.x (i + 1)) ⊆ Set.Ioc a b :=
  Set.Ioc_subset_Ioc (pmem P (by omega)).1 (pmem P (by omega)).2

theorem integral_step (P : Partition a b) (c : ℕ → ℝ) :
    (∫ t in Set.Ioc a b, ∑ i ∈ Finset.range P.n,
        Set.indicator (Set.Ioc (P.x i) (P.x (i + 1))) (fun _ => c i) t)
      = ∑ i ∈ Finset.range P.n, c i * (P.x (i + 1) - P.x i) := by
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i < P.n := Finset.mem_range.1 hi
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    rw [Set.inter_eq_self_of_subset_right (sub_Ioc P hin)]
    rw [MeasureTheory.setIntegral_const]
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [P.mono i hin])]
    rw [smul_eq_mul]
    ring
  · intro i hi
    refine (MeasureTheory.integrableOn_const ?_).indicator measurableSet_Ioc
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top

end Step

/-! ## The sandwich -/

section Sandwich

variable {K : ℝ} (hK : ∀ x ∈ Set.Icc a b, |f x| ≤ K)

include hK

theorem K_nonneg (hab : a ≤ b) : 0 ≤ K := le_trans (abs_nonneg _) (hK a ⟨le_rfl, hab⟩)

theorem upStep_ge (P : Partition a b) {t : ℝ} (ht : t ∈ Set.Ioc a b) : f t ≤ upStep f P t := by
  obtain ⟨i, hi, hti⟩ := exists_index P ht
  rw [upStep_apply P hi hti]
  exact le_sSup_image hK (P.mono i hi) (sub_Icc P hi) ⟨le_of_lt hti.1, hti.2⟩

theorem loStep_le (P : Partition a b) {t : ℝ} (ht : t ∈ Set.Ioc a b) : loStep f P t ≤ f t := by
  obtain ⟨i, hi, hti⟩ := exists_index P ht
  rw [loStep_apply P hi hti]
  exact sInf_image_le hK (P.mono i hi) (sub_Icc P hi) ⟨le_of_lt hti.1, hti.2⟩

theorem abs_upStep_le (hab : a ≤ b) (P : Partition a b) (t : ℝ) : |upStep f P t| ≤ K := by
  by_cases h : ∃ i, i < P.n ∧ t ∈ Set.Ioc (P.x i) (P.x (i + 1))
  · obtain ⟨i, hi, hti⟩ := h
    rw [upStep_apply P hi hti, abs_le]
    exact ⟨neg_K_le_sSup hK (P.mono i hi) (sub_Icc P hi),
      sSup_image_le_K hK (P.mono i hi) (sub_Icc P hi)⟩
  · push Not at h
    have hz : upStep f P t = 0 := by
      rw [upStep]
      exact Finset.sum_eq_zero fun i hi =>
        Set.indicator_of_notMem (h i (Finset.mem_range.1 hi)) _
    rw [hz, abs_zero]
    exact K_nonneg hK hab

theorem abs_loStep_le (hab : a ≤ b) (P : Partition a b) (t : ℝ) : |loStep f P t| ≤ K := by
  by_cases h : ∃ i, i < P.n ∧ t ∈ Set.Ioc (P.x i) (P.x (i + 1))
  · obtain ⟨i, hi, hti⟩ := h
    rw [loStep_apply P hi hti, abs_le]
    exact ⟨neg_K_le_sInf hK (P.mono i hi) (sub_Icc P hi),
      sInf_le_K hK (P.mono i hi) (sub_Icc P hi)⟩
  · push Not at h
    have hz : loStep f P t = 0 := by
      rw [loStep]
      exact Finset.sum_eq_zero fun i hi =>
        Set.indicator_of_notMem (h i (Finset.mem_range.1 hi)) _
    rw [hz, abs_zero]
    exact K_nonneg hK hab

omit hK in
theorem integral_upStep (P : Partition a b) :
    (∫ t in Set.Ioc a b, upStep f P t) = upperSum f id P :=
  integral_step P (fun i => sSup (f '' Set.Icc (P.x i) (P.x (i + 1))))

omit hK in
theorem integral_loStep (P : Partition a b) :
    (∫ t in Set.Ioc a b, loStep f P t) = lowerSum f id P :=
  integral_step P (fun i => sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))

omit hK in
theorem integrableOn_of_bdd {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ t, |g t| ≤ C) :
    IntegrableOn g (Set.Ioc a b) volume := by
  refine Measure.integrableOn_of_bounded (M := C) ?_ hg.aestronglyMeasurable ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · filter_upwards with t
    simpa [Real.norm_eq_abs] using hC t

/-- The trivial one-interval partition. -/
def triv (a b : ℝ) (hab : a ≤ b) : Partition a b where
  n := 1
  x := fun i => if i = 0 then a else b
  first := by simp
  last := by norm_num
  mono := by
    intro i hi
    interval_cases i
    simpa using hab

theorem upperSum_ge (hab : a ≤ b) (P : Partition a b) :
    -K * (b - a) ≤ upperSum f id P := by
  have h : ∀ i ∈ Finset.range P.n,
      -K * (P.x (i + 1) - P.x i)
        ≤ sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) * (id (P.x (i + 1)) - id (P.x i)) := by
    intro i hi
    have hin : i < P.n := Finset.mem_range.1 hi
    have hd : 0 ≤ P.x (i + 1) - P.x i := by linarith [P.mono i hin]
    have hc := neg_K_le_sSup hK (P.mono i hin) (sub_Icc P hin)
    simp only [id]
    nlinarith
  have := Finset.sum_le_sum h
  rw [upperSum]
  calc -K * (b - a) = ∑ i ∈ Finset.range P.n, -K * (P.x (i + 1) - P.x i) := by
        rw [← Finset.mul_sum, psum P]
    _ ≤ _ := this

theorem lowerSum_le (hab : a ≤ b) (P : Partition a b) :
    lowerSum f id P ≤ K * (b - a) := by
  have h : ∀ i ∈ Finset.range P.n,
      sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) * (id (P.x (i + 1)) - id (P.x i))
        ≤ K * (P.x (i + 1) - P.x i) := by
    intro i hi
    have hin : i < P.n := Finset.mem_range.1 hi
    have hd : 0 ≤ P.x (i + 1) - P.x i := by linarith [P.mono i hin]
    have hc := sInf_le_K hK (P.mono i hin) (sub_Icc P hin)
    simp only [id]
    nlinarith
  have := Finset.sum_le_sum h
  rw [lowerSum]
  calc lowerSum f id P ≤ ∑ i ∈ Finset.range P.n, K * (P.x (i + 1) - P.x i) := this
    _ = K * (b - a) := by rw [← Finset.mul_sum, psum P]

end Sandwich

/-! ## The theorem -/

theorem riemann_implies_lebesgue {K : ℝ} (hab : a ≤ b) (hf : RiemannIntegrable a b f)
    (hK : ∀ x ∈ Set.Icc a b, |f x| ≤ K) :
    IntegrableOn f (Set.Icc a b) volume ∧
      (∫ x in a..b, f x) = RiemannIntegral a b f := by
  classical
  set I : ℝ := upperIntegral a b f id with hI
  have hSUne : {y : ℝ | ∃ P : Partition a b, y = upperSum f id P}.Nonempty :=
    ⟨_, triv a b hab, rfl⟩
  have hSLne : {y : ℝ | ∃ P : Partition a b, y = lowerSum f id P}.Nonempty :=
    ⟨_, triv a b hab, rfl⟩
  have hup : ∀ k : ℕ, ∃ P : Partition a b, upperSum f id P < I + 1 / (k + 1) := by
    intro k
    obtain ⟨y, hy, hlt⟩ := Real.lt_sInf_add_pos hSUne (ε := 1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, hlt⟩
  have hlo : ∀ k : ℕ, ∃ Q : Partition a b, I - 1 / (k + 1) < lowerSum f id Q := by
    intro k
    obtain ⟨y, hy, hlt⟩ :=
      Real.add_neg_lt_sSup hSLne (ε := -(1 / ((k : ℝ) + 1))) (by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith)
    obtain ⟨Q, rfl⟩ := hy
    refine ⟨Q, ?_⟩
    have hIL : I = sSup {y : ℝ | ∃ P : Partition a b, y = lowerSum f id P} := by
      rw [hI]; exact hf
    rw [hIL]
    linarith
  choose P hP using hup
  choose Q hQ using hlo
  set U : ℝ → ℝ := fun t => ⨅ k : ℕ, upStep f (P k) t with hU
  set L : ℝ → ℝ := fun t => ⨆ k : ℕ, loStep f (Q k) t with hL
  have hbddU : ∀ t : ℝ, BddBelow (Set.range fun k : ℕ => upStep f (P k) t) := by
    intro t
    refine ⟨-K, ?_⟩
    rintro y ⟨k, rfl⟩
    exact (abs_le.1 (abs_upStep_le hK hab (P k) t)).1
  have hbddL : ∀ t : ℝ, BddAbove (Set.range fun k : ℕ => loStep f (Q k) t) := by
    intro t
    refine ⟨K, ?_⟩
    rintro y ⟨k, rfl⟩
    exact (abs_le.1 (abs_loStep_le hK hab (Q k) t)).2
  have hUle : ∀ (k : ℕ) (t : ℝ), U t ≤ upStep f (P k) t :=
    fun k t => ciInf_le (hbddU t) k
  have hLge : ∀ (k : ℕ) (t : ℝ), loStep f (Q k) t ≤ L t :=
    fun k t => le_ciSup (hbddL t) k
  have habsU : ∀ t : ℝ, |U t| ≤ K := by
    intro t
    rw [abs_le]
    constructor
    · exact le_ciInf fun k => (abs_le.1 (abs_upStep_le hK hab (P k) t)).1
    · exact le_trans (hUle 0 t) (abs_le.1 (abs_upStep_le hK hab (P 0) t)).2
  have habsL : ∀ t : ℝ, |L t| ≤ K := by
    intro t
    rw [abs_le]
    constructor
    · exact le_trans (abs_le.1 (abs_loStep_le hK hab (Q 0) t)).1 (hLge 0 t)
    · exact ciSup_le fun k => (abs_le.1 (abs_loStep_le hK hab (Q k) t)).2
  have hmU : Measurable U := Measurable.iInf fun k => measurable_upStep (P k)
  have hmL : Measurable L := Measurable.iSup fun k => measurable_loStep (Q k)
  have hiU : IntegrableOn U (Set.Ioc a b) volume := integrableOn_of_bdd hmU K habsU
  have hiL : IntegrableOn L (Set.Ioc a b) volume := integrableOn_of_bdd hmL K habsL
  have hiStepU : ∀ k, IntegrableOn (upStep f (P k)) (Set.Ioc a b) volume :=
    fun k => integrableOn_of_bdd (measurable_upStep (P k)) K (abs_upStep_le hK hab (P k))
  have hiStepL : ∀ k, IntegrableOn (loStep f (Q k)) (Set.Ioc a b) volume :=
    fun k => integrableOn_of_bdd (measurable_loStep (Q k)) K (abs_loStep_le hK hab (Q k))
  -- the integral of `U` is at most `I`
  have hintU : (∫ t in Set.Ioc a b, U t) ≤ I := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have h1 : (∫ t in Set.Ioc a b, U t) ≤ ∫ t in Set.Ioc a b, upStep f (P k) t :=
      MeasureTheory.integral_mono hiU (hiStepU k) (fun t => hUle k t)
    rw [integral_upStep (P k)] at h1
    linarith [hP k]
  have hintL : I ≤ ∫ t in Set.Ioc a b, L t := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have h1 : (∫ t in Set.Ioc a b, loStep f (Q k) t) ≤ ∫ t in Set.Ioc a b, L t :=
      MeasureTheory.integral_mono (hiStepL k) hiL (fun t => hLge k t)
    rw [integral_loStep (Q k)] at h1
    linarith [hQ k]
  -- the sandwich on `(a, b]`
  have hfU : ∀ t ∈ Set.Ioc a b, f t ≤ U t := fun t ht =>
    le_ciInf fun k => upStep_ge hK (P k) ht
  have hfL : ∀ t ∈ Set.Ioc a b, L t ≤ f t := fun t ht =>
    ciSup_le fun k => loStep_le hK (Q k) ht
  have hLUae : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), 0 ≤ (U - L) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h1 := hfU t ht
    have h2 := hfL t ht
    simp only [Pi.sub_apply]
    linarith
  have hintLU : (∫ t in Set.Ioc a b, L t) ≤ ∫ t in Set.Ioc a b, U t :=
    MeasureTheory.integral_mono_ae hiL hiU (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      linarith [hfU t ht, hfL t ht])
  have heqUL : (∫ t in Set.Ioc a b, (U - L) t) = 0 := by
    show (∫ t in Set.Ioc a b, (U t - L t)) = 0
    rw [MeasureTheory.integral_sub hiU hiL]
    linarith
  have hzero : (U - L) =ᵐ[volume.restrict (Set.Ioc a b)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hLUae (hiU.sub hiL)).1 heqUL
  have hfeq : f =ᵐ[volume.restrict (Set.Ioc a b)] U := by
    filter_upwards [hzero, ae_restrict_mem measurableSet_Ioc] with t h1 ht
    have h2 := hfU t ht
    have h3 := hfL t ht
    simp only [Pi.sub_apply, Pi.zero_apply] at h1
    linarith
  have hfint : IntegrableOn f (Set.Ioc a b) volume := hiU.congr hfeq.symm
  have hfval : (∫ t in Set.Ioc a b, f t) = I := by
    rw [MeasureTheory.integral_congr_ae hfeq]
    linarith [hintU, hintL, hintLU]
  refine ⟨?_, ?_⟩
  · exact hfint.congr_set_ae (Ioc_ae_eq_Icc (a := a) (b := b)).symm
  · rw [intervalIntegral.integral_of_le hab, hfval]
    rfl


end RiemLeb

open Filter Topology MeasureTheory in
theorem solution (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : Rudin.RiemannIntegrable a b f) (hbdd : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    IntegrableOn f (Set.Icc a b) volume ∧
      (∫ x in a..b, f x) = Rudin.RiemannIntegral a b f := by
  obtain ⟨M, hM⟩ := hbdd
  exact RiemLeb.riemann_implies_lebesgue hab hf hM
