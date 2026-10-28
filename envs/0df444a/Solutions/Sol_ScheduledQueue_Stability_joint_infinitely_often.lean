-- Prove2me | solution 1 for ScheduledQueue.Stability.joint_infinitely_often
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:12:39.907991+00:00
-- url     : https://prove2.me/submissions/c9cd42c4-740d-42ee-99d0-d6ba5efa897c

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace SQJointAux

/-- Centre of the `k`-th block: `n_k = 4a·8^k`. -/
def nK (a k : ℕ) : ℕ := 4 * a * 8 ^ k

/-- Left end (exclusive) of the `k`-th block: `L_k = a·8^k`. -/
def LK (a k : ℕ) : ℕ := a * 8 ^ k

/-- Indices of the `k`-th block: `L_k + 1, …, n_k + a`. -/
noncomputable def S (a k : ℕ) : Finset ℤ := Finset.Icc ((LK a k : ℤ) + 1) ((nK a k : ℤ) + a)

/-- Threshold imposed on `ξ_i` in the `k`-th block. -/
noncomputable def θ (h : ℝ) (a k : ℕ) (i : ℤ) : ℝ :=
  if i ≤ (nK a k : ℤ) then ((i : ℝ) - nK a k + 1) * h else ((i : ℝ) - nK a k + 2) * h

/-- The block event `G_k`. -/
def G {Ω : Type*} (h : ℝ) (ξ : ℤ → Ω → ℝ) (a k : ℕ) : Set Ω :=
  ⋂ i ∈ S a k, ξ i ⁻¹' Ici (θ h a k i)

theorem bc_eventually_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : ℝ} (hh : 0 < h) {W : Ω → ℝ} (hW : Integrable W P)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, IdentDistrib (Z n) W P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, Z n ω < n * h := by
  set X : Ω → ℝ := fun ω => max (W ω / h + 1) 0
  have hXint : Integrable X P := ((hW.div_const h).add (integrable_const 1)).pos_part
  have hX0 : 0 ≤ X := fun ω => le_max_right _ _
  have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
  have hle : ∀ n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω} ≤ P {ω | X ω ∈ Ioi (n : ℝ)} := by
    intro n
    have e : P {ω | (n : ℝ) * h ≤ Z n ω} = P {ω | (n : ℝ) * h ≤ W ω} :=
      (hZ n).measure_mem_eq (s := {x | (n : ℝ) * h ≤ x}) (measurableSet_le measurable_const measurable_id)
    rw [e]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, mem_Ioi, X] at hω ⊢
    have : (n : ℝ) ≤ W ω / h := by rw [le_div_iff₀ hh]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsum : (∑' n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω}) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hfin).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa using hn

open ScheduledQueue.Stability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : ℝ} {ξ : ℤ → Ω → ℝ} {U : Ω → ℝ}

/-- Almost surely `-ξ_i ≤ B + |i| h` for all `i`, for some finite `B`. -/
theorem ae_linear_bound (hh : 0 < h) (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ i : ℤ, -ξ i ω ≤ B + |(i : ℝ)| * h := by
  have h1 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (m : ℤ) ω < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω) hin.integrable.neg
    intro m
    exact (hin.identDistrib _).comp (u := fun x : ℝ => -x) (by fun_prop)
  have h2 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (-(m : ℤ)) ω < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω) hin.integrable.neg
    intro m
    exact (hin.identDistrib _).comp (u := fun x : ℝ => -x) (by fun_prop)
  filter_upwards [h1, h2] with ω h1 h2
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 h1
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  set N : ℕ := max N1 N2
  obtain ⟨B, hB⟩ : BddAbove ((fun i : ℤ => -ξ i ω) '' (Finset.Icc (-(N : ℤ)) N : Set ℤ)) :=
    ((Finset.finite_toSet _).image _).bddAbove
  refine ⟨max B 0, fun i => ?_⟩
  have habs : 0 ≤ |(i : ℝ)| * h := mul_nonneg (abs_nonneg _) hh.le
  by_cases hi : -(N : ℤ) ≤ i ∧ i ≤ N
  · have : -ξ i ω ≤ B := hB ⟨i, by simpa using hi, rfl⟩
    linarith [le_max_left B 0]
  · rcases le_or_gt 0 i with hi0 | hi0
    · have hm := hN1 i.toNat (by omega)
      have e : ((i.toNat : ℕ) : ℤ) = i := by omega
      have e2 : ((i.toNat : ℕ) : ℝ) = (i : ℝ) := by exact_mod_cast e
      rw [e, e2] at hm
      rw [abs_of_nonneg (by exact_mod_cast hi0)]
      linarith [le_max_right B 0]
    · have hm := hN2 (-i).toNat (by omega)
      have e : (-(((-i).toNat : ℕ) : ℤ)) = i := by omega
      have e2 : (((-i).toNat : ℕ) : ℝ) = -(i : ℝ) := by
        have : (((-i).toNat : ℕ) : ℤ) = -i := by omega
        exact_mod_cast this
      rw [e, e2] at hm
      rw [abs_of_neg (by exact_mod_cast hi0)]
      linarith [le_max_right B 0]

theorem det_bound (hh : 0 < h) {a k : ℕ} {ω : Ω} {B : ℝ} (ha : 1 ≤ a)
    (hG : ω ∈ G h ξ a k) (hB : ∀ i : ℤ, -ξ i ω ≤ B + |(i : ℝ)| * h)
    (hBk : B ≤ (2 * (LK a k : ℝ) - 1) * h) :
    Y h ξ (nK a k) ω = 0 ∧ (a : ℕ∞) ≤ tildeY h ξ (nK a k) ω := by
  have hLn : (nK a k : ℤ) = 4 * (LK a k : ℤ) := by simp [nK, LK]; ring
  have hL1 : (1 : ℤ) ≤ LK a k := by
    have : 1 ≤ LK a k := Nat.one_le_iff_ne_zero.2 (by simp [LK]; omega)
    exact_mod_cast this
  simp only [G, mem_iInter, mem_preimage, mem_Ici] at hG
  constructor
  · simp only [Y, encard_eq_zero]
    ext j
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
    intro hj
    set i : ℤ := (nK a k : ℤ) + 1 - j with hi
    by_cases hiL : (LK a k : ℤ) + 1 ≤ i
    · have hiS : i ∈ S a k := by
        simp only [S, Finset.mem_Icc]; constructor <;> omega
      have hθ := hG i hiS
      have hle : i ≤ (nK a k : ℤ) := by omega
      simp only [θ, hle, if_true] at hθ
      have : (i : ℝ) = (nK a k : ℝ) + 1 - j := by simp [hi]
      rw [this] at hθ
      linarith
    · have hb := hB i
      have hiR : (i : ℝ) ≤ LK a k := by exact_mod_cast (show i ≤ (LK a k : ℤ) by omega)
      have hnR : (nK a k : ℝ) = 4 * (LK a k : ℝ) := by exact_mod_cast hLn
      have hiv : (i : ℝ) = (nK a k : ℝ) + 1 - j := by simp [hi]
      rcases le_or_gt 0 (i : ℝ) with hi0 | hi0
      · rw [abs_of_nonneg hi0] at hb
        nlinarith
      · rw [abs_of_neg hi0] at hb
        nlinarith
  · have hsub : (Finset.Icc (1 : ℤ) a : Set ℤ) ⊆
        {j : ℤ | 1 ≤ j ∧ (j + 2) * h ≤ max (ξ (((nK a k : ℕ) : ℤ) + j) ω) 0} := by
      intro j hj
      simp only [Finset.coe_Icc, mem_Icc] at hj
      refine ⟨hj.1, ?_⟩
      have hiS : (nK a k : ℤ) + j ∈ S a k := by
        simp only [S, Finset.mem_Icc]; constructor <;> omega
      have hθ := hG _ hiS
      have hle : ¬ ((nK a k : ℤ) + j ≤ (nK a k : ℤ)) := by omega
      simp only [θ, hle, if_false] at hθ
      push_cast at hθ
      refine le_trans (le_of_eq ?_) (hθ.trans (le_max_left _ _))
      ring
    calc (a : ℕ∞) = (Finset.Icc (1 : ℤ) a : Set ℤ).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard]; simp
      _ ≤ _ := encard_le_encard hsub

theorem prob_G_eq (hin : ScheduledInput P ξ U) (a k : ℕ) (T : Finset ℤ) :
    P (⋂ i ∈ T, ξ i ⁻¹' Ici (θ h a k i)) = ∏ i ∈ T, P (ξ 0 ⁻¹' Ici (θ h a k i)) := by
  rw [hin.indep.measure_inter_preimage_eq_mul T (fun i _ => measurableSet_Ici)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (hin.identDistrib i).measure_mem_eq measurableSet_Ici

theorem prob_G_lower (hh : 0 < h) (hin : ScheduledInput P ξ U)
    (hunb : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) (a : ℕ) (ha : 1 ≤ a) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∃ k0 : ℕ, ∀ k ≥ k0, p ≤ P (G h ξ a k) := by
  -- positivity of upper tails
  have hQpos : ∀ x : ℝ, 0 < P (ξ 0 ⁻¹' Ici x) := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    apply hunb
    refine ⟨x, ?_⟩
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [mem_setOf_eq, not_le] at hω
    exact hω.le
  -- summable lower tails
  set A : ℕ → ℝ≥0∞ := fun m => P (ξ 0 ⁻¹' Iio ((1 - (m : ℝ)) * h))
  have hAsum : (∑' m, A m) ≠ ∞ := by
    set X : Ω → ℝ := fun ω => max (-ξ 0 ω / h + 1) 0
    have hXint : Integrable X P := ((hin.integrable.neg.div_const h).add (integrable_const 1)).pos_part
    have hX0 : 0 ≤ X := fun ω => le_max_right _ _
    have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
      let _ : MeasureSpace Ω := ⟨P⟩
      exact tsum_prob_mem_Ioi_lt_top hXint hX0
    refine (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun m => measure_mono ?_) hfin).ne
    intro ω hω
    simp only [mem_preimage, mem_Iio] at hω
    simp only [mem_setOf_eq, mem_Ioi, X]
    have : (m : ℝ) - 1 < -ξ 0 ω / h := by rw [lt_div_iff₀ hh]; nlinarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, (∑' m, A (m + J)) ≤ 2⁻¹ := by
    have := ENNReal.tendsto_sum_nat_add A hAsum
    have h2 : (0 : ℝ≥0∞) < 2⁻¹ := by simp
    obtain ⟨J, hJ⟩ := (this.eventually (gt_mem_nhds h2)).exists
    exact ⟨J, hJ.le⟩
  set c : ℝ≥0∞ := P (ξ 0 ⁻¹' Ici (((a : ℝ) + 2) * h)) ^ (J + a)
  have hc : c ≠ 0 := pow_ne_zero _ (hQpos _).ne'
  refine ⟨c * 2⁻¹, ENNReal.mul_pos hc (by simp), J, fun k hk => ?_⟩
  set n : ℤ := (nK a k : ℤ)
  set L : ℤ := (LK a k : ℤ)
  have hnL : n = 4 * L := by simp only [n, L, nK, LK]; push_cast; ring
  have hLJ : (J : ℤ) ≤ 3 * L := by
    have h8 : k < 8 ^ k := Nat.lt_pow_self (by norm_num)
    have : J ≤ 3 * (a * 8 ^ k) := by
      have : 8 ^ k ≤ a * 8 ^ k := Nat.le_mul_of_pos_left _ ha
      omega
    simp only [L, LK]; exact_mod_cast this
  set f : ℤ → ℝ≥0∞ := fun i => P (ξ 0 ⁻¹' Ici (θ h a k i))
  set S1 : Finset ℤ := Finset.Icc (L + 1) (n - J)
  set S2 : Finset ℤ := Finset.Icc (n - J + 1) (n + a)
  have hsplit : S a k = S1 ∪ S2 := by
    ext i; simp only [S, S1, S2, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [S1, S2, Finset.mem_Icc] at h1 h2; omega
  have hPG : P (G h ξ a k) = (∏ i ∈ S1, f i) * ∏ i ∈ S2, f i := by
    rw [G, prob_G_eq hin, hsplit, Finset.prod_union hdisj]
  -- the near block
  have h2 : c ≤ ∏ i ∈ S2, f i := by
    have hcard : S2.card = J + a := by
      simp only [S2, Int.card_Icc]; omega
    show P (ξ 0 ⁻¹' Ici (((a : ℝ) + 2) * h)) ^ (J + a) ≤ _
    rw [← hcard]
    apply Finset.pow_card_le_prod
    intro i hi
    simp only [S2, Finset.mem_Icc] at hi
    apply measure_mono
    intro ω hω
    simp only [mem_preimage, mem_Ici] at hω ⊢
    refine le_trans ?_ hω
    have hiR : (i : ℝ) ≤ n + a := by exact_mod_cast hi.2
    have hn : (n : ℝ) = (nK a k : ℝ) := by simp [n]
    simp only [θ]
    split_ifs with hle
    · have : (i : ℝ) ≤ n := by exact_mod_cast hle
      apply mul_le_mul_of_nonneg_right _ hh.le
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    · apply mul_le_mul_of_nonneg_right _ hh.le
      linarith
  -- the far block
  have h1 : 2⁻¹ ≤ ∏ i ∈ S1, f i := by
    rw [← prob_G_eq hin]
    set E := ⋂ i ∈ S1, ξ i ⁻¹' Ici (θ h a k i)
    have hcompl : P Eᶜ ≤ 2⁻¹ := by
      have e1 : Eᶜ = ⋃ i ∈ S1, ξ i ⁻¹' Iio (θ h a k i) := by
        simp only [E, compl_iInter, preimage_compl.symm, compl_Ici]
      rw [e1]
      refine (measure_biUnion_finset_le _ _).trans ?_
      have e2 : ∀ i ∈ S1, P (ξ i ⁻¹' Iio (θ h a k i)) = A ((n - i - J).toNat + J) := by
        intro i hi
        simp only [S1, Finset.mem_Icc] at hi
        rw [(hin.identDistrib i).measure_mem_eq measurableSet_Iio]
        have hle : i ≤ (nK a k : ℤ) := by omega
        simp only [A, θ, hle, if_true]
        congr 3
        have : (((n - i - J).toNat + J : ℕ) : ℤ) = n - i := by omega
        have h' : (((n - i - J).toNat + J : ℕ) : ℝ) = (n : ℝ) - i := by exact_mod_cast this
        rw [h']; simp only [n]; push_cast; ring
      rw [Finset.sum_congr rfl e2]
      have hinj : Set.InjOn (fun i : ℤ => (n - i - J).toNat) S1 := by
        intro i hi j hj hij
        simp only [S1, Finset.coe_Icc, mem_Icc] at hi hj
        simp only at hij
        omega
      rw [← Finset.sum_image (g := fun i : ℤ => (n - i - J).toNat) (f := fun m => A (m + J)) hinj]
      exact (ENNReal.sum_le_tsum _).trans hJ
    have hone : (1 : ℝ≥0∞) ≤ P E + 2⁻¹ := by
      calc (1 : ℝ≥0∞) = P (E ∪ Eᶜ) := by rw [union_compl_self, measure_univ]
        _ ≤ P E + P Eᶜ := measure_union_le _ _
        _ ≤ P E + 2⁻¹ := by gcongr
    have := tsub_le_iff_right.2 hone
    rwa [ENNReal.one_sub_inv_two] at this
  rw [hPG, mul_comm c]
  exact mul_le_mul' h1 h2 |>.trans' (by rw [mul_comm])

theorem measurableSet_block (hin : ScheduledInput P ξ U) (T : Set ℤ) {i : ℤ} (hi : i ∈ T)
    {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet[⨆ j ∈ T, MeasurableSpace.comap (ξ j) inferInstance] (ξ i ⁻¹' s) := by
  have hle : MeasurableSpace.comap (ξ i) inferInstance ≤
      ⨆ j ∈ T, MeasurableSpace.comap (ξ j) inferInstance :=
    le_iSup₂ (f := fun j (_ : j ∈ T) => MeasurableSpace.comap (ξ j) inferInstance) i hi
  exact hle _ ⟨s, hs, rfl⟩

theorem measurableSet_G (hin : ScheduledInput P ξ U) (T : Set ℤ) (a k : ℕ)
    (hT : ∀ i ∈ S a k, i ∈ T) :
    MeasurableSet[⨆ j ∈ T, MeasurableSpace.comap (ξ j) inferInstance] (G h ξ a k) := by
  simp only [G]
  exact Finset.measurableSet_biInter _ fun i hi => measurableSet_block hin T (hT i hi) measurableSet_Ici

theorem block_le (a k k' : ℕ) (hk : k < k') : (nK a k : ℤ) + a ≤ LK a k' := by
  have h1 : 8 ^ (k + 1) ≤ 8 ^ k' := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 1 ≤ 8 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have : 4 * a * 8 ^ k + a ≤ a * 8 ^ k' := by
    have : a * 8 ^ (k + 1) ≤ a * 8 ^ k' := Nat.mul_le_mul_left _ h1
    rw [pow_succ] at this
    nlinarith
  simp only [nK, LK]; exact_mod_cast this

theorem prob_none (hin : ScheduledInput P ξ U) (a K : ℕ) (p : ℝ≥0∞)
    (hp : ∀ k ≥ K, p ≤ P (G h ξ a k)) :
    ∀ N : ℕ, P (⋂ k ∈ Finset.Ico K (K + N), (G h ξ a k)ᶜ) ≤ (1 - p) ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    set T : Set ℤ := Iic (LK a (K + N) : ℤ)
    have hmeasG : ∀ k, MeasurableSet (G h ξ a k) := fun k =>
      Finset.measurableSet_biInter _ fun i _ => (hin.measurable i) measurableSet_Ici
    have hE : MeasurableSet[⨆ j ∈ T, MeasurableSpace.comap (ξ j) inferInstance]
        (⋂ k ∈ Finset.Ico K (K + N), (G h ξ a k)ᶜ) := by
      refine Finset.measurableSet_biInter _ fun k hk => (measurableSet_G hin T a k ?_).compl
      intro i hi
      simp only [Finset.mem_Ico] at hk
      simp only [S, Finset.mem_Icc] at hi
      have := block_le a k (K + N) hk.2
      simp only [T, mem_Iic]; omega
    have hB : MeasurableSet[⨆ j ∈ (Ioi (LK a (K + N) : ℤ)), MeasurableSpace.comap (ξ j) inferInstance]
        (G h ξ a (K + N))ᶜ := by
      refine (measurableSet_G hin _ a _ ?_).compl
      intro i hi
      simp only [S, Finset.mem_Icc] at hi
      simp only [mem_Ioi]; omega
    have hind := indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (ξ i) inferInstance)
      (fun i => (hin.measurable i).comap_le)
      ((iIndepFun_iff_iIndep _ _ _).1 hin.indep)
      (S := T) (T := Ioi (LK a (K + N) : ℤ))
      (by rw [Set.disjoint_left]; intro i h1 h2; simp only [T, mem_Iic, mem_Ioi] at h1 h2; omega)
    have hsplit : (⋂ k ∈ Finset.Ico K (K + (N + 1)), (G h ξ a k)ᶜ) =
        (⋂ k ∈ Finset.Ico K (K + N), (G h ξ a k)ᶜ) ∩ (G h ξ a (K + N))ᶜ := by
      rw [show K + (N + 1) = (K + N) + 1 by ring, ← Finset.insert_Ico_right_eq_Ico_add_one (by omega)]
      rw [Finset.set_biInter_insert, inter_comm]
    rw [hsplit, (Indep_iff _ _ P).1 hind _ _ hE hB, pow_succ]
    gcongr
    rw [prob_compl_eq_one_sub (hmeasG _)]
    gcongr
    exact hp _ (by omega)

end SQJointAux

open ScheduledQueue.Stability SQJointAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (¬ ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ l r : ℕ, 0 < P {ω | Y h ξ 0 ω ≤ l} →
        ∀ᵐ ω ∂P, ∃ᶠ n : ℕ in atTop, Y h ξ n ω ≤ l ∧ (r : ℕ∞) < tildeY h ξ n ω := by
  intro hunb l r _
  set a : ℕ := r + 1
  obtain ⟨p, hp0, k0, hp⟩ := prob_G_lower hh hin hunb a (by omega)
  have hinf : ∀ᵐ ω ∂P, ∀ K : ℕ, ∃ k ≥ K, ω ∈ G h ξ a k := by
    rw [ae_all_iff]
    intro K
    set K' := max K k0
    have hnull : P (⋂ k, ⋂ (_ : K' ≤ k), (G h ξ a k)ᶜ) = 0 := by
      have hle : ∀ N : ℕ, P (⋂ k, ⋂ (_ : K' ≤ k), (G h ξ a k)ᶜ) ≤ (1 - p) ^ N := by
        intro N
        refine le_trans (measure_mono ?_) (prob_none hin a K' p (fun k hk => hp k (le_trans (le_max_right _ _) hk)) N)
        intro ω hω
        simp only [mem_iInter] at hω ⊢
        intro k hk
        exact hω k (Finset.mem_Ico.1 hk).1
      have hlt : 1 - p < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0.ne'
      have htend := ENNReal.tendsto_pow_atTop_nhds_zero_iff.2 hlt
      exact le_antisymm (ge_of_tendsto' htend hle) bot_le
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simp only [mem_setOf_eq, not_exists, not_and] at hω
    simp only [mem_iInter, mem_compl_iff]
    intro k hk
    exact hω k (le_trans (le_max_left _ _) hk)
  filter_upwards [hinf, ae_linear_bound hh hin] with ω hinf ⟨B, hB⟩
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨k, hkK, hG⟩ := hinf (max N ⌈B / h⌉₊)
  have h8 : k < 8 ^ k := Nat.lt_pow_self (by norm_num)
  have hLk : 8 ^ k ≤ LK a k := by simp only [LK]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hBk : B ≤ (2 * (LK a k : ℝ) - 1) * h := by
    have h1 : B / h ≤ ⌈B / h⌉₊ := Nat.le_ceil _
    have h2 : (⌈B / h⌉₊ : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hkK
    have h3 : ((k : ℝ) + 1) ≤ LK a k := by exact_mod_cast (show k + 1 ≤ LK a k by omega)
    have h4 : B ≤ k * h := by rw [div_le_iff₀ hh] at h1; nlinarith
    nlinarith
  obtain ⟨hY, hT⟩ := det_bound hh (by omega) hG hB hBk
  refine ⟨nK a k, ?_, ?_, ?_⟩
  · have : 8 ^ k ≤ nK a k := by
      simp only [nK]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [hY]; exact bot_le
  · exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self r) hT
