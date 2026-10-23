-- Prove2me | solution 1 for RegretMatching.Approach.theorem_A
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T07:36:07.863095+00:00
-- url     : https://prove2.me/submissions/661aa16e-ad79-491e-a845-4f58918e9b4a

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretApproachProof

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

noncomputable def cumulative (u : ι → (∀ i, S i) → ℝ) {t : ℕ}
    (h : Fin t → (∀ i, S i)) (i : ι) (j k : S i) : ℝ :=
  ∑ τ : Fin t, RegretMatching.Main.regretA u i (h τ) j k

noncomputable def potential (u : ι → (∀ i, S i) → ℝ) {t : ℕ}
    (h : Fin t → (∀ i, S i)) (i : ι) : ℝ :=
  ∑ j : S i, ∑ k : S i, (max (cumulative u h i j k) 0)^2

end RegretApproachProof

open Finset

namespace RegretApproachProof

theorem pospart_sq_add_le (a b : ℝ) :
    (max (a + b) 0)^2 ≤ (max a 0)^2 + 2 * max a 0 * b + b^2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    by_cases hab : 0 ≤ a + b
    · rw [max_eq_left hab]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hab)]
      nlinarith [sq_nonneg (a + b)]
  · rw [max_eq_right (le_of_not_ge ha)]
    by_cases hab : 0 ≤ a + b
    · rw [max_eq_left hab]
      have hb : 0 ≤ b := by linarith
      nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) hb,
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hab]
    · rw [max_eq_right (le_of_not_ge hab)]
      nlinarith [sq_nonneg b]

section Game
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem regretA_diagonal (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (s : ∀ i, S i) (j : S i) : RegretMatching.Main.regretA u i s j j = 0 := by
  by_cases h : s i = j
  · unfold RegretMatching.Main.regretA
    rw [if_pos h, ← h, Function.update_eq_self, sub_self]
  · simp [RegretMatching.Main.regretA, h]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem cumulative_diagonal (u : ι → (∀ i, S i) → ℝ)
    {t : ℕ} (h : Fin t → (∀ i, S i)) (i : ι) (j : S i) :
    cumulative u h i j j = 0 := by
  simp [cumulative, regretA_diagonal]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem cumulative_snoc (u : ι → (∀ i, S i) → ℝ)
    {t : ℕ} (h : Fin t → (∀ i, S i)) (s : ∀ i, S i) (i : ι) (j k : S i) :
    cumulative u (Fin.snoc h s) i j k =
      cumulative u h i j k + RegretMatching.Main.regretA u i s j k := by
  simp [cumulative, Fin.sum_univ_castSucc]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem regret_eq_cumulative (u : ι → (∀ i, S i) → ℝ)
    {t : ℕ} (h : Fin t → (∀ i, S i)) (i : ι) (j k : S i) :
    RegretMatching.Main.regretR u h i j k = max (cumulative u h i j k) 0 / (t : ℝ) := by
  classical
  have hd : RegretMatching.Main.regretD u h i j k = cumulative u h i j k / (t : ℝ) := by
    simp only [RegretMatching.Main.regretD, cumulative, RegretMatching.Main.regretA,
      Finset.sum_filter, div_eq_mul_inv, one_mul]
    ring
  rw [RegretMatching.Main.regretR, hd]
  by_cases ht : t = 0
  · simp [ht]
  · have ht0 : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
    by_cases hc : 0 ≤ cumulative u h i j k
    · rw [max_eq_left hc, max_eq_left (div_nonneg hc ht0.le)]
    · rw [max_eq_right (le_of_not_ge hc),
        max_eq_right (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) ht0.le)]
      simp

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem regret_diagonal (u : ι → (∀ i, S i) → ℝ)
    {t : ℕ} (h : Fin t → (∀ i, S i)) (i : ι) (j : S i) :
    RegretMatching.Main.regretR u h i j j = 0 := by
  simp [regret_eq_cumulative, cumulative_diagonal]

theorem exists_increment_bound (u : ι → (∀ i, S i) → ℝ) (i : ι) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ∀ i, S i) (j k : S i),
      |RegretMatching.Main.regretA u i s j k| ≤ B := by
  classical
  let U : ℝ := ∑ s : (∀ i, S i), |u i s|
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hu (s : ∀ i, S i) : |u i s| ≤ U := by
    change |u i s| ≤ ∑ z : (∀ i, S i), |u i z|
    exact Finset.single_le_sum (fun z _ => abs_nonneg (u i z)) (Finset.mem_univ s)
  refine ⟨2 * U, by positivity, ?_⟩
  intro s j k
  unfold RegretMatching.Main.regretA
  split_ifs
  · exact (abs_sub _ _).trans (by linarith [hu s, hu (Function.update s i k)])
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hU

omit [Fintype ι] [∀ i, Fintype (S i)] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
theorem hist_snoc {Ω : Type} (play : ℕ → Ω → (∀ i, S i)) (t : ℕ) (ω : Ω) :
    RegretMatching.Approach.hist play (t + 1) ω =
      Fin.snoc (RegretMatching.Approach.hist play t ω) (play t ω) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [RegretMatching.Approach.hist]
  · simp [RegretMatching.Approach.hist]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem cumulative_hist_succ {Ω : Type} (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (play : ℕ → Ω → (∀ i, S i)) (t : ℕ) (ω : Ω) (j k : S i) :
    cumulative u (RegretMatching.Approach.hist play (t + 1) ω) i j k =
      cumulative u (RegretMatching.Approach.hist play t ω) i j k +
        RegretMatching.Main.regretA u i (play t ω) j k := by
  rw [hist_snoc, cumulative_snoc]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem regret_interpolate {Ω : Type}
    (u : ι → (∀ i, S i) → ℝ) (i : ι) (play : ℕ → Ω → (∀ i, S i))
    (B : ℝ) (hB : 0 ≤ B)
    (hinc : ∀ (s : ∀ i, S i) (j k : S i), |RegretMatching.Main.regretA u i s j k| ≤ B)
    (ω : Ω) (j k : S i) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    RegretMatching.Main.regretR u (RegretMatching.Approach.hist play n ω) i j k ≤
      RegretMatching.Main.regretR u (RegretMatching.Approach.hist play m ω) i j k +
        B * ((n-m : ℕ) : ℝ) / (m : ℝ) := by
  have hc (d : ℕ) :
      cumulative u (RegretMatching.Approach.hist play (m+d) ω) i j k ≤
        cumulative u (RegretMatching.Approach.hist play m ω) i j k + B * (d : ℝ) := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.add_succ, cumulative_hist_succ]
      have hi := (le_abs_self (RegretMatching.Main.regretA u i (play (m+d) ω) j k)).trans
        (hinc (play (m+d) ω) j k)
      push_cast
      linarith
  have hc' := hc (n-m)
  rw [Nat.add_sub_of_le hmn] at hc'
  have hp : max (cumulative u (RegretMatching.Approach.hist play n ω) i j k) 0 ≤
      max (cumulative u (RegretMatching.Approach.hist play m ω) i j k) 0 +
        B * ((n-m : ℕ) : ℝ) := by
    apply max_le
    · exact hc'.trans (add_le_add (le_max_left _ _) le_rfl)
    · positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  rw [regret_eq_cumulative, regret_eq_cumulative]
  calc
    _ ≤ (max (cumulative u (RegretMatching.Approach.hist play m ω) i j k) 0 +
        B * ((n-m : ℕ) : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hp (hm0.le.trans hmn')
    _ ≤ (max (cumulative u (RegretMatching.Approach.hist play m ω) i j k) 0 +
        B * ((n-m : ℕ) : ℝ)) / (m : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hm0 hmn'
    _ = _ := add_div _ _ _
end Game
end RegretApproachProof

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretApproachProof

section FiniteLaw
variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
  (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → α)
  (hX : ∀ a, MeasurableSet {ω | X ω = a})

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
private theorem fiber_expansion (g : α → ℝ) :
    (fun ω => g (X ω)) = (fun ω => ∑ a : α, Set.indicator {ω | X ω = a} (fun _ => g a) ω) := by
  classical
  funext ω
  simp [Set.indicator_apply]

include hX

theorem finite_fiber_integrable (g : α → ℝ) : Integrable (fun ω => g (X ω)) P := by
  classical
  rw [fiber_expansion X g]
  exact integrable_finsetSum _ fun a _ => (integrable_const (g a)).indicator (hX a)

theorem finite_fiber_integral (g : α → ℝ) :
    (∫ ω, g (X ω) ∂P) = ∑ a : α, (P {ω | X ω = a}).toReal * g a := by
  classical
  rw [fiber_expansion X g, integral_finsetSum]
  · simp [integral_indicator_const, hX, Measure.real, smul_eq_mul]
  · intro a _
    exact (integrable_const (g a)).indicator (hX a)

theorem finite_fiber_mass : ∑ a : α, (P {ω | X ω = a}).toReal = 1 := by
  simpa using (finite_fiber_integral P X hX (fun _ => 1)).symm
end FiniteLaw

section History
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
  {Ω : Type} [MeasurableSpace Ω]
  (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i : ι) → S i → ℝ)
  (P : Measure Ω) [IsProbabilityMeasure P] (play : ℕ → Ω → (∀ i, S i))
  (hplay : RegretMatching.Main.IsPlay σ P play)

include hplay

omit [DecidableEq ι] [∀ i, Fintype (S i)] [IsProbabilityMeasure P] in
 theorem history_fiber_measurable (t : ℕ) (h : Fin t → (∀ i, S i)) :
    MeasurableSet {ω | RegretMatching.Approach.hist play t ω = h} := by
  have he : {ω | RegretMatching.Approach.hist play t ω = h} =
      ⋂ τ : Fin t, {ω | play τ ω = h τ} := by
    ext ω
    simp [RegretMatching.Approach.hist, funext_iff]
  rw [he]
  exact MeasurableSet.iInter fun τ => hplay.1 τ (h τ)

 theorem history_integrable (t : ℕ) (g : (Fin t → (∀ i, S i)) → ℝ) :
    Integrable (fun ω => g (RegretMatching.Approach.hist play t ω)) P :=
  finite_fiber_integrable P _ (history_fiber_measurable σ P play hplay t) g

 theorem history_integral (t : ℕ) (g : (Fin t → (∀ i, S i)) → ℝ) :
    (∫ ω, g (RegretMatching.Approach.hist play t ω) ∂P) =
      ∑ h : Fin t → (∀ i, S i),
        (P {ω | RegretMatching.Approach.hist play t ω = h}).toReal * g h :=
  finite_fiber_integral P _ (history_fiber_measurable σ P play hplay t) g

 theorem history_mass (t : ℕ) :
    ∑ h : Fin t → (∀ i, S i),
      (P {ω | RegretMatching.Approach.hist play t ω = h}).toReal = 1 :=
  finite_fiber_mass P _ (history_fiber_measurable σ P play hplay t)

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
 theorem history_joint_mass (t : ℕ) (h : Fin t → (∀ i, S i)) (s : ∀ i, S i) :
    (P {ω | RegretMatching.Approach.hist play t ω = h ∧ play t ω = s}).toReal =
      (P {ω | RegretMatching.Approach.hist play t ω = h}).toReal *
        ∏ i, σ t h i (s i) := by
  by_cases hz : P {ω | RegretMatching.Approach.hist play t ω = h} = 0
  · have hj : P {ω | RegretMatching.Approach.hist play t ω = h ∧ play t ω = s} = 0 :=
      measure_mono_null (fun _ hω => hω.1) hz
    rw [hj, hz]
    simp
  · have he := cond_mul_eq_inter (history_fiber_measurable σ P play hplay t h)
      {ω | play t ω = s} P
    have hr := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_mul] at hr
    have hc := hplay.2 t h hz s
    change (P[|{ω | RegretMatching.Approach.hist play t ω = h}] {ω | play t ω = s}).toReal
      = ∏ i, σ t h i (s i) at hc
    rw [hc] at hr
    simpa only [Set.inter_def, Set.mem_ofPred_eq, mul_comm] using hr.symm

 theorem history_expectation_succ (t : ℕ) (g : (Fin (t + 1) → (∀ i, S i)) → ℝ) :
    (∫ ω, g (RegretMatching.Approach.hist play (t + 1) ω) ∂P) =
      ∑ h : Fin t → (∀ i, S i),
        (P {ω | RegretMatching.Approach.hist play t ω = h}).toReal *
          ∑ s : ∀ i, S i, (∏ i, σ t h i (s i)) * g (Fin.snoc h s) := by
  classical
  let X := fun ω => (RegretMatching.Approach.hist play t ω, play t ω)
  have hX : ∀ a : (Fin t → (∀ i, S i)) × (∀ i, S i), MeasurableSet {ω | X ω = a} := by
    rintro ⟨h, s⟩
    change MeasurableSet {ω | (RegretMatching.Approach.hist play t ω, play t ω) = (h, s)}
    simpa only [Prod.mk.injEq, Set.inter_def, Set.mem_ofPred_eq] using
      (history_fiber_measurable σ P play hplay t h).inter (hplay.1 t s)
  have hs (ω : Ω) : RegretMatching.Approach.hist play (t + 1) ω =
      Fin.snoc (RegretMatching.Approach.hist play t ω) (play t ω) := by
    funext τ
    refine Fin.lastCases ?_ (fun j => ?_) τ
    · simp [RegretMatching.Approach.hist]
    · simp [RegretMatching.Approach.hist]
  have he := finite_fiber_integral P X hX (fun a => g (Fin.snoc a.1 a.2))
  simp only [X, ← hs, Fintype.sum_prod_type, Prod.mk.injEq] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [history_joint_mass σ P play hplay]
  ring
end History
end RegretApproachProof

open Finset

namespace RegretApproachProof

private theorem balanced_payoff_sum {A : Type*} [Fintype A]
    (q : A → ℝ) (L : A → A → ℝ) (v : A → ℝ)
    (hb : ∀ k, ∑ j, q j * L j k = q k * ∑ j, L k j) :
    (∑ j, ∑ k, q j * L j k * (v k - v j)) = 0 := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hl : (∑ j, ∑ k, q j * L j k * v k) =
      ∑ k, (q k * ∑ j, L k j) * v k := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hb]
  have hr : (∑ j, ∑ k, q j * L j k * v j) =
      ∑ j, (q j * ∑ k, L j k) * v j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [hl, hr, sub_self]

section Game
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

omit [Fintype ι] in
theorem cumulative_balance (u : ι → (∀ i, S i) → ℝ) (i : ι)
    {t : ℕ} (h : Fin t → (∀ i, S i)) (q : S i → ℝ) (ht : 0 < t)
    (h31 : RegretMatching.Approach.SatisfiesEq31 u h i q) :
    ∀ j, ∑ k, q k * max (cumulative u h i k j) 0 =
      q j * ∑ k, max (cumulative u h i j k) 0 := by
  have hR (j k : S i) : RegretMatching.Approach.regretR0 u h i j k =
      max (cumulative u h i j k) 0 / (t : ℝ) := by
    by_cases he : j = k
    · subst k
      simp [RegretMatching.Approach.regretR0, cumulative_diagonal]
    · simp [RegretMatching.Approach.regretR0, he, regret_eq_cumulative]
  intro j
  have he := h31 j
  simp only [hR, ← mul_div_assoc, ← Finset.sum_div] at he
  exact (div_left_inj' (by exact_mod_cast ht.ne' : (t : ℝ) ≠ 0)).mp he

omit [Fintype ι] in
private theorem own_cross_zero (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (q : S i → ℝ) (L : S i → S i → ℝ)
    (hb : ∀ k, ∑ j, q j * L j k = q k * ∑ j, L k j) (s : ∀ i, S i) :
    (∑ a, q a * ∑ j, ∑ k, L j k *
      RegretMatching.Main.regretA u i (Function.update s i a) j k) = 0 := by
  classical
  have ha (a : S i) : (∑ j, ∑ k, L j k *
      RegretMatching.Main.regretA u i (Function.update s i a) j k) =
      ∑ k, L a k * (u i (Function.update s i k) - u i (Function.update s i a)) := by
    simp [RegretMatching.Main.regretA, mul_ite, Finset.sum_ite_irrel]
  simp_rw [ha, Finset.mul_sum]
  simpa only [mul_assoc] using balanced_payoff_sum q L (fun a => u i (Function.update s i a)) hb

omit [∀ i, DecidableEq (S i)] in
theorem product_weights_sum (q : (i : ι) → S i → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ (S i)) :
    (∑ s : ∀ i, S i, ∏ i, q i (s i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp [fun i => (hq i).2]

omit [DecidableEq ι] [∀ i, DecidableEq (S i)] in
theorem product_weights_nonneg (q : (i : ι) → S i → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ (S i)) (s : ∀ i, S i) :
    0 ≤ ∏ i, q i (s i) := Finset.prod_nonneg fun i _ => (hq i).1 (s i)

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
private theorem profile_weight_split (q : (i : ι) → S i → ℝ) (i : ι) (s : ∀ i, S i) :
    (∏ j, q j (s j)) = q i (s i) * ∏ j : {j // j ≠ i}, q j (s j) := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl i]
  congr 1
  exact Finset.prod_subtype ({i}ᶜ) (by simp) (fun j => q j (s j))

 theorem product_cross_zero [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι) (q : (i : ι) → S i → ℝ)
    (L : S i → S i → ℝ)
    (hb : ∀ k, ∑ j, q i j * L j k = q i k * ∑ j, L k j) :
    (∑ s : ∀ i, S i, (∏ j, q j (s j)) *
      ∑ j, ∑ k, L j k * RegretMatching.Main.regretA u i s j k) = 0 := by
  classical
  let e := Equiv.piSplitAt i S
  have hp (a : S i) (r : ∀ j : {j // j ≠ i}, S j) :
      (∏ j, q j (e.symm (a,r) j)) = q i a * ∏ j : {j // j ≠ i}, q j (r j) := by
    rw [profile_weight_split q i]
    congr 1
    · simp [e, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro j _
      simp [e, Equiv.piSplitAt, j.property]
  have hu (a : S i) (r : ∀ j : {j // j ≠ i}, S j) :
      Function.update (e.symm (Classical.choice (inferInstance : Nonempty (S i)), r)) i a =
        e.symm (a,r) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hj]
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  simp_rw [hp]
  have hh := own_cross_zero u i (q i) L hb
    (e.symm (Classical.choice (inferInstance : Nonempty (S i)), r))
  simp_rw [hu] at hh
  calc
    _ = (∏ j : {j // j ≠ i}, q j (r j)) *
        ∑ a, q i a * ∑ j, ∑ k, L j k * RegretMatching.Main.regretA u i (e.symm (a,r)) j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [hh, mul_zero]

 theorem history_cross_zero [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i' : ι) → S i' → ℝ)
    (h31 : ∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)),
      RegretMatching.Approach.SatisfiesEq31 u h i (σ (t + 1) h i))
    (t : ℕ) (h : Fin t → (∀ i, S i)) :
    (∑ s : ∀ i, S i, (∏ j, σ t h j (s j)) *
      ∑ j, ∑ k, max (cumulative u h i j k) 0 * RegretMatching.Main.regretA u i s j k) = 0 := by
  cases t with
  | zero => simp [cumulative]
  | succ t =>
    exact product_cross_zero u i (σ (t+1) h) _
      (cumulative_balance u i h _ (Nat.succ_pos t) (h31 t h))
end Game
end RegretApproachProof

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretApproachProof

section Game
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

omit [Fintype ι] in
theorem potential_nonneg (u : ι → (∀ i, S i) → ℝ) {t : ℕ}
    (h : Fin t → (∀ i, S i)) (i : ι) : 0 ≤ potential u h i :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype ι] in
theorem coordinate_le_potential (u : ι → (∀ i, S i) → ℝ) {t : ℕ}
    (h : Fin t → (∀ i, S i)) (i : ι) (j k : S i) :
    (max (cumulative u h i j k) 0)^2 ≤ potential u h i := by
  exact (Finset.single_le_sum (fun l _ => sq_nonneg (max (cumulative u h i j l) 0))
    (Finset.mem_univ k)).trans
    (Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ =>
      sq_nonneg (max (cumulative u h i l k) 0)) (Finset.mem_univ j))

omit [Fintype ι] in
theorem potential_snoc_le (u : ι → (∀ i, S i) → ℝ) (i : ι) (B : ℝ) (_hB : 0 ≤ B)
    (hinc : ∀ (s : ∀ i, S i) (j k : S i), |RegretMatching.Main.regretA u i s j k| ≤ B)
    {t : ℕ} (h : Fin t → (∀ i, S i)) (s : ∀ i, S i) :
    potential u (Fin.snoc h s) i ≤ potential u h i +
      2 * (∑ j, ∑ k, max (cumulative u h i j k) 0 * RegretMatching.Main.regretA u i s j k) +
      (Fintype.card (S i) : ℝ)^2 * B^2 := by
  calc
    _ ≤ ∑ j : S i, ∑ k : S i, ((max (cumulative u h i j k) 0)^2 +
        2 * (max (cumulative u h i j k) 0 * RegretMatching.Main.regretA u i s j k) + B^2) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [cumulative_snoc]
      have hb := (abs_le.mp (hinc s j k))
      have hs : (RegretMatching.Main.regretA u i s j k)^2 ≤ B^2 := by nlinarith
      nlinarith [pospart_sq_add_le (cumulative u h i j k) (RegretMatching.Main.regretA u i s j k)]
    _ = _ := by
      simp only [potential, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum]
      ring

variable [∀ i, Nonempty (S i)]

theorem conditional_potential_le
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i' : ι) → S i' → ℝ)
    (hσ : ∀ (t : ℕ) (h : Fin t → (∀ i, S i)) (i' : ι), σ t h i' ∈ stdSimplex ℝ (S i'))
    (h31 : ∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)),
      RegretMatching.Approach.SatisfiesEq31 u h i (σ (t + 1) h i))
    (B : ℝ) (hB : 0 ≤ B)
    (hinc : ∀ (s : ∀ i, S i) (j k : S i), |RegretMatching.Main.regretA u i s j k| ≤ B)
    (t : ℕ) (h : Fin t → (∀ i, S i)) :
    (∑ s : ∀ i, S i, (∏ j, σ t h j (s j)) * potential u (Fin.snoc h s) i) ≤
      potential u h i + (Fintype.card (S i) : ℝ)^2 * B^2 := by
  let w := fun s : ∀ i, S i => ∏ j, σ t h j (s j)
  let cross := fun s : ∀ i, S i =>
    ∑ j, ∑ k, max (cumulative u h i j k) 0 * RegretMatching.Main.regretA u i s j k
  have hw : ∑ s, w s = 1 := product_weights_sum (σ t h) (hσ t h)
  have hc : ∑ s, w s * cross s = 0 := history_cross_zero u i σ h31 t h
  have hc2 : (∑ s, w s * (2 * cross s)) = 0 := by
    calc
      _ = 2 * ∑ s, w s * cross s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 0 := by rw [hc, mul_zero]
  calc
    _ ≤ ∑ s : ∀ i, S i, w s * (potential u h i + 2 * cross s +
        (Fintype.card (S i) : ℝ)^2 * B^2) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (potential_snoc_le u i B hB hinc h s)
        (product_weights_nonneg (σ t h) (hσ t h) s)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hc2, ← Finset.sum_mul, ← Finset.sum_mul, hw]
      ring

theorem potential_moment
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i' : ι) → S i' → ℝ)
    (hσ : ∀ (t : ℕ) (h : Fin t → (∀ i, S i)) (i' : ι), σ t h i' ∈ stdSimplex ℝ (S i'))
    (h31 : ∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)),
      RegretMatching.Approach.SatisfiesEq31 u h i (σ (t + 1) h i))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : RegretMatching.Main.IsPlay σ P play)
    (B : ℝ) (hB : 0 ≤ B)
    (hinc : ∀ (s : ∀ i, S i) (j k : S i), |RegretMatching.Main.regretA u i s j k| ≤ B)
    (t : ℕ) :
    (∫ ω, potential u (RegretMatching.Approach.hist play t ω) i ∂P) ≤
      ((Fintype.card (S i) : ℝ)^2 * B^2) * (t : ℝ) := by
  let K : ℝ := (Fintype.card (S i) : ℝ)^2 * B^2
  induction t with
  | zero => simp [potential, cumulative]
  | succ t ih =>
    rw [history_expectation_succ σ P play hplay t (fun h => potential u h i)]
    calc
      _ ≤ ∑ h : Fin t → (∀ i, S i),
          (P {ω | RegretMatching.Approach.hist play t ω = h}).toReal * (potential u h i + K) := by
        apply Finset.sum_le_sum
        intro h _
        exact mul_le_mul_of_nonneg_left
          (conditional_potential_le u i σ hσ h31 B hB hinc t h) ENNReal.toReal_nonneg
      _ = (∫ ω, potential u (RegretMatching.Approach.hist play t ω) i ∂P) + K := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← history_integral σ P play hplay t (fun h => potential u h i), ← Finset.sum_mul, history_mass σ P play hplay,
          one_mul]
      _ ≤ K * (t : ℝ) + K := add_le_add ih le_rfl
      _ = _ := by push_cast; ring
end Game

theorem regret_second_moment
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i' : ι) → S i' → ℝ)
    (hσ : ∀ (t : ℕ) (h : Fin t → (∀ i, S i)) (i' : ι), σ t h i' ∈ stdSimplex ℝ (S i'))
    (h31 : ∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)),
      RegretMatching.Approach.SatisfiesEq31 u h i (σ (t + 1) h i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : RegretMatching.Main.IsPlay σ P play) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℕ) (j k : S i),
      (∫ ω, (RegretMatching.Main.regretR u (RegretMatching.Approach.hist play t ω) i j k)^2 ∂P)
        ≤ C / (t : ℝ) := by
  obtain ⟨B, hB, hinc⟩ := exists_increment_bound u i
  let C : ℝ := (Fintype.card (S i) : ℝ)^2 * B^2
  refine ⟨C, mul_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  intro t j k
  by_cases ht : t = 0
  · subst t
    simp [regret_eq_cumulative]
  · have ht0 : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
    have hcoord := integral_mono
      (history_integrable σ P play hplay t (fun h => (max (cumulative u h i j k) 0)^2))
      (history_integrable σ P play hplay t (fun h => potential u h i))
      (fun ω => coordinate_le_potential u (RegretMatching.Approach.hist play t ω) i j k)
    have hpot := potential_moment u i σ hσ h31 P play hplay B hB hinc t
    calc
      _ = (∫ ω, (max (cumulative u (RegretMatching.Approach.hist play t ω) i j k) 0)^2 ∂P) /
          (t : ℝ)^2 := by simp_rw [regret_eq_cumulative, div_pow]; rw [integral_div]
      _ ≤ (C * (t : ℝ)) / (t : ℝ)^2 :=
        div_le_div_of_nonneg_right (hcoord.trans hpot) (sq_nonneg _)
      _ = C / (t : ℝ) := by field_simp
end RegretApproachProof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace RegretApproachProof

theorem square_subsequence_convergence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → Ω → ℝ) (C : ℝ)
    (hnonneg : ∀ t ω, 0 ≤ R t ω)
    (hint : ∀ t, Integrable (fun ω => (R t ω)^2) P)
    (hmoment : ∀ t, (∫ ω, (R t ω)^2 ∂P) ≤ C / (t : ℝ)) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => R (k^2) ω) atTop (𝓝 0) := by
  have hs : Summable (fun k : ℕ => C / (k : ℝ)^2) := by
    have h := (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < (2 : ℕ))).mul_left C
    simpa only [mul_one_div] using h
  have hLp (k : ℕ) : eLpNorm (fun ω => (R (k^2) ω)^2) 1 P ≤
      ENNReal.ofReal (C / (k : ℝ)^2) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hint (k^2))]
    apply ENNReal.ofReal_le_ofReal
    have he : (fun ω => ‖(R (k^2) ω)^2‖) = fun ω => (R (k^2) ω)^2 := by
      funext ω
      exact Real.norm_of_nonneg (sq_nonneg _)
    rw [he]
    convert! hmoment (k^2) using 1
    norm_cast
  have hsum : (∑' k : ℕ, eLpNorm (fun ω => (R (k^2) ω)^2) 1 P) ≠ ⊤ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hLp)
  have ha := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (fun k : ℕ => (hint (k^2)).aestronglyMeasurable) hsum
  filter_upwards [ha] with ω hω
  have hsq : Tendsto (fun k : ℕ => (R (k^2) ω)^2) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_sq] using hω.tendsto_atTop_zero
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun k : ℕ => Real.sqrt ((R (k^2) ω)^2)) atTop (𝓝 (Real.sqrt 0)) at hroot
  have he : (fun k : ℕ => Real.sqrt ((R (k^2) ω)^2)) = fun k => R (k^2) ω := by
    funext k
    exact Real.sqrt_sq (hnonneg _ _)
  rwa [he, Real.sqrt_zero] at hroot

theorem square_interpolation_convergence
    (R : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hnonneg : ∀ n, 0 ≤ R n)
    (hsq : Tendsto (fun k : ℕ => R (k^2)) atTop (𝓝 0))
    (hinter : ∀ (m n : ℕ), 1 ≤ m → m ≤ n →
      R n ≤ R m + B * ((n-m : ℕ) : ℝ) / (m : ℝ)) :
    Tendsto R atTop (𝓝 0) := by
  have hsqrt : Tendsto Nat.sqrt atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b^2, fun n hn => Nat.le_sqrt'.2 hn⟩
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hInv := hinv.comp hsqrt
  have hG : Tendsto (fun n : ℕ => R ((Nat.sqrt n)^2) +
      (2 * B) * ((Nat.sqrt n : ℕ) : ℝ)⁻¹ +
        B * (((Nat.sqrt n : ℕ) : ℝ)⁻¹)^2) atTop (𝓝 0) := by
    simpa using ((hsq.comp hsqrt).add (hInv.const_mul (2 * B))).add
      ((hInv.pow 2).const_mul B)
  apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ hG
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  let q := Nat.sqrt n
  have hq : 1 ≤ q := Nat.sqrt_pos.2 (by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqq : q^2 ≤ n := Nat.sqrt_le' n
  have hlt : n < (q+1)^2 := Nat.lt_succ_sqrt' n
  have hdelta : n-q^2 ≤ 2*q+1 := by
    have he := Nat.sub_add_cancel hqq
    nlinarith
  have hd : ((n-q^2 : ℕ) : ℝ) ≤ 2 * (q : ℝ) + 1 := by exact_mod_cast hdelta
  have hq2 : 1 ≤ q^2 := by nlinarith
  calc
    R n ≤ R (q^2) + B * ((n-q^2 : ℕ) : ℝ) / ((q^2 : ℕ) : ℝ) :=
      hinter (q^2) n hq2 hqq
    _ ≤ R (q^2) + B * (2 * (q : ℝ) + 1) / (q : ℝ)^2 := by
      rw [Nat.cast_pow]
      gcongr
    _ = _ := by
      dsimp [q]
      field_simp
      ring

theorem square_time_convergence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → Ω → ℝ) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hnonneg : ∀ t ω, 0 ≤ R t ω)
    (hint : ∀ t, Integrable (fun ω => (R t ω)^2) P)
    (hmoment : ∀ t, (∫ ω, (R t ω)^2 ∂P) ≤ C / (t : ℝ))
    (hinter : ∀ ω (m n : ℕ), 1 ≤ m → m ≤ n →
      R n ω ≤ R m ω + B * ((n-m : ℕ) : ℝ) / (m : ℝ)) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => R (t+1) ω) atTop (𝓝 0) := by
  have _ := hC
  filter_upwards [square_subsequence_convergence P R C hnonneg hint hmoment] with ω hω
  exact (square_interpolation_convergence (fun n => R n ω) B hB
    (fun n => hnonneg n ω) hω (hinter ω)).comp (tendsto_add_atTop_nat 1)

end RegretApproachProof

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem theorem_A
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i' : ι) → S i' → ℝ)
    (hσ : ∀ (t : ℕ) (h : Fin t → (∀ i, S i)) (i' : ι), σ t h i' ∈ stdSimplex ℝ (S i'))
    (h31 : ∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)), SatisfiesEq31 u h i (σ (t + 1) h i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : RegretMatching.Main.IsPlay σ P play) :
    ∀ᵐ ω ∂P, ∀ j k : S i, j ≠ k →
      Tendsto (fun t : ℕ => RegretMatching.Main.regretR u (hist play (t + 1) ω) i j k) atTop (𝓝 0) := by
  obtain ⟨B, hB, hinc⟩ := RegretApproachProof.exists_increment_bound u i
  obtain ⟨C, hC, hmoment⟩ := RegretApproachProof.regret_second_moment u i σ hσ h31 Ω P play hplay
  have hp (j k : S i) : ∀ᵐ ω ∂P,
      Tendsto (fun t : ℕ => RegretMatching.Main.regretR u (hist play (t+1) ω) i j k)
        atTop (𝓝 0) := by
    apply RegretApproachProof.square_time_convergence P
      (fun t ω => RegretMatching.Main.regretR u (hist play t ω) i j k) B C hB hC
    · intro t ω
      exact le_max_right _ _
    · intro t
      exact RegretApproachProof.history_integrable σ P play hplay t
        (fun h => (RegretMatching.Main.regretR u h i j k)^2)
    · exact fun t => hmoment t j k
    · exact fun ω m n hm hmn =>
        RegretApproachProof.regret_interpolate u i play B hB hinc ω j k m n hm hmn
  have ha : ∀ᵐ ω ∂P, ∀ j k : S i,
      Tendsto (fun t : ℕ => RegretMatching.Main.regretR u (hist play (t+1) ω) i j k)
        atTop (𝓝 0) := ae_all_iff.2 (fun j => ae_all_iff.2 (fun k => hp j k))
  filter_upwards [ha] with ω hω
  intro j k _
  exact hω j k

end RegretMatching.Approach

open RegretMatching.Approach

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i' : ι) → S i' → ℝ)
    (hσ : ∀ (t : ℕ) (h : Fin t → (∀ i, S i)) (i' : ι), σ t h i' ∈ stdSimplex ℝ (S i'))
    (h31 : ∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)), SatisfiesEq31 u h i (σ (t + 1) h i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : RegretMatching.Main.IsPlay σ P play) :
    ∀ᵐ ω ∂P, ∀ j k : S i, j ≠ k →
      Tendsto (fun t : ℕ => RegretMatching.Main.regretR u (hist play (t + 1) ω) i j k) atTop (𝓝 0) := by
  exact RegretMatching.Approach.theorem_A u i σ hσ h31 Ω P play hplay
