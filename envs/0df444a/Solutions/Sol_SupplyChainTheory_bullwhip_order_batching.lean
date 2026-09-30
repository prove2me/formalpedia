-- Prove2me | solution 1 for SupplyChainTheory.bullwhip_order_batching
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:01:09.429925+00:00
-- url     : https://prove2.me/submissions/18f8351c-e5fc-4b45-a27b-2a34cddd0d63

import Mathlib
import Definitions.Def_SupplyChainTheory_bullwhip

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

section Batch

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {N R : ℕ} {mu sigma : ℝ}

lemma bD_memLp (B : BatchOrders P N R mu sigma) (i : Fin N) (k : Fin R) :
    MemLp (B.D i k) 2 P := by
  have h := memLp_id_gaussianReal' (μ := mu) (v := Real.toNNReal (sigma ^ 2)) 2 (by norm_num)
  rw [← B.D_law i k] at h
  exact (memLp_map_measure_iff h.aestronglyMeasurable (B.measurable_D i k).aemeasurable).mp h

lemma bD_mean (B : BatchOrders P N R mu sigma) (i : Fin N) (k : Fin R) :
    ∫ ω, B.D i k ω ∂P = mu := by
  have h := integral_map (μ := P) (B.measurable_D i k).aemeasurable
    (f := fun x : ℝ => x) aestronglyMeasurable_id
  rw [← h, B.D_law i k, integral_id_gaussianReal]

lemma bD_var (B : BatchOrders P N R mu sigma) (i : Fin N) (k : Fin R) :
    variance (B.D i k) P = sigma ^ 2 := by
  have h := variance_map (X := id) (μ := P) (Y := B.D i k) aemeasurable_id
    (B.measurable_D i k).aemeasurable
  rw [B.D_law i k, variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)] at h
  exact h.symm

lemma bD_sq (B : BatchOrders P N R mu sigma) (i : Fin N) (k : Fin R) :
    ∫ ω, B.D i k ω * B.D i k ω ∂P = sigma ^ 2 + mu ^ 2 := by
  have h := variance_eq_sub (bD_memLp B i k)
  rw [bD_var, bD_mean] at h
  have e : ∫ ω, B.D i k ω * B.D i k ω ∂P = ∫ ω, (B.D i k ^ 2) ω ∂P := by
    congr 1; funext ω; simp [sq]
  rw [e]; linarith

lemma bD_cross (B : BatchOrders P N R mu sigma) (p q : Fin N × Fin R) :
    ∫ ω, B.D p.1 p.2 ω * B.D q.1 q.2 ω ∂P = mu ^ 2 + (if p = q then sigma ^ 2 else 0) := by
  by_cases hpq : p = q
  · subst hpq; rw [if_pos rfl, bD_sq]; ring
  · rw [if_neg hpq, add_zero]
    have hind : IndepFun (B.D p.1 p.2) (B.D q.1 q.2) P := B.D_indep.indepFun hpq
    rw [hind.integral_fun_mul_eq_mul_integral (B.measurable_D _ _).aestronglyMeasurable
      (B.measurable_D _ _).aestronglyMeasurable, bD_mean, bD_mean]
    ring

/-- The order of retailer `i` over the reorder interval. -/
noncomputable def rowSum (B : BatchOrders P N R mu sigma) (i : Fin N) (ω : Ω) : ℝ :=
  ∑ k : Fin R, B.D i k ω

lemma rowSum_memLp (B : BatchOrders P N R mu sigma) (i : Fin N) : MemLp (rowSum B i) 2 P :=
  memLp_finsetSum _ (fun k _ => bD_memLp B i k)

lemma rowSum_meas (B : BatchOrders P N R mu sigma) (i : Fin N) : Measurable (rowSum B i) :=
  Finset.measurable_sum _ (fun k _ => B.measurable_D i k)

lemma rowSum_mean (B : BatchOrders P N R mu sigma) (i : Fin N) :
    ∫ ω, rowSum B i ω ∂P = R * mu := by
  unfold rowSum
  rw [integral_finsetSum _ (fun k _ => (bD_memLp B i k).integrable (by norm_num))]
  simp [bD_mean]

lemma rowSum_cross (B : BatchOrders P N R mu sigma) (i j : Fin N) :
    ∫ ω, rowSum B i ω * rowSum B j ω ∂P =
      (R : ℝ) ^ 2 * mu ^ 2 + (if i = j then R * sigma ^ 2 else 0) := by
  unfold rowSum
  simp_rw [Finset.sum_mul_sum]
  have hint : ∀ k l : Fin R, Integrable (fun ω => B.D i k ω * B.D j l ω) P := fun k l =>
    (bD_memLp B i k).integrable_mul (bD_memLp B j l)
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hint k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hint _ l)]
  have hterm : ∀ k l : Fin R, ∫ ω, B.D i k ω * B.D j l ω ∂P =
      mu ^ 2 + (if i = j ∧ k = l then sigma ^ 2 else 0) := by
    intro k l
    rw [bD_cross B (i, k) (j, l)]
    simp [Prod.mk.injEq]
  simp_rw [hterm]
  by_cases hij : i = j
  · subst hij
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
    ring
  · simp [hij, Finset.sum_add_distrib]
    ring

/-- The indicator that retailer `i` orders. -/
noncomputable def ind (B : BatchOrders P N R mu sigma) (i : Fin N) (ω : Ω) : ℝ :=
  if (i : ℕ) < B.X ω then 1 else 0

lemma ind_meas (B : BatchOrders P N R mu sigma) (i : Fin N) : Measurable (ind B i) := by
  have : ind B i = (fun n : ℕ => if (i : ℕ) < n then (1:ℝ) else 0) ∘ B.X := rfl
  rw [this]; exact measurable_from_nat.comp B.measurable_X

lemma ind_bound (B : BatchOrders P N R mu sigma) (i : Fin N) (ω : Ω) : ‖ind B i ω‖ ≤ 1 := by
  unfold ind; split_ifs <;> simp

lemma ind_integrable (B : BatchOrders P N R mu sigma) (i : Fin N) : Integrable (ind B i) P :=
  Integrable.of_bound (ind_meas B i).aestronglyMeasurable 1 (Filter.Eventually.of_forall
    (ind_bound B i))

lemma ind_sum (B : BatchOrders P N R mu sigma) (ω : Ω) : ∑ i : Fin N, ind B i ω = B.X ω := by
  unfold ind
  rw [Finset.sum_boole]
  have h : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < B.X ω)).map Fin.valEmbedding =
      Finset.range (B.X ω) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx; exact ⟨⟨x, lt_of_lt_of_le hx (B.X_le ω)⟩, hx, rfl⟩
  have := congrArg Finset.card h
  rw [Finset.card_map, Finset.card_range] at this
  rw [this]

lemma ind_indep (B : BatchOrders P N R mu sigma) (i j i' j' : Fin N) :
    IndepFun (fun ω => ind B i ω * ind B j ω) (fun ω => rowSum B i' ω * rowSum B j' ω) P := by
  have hφ : Measurable (fun n : ℕ => (if (i : ℕ) < n then (1:ℝ) else 0) *
      (if (j : ℕ) < n then (1:ℝ) else 0)) := measurable_from_nat
  have hψ : Measurable (fun v : Fin N × Fin R → ℝ => (∑ k : Fin R, v (i', k)) *
      (∑ l : Fin R, v (j', l))) :=
    (Finset.measurable_sum _ fun k _ => measurable_pi_apply (i', k)).mul
      (Finset.measurable_sum _ fun l _ => measurable_pi_apply (j', l))
  exact B.X_indep.comp hφ hψ

lemma ind_indep1 (B : BatchOrders P N R mu sigma) (i : Fin N) :
    IndepFun (ind B i) (rowSum B i) P := by
  have hφ : Measurable (fun n : ℕ => if (i : ℕ) < n then (1:ℝ) else 0) := measurable_from_nat
  have hψ : Measurable (fun v : Fin N × Fin R → ℝ => ∑ k : Fin R, v (i, k)) :=
    Finset.measurable_sum _ fun k _ => measurable_pi_apply (i, k)
  exact B.X_indep.comp hφ hψ

lemma supplierOrder_eq (B : BatchOrders P N R mu sigma) :
    B.supplierOrder = fun ω => ∑ i : Fin N, ind B i ω * rowSum B i ω := by
  funext ω
  unfold BatchOrders.supplierOrder ind rowSum
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma term_memLp (B : BatchOrders P N R mu sigma) (i : Fin N) :
    MemLp (fun ω => ind B i ω * rowSum B i ω) 2 P := by
  refine (rowSum_memLp B i).of_le ((ind_meas B i).mul (rowSum_meas B i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  calc ‖ind B i ω‖ * ‖rowSum B i ω‖ ≤ 1 * ‖rowSum B i ω‖ :=
        mul_le_mul_of_nonneg_right (ind_bound B i ω) (norm_nonneg _)
    _ = ‖rowSum B i ω‖ := one_mul _

theorem batch_moments (B : BatchOrders P N R mu sigma) :
    (∫ ω, B.supplierOrder ω ∂P) = R * mu * ∫ ω, (B.X ω : ℝ) ∂P ∧
    variance B.supplierOrder P = R * sigma ^ 2 * (∫ ω, (B.X ω : ℝ) ∂P) +
      (R : ℝ) ^ 2 * mu ^ 2 * ((∫ ω, (B.X ω : ℝ) ^ 2 ∂P) - (∫ ω, (B.X ω : ℝ) ∂P) ^ 2) := by
  have hEX : ∫ ω, (B.X ω : ℝ) ∂P = ∑ i : Fin N, ∫ ω, ind B i ω ∂P := by
    rw [← integral_finsetSum _ (fun i _ => ind_integrable B i)]
    congr 1; funext ω; rw [ind_sum]
  have hEX2 : ∫ ω, (B.X ω : ℝ) ^ 2 ∂P = ∑ i : Fin N, ∑ j : Fin N, ∫ ω, ind B i ω * ind B j ω ∂P := by
    have hint : ∀ i j : Fin N, Integrable (fun ω => ind B i ω * ind B j ω) P := fun i j =>
      (ind_integrable B j).bdd_mul (ind_meas B i).aestronglyMeasurable
        (Filter.Eventually.of_forall (ind_bound B i))
    simp_rw [← integral_finsetSum _ (fun j _ => hint _ j)]
    rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    congr 1; funext ω
    rw [← Finset.sum_mul_sum, ind_sum, sq]
  have hES : ∫ ω, B.supplierOrder ω ∂P = R * mu * ∫ ω, (B.X ω : ℝ) ∂P := by
    rw [supplierOrder_eq, integral_finsetSum _ (fun i _ => (term_memLp B i).integrable
      (by norm_num)), hEX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(ind_indep1 B i).integral_fun_mul_eq_mul_integral (ind_meas B i).aestronglyMeasurable
      (rowSum_meas B i).aestronglyMeasurable, rowSum_mean]
    ring
  refine ⟨hES, ?_⟩
  have hS2 : MemLp B.supplierOrder 2 P := by
    rw [supplierOrder_eq]
    exact memLp_finsetSum _ (fun i _ => term_memLp B i)
  have hES2 : ∫ ω, B.supplierOrder ω ^ 2 ∂P = (R : ℝ) ^ 2 * mu ^ 2 * ∫ ω, (B.X ω : ℝ) ^ 2 ∂P +
      R * sigma ^ 2 * ∫ ω, (B.X ω : ℝ) ∂P := by
    have hint : ∀ i j : Fin N, Integrable
        (fun ω => (ind B i ω * ind B j ω) * (rowSum B i ω * rowSum B j ω)) P := fun i j =>
      ((rowSum_memLp B i).integrable_mul (rowSum_memLp B j)).bdd_mul
        ((ind_meas B i).mul (ind_meas B j)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [norm_mul]
          calc ‖ind B i ω‖ * ‖ind B j ω‖ ≤ 1 * 1 :=
                mul_le_mul (ind_bound B i ω) (ind_bound B j ω) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1)
    have hpt : ∀ ω, B.supplierOrder ω ^ 2 = ∑ i : Fin N, ∑ j : Fin N,
        (ind B i ω * ind B j ω) * (rowSum B i ω * rowSum B j ω) := by
      intro ω
      rw [supplierOrder_eq, sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hint _ j)]
    have hfac : ∀ i j : Fin N, ∫ ω, (ind B i ω * ind B j ω) * (rowSum B i ω * rowSum B j ω) ∂P
        = (∫ ω, ind B i ω * ind B j ω ∂P) *
          ((R : ℝ) ^ 2 * mu ^ 2 + (if i = j then R * sigma ^ 2 else 0)) := by
      intro i j
      rw [(ind_indep B i j i j).integral_fun_mul_eq_mul_integral
        ((ind_meas B i).mul (ind_meas B j)).aestronglyMeasurable
        ((rowSum_meas B i).mul (rowSum_meas B j)).aestronglyMeasurable, rowSum_cross]
    simp_rw [hfac]
    rw [hEX2, hEX]
    have hdiag : ∀ i : Fin N, ∫ ω, ind B i ω * ind B i ω ∂P = ∫ ω, ind B i ω ∂P := by
      intro i; congr 1; funext ω; unfold ind; split_ifs <;> simp
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hdiag, ← Finset.sum_mul]
    ring
  rw [variance_eq_sub hS2]
  have e1 : ∫ ω, (B.supplierOrder ^ 2) ω ∂P = ∫ ω, B.supplierOrder ω ^ 2 ∂P := rfl
  rw [e1, hES2, hES]
  ring

lemma two_point (B : BatchOrders P N R mu sigma) (a b : ℕ) (hab : a ≠ b)
    (hsum : P.real {ω | B.X ω = a} + P.real {ω | B.X ω = b} = 1) (f : ℕ → ℝ) :
    ∫ ω, f (B.X ω) ∂P = f a * P.real {ω | B.X ω = a} + f b * P.real {ω | B.X ω = b} := by
  have hA : MeasurableSet {ω | B.X ω = a} := B.measurable_X (measurableSet_singleton a)
  have hB : MeasurableSet {ω | B.X ω = b} := B.measurable_X (measurableSet_singleton b)
  have hdisj : Disjoint {ω | B.X ω = a} {ω | B.X ω = b} := by
    rw [Set.disjoint_left]; intro ω h1 h2; exact hab (h1.symm.trans h2)
  have hunion : P.real ({ω | B.X ω = a} ∪ {ω | B.X ω = b}) = 1 := by
    rw [measureReal_union hdisj hB, hsum]
  have hone : P ({ω | B.X ω = a} ∪ {ω | B.X ω = b}) = 1 := by
    have h1 : (P ({ω | B.X ω = a} ∪ {ω | B.X ω = b})).toReal = 1 := hunion
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _), h1, ENNReal.ofReal_one]
  have hnull : P ({ω | B.X ω = a} ∪ {ω | B.X ω = b})ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (hA.union hB), hone, tsub_self]
  have hae : (fun ω => f (B.X ω)) =ᵐ[P] fun ω => f a * ({ω | B.X ω = a}.indicator 1 ω) +
      f b * ({ω | B.X ω = b}.indicator 1 ω) := by
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null _ hnull
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or]
    constructor
    · intro h; apply hω; simp [Set.indicator_apply, h, hab]
    · intro h; apply hω; simp [Set.indicator_apply, h, Ne.symm hab]
  have iA : Integrable (fun ω => f a * ({ω | B.X ω = a}.indicator 1 ω)) P :=
    ((integrable_const (1:ℝ)).indicator hA).const_mul _
  have iB : Integrable (fun ω => f b * ({ω | B.X ω = b}.indicator 1 ω)) P :=
    ((integrable_const (1:ℝ)).indicator hB).const_mul _
  rw [integral_congr_ae hae, integral_add iA iB, integral_const_mul, integral_const_mul,
    integral_indicator_one hA, integral_indicator_one hB]

lemma range_moment (B : BatchOrders P N R mu sigma) (f : ℕ → ℝ) :
    ∫ ω, f (B.X ω) ∂P = ∑ j ∈ Finset.range (N + 1), f j * P.real {ω | B.X ω = j} := by
  have hA : ∀ j : ℕ, MeasurableSet {ω | B.X ω = j} :=
    fun j => B.measurable_X (measurableSet_singleton j)
  have hpt : ∀ ω, f (B.X ω) = ∑ j ∈ Finset.range (N + 1), f j * ({ω | B.X ω = j}.indicator 1 ω) := by
    intro ω
    rw [Finset.sum_eq_single (B.X ω)]
    · simp [Set.indicator_apply]
    · intro j _ hj
      simp [Set.indicator_apply, Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (B.X_le ω))) h
  have hint : ∀ j : ℕ, Integrable (fun ω => f j * ({ω | B.X ω = j}.indicator 1 ω)) P :=
    fun j => ((integrable_const (1:ℝ)).indicator (hA j)).const_mul _
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_indicator_one (hA j)]

lemma binom_fact1 (n : ℕ) (p q : ℝ) :
    ∑ j ∈ Finset.range (n + 2), (j : ℝ) * ((n + 1).choose j * p ^ j * q ^ (n + 1 - j)) =
      (n + 1) * p * (p + q) ^ n := by
  rw [Finset.sum_range_succ', add_pow, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ((n + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1) = (n + 1) * n.choose i := by
    have := Nat.add_one_mul_choose_eq n i
    exact_mod_cast this.symm
  rw [show n + 1 - (i + 1) = n - i by omega]
  push_cast
  calc ((i : ℝ) + 1) * ((n + 1).choose (i + 1) * p ^ (i + 1) * q ^ (n - i))
      = ((n + 1).choose (i + 1) * ((i : ℝ) + 1)) * p ^ (i + 1) * q ^ (n - i) := by ring
    _ = (n + 1) * p * (p ^ i * q ^ (n - i) * n.choose i) := by rw [hc]; ring

lemma binom_fact2 (n : ℕ) (p q : ℝ) :
    ∑ j ∈ Finset.range (n + 3), (j : ℝ) * ((j : ℝ) - 1) *
      ((n + 2).choose j * p ^ j * q ^ (n + 2 - j)) = (n + 2) * (n + 1) * p ^ 2 * (p + q) ^ n := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ', add_pow, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one, sub_self, mul_zero,
    zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have hc1 : ((n + 2).choose (i + 2) : ℝ) * ((i : ℝ) + 2) = (n + 2) * (n + 1).choose (i + 1) := by
    have h := Nat.add_one_mul_choose_eq (n + 1) (i + 1)
    have h' : (n + 2) * (n + 1).choose (i + 1) = (n + 2).choose (i + 2) * (i + 2) := h
    exact_mod_cast h'.symm
  have hc2 : ((n + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1) = (n + 1) * n.choose i := by
    have := Nat.add_one_mul_choose_eq n i
    exact_mod_cast this.symm
  rw [show n + 2 - (i + 1 + 1) = n - i by omega]
  push_cast
  calc ((i : ℝ) + 1 + 1) * ((i : ℝ) + 1 + 1 - 1) *
        ((n + 2).choose (i + 1 + 1) * p ^ (i + 1 + 1) * q ^ (n - i))
      = (((n + 2).choose (i + 2) : ℝ) * ((i : ℝ) + 2)) * ((i : ℝ) + 1) * p ^ (i + 2) *
          q ^ (n - i) := by ring_nf
    _ = (n + 2) * (((n + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1)) * p ^ (i + 2) * q ^ (n - i) := by
        rw [hc1]; ring
    _ = (n + 2) * (n + 1) * p ^ 2 * (p ^ i * q ^ (n - i) * n.choose i) := by rw [hc2]; ring

lemma binom_mean (N : ℕ) (p q : ℝ) (hpq : p + q = 1) :
    ∑ j ∈ Finset.range (N + 1), (j : ℝ) * (N.choose j * p ^ j * q ^ (N - j)) = N * p := by
  rcases N with _ | n
  · simp
  · rw [binom_fact1, hpq, one_pow, mul_one]; push_cast; ring

lemma binom_sq (N : ℕ) (p q : ℝ) (hpq : p + q = 1) :
    ∑ j ∈ Finset.range (N + 1), (j : ℝ) ^ 2 * (N.choose j * p ^ j * q ^ (N - j)) =
      N * (N - 1) * p ^ 2 + N * p := by
  have hsplit : ∀ j : ℕ, (j : ℝ) ^ 2 * (N.choose j * p ^ j * q ^ (N - j)) =
      (j : ℝ) * ((j : ℝ) - 1) * (N.choose j * p ^ j * q ^ (N - j)) +
        (j : ℝ) * (N.choose j * p ^ j * q ^ (N - j)) := fun j => by ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, binom_mean N p q hpq]
  rcases N with _ | _ | n
  · simp
  · simp [Finset.sum_range_succ]
  · rw [binom_fact2, hpq, one_pow, mul_one]; push_cast; ring

theorem correlated_main (B : BatchOrders P N R mu sigma) (hR : 0 < R)
    (hX0 : P.real {ω | B.X ω = 0} = 1 - 1 / R) (hXN : P.real {ω | B.X ω = N} = 1 / R) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ variance B.supplierOrder P = N * sigma ^ 2 + mu ^ 2 * (N : ℝ) ^ 2 * (R - 1) := by
  have hRR : (0:ℝ) < R := by exact_mod_cast hR
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exfalso
    subst hN0
    have huniv : {ω | B.X ω = 0} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact Nat.le_zero.mp (B.X_le ω)
    rw [huniv, probReal_univ] at hX0 hXN
    linarith
  have hne : (0:ℕ) ≠ N := by omega
  have hsum : P.real {ω | B.X ω = 0} + P.real {ω | B.X ω = N} = 1 := by rw [hX0, hXN]; ring
  have hE1 := two_point B 0 N hne hsum (fun j => (j : ℝ))
  have hE2 := two_point B 0 N hne hsum (fun j => (j : ℝ) ^ 2)
  simp only [Nat.cast_zero, zero_mul, zero_add, hXN] at hE1 hE2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add] at hE2
  obtain ⟨hm, hv⟩ := batch_moments B
  refine ⟨?_, ?_⟩
  · rw [hm, hE1]; field_simp
  · rw [hv, hE1, hE2]; field_simp

theorem balanced_main (B : BatchOrders P N R mu sigma) (hR : 0 < R) (M k : ℕ) (hk : k < R)
    (hN : N = M * R + k) (hXM : P.real {ω | B.X ω = M} = 1 - k / R)
    (hXM1 : P.real {ω | B.X ω = M + 1} = k / R) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ variance B.supplierOrder P = N * sigma ^ 2 + mu ^ 2 * k * (R - k) := by
  have hRR : (0:ℝ) < R := by exact_mod_cast hR
  have hne : M ≠ M + 1 := by omega
  have hsum : P.real {ω | B.X ω = M} + P.real {ω | B.X ω = M + 1} = 1 := by
    rw [hXM, hXM1]; ring
  have hE1 := two_point B M (M + 1) hne hsum (fun j => (j : ℝ))
  have hE2 := two_point B M (M + 1) hne hsum (fun j => (j : ℝ) ^ 2)
  simp only [hXM, hXM1] at hE1 hE2
  obtain ⟨hm, hv⟩ := batch_moments B
  have hNR : (N : ℝ) = M * R + k := by rw [hN]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hm, hE1, hNR]; push_cast; field_simp; ring
  · rw [hv, hE1, hE2, hNR]; push_cast; field_simp; ring

theorem random_main (B : BatchOrders P N R mu sigma) (hR : 0 < R)
    (hX : ∀ j : ℕ, P.real {ω | B.X ω = j}
      = (Nat.choose N j : ℝ) * (1 / R) ^ j * (1 - 1 / R) ^ (N - j)) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ variance B.supplierOrder P = N * sigma ^ 2 + mu ^ 2 * N * (R - 1) := by
  have hRR : (0:ℝ) < R := by exact_mod_cast hR
  have hpq : (1 / (R : ℝ)) + (1 - 1 / R) = 1 := by ring
  have hE1 : ∫ ω, (B.X ω : ℝ) ∂P = N * (1 / R) := by
    rw [range_moment B (fun j => (j : ℝ))]
    simp_rw [hX]
    exact binom_mean N _ _ hpq
  have hE2 : ∫ ω, (B.X ω : ℝ) ^ 2 ∂P = N * (N - 1) * (1 / R) ^ 2 + N * (1 / R) := by
    rw [range_moment B (fun j => (j : ℝ) ^ 2)]
    simp_rw [hX]
    exact binom_sq N _ _ hpq
  obtain ⟨hm, hv⟩ := batch_moments B
  refine ⟨?_, ?_⟩
  · rw [hm, hE1]; field_simp
  · rw [hv, hE1, hE2]; field_simp; ring

theorem batching_main (hN : 0 < N) (hR : 0 < R)
    (Br Bc Bb : BatchOrders P N R mu sigma)
    (hXr : ∀ j : ℕ, P.real {ω | Br.X ω = j}
      = (Nat.choose N j : ℝ) * (1 / R) ^ j * (1 - 1 / R) ^ (N - j))
    (hXc0 : P.real {ω | Bc.X ω = 0} = 1 - 1 / R) (hXcN : P.real {ω | Bc.X ω = N} = 1 / R)
    (M k : ℕ) (hk : k < R) (hNMk : N = M * R + k)
    (hXbM : P.real {ω | Bb.X ω = M} = 1 - k / R)
    (hXbM1 : P.real {ω | Bb.X ω = M + 1} = k / R) :
    ((∫ ω, Bc.supplierOrder ω ∂P) = N * mu ∧ (∫ ω, Br.supplierOrder ω ∂P) = N * mu
        ∧ (∫ ω, Bb.supplierOrder ω ∂P) = N * mu)
      ∧ (variance Br.supplierOrder P ≤ variance Bc.supplierOrder P
          ∧ variance Bb.supplierOrder P ≤ variance Br.supplierOrder P
          ∧ N * sigma ^ 2 ≤ variance Bb.supplierOrder P) := by
  obtain ⟨mr, vr⟩ := random_main Br hR hXr
  obtain ⟨mc, vc⟩ := correlated_main Bc hR hXc0 hXcN
  obtain ⟨mb, vb⟩ := balanced_main Bb hR M k hk hNMk hXbM hXbM1
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hR1 : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hkR : (k:ℝ) + 1 ≤ R := by exact_mod_cast hk
  have hkN : (k:ℝ) ≤ N := by
    have : k ≤ N := by rw [hNMk]; exact Nat.le_add_left k (M * R)
    exact_mod_cast this
  refine ⟨⟨mc, mr, mb⟩, ?_, ?_, ?_⟩
  · rw [vr, vc]
    have h1 : (N : ℝ) * (R - 1) ≤ (N : ℝ) ^ 2 * (R - 1) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg mu)
    nlinarith
  · rw [vb, vr]
    have h1 : (k : ℝ) * (R - k) ≤ N * (R - 1) := by
      rcases Nat.eq_zero_or_pos k with hk0' | hkpos
      · subst hk0'
        simp only [Nat.cast_zero, zero_mul]
        exact mul_nonneg (by linarith) (by linarith)
      · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
        nlinarith [mul_nonneg (sub_nonneg.mpr hk1) hk0,
          mul_nonneg (sub_nonneg.mpr hkN) (sub_nonneg.mpr hR1)]
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg mu)
    nlinarith
  · rw [vb]
    have : 0 ≤ mu ^ 2 * k * (R - k) :=
      mul_nonneg (mul_nonneg (sq_nonneg mu) hk0) (by linarith)
    linarith

end Batch

end SupplyChainTheory

open SupplyChainTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hN : 0 < N) (hR : 0 < R)
    (Br Bc Bb : BatchOrders P N R mu sigma)
    (hXr : ∀ j : ℕ, P.real {ω | Br.X ω = j}
      = (Nat.choose N j : ℝ) * (1 / R) ^ j * (1 - 1 / R) ^ (N - j))
    (hXc0 : P.real {ω | Bc.X ω = 0} = 1 - 1 / R) (hXcN : P.real {ω | Bc.X ω = N} = 1 / R)
    (M k : ℕ) (hk : k < R) (hNMk : N = M * R + k)
    (hXbM : P.real {ω | Bb.X ω = M} = 1 - k / R)
    (hXbM1 : P.real {ω | Bb.X ω = M + 1} = k / R) :
    ((∫ ω, Bc.supplierOrder ω ∂P) = N * mu ∧ (∫ ω, Br.supplierOrder ω ∂P) = N * mu
        ∧ (∫ ω, Bb.supplierOrder ω ∂P) = N * mu)
      ∧ (ProbabilityTheory.variance Br.supplierOrder P
            ≤ ProbabilityTheory.variance Bc.supplierOrder P
          ∧ ProbabilityTheory.variance Bb.supplierOrder P
            ≤ ProbabilityTheory.variance Br.supplierOrder P
          ∧ N * sigma ^ 2 ≤ ProbabilityTheory.variance Bb.supplierOrder P) := by
  exact batching_main hN hR Br Bc Bb hXr hXc0 hXcN M k hk hNMk hXbM hXbM1
