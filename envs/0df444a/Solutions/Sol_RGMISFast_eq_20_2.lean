-- Prove2me | solution 2 for RGMISFast.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T03:08:58.104368+00:00
-- url     : https://prove2.me/submissions/10bc5940-36e8-480a-9294-b4ebb3398462

import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw
import Mathlib
set_option maxHeartbeats 1000000

-- Source: Solutions.ExponentialArrivals
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ExponentialArrivals
open Classical
instance expOne_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)
instance expOne_nullSingleton : NullSingletonClass (expMeasure 1) := by
  unfold expMeasure gammaMeasure
  infer_instance

lemma expOne_real_Iio (s : ℝ) (hs : 0 ≤ s) :
    (expMeasure 1).real (Set.Iio s) = 1 - Real.exp (-s) := by
  rw [measureReal_def, measure_congr Iio_ae_eq_Iic, ← measureReal_def,
    ← cdf_eq_real, cdf_expMeasure_eq (by norm_num), if_pos hs]
  simp only [one_mul]
lemma expOne_real_Ici (s : ℝ) (hs : 0 ≤ s) :
    (expMeasure 1).real (Set.Ici s) = Real.exp (-s) := by
  rw [← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio, expOne_real_Iio s hs]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def retainedVertices (S : Finset V) (s : ℝ) (r : V → ℝ) : Finset V :=
  S.filter (fun v => r v < s)
omit [DecidableEq V] in
theorem measurableSet_retainedVertices_eq (S T : Finset V) (b : ℝ) :
    MeasurableSet {u : V → ℝ | retainedVertices S b u = T} := by
  have heq : {u : V → ℝ | retainedVertices S b u = T} =
      {u : V → ℝ | ∀ v, (v ∈ S ∧ u v < b) ↔ v ∈ T} := by
    ext u
    simp [Finset.ext_iff, retainedVertices]
  rw [heq]
  apply Measurable.setOf
  apply Measurable.forall
  intro v
  exact (measurable_const.and ((measurable_pi_apply v).lt measurable_const)).iff
    measurable_const

omit [Fintype V] [DecidableEq V] in
theorem measurable_retainedVertices_card (S : Finset V) (b : ℝ) :
    Measurable (fun u : V → ℝ => (retainedVertices S b u).card) := by
  have heq : (fun u : V → ℝ => (retainedVertices S b u).card) =
      fun u => ∑ v ∈ S, if u v < b then (1 : ℕ) else 0 := by
    funext u
    simp only [retainedVertices, Finset.card_filter]
  rw [heq]
  apply Finset.measurable_sum
  intro v _
  exact Measurable.ite ((measurable_pi_apply v).lt measurable_const).setOf
    measurable_const measurable_const

omit [Fintype V] in
theorem retainedVertices_eq_pi (S T : Finset V) (hTS : T ⊆ S) (b : ℝ) :
    {u : V → ℝ | retainedVertices S b u = T} =
      (S : Set V).pi (fun v => if v ∈ T then Set.Iio b else Set.Ici b) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe]
  constructor
  · intro heq v hv
    by_cases hvT : v ∈ T
    · have hmem : v ∈ retainedVertices S b u := heq.symm ▸ hvT
      simpa [hvT] using (Finset.mem_filter.mp hmem).2
    · simp only [hvT, ↓reduceIte, Set.mem_Ici]
      by_contra h
      exact hvT (heq ▸ Finset.mem_filter.mpr ⟨hv, lt_of_not_ge h⟩)
  · intro h
    apply Finset.ext
    intro v
    simp only [retainedVertices, Finset.mem_filter]
    constructor
    · rintro ⟨hvS, hvb⟩
      by_contra hvT
      have hge : b ≤ u v := by simpa [hvT] using h v hvS
      exact (not_lt_of_ge hge) hvb
    · intro hvT
      exact ⟨hTS hvT, by simpa [hvT] using h v (hTS hvT)⟩


theorem measure_retainedVertices_eq (S T : Finset V) (hTS : T ⊆ S)
    (s : ℝ) (hs : 0 ≤ s) :
    Measure.pi (fun _ : V => expMeasure 1) {u | retainedVertices S s u = T} =
      ENNReal.ofReal (1 - Real.exp (-s)) ^ T.card *
        ENNReal.ofReal (Real.exp (-s)) ^ (S.card - T.card) := by
  rw [retainedVertices_eq_pi S T hTS s, Measure.pi_pi_finset]
  have hlo : expMeasure 1 (Set.Iio s) = ENNReal.ofReal (1 - Real.exp (-s)) := by
    rw [← ofReal_measureReal, expOne_real_Iio s hs]
  have hhi : expMeasure 1 (Set.Ici s) = ENNReal.ofReal (Real.exp (-s)) := by
    rw [← ofReal_measureReal, expOne_real_Ici s hs]
  simp only [apply_ite,hlo,hhi]
  rw [Finset.prod_ite]
  have hfilter : S.filter (fun v => v ∈ T) = T := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨hTS hv,hv⟩⟩
  rw [hfilter, ← Finset.sdiff_eq_filter]
  simp [Finset.card_sdiff,Finset.inter_eq_left.mpr hTS]

theorem measureReal_retainedVertices_eq (S T : Finset V) (hTS : T ⊆ S)
    (s : ℝ) (hs : 0 ≤ s) :
    (Measure.pi (fun _ : V => expMeasure 1)).real {u | retainedVertices S s u = T} =
      (1 - Real.exp (-s)) ^ T.card * Real.exp (-s) ^ (S.card - T.card) := by
  have hp : 0 ≤ 1 - Real.exp (-s) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  rw [measureReal_def,measure_retainedVertices_eq S T hTS s hs,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal (Real.exp_pos _).le]
/-- The cardinality of the retained set has the binomial distribution. -/
theorem measureReal_retainedVertices_card (S : Finset V) (j : ℕ)
    (b : ℝ) (hb : 0 ≤ b) :
    (Measure.pi (fun _ : V => expMeasure 1)).real
      {u | (retainedVertices S b u).card = j} =
      (S.card.choose j : ℝ) * (1 - Real.exp (-b)) ^ j *
        Real.exp (-b) ^ (S.card - j) := by
  have heq : {u : V → ℝ | (retainedVertices S b u).card = j} =
      ⋃ T ∈ S.powersetCard j, {u | retainedVertices S b u = T} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard]
    constructor
    · intro hcard
      exact ⟨retainedVertices S b u, ⟨Finset.filter_subset _ _, hcard⟩, rfl⟩
    · rintro ⟨T, ⟨_, hT⟩, hEq⟩
      simpa [hEq] using hT
  rw [heq, measureReal_biUnion_finset]
  · calc
      _ = ∑ _T ∈ S.powersetCard j,
          (1 - Real.exp (-b)) ^ j *
            Real.exp (-b) ^ (S.card - j) := by
        apply Finset.sum_congr rfl
        intro T hT
        rcases Finset.mem_powersetCard.mp hT with ⟨hTS, hcard⟩
        rw [measureReal_retainedVertices_eq S T hTS b hb, hcard]
      _ = _ := by simp [mul_assoc]
  · intro T _ U _ hTU
    apply Set.disjoint_left.mpr
    intro u huT huU
    exact hTU (huT.symm.trans huU)
  · intro T _
    exact measurableSet_retainedVertices_eq S T b


end ExponentialArrivals

-- Source: Solutions.PermutationSymmetry
namespace ArrivalSymmetry
open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- Relabel independent rank coordinates by a finite permutation. -/
def coordinatePermutation (σ : Equiv.Perm V) : (V → ℝ) ≃ᵐ (V → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) σ.symm

@[simp] theorem coordinatePermutation_apply (σ : Equiv.Perm V) (r : V → ℝ) (v : V) :
    coordinatePermutation σ r v = r (σ v) := by
  simp [coordinatePermutation, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem coordinatePermutation_measurePreserving (σ : Equiv.Perm V) :
    MeasurePreserving (coordinatePermutation σ)
      (Measure.pi (fun _ : V => μ))
      (Measure.pi (fun _ : V => μ)) :=
  measurePreserving_piCongrLeft (fun _ : V => μ) σ.symm

theorem integral_coordinatePermutation (σ : Equiv.Perm V) (F : (V → ℝ) → ℝ) :
    (∫ r, F (coordinatePermutation σ r) ∂Measure.pi (fun _ => μ)) =
      ∫ r, F r ∂Measure.pi (fun _ => μ) :=
  (coordinatePermutation_measurePreserving μ σ).integral_comp
    (coordinatePermutation σ).measurableEmbedding F

/-- Pointwise uniform average over all coordinate permutations. -/
noncomputable def permutationAverage (F : (V → ℝ) → ℝ) (r : V → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm V, F (coordinatePermutation σ r)) / Fintype.card (Equiv.Perm V)

theorem integral_permutationAverage (F : (V → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun _ : V => μ))) :
    (∫ r, permutationAverage F r ∂Measure.pi (fun _ => μ)) =
      ∫ r, F r ∂Measure.pi (fun _ => μ) := by
  have hcomp (σ : Equiv.Perm V) :
      Integrable (fun r => F (coordinatePermutation σ r))
        (Measure.pi (fun _ : V => μ)) :=
    ((coordinatePermutation_measurePreserving μ σ).integrable_comp hF.aestronglyMeasurable).mpr hF
  unfold permutationAverage
  rw [integral_div, integral_finsetSum _ (fun σ _ => hcomp σ)]
  simp_rw [integral_coordinatePermutation μ]
  have hn : (Fintype.card (Equiv.Perm V) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hn

/-- Averaging over permutations may be replaced by an a.e. identified statistic. -/
theorem integral_eq_of_permutationAverage_ae (F H : (V → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun _ : V => μ)))
    (havg : permutationAverage F =ᵐ[Measure.pi (fun _ : V => μ)] H) :
    (∫ r, F r ∂Measure.pi (fun _ => μ)) =
      ∫ r, H r ∂Measure.pi (fun _ => μ) := by
  rw [← integral_permutationAverage μ F hF]
  exact integral_congr_ae havg

/-- Finite-range expectation written using the actual masses of its level sets. -/
theorem integral_comp_nat_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → ℕ) (hK : Measurable K)
    (n : ℕ) (hKn : ∀ ω, K ω ≤ n) (g : ℕ → ℝ) :
    (∫ ω, g (K ω) ∂μ) =
      ∑ j ∈ Finset.range (n + 1), μ.real {ω | K ω = j} * g j := by
  classical
  have heq (ω : Ω) : g (K ω) =
      ∑ j ∈ Finset.range (n + 1), if K ω = j then g j else 0 := by
    simp [eq_comm, Finset.mem_range.mpr (Nat.lt_succ_of_le (hKn ω))]
  have hmeas (j : ℕ) : MeasurableSet {ω | K ω = j} :=
    (hK.eq measurable_const).setOf
  have hf (j : ℕ) : (fun ω => if K ω = j then g j else 0) =
      ({ω | K ω = j}).indicator (fun _ => g j) := by
    funext ω
    simp [Set.indicator]
  have hint (j : ℕ) : Integrable (fun ω => if K ω = j then g j else 0) μ := by
    rw [hf]
    exact (integrable_const (μ := μ) (g j)).indicator (hmeas j)
  simp_rw [heq]
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hf]
  rw [integral_indicator (hmeas j), integral_const]
  simp [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]


end ArrivalSymmetry

-- Source: Solutions.ArrivalOrder
open MeasureTheory ProbabilityTheory
namespace ArrivalOrder
open Classical ExponentialArrivals ArrivalSymmetry
/-- Number of raw coordinates strictly below a threshold. -/
noncomputable def rankArrivalCount {V : Type*} [Fintype V] (raw : V → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun v => raw v < t).card

theorem rankArrivalCount_le {V : Type*} [Fintype V] (raw : V → ℝ) (t : ℝ) :
    rankArrivalCount raw t ≤ Fintype.card V := Finset.card_le_univ _

/-- The increasing enumeration of an injective finite rank assignment. -/
noncomputable def sortedRankEquiv {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) : Fin n ≃ V := by
  letI := LinearOrder.lift' raw hinj
  exact (Fintype.orderIsoFinOfCardEq V (by simpa using Fintype.card_congr e.symm)).toEquiv

theorem sortedRankEquiv_strictMono {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) :
    StrictMono (fun i => raw (sortedRankEquiv e raw hinj i)) := by
  letI := LinearOrder.lift' raw hinj
  exact (Fintype.orderIsoFinOfCardEq V
    (by simpa using Fintype.card_congr e.symm)).strictMono

theorem rankArrivalCount_le_of_equiv {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (t : ℝ) : rankArrivalCount raw t ≤ n := by
  have hcard : Fintype.card V = n := by simpa using Fintype.card_congr e.symm
  simpa [hcard] using rankArrivalCount_le raw t

/-- In increasing rank order, precisely the first `rankArrivalCount` positions have arrived. -/
theorem sortedRankEquiv_lt_iff {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) (t : ℝ) (i : Fin n) :
    i.val < rankArrivalCount raw t ↔ raw (sortedRankEquiv e raw hinj i) < t := by
  have hcard : (Finset.univ.filter fun j : Fin n =>
      raw (sortedRankEquiv e raw hinj j) < t).card = rankArrivalCount raw t := by
    apply Finset.card_equiv (sortedRankEquiv e raw hinj)
    intro j
    simp
  rw [← hcard]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  exact ((sortedRankEquiv_strictMono e raw hinj).monotone hba).trans_lt ha


section
variable {V : Type*} [Fintype V]
theorem ae_rawRanks_distinct {v w : V} (hvw : v ≠ w) :
    ∀ᵐ r : V → ℝ ∂Measure.pi (fun _ => (expMeasure 1)), r v ≠ r w := by
  have hind : IndepFun (fun r : V → ℝ => r v) (fun r : V → ℝ => r w)
      (Measure.pi (fun _ => (expMeasure 1))) :=
    (iIndepFun_pi (μ := fun _ : V => (expMeasure 1))
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hvw
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply v).aemeasurable (measurable_pi_apply w).aemeasurable
  rw [(measurePreserving_eval (fun _ : V => (expMeasure 1)) v).map_eq,
    (measurePreserving_eval (fun _ : V => (expMeasure 1)) w).map_eq] at hmap
  have hpair : ∀ᵐ z ∂(expMeasure 1).prod (expMeasure 1), z.1 ≠ z.2 := by
    rw [ae_iff]
    simp only [not_not]
    apply Measure.measure_prod_null_of_ae_null
    · exact measurableSet_eq_fun
        (measurable_fst : Measurable (fun z : ℝ × ℝ => z.1)) measurable_snd
    · filter_upwards [] with x
      change (expMeasure 1) {y : ℝ | x = y} = 0
      simp
  apply ae_of_ae_map (μ := Measure.pi (fun _ : V => (expMeasure 1)))
    (f := fun r : V → ℝ => (r v, r w)) (p := fun z : ℝ × ℝ => z.1 ≠ z.2)
    ((measurable_pi_apply v).prodMk (measurable_pi_apply w)).aemeasurable
  rw [hmap]
  exact hpair

theorem ae_rawRanks_injective :
    ∀ᵐ r : V → ℝ ∂Measure.pi (fun _ => (expMeasure 1)), Function.Injective r := by
  apply Filter.eventually_all.mpr
  intro v
  apply Filter.eventually_all.mpr
  intro w
  by_cases h : v = w
  · exact Filter.Eventually.of_forall (fun _ _ => h)
  · filter_upwards [ae_rawRanks_distinct h] with r hr heq
    exact (hr heq).elim


end
end ArrivalOrder

-- Source: Solutions.ArrivalPolynomial
namespace ArrivalPolynomial
open scoped BigOperators
open Set

noncomputable def arrivalWeight (n j : ℕ) (t : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n j).eval t

theorem arrivalWeight_formula (n j : ℕ) (t : ℝ) :
    arrivalWeight n j t = (n.choose j : ℝ) * t ^ j * (1 - t) ^ (n - j) := by
  simp [arrivalWeight, bernsteinPolynomial]

theorem arrivalWeight_nonneg (n j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    0 ≤ arrivalWeight n j t := by
  rw [arrivalWeight_formula]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)

theorem arrivalWeight_sum (n : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (n + 1), arrivalWeight n j t) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ ↦ p.eval t) (bernsteinPolynomial.sum ℝ n)
  simpa [arrivalWeight, Polynomial.eval_finsetSum] using h

theorem arrivalWeight_eq_zero_of_lt (n j : ℕ) (t : ℝ) (h : n < j) :
    arrivalWeight n j t = 0 := by
  simp [arrivalWeight, bernsteinPolynomial.eq_zero_of_lt ℝ h]

theorem hasDerivAt_arrivalWeight_zero (n : ℕ) (t : ℝ) :
    HasDerivAt (arrivalWeight n 0) (-(n : ℝ) * arrivalWeight (n - 1) 0 t) t := by
  have h := (bernsteinPolynomial ℝ n 0).hasDerivAt t
  rw [bernsteinPolynomial.derivative_zero] at h
  convert! h using 1
  simp [arrivalWeight]

theorem hasDerivAt_arrivalWeight_succ (n j : ℕ) (t : ℝ) :
    HasDerivAt (arrivalWeight (n + 1) (j + 1))
      (((n : ℝ) + 1) * (arrivalWeight n j t - arrivalWeight n (j + 1) t)) t := by
  have h := (bernsteinPolynomial ℝ (n + 1) (j + 1)).hasDerivAt t
  rw [bernsteinPolynomial.derivative_succ_aux] at h
  convert! h using 1
  simp [arrivalWeight]

noncomputable def arrivalMixture (n : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * g j

/-- The derivative is the Bernstein mixture of successive differences. -/
theorem hasDerivAt_arrivalMixture_succ (n : ℕ) (g : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (arrivalMixture (n + 1) g)
      (((n : ℝ) + 1) *
        ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * (g (j + 1) - g j)) t := by
  have htail : HasDerivAt
      (fun t ↦ ∑ j ∈ Finset.range (n + 1), arrivalWeight (n + 1) (j + 1) t * g (j + 1))
      (∑ j ∈ Finset.range (n + 1),
        (((n : ℝ) + 1) * (arrivalWeight n j t - arrivalWeight n (j + 1) t)) * g (j + 1)) t := by
    convert! HasDerivAt.sum
      (fun j (_hj : j ∈ Finset.range (n + 1)) ↦
        (hasDerivAt_arrivalWeight_succ n j t).mul_const (g (j + 1))) using 1
    ext x
    simp only [Finset.sum_apply]
  have hhead := (hasDerivAt_arrivalWeight_zero (n + 1) t).mul_const (g 0)
  have htotal := htail.add hhead
  have hshift :
      (∑ j ∈ Finset.range (n + 1), arrivalWeight n (j + 1) t * g (j + 1)) +
        arrivalWeight n 0 t * g 0 =
      ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * g j := by
    rw [← Finset.sum_range_succ' (fun j ↦ arrivalWeight n j t * g j) (n + 1),
      Finset.sum_range_succ]
    rw [arrivalWeight_eq_zero_of_lt n (n + 1) t (Nat.lt_succ_self n)]
    ring
  convert! htotal using 1
  · ext x
    exact Finset.sum_range_succ' (fun j ↦ arrivalWeight (n + 1) j x * g j) (n + 1)
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    have hm := congrArg (fun z : ℝ ↦ ((n : ℝ) + 1) * z) hshift
    nlinarith

/-- The change from `n-1` to `n` Bernstein weights is exactly the number of
unarrived coordinates times the remaining-time factor. -/
theorem arrivalWeight_step_identity (n j : ℕ) (t : ℝ) (hj : j ≤ n) :
    ((n + 1 - j : ℕ) : ℝ) * arrivalWeight (n + 1) j t =
      ((n : ℝ) + 1) * (1 - t) * arrivalWeight n j t := by
  have hchoose : ((n + 1 - j : ℕ) : ℝ) * ((n + 1).choose j : ℝ) =
      ((n : ℝ) + 1) * (n.choose j : ℝ) := by
    have h := congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.choose_mul_succ_eq n j)
    push_cast at h
    nlinarith [h]
  have hsub : n + 1 - j = (n - j) + 1 := by omega
  rw [arrivalWeight_formula, arrivalWeight_formula, hsub, pow_succ]
  calc
    _ = (((n - j + 1 : ℕ) : ℝ) * ((n + 1).choose j : ℝ)) *
        (t ^ j * (1 - t) ^ (n - j) * (1 - t)) := by ring
    _ = (((n : ℝ) + 1) * (n.choose j : ℝ)) *
        (t ^ j * (1 - t) ^ (n - j) * (1 - t)) := by rw [← hsub, hchoose]
    _ = _ := by ring

noncomputable def arrivalDrift (n : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, arrivalWeight n j t * ((n - j : ℕ) : ℝ) * (g j - g (j + 1))

/-- The actual derivative identity in arrival-hazard form. -/
theorem hasDerivAt_arrivalMixture (n : ℕ) (g : ℕ → ℝ) (t : ℝ)
    (hn : 0 < n) (ht : t ≠ 1) :
    HasDerivAt (arrivalMixture n g) (-arrivalDrift n g t / (1 - t)) t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  convert! hasDerivAt_arrivalMixture_succ m g t using 1
  dsimp [arrivalDrift]
  rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hweight := arrivalWeight_step_identity m j t (by simp only [Finset.mem_range] at hj; omega)
  have htne : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply (div_eq_iff htne).mpr
  have hm := congrArg (fun z : ℝ ↦ z * (g j - g (j + 1))) hweight
  nlinarith [hm]


end ArrivalPolynomial

-- Source: Solutions.OrderMixture
open MeasureTheory ProbabilityTheory
namespace OrderMixture
open Classical ArrivalSymmetry ArrivalOrder ExponentialArrivals ArrivalPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
noncomputable def representative (e : Fin n ≃ V) (σ : Equiv.Perm V) : V → ℝ :=
  fun v => ((e.symm (σ v)).val : ℝ)
noncomputable def profile (e : Fin n ≃ V) (H : ℝ → (V → ℝ) → ℝ) (j : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm V, H (j : ℝ) (representative e σ)) / Fintype.card (Equiv.Perm V)

def PrefixInvariant (H : ℝ → (V → ℝ) → ℝ) : Prop :=
  ∀ r q s t,
    (∀ v, r v < s ↔ q v < t) →
    (∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) →
    H s r = H t q

theorem permutation_average_eq_profile (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (r : V → ℝ) (hr : Function.Injective r) (s : ℝ) :
    permutationAverage (H s) r = profile e H (rankArrivalCount r s) := by
  let q := sortedRankEquiv e r hr
  let K : Equiv.Perm V := q.symm.trans e
  have hv (σ : Equiv.Perm V) : H s (coordinatePermutation σ r) =
      H (rankArrivalCount r s : ℝ) (representative e (K * σ)) := by
    apply hH
    · intro v
      have hi : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have h := sortedRankEquiv_lt_iff e r hr s (q.symm (σ v))
      have he : sortedRankEquiv e r hr (q.symm (σ v)) = σ v := q.apply_symm_apply _
      rw [he] at h
      exact h.symm.trans (by simp)
    · intro v w hv hw
      have hi (v : V) : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have hmono : StrictMono (fun i => r (q i)) := sortedRankEquiv_strictMono e r hr
      have hh := hmono.lt_iff_lt (a := q.symm (σ v)) (b := q.symm (σ w))
      simpa only [Equiv.apply_symm_apply,Fin.lt_def,Nat.cast_lt] using hh
  unfold permutationAverage profile
  simp_rw [hv]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft K)
  intro σ
  rfl

/-- A prefix-invariant statistic has a finite binomial-mixture expectation.
This is the exact permutation argument, with no conditioning on null events. -/
theorem expectation_eq_mixture (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (s : ℝ) (hs : 0 ≤ s)
    (hInt : Integrable (H s) (Measure.pi (fun _ : V => expMeasure 1))) :
    (∫ r, H s r ∂Measure.pi (fun _ : V => expMeasure 1)) =
      arrivalMixture n (profile e H) (1 - Real.exp (-s)) := by
  have havg : permutationAverage (H s) =ᵐ[Measure.pi (fun _ : V => expMeasure 1)]
      (fun r => profile e H (rankArrivalCount r s)) := by
    filter_upwards [ae_rawRanks_injective (V := V)] with r hr
    exact permutation_average_eq_profile e H hH r hr s
  rw [integral_eq_of_permutationAverage_ae (expMeasure 1) (H s) _ hInt havg]
  rw [integral_comp_nat_bounded _ (fun r => rankArrivalCount r s)
    (measurable_retainedVertices_card Finset.univ s) n
    (fun r => rankArrivalCount_le_of_equiv e r s)]
  unfold arrivalMixture
  apply Finset.sum_congr rfl
  intro j hj
  have hc : Fintype.card V = n := by simpa using Fintype.card_congr e.symm
  have hm := measureReal_retainedVertices_card (V := V) Finset.univ j s hs
  simpa only [rankArrivalCount,retainedVertices,Finset.card_univ,hc,
    arrivalWeight_formula,sub_sub_cancel] using congrArg (fun x : ℝ => x * profile e H j) hm
end OrderMixture

-- Source: Solutions.CountMeasurability
open RGMISFast MeasureTheory
set_option autoImplicit false

lemma mis_true_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (v : V) :
    inMIS G r v = true ↔ ∀ w, G.Adj v w → r w < r v → inMIS G r w = false := by
  rw [inMIS_eq]
  simp only [List.all_eq_true]
  constructor
  · intro h w ha hr
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h ⟨w,(mem_lowerNbrs G r).mpr ⟨ha,hr⟩⟩ (by simp)
  · intro h w hw
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h w.val ((mem_lowerNbrs G r).mp w.property).1 ((mem_lowerNbrs G r).mp w.property).2

lemma mis_order_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V → ℝ)
    (hord : ∀ v w, r v < r w ↔ s v < s w) (v : V) : inMIS G r v = inMIS G s v := by
  induction v using (measure (rk r)).wf.induction with
  | h v ih =>
    have he : inMIS G r v = true ↔ inMIS G s v = true := by
      rw [mis_true_iff,mis_true_iff]
      constructor
      · intro h w ha hw
        rw [← ih w (rk_lt r ((hord w v).mpr hw))]
        exact h w ha ((hord w v).mpr hw)
      · intro h w ha hw
        rw [ih w (rk_lt r hw)]
        exact h w ha ((hord w v).mp hw)
    cases hr : inMIS G r v <;> cases hs : inMIS G s v <;> simp_all

lemma mis_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Measurable (fun r : V → ℝ => inMIS G r v) := by
  classical
  let code : (V → ℝ) → (V → V → Prop) := fun r a b => r a < r b
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    exact measurableSet_setOf.mp (measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b))
  have hf : (fun r : V → ℝ => inMIS G r v).FactorsThrough code := by
    intro r s he
    apply mis_order_congr G r s
    intro a b
    exact iff_of_eq (congrFun (congrFun he a) b)
  obtain ⟨f,he⟩ := (Function.factorsThrough_iff _).mp hf
  rw [he]
  exact (measurable_of_countable f).comp hm

lemma active_vertex_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (t : ℝ) (v : V) :
    t ≤ tau G r v ↔ ∀ w, (w = v ∨ G.Adj v w) → inMIS G r w = true → t ≤ r w := by
  classical
  unfold tau
  rw [Finset.le_min'_iff]
  constructor
  · intro h w hw hm
    exact h (r w) (Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr
      ⟨by simpa using hw,hm⟩,rfl⟩)
  · intro h y hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw,hm⟩ := Finset.mem_filter.mp hw
    exact h w (by simpa using hw) hm

lemma active_vertex_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (v : V) :
    MeasurableSet {r : V → ℝ | t ≤ tau G r v} := by
  simp only [active_vertex_iff, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro w
  apply MeasurableSet.iInter
  intro hw
  have hm := mis_measurable G w
  have hb : MeasurableSet {r : V → ℝ | inMIS G r w = true} := measurableSet_eq_fun hm measurable_const
  have ht : MeasurableSet {r : V → ℝ | t ≤ r w} := measurableSet_le measurable_const (measurable_pi_apply w)
  convert hb.compl.union ht using 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]

lemma measurable_of_activity {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (f : (V → ℝ) → ℕ)
    (hf : ∀ r s, (∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) → f r = f s) : Measurable f := by
  classical
  let code : (V → ℝ) → (V → Prop) := fun r v => t ≤ tau G r v
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro v
    exact measurableSet_setOf.mp (active_vertex_measurable G t v)
  have hfac : f.FactorsThrough code := by
    intro r s he
    exact hf r s (fun v => iff_of_eq (congrFun he v))
  obtain ⟨g,he⟩ := (Function.factorsThrough_iff _).mp hfac
  rw [he]
  exact (measurable_of_countable g).comp hm

lemma activeAt_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (r s : V → ℝ)
    (h : ∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) (A : Finset V) :
    ActiveAt G r t A = ActiveAt G s t A := by
  unfold ActiveAt
  simp_rw [h]

lemma Ncount_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Ncount G A k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Ncount
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma Y_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Y G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Y
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma dsSum_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => dsSum G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  have he : {x | t ≤ tau G r x} = {x | t ≤ tau G s x} := Set.ext h
  have hc : countedW G u k t r = countedW G u k t s := by
    unfold countedW
    apply Finset.filter_congr
    intro W hw
    rw [activeAt_congr G t r s h]
  unfold dsSum
  rw [he,hc]

-- Source: Solutions.PrefixOrderActivity
open RGMISFast
namespace PrefixOrderActivity
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma activity_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (hlow : ∀ v, r v < s ↔ q v < t)
    (hord : ∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) (v : V) :
    s ≤ tau G r v ↔ t ≤ tau G q v := by
  have hm : ∀ w, r w < s → inMIS G r w = inMIS G q w := by
    intro w
    induction w using (measure (rk r)).wf.induction with
    | h w ih =>
      intro hw
      have hh : inMIS G r w = true ↔ inMIS G q w = true := by
        rw [mis_true_iff,mis_true_iff]
        constructor
        · intro h z ha hz
          have hzs : q z < t := hz.trans ((hlow w).mp hw)
          have hzr := (hlow z).mpr hzs
          have hzw := (hord z w hzr hw).mpr hz
          rw [← ih z (rk_lt r hzw) hzr]
          exact h z ha hzw
        · intro h z ha hz
          have hzs := hz.trans hw
          rw [ih z (rk_lt r hz) hzs]
          exact h z ha ((hord z w hzs hw).mp hz)
      cases hr : inMIS G r w <;> cases hq : inMIS G q w <;> simp_all
  rw [active_vertex_iff,active_vertex_iff]
  constructor
  · intro h w ha hqw
    by_contra hs
    have hwr := (hlow w).mpr (lt_of_not_ge hs)
    have hrw : inMIS G r w = true := (hm w hwr).trans hqw
    exact (not_le_of_gt hwr) (h w ha hrw)
  · intro h w ha hrw
    by_contra hs
    have hwr := lt_of_not_ge hs
    have hqw : inMIS G q w = true := (hm w hwr).symm.trans hrw
    exact (not_le_of_gt ((hlow w).mp hwr)) (h w ha hqw)

lemma Y_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) (u : V) (k : ℕ) :
    Y G u k s r = Y G u k t q := by
  classical
  unfold Y
  congr 1
  apply Finset.filter_congr
  intro A hA
  have ha : ActiveAt G r s A ↔ ActiveAt G q t A := by
    unfold ActiveAt
    simp_rw [h]
  rw [ha]
lemma dsSum_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) (u : V) (k : ℕ) :
    dsSum G u k s r = dsSum G u k t q := by
  classical
  have hc : countedW G u k s r = countedW G u k t q := by
    unfold countedW
    apply Finset.filter_congr
    intro W hw
    have ha : ActiveAt G r s (insert u W) ↔ ActiveAt G q t (insert u W) := by
      unfold ActiveAt
      simp_rw [h]
    rw [ha]
  have he : {v | s ≤ tau G r v} = {v | t ≤ tau G q v} := Set.ext h
  unfold dsSum
  rw [hc,he]
end PrefixOrderActivity

-- Source: Solutions.RootArrivalProfile
open MeasureTheory ProbabilityTheory RGMISFast
set_option maxHeartbeats 1000000
namespace RootArrivalProfile
open Classical ExponentialArrivals OrderMixture ArrivalPolynomial
variable {V : Type*} [Fintype V] [LinearOrder V]
def pin (u : V) (ρ : ℝ) (r : V → ℝ) : V → ℝ := fun v => if v = u then ρ else r v
lemma pin_measurable (u : V) (ρ : ℝ) : Measurable (pin u ρ) := by
  apply measurable_pi_lambda
  intro v
  by_cases h : v = u
  · simpa only [pin,if_pos h] using (measurable_const : Measurable (fun _ : V → ℝ => ρ))
  · simpa only [pin,if_neg h] using (measurable_pi_apply v : Measurable (fun r : V → ℝ => r v))
lemma pin_map (u : V) (ρ : ℝ) :
    (Measure.pi (fun _ : V => expMeasure 1)).map (pin u ρ) = rootLaw u ρ := by
  have hm (v : V) : Measurable (fun x : ℝ => if v = u then ρ else x) := by
    split_ifs <;> fun_prop
  unfold pin
  rw [Measure.pi_map_pi (fun v => (hm v).aemeasurable)]
  unfold rootLaw
  congr 1
  funext v
  by_cases h : v = u <;> simp [h]

lemma pinned_activity_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (r q : V → ℝ) (s t ρ σ : ℝ) (hρ : s ≤ ρ) (hσ : t ≤ σ)
    (hlow : ∀ v, r v < s ↔ q v < t)
    (hord : ∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) (v : V) :
    s ≤ tau G (pin u ρ r) v ↔ t ≤ tau G (pin u σ q) v := by
  apply PrefixOrderActivity.activity_congr
  · intro w
    by_cases h : w = u
    · simp only [pin,if_pos h]
      exact iff_of_false (not_lt_of_ge hρ) (not_lt_of_ge hσ)
    · simpa only [pin,if_neg h] using hlow w
  · intro w z hw hz
    have hwu : w ≠ u := by intro h; simpa [pin,h,not_lt_of_ge hρ] using hw
    have hzu : z ≠ u := by intro h; simpa [pin,h,not_lt_of_ge hρ] using hz
    simp only [pin,if_neg hwu,if_neg hzu] at hw hz ⊢
    exact hord w z hw hz

noncomputable def countProfile (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s : ℝ) (r : V → ℝ) : ℝ := (Y G u k s (pin u s r) : ℝ)
noncomputable def lossProfile (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s : ℝ) (r : V → ℝ) : ℝ := (dsSum G u k s (pin u s r) : ℝ)
lemma count_prefix_invariant (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) :
    PrefixInvariant (countProfile G u k) := by
  intro r q s t hlo hord
  unfold countProfile
  congr 1
  exact PrefixOrderActivity.Y_congr G _ _ s t
    (pinned_activity_congr G u r q s t s t le_rfl le_rfl hlo hord) u k
lemma loss_prefix_invariant (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) :
    PrefixInvariant (lossProfile G u k) := by
  intro r q s t hlo hord
  unfold lossProfile
  congr 1
  exact PrefixOrderActivity.dsSum_congr G _ _ s t
    (pinned_activity_congr G u r q s t s t le_rfl le_rfl hlo hord) u k

lemma count_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) :
    Measurable (countProfile G u k s) :=
  ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (Y_measurable_complete G u k s)).comp (pin_measurable u s)
lemma loss_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) :
    Measurable (lossProfile G u k s) :=
  ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (dsSum_measurable_complete G u k s)).comp (pin_measurable u s)
lemma count_integrable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] : Integrable (countProfile G u k s) μ := by
  apply Integrable.of_bound (count_measurable G u k s).aestronglyMeasurable
    (Fintype.card (Finset V) : ℝ)
  filter_upwards [] with r
  rw [countProfile,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.card_le_univ (α := Finset V) _)
lemma dsSum_bound (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) :
    dsSum G u k s r ≤ Fintype.card (Finset V) * Fintype.card V := by
  calc
    _ ≤ ∑ _W ∈ countedW G u k s r, Fintype.card V :=
      Finset.sum_le_sum (fun W _ => Finset.card_le_univ _)
    _ = (countedW G u k s r).card * Fintype.card V := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
lemma loss_integrable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] : Integrable (lossProfile G u k s) μ := by
  apply Integrable.of_bound (loss_measurable G u k s).aestronglyMeasurable
    ((Fintype.card (Finset V) * Fintype.card V : ℕ) : ℝ)
  filter_upwards [] with r
  rw [lossProfile,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast dsSum_bound G u k s _

lemma count_integral_rootLaw (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s ρ : ℝ) (hρ : s ≤ ρ) :
    (∫ r, (Y G u k s r : ℝ) ∂rootLaw u ρ) =
      ∫ r, countProfile G u k s r ∂Measure.pi (fun _ : V => expMeasure 1) := by
  have hm : Measurable (fun r : V → ℝ => (Y G u k s r : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (Y_measurable_complete G u k s)
  rw [← pin_map,integral_map (pin_measurable u ρ).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold countProfile
  congr 1
  exact PrefixOrderActivity.Y_congr G _ _ s s
    (pinned_activity_congr G u r r s s ρ s hρ le_rfl (fun _ => Iff.rfl)
      (fun _ _ _ _ => Iff.rfl)) u k
lemma loss_integral_rootLaw (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s ρ : ℝ) (hρ : s ≤ ρ) :
    (∫ r, (dsSum G u k s r : ℝ) ∂rootLaw u ρ) =
      ∫ r, lossProfile G u k s r ∂Measure.pi (fun _ : V => expMeasure 1) := by
  have hm : Measurable (fun r : V → ℝ => (dsSum G u k s r : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (dsSum_measurable_complete G u k s)
  rw [← pin_map,integral_map (pin_measurable u ρ).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold lossProfile
  congr 1
  exact PrefixOrderActivity.dsSum_congr G _ _ s s
    (pinned_activity_congr G u r r s s ρ s hρ le_rfl (fun _ => Iff.rfl)
      (fun _ _ _ _ => Iff.rfl)) u k
end RootArrivalProfile

-- Source: Solutions.PermutationRankSwap
open Classical
namespace PermutationRankSwap
open OrderMixture
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
def swapRanks (e : Fin n ≃ V) (j l : Fin n) : Equiv.Perm V := Equiv.swap (e j) (e l)
lemma rank_swap_eq_below (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n)
    (hl : j ≤ l) (v : V) (hv : representative e σ v < (j.val : ℝ)) :
    representative e (swapRanks e j l * σ) v = representative e σ v := by
  have hpos : (e.symm (σ v)).val < j.val := by
    unfold representative at hv
    exact_mod_cast hv
  have ha : σ v ≠ e j := by intro h; simp only [h,Equiv.symm_apply_apply] at hpos; omega
  have hb : σ v ≠ e l := by intro h; simp only [h,Equiv.symm_apply_apply] at hpos; exact (not_lt_of_ge hl) hpos
  simp only [representative,Equiv.Perm.mul_apply,swapRanks,Equiv.swap_apply_of_ne_of_ne ha hb]
lemma rank_swap_low_iff (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n)
    (hl : j ≤ l) (v : V) :
    representative e σ v < (j.val : ℝ) ↔
      representative e (swapRanks e j l * σ) v < (j.val : ℝ) := by
  constructor
  · intro h
    rw [rank_swap_eq_below e σ j l hl v h]
    exact h
  · intro h
    have hh := rank_swap_eq_below e (swapRanks e j l * σ) j l hl v h
    have he : swapRanks e j l * (swapRanks e j l * σ) = σ := by
      ext w
      simp [swapRanks,Equiv.Perm.mul_apply]
    rw [he] at hh
    rwa [← hh] at h
lemma swap_next_rank (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n) :
    representative e (swapRanks e j l * σ) (σ.symm (e l)) = (j.val : ℝ) := by
  simp [representative,swapRanks,Equiv.Perm.mul_apply]
lemma rank_injective (e : Fin n ≃ V) (σ : Equiv.Perm V) :
    Function.Injective (representative e σ) := by
  intro v w h
  apply σ.injective
  apply e.symm.injective
  apply Fin.ext
  unfold representative at h
  exact_mod_cast h
lemma rank_interval_unique (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n) (v : V)
    (hv : (j.val : ℝ) ≤ representative e (swapRanks e j l * σ) v ∧
      representative e (swapRanks e j l * σ) v < (j.val : ℝ) + 1) : v = σ.symm (e l) := by
  apply rank_injective e (swapRanks e j l * σ)
  rw [swap_next_rank]
  unfold representative at hv ⊢
  have ha : j.val ≤ (e.symm ((swapRanks e j l * σ) v)).val := by exact_mod_cast hv.1
  have hb : (e.symm ((swapRanks e j l * σ) v)).val < j.val + 1 := by exact_mod_cast hv.2
  exact_mod_cast (show (e.symm ((swapRanks e j l * σ) v)).val = j.val by omega)
end PermutationRankSwap

-- Source: Solutions.SingleArrival
open RGMISFast
namespace SingleArrival
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ)

/-- Across an interval with exactly one possible arriving vertex, only that
vertex's selection can change activity. -/
lemma activity_transition (s t : ℝ) (hst : s ≤ t) (x v : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    t ≤ tau G r v ↔ s ≤ tau G r v ∧
      (inMIS G r x = true → v ≠ x ∧ ¬ G.Adj v x) := by
  constructor
  · intro ht
    refine ⟨hst.trans ht, ?_⟩
    intro hm
    have h := (active_vertex_iff G r t v).mp ht
    constructor
    · intro he
      subst v
      exact (not_le_of_gt hx.2) (h x (Or.inl rfl) hm)
    · intro ha
      exact (not_le_of_gt hx.2) (h x (Or.inr ha) hm)
  · rintro ⟨hs, hsafe⟩
    apply (active_vertex_iff G r t v).mpr
    intro w hw hm
    have hsw := (active_vertex_iff G r s v).mp hs w hw hm
    by_contra htw
    have hwx := hone w hsw (lt_of_not_ge htw)
    subst w
    rcases hw with he | ha
    · exact (hsafe hm).1 he.symm
    · exact (hsafe hm).2 ha

/-- The unique arrival is selected exactly when it is still active at the
start of the interval. -/
lemma arrival_selected_iff (s t : ℝ) (x : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    inMIS G r x = true ↔ s ≤ tau G r x := by
  constructor
  · intro hm
    apply (active_vertex_iff G r s x).mpr
    intro w hw hwm
    rcases hw with he | ha
    · simpa only [he] using hx.1
    · by_contra hws
      have hl : r w < r x := (lt_of_not_ge hws).trans_le hx.1
      have hf := (mis_true_iff G r x).mp hm w ha hl
      simp_all
  · intro hs
    apply (mis_true_iff G r x).mpr
    intro w ha hw
    cases hm : inMIS G r w with
    | false => rfl
    | true =>
      have hsw := (active_vertex_iff G r s x).mp hs w (Or.inr ha) hm
      have he := hone w hsw (hw.trans hx.2)
      subst w
      exact False.elim (lt_irrefl _ hw)

lemma active_transition (s t : ℝ) (hst : s ≤ t) (x v : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    t ≤ tau G r v ↔ s ≤ tau G r v ∧
      (s ≤ tau G r x → v ≠ x ∧ ¬ G.Adj v x) := by
  rw [activity_transition G r s t hst x v hx hone, ← arrival_selected_iff G r s t x hx hone]
end SingleArrival

namespace SingleArrival
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ)
lemma active_set_transition (s t : ℝ) (hst : s ≤ t) (x : V) (A : Finset V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    ActiveAt G r t A ↔ ActiveAt G r s A ∧
      (s ≤ tau G r x → ∀ v ∈ A, v ≠ x ∧ ¬ G.Adj v x) := by
  constructor
  · intro h
    constructor
    · intro v hv
      exact hst.trans (h v hv)
    · intro hxa v hv
      exact ((active_transition G r s t hst x v hx hone).mp (h v hv)).2 hxa
  · rintro ⟨h,hkeep⟩ v hv
    exact (active_transition G r s t hst x v hx hone).mpr ⟨h v hv,fun hxa => hkeep hxa v hv⟩
end SingleArrival

-- Source: Solutions.ArrivalLoss
open RGMISFast
open scoped BigOperators
namespace ArrivalLoss
open Classical
section
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] in
/-- The number lost under one arrival is the number of sets it kills. -/
theorem count_loss_eq_killed {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (kill : ι → Finset V) (w : V) :
    (F.card : ℝ) - ((F.filter fun i => w ∉ kill i).card : ℝ) =
      ((F.filter fun i => w ∈ kill i).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := F) (p := fun i => w ∈ kill i)
  have hr : ((F.filter fun i => w ∈ kill i).card : ℝ) +
      ((F.filter fun i => w ∉ kill i).card : ℝ) = (F.card : ℝ) := by
    exact_mod_cast h
  linarith

omit [Fintype V] in
/-- Exact double counting of the total loss over all possible arrivals. -/
theorem sum_count_loss_eq_sum_killing_card {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (R : Finset V) (kill : ι → Finset V)
    (hkill : ∀ i ∈ F, kill i ⊆ R) :
    ∑ w ∈ R, ((F.card : ℝ) - ((F.filter fun i => w ∉ kill i).card : ℝ)) =
      ∑ i ∈ F, ((kill i).card : ℝ) := by
  simp_rw [count_loss_eq_killed]
  have hind (w : V) : ((F.filter fun i => w ∈ kill i).card : ℝ) =
      ∑ i ∈ F, if w ∈ kill i then (1 : ℝ) else 0 := by simp
  simp_rw [hind]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.inter_eq_right.mpr (hkill i hi)]

noncomputable def killers (H : SimpleGraph V) (u : V) (W : Finset V) : Finset V :=
  Finset.univ.filter (fun x => x ≠ u ∧ (x ∈ W ∨ ∃ y ∈ insert u W, H.Adj y x))

lemma killers_card (H : SimpleGraph V) (u : V) (W : Finset V) :
    (killers H u W).card = dW H u W := rfl

end

/-- Exact finite loss identity for the mission's active graph and counted family. -/
theorem dsSum_eq_total_loss {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) :
    (dsSum G u k s r : ℝ) =
      ∑ x ∈ (Finset.univ.filter (fun x => x ≠ u ∧ s ≤ tau G r x)),
        ((countedW G u k s r).card -
          (((countedW G u k s r).filter
            (fun W => x ∉ killers (restrictTo G {v | s ≤ tau G r v}) u W)).card : ℝ)) := by
  let F := countedW G u k s r
  let R := Finset.univ.filter (fun x => x ≠ u ∧ s ≤ tau G r x)
  let kill := killers (restrictTo G {v | s ≤ tau G r v}) u
  have hkill : ∀ W ∈ F, kill W ⊆ R := by
    intro W hW x hx
    obtain ⟨hne, hxW | ⟨y,hy,hyx⟩⟩ := (Finset.mem_filter.mp hx).2
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hne, ?_⟩
      have hact := (Finset.mem_filter.mp hW).2.2.2.2
      exact hact x (Finset.mem_insert_of_mem hxW)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,hyx.2.2⟩
  have h := sum_count_loss_eq_sum_killing_card F R kill hkill
  rw [h]
  simp only [dsSum, Nat.cast_sum, killers_card, F, kill]
end ArrivalLoss

-- Source: Solutions.ArrivalCountTransition
open RGMISFast
open Classical
namespace ArrivalLoss
variable {V : Type*} [Fintype V] [LinearOrder V]

lemma active_insert_transition
    (G : SimpleGraph V) [DecidableRel G.Adj] (u x : V) (W : Finset V)
    (r : V → ℝ) (s t : ℝ) (hst : s ≤ t) (hxu : x ≠ u)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    ActiveAt G r t (insert u W) ↔ ActiveAt G r s (insert u W) ∧
      x ∉ killers (restrictTo G {v | s ≤ tau G r v}) u W := by
  rw [SingleArrival.active_set_transition G r s t hst x (insert u W) hx hone]
  constructor
  · rintro ⟨ha,hkeep⟩
    refine ⟨ha,?_⟩
    intro hk
    obtain ⟨_,hw | ⟨y,hy,hyx⟩⟩ := (Finset.mem_filter.mp hk).2
    · exact (hkeep (ha x (Finset.mem_insert_of_mem hw)) x
        (Finset.mem_insert_of_mem hw)).1 rfl
    · exact (hkeep hyx.2.2 y hy).2 hyx.1
  · rintro ⟨ha,hkeep⟩
    refine ⟨ha,?_⟩
    intro hxa v hv
    constructor
    · intro hvx
      subst v
      have hxW : x ∈ W := (Finset.mem_insert.mp hv).resolve_left hxu
      exact hkeep (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxu,Or.inl hxW⟩)
    · intro hadj
      exact hkeep (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxu,
        Or.inr ⟨v,hv,hadj,ha v hv,hxa⟩⟩)

/-- The actual counted family after a single nonroot arrival is exactly the
old family with the sets killed by that arrival removed. -/
theorem countedW_single_arrival
    (G : SimpleGraph V) [DecidableRel G.Adj] (u x : V) (k : ℕ)
    (r : V → ℝ) (s t : ℝ) (hst : s ≤ t) (hxu : x ≠ u)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    countedW G u k t r = (countedW G u k s r).filter
      (fun W => x ∉ killers (restrictTo G {v | s ≤ tau G r v}) u W) := by
  ext W
  simp only [countedW,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [active_insert_transition G u x W r s t hst hxu hx hone]
  tauto

end ArrivalLoss

-- Source: Solutions.RootCountCorrespondence
open RGMISFast
set_option autoImplicit false

lemma singleton_attached_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V) (W : Finset V) :
    IsAttached G {u} W ↔ u ∉ W ∧ IsRootConnected G u (insert u W) := by
  classical
  constructor
  · rintro ⟨hd,hr⟩
    have hu : u ∉ W := by simpa using hd
    refine ⟨hu,Finset.mem_insert_self _ _,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact .refl _
    · obtain ⟨y,hy,hyx⟩ := hr x hx
      have he : y = u := Finset.mem_singleton.mp hy
      subst y
      simpa using hyx
  · rintro ⟨hu,hroot⟩
    refine ⟨by simpa using hu,?_⟩
    intro w hw
    exact ⟨u,Finset.mem_singleton_self _,by simpa using hroot.2 w (Finset.mem_insert_of_mem hw)⟩

lemma Y_eq_Ncount_singleton {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) (r : V → ℝ) :
    Y G u k t r = Ncount G {u} k t r := by
  classical
  unfold Y Ncount
  symm
  apply Finset.card_bij (fun W _ => insert u W)
  · intro W hW
    obtain ⟨_,hc,ha,ht⟩ := Finset.mem_filter.mp hW
    obtain ⟨hu,hr⟩ := (singleton_attached_iff G u W).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hr,?_,by simpa using ht⟩
    rw [Finset.card_insert_of_notMem hu,hc]
  · intro W hW Z hZ he
    have huW := ((singleton_attached_iff G u W).mp (Finset.mem_filter.mp hW).2.2.1).1
    have huZ := ((singleton_attached_iff G u Z).mp (Finset.mem_filter.mp hZ).2.2.1).1
    have hh := congrArg (fun A : Finset V => A.erase u) he
    simpa [Finset.erase_insert,Finset.erase_eq_of_notMem huW,Finset.erase_eq_of_notMem huZ] using hh
  · intro B hB
    obtain ⟨_,hr,hcard,ht⟩ := Finset.mem_filter.mp hB
    have he : insert u (B.erase u) = B := Finset.insert_erase hr.1
    refine ⟨B.erase u,?_,he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_,?_⟩
    · rw [Finset.card_erase_of_mem hr.1,hcard]
      omega
    · apply (singleton_attached_iff G u _).mpr
      exact ⟨Finset.notMem_erase _ _,by simpa only [he] using hr⟩
    · simpa [he] using ht

-- Source: Solutions.ArrivalAuxiliary
open RGMISFast
namespace ArrivalAuxiliary
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma active_le_rank (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (s : ℝ) (v : V)
    (hv : s ≤ tau G r v) : s ≤ r v := by
  by_contra hvs
  have hlt := lt_of_not_ge hvs
  have hm : inMIS G r v = true := by
    apply (mis_true_iff G r v).mpr
    intro w ha hw
    cases he : inMIS G r w with
    | false => rfl
    | true =>
      have hs := (active_vertex_iff G r s v).mp hv w (Or.inr ha) he
      exact False.elim ((not_le_of_gt (hw.trans hlt)) hs)
  exact (not_le_of_gt hlt) ((active_vertex_iff G r s v).mp hv v (Or.inl rfl) hm)
lemma activity_no_arrival (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hn : ∀ w, ¬ (s ≤ r w ∧ r w < t)) (v : V) :
    s ≤ tau G r v ↔ t ≤ tau G r v := by
  constructor
  · intro h
    apply (active_vertex_iff G r t v).mpr
    intro w hw hm
    have hs := (active_vertex_iff G r s v).mp h w hw hm
    exact le_of_not_gt (fun ht => hn w ⟨hs,ht⟩)
  · exact fun h => hst.trans h
lemma Y_eq_countedW (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) : Y G u k s r = (countedW G u k s r).card := by
  classical
  rw [Y_eq_Ncount_singleton]
  unfold Ncount countedW
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [singleton_attached_iff]
  simp only [Finset.singleton_union]
  tauto
end ArrivalAuxiliary

-- Source: Solutions.PermutationGraphTransition
open RGMISFast
namespace PermutationGraphTransition
open Classical RootArrivalProfile OrderMixture PermutationRankSwap ArrivalLoss ArrivalAuxiliary
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
noncomputable def ranks (e : Fin n ≃ V) (u : V) (σ : Equiv.Perm V) : V → ℝ :=
  pin u (n : ℝ) (representative e σ)
lemma activity_before_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (σ : Equiv.Perm V) (j l : Fin n) (hl : j ≤ l) (v : V) :
    (j.val : ℝ) ≤ tau G (ranks e u σ) v ↔
      (j.val : ℝ) ≤ tau G (ranks e u (swapRanks e j l * σ)) v := by
  apply pinned_activity_congr
  · exact_mod_cast j.isLt.le
  · exact_mod_cast j.isLt.le
  · exact rank_swap_low_iff e σ j l hl
  · intro w z hw hz
    rw [rank_swap_eq_below e σ j l hl w hw,rank_swap_eq_below e σ j l hl z hz]
lemma family_before_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) (j l : Fin n) (hl : j ≤ l) :
    countedW G u k (j.val : ℝ) (ranks e u σ) =
      countedW G u k (j.val : ℝ) (ranks e u (swapRanks e j l * σ)) := by
  unfold countedW
  apply Finset.filter_congr
  intro W hw
  have ha : ActiveAt G (ranks e u σ) (j.val : ℝ) (insert u W) ↔
      ActiveAt G (ranks e u (swapRanks e j l * σ)) (j.val : ℝ) (insert u W) := by
    unfold ActiveAt
    simp_rw [activity_before_swap G e u σ j l hl]
  rw [ha]

lemma next_family (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) (j l : Fin n) (hl : j ≤ l) :
    countedW G u k ((j.val : ℝ)+1) (ranks e u (swapRanks e j l * σ)) =
      (countedW G u k (j.val : ℝ) (ranks e u σ)).filter
        (fun W => σ.symm (e l) ∉ killers
          (restrictTo G {v | (j.val : ℝ) ≤ tau G (ranks e u σ) v}) u W) := by
  let r := ranks e u (swapRanks e j l * σ)
  let x := σ.symm (e l)
  have hn : (j.val : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
  have hroot : r u = n := by simp [r,ranks,pin]
  have hone : ∀ w, (j.val : ℝ) ≤ r w → r w < (j.val : ℝ)+1 → w = x := by
    intro w hw ht
    have hwu : w ≠ u := by intro he; subst w; rw [hroot] at ht; linarith
    apply rank_interval_unique e σ j l w
    simpa only [r,ranks,pin,if_neg hwu] using And.intro hw ht
  have hc := family_before_swap G e u k σ j l hl
  have hg : {v | (j.val : ℝ) ≤ tau G (ranks e u σ) v} =
      {v | (j.val : ℝ) ≤ tau G r v} :=
    Set.ext (activity_before_swap G e u σ j l hl)
  by_cases hxu : x = u
  · have hnone : ∀ w, ¬ ((j.val : ℝ) ≤ r w ∧ r w < (j.val : ℝ)+1) := by
      intro w hw
      have he := (hone w hw.1 hw.2).trans hxu
      rw [he,hroot] at hw
      linarith [hw.2]
    have hsame : countedW G u k ((j.val : ℝ)+1) r = countedW G u k (j.val : ℝ) r := by
      unfold countedW
      apply Finset.filter_congr
      intro W hw
      have ha : ActiveAt G r ((j.val : ℝ)+1) (insert u W) ↔
          ActiveAt G r (j.val : ℝ) (insert u W) := by
        unfold ActiveAt
        simp_rw [← activity_no_arrival G r (j.val : ℝ) ((j.val : ℝ)+1) (by linarith) hnone]
      rw [ha]
    change countedW G u k ((j.val : ℝ)+1) r = _
    rw [hsame,← hc]
    have he : σ.symm (e l) = u := hxu
    simp [he,killers]
  · have hx : (j.val : ℝ) ≤ r x ∧ r x < (j.val : ℝ)+1 := by
      have hrx : r x = (j.val : ℝ) := by
        simp only [r,ranks,pin,if_neg hxu]
        exact swap_next_rank e σ j l
      rw [hrx]
      constructor <;> linarith
    change countedW G u k ((j.val : ℝ)+1) r = _
    rw [countedW_single_arrival G u x k r (j.val : ℝ) ((j.val : ℝ)+1)
      (by linarith) hxu hx hone,← hc,← hg]
end PermutationGraphTransition

-- Source: Solutions.PermutationTotalLoss
open RGMISFast
namespace PermutationTotalLoss
open Classical RootArrivalProfile OrderMixture PermutationRankSwap PermutationGraphTransition
open ArrivalLoss ArrivalAuxiliary
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
lemma killing_position (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (σ : Equiv.Perm V)
    (W : Finset V) (hW : W ∈ countedW G u k (j : ℝ) (ranks e u σ))
    (x : V) (hx : x ∈ killers (restrictTo G {v | (j : ℝ) ≤ tau G (ranks e u σ) v}) u W) :
    j ≤ (e.symm (σ x)).val := by
  obtain ⟨hne,hxW | ⟨y,hy,hyx⟩⟩ := (Finset.mem_filter.mp hx).2
  · have hact := (Finset.mem_filter.mp hW).2.2.2.2
    have hh := active_le_rank G (ranks e u σ) j x (hact x (Finset.mem_insert_of_mem hxW))
    simp only [ranks,pin,if_neg hne,representative] at hh
    exact_mod_cast hh
  · have hh := active_le_rank G (ranks e u σ) j x hyx.2.2
    simp only [ranks,pin,if_neg hne,representative] at hh
    exact_mod_cast hh

lemma total_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) (j : Fin n) :
    (∑ l ∈ Finset.Ici j,
      ((Y G u k (j.val : ℝ) (ranks e u σ) : ℝ) -
        (Y G u k ((j.val : ℝ)+1) (ranks e u (swapRanks e j l * σ)) : ℝ))) =
      (dsSum G u k (j.val : ℝ) (ranks e u σ) : ℝ) := by
  let F := countedW G u k (j.val : ℝ) (ranks e u σ)
  let kill := killers (restrictTo G {v | (j.val : ℝ) ≤ tau G (ranks e u σ) v}) u
  let R := Finset.univ.filter (fun x => j.val ≤ (e.symm (σ x)).val)
  have hkill : ∀ W ∈ F, kill W ⊆ R := by
    intro W hW x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,killing_position G e u k j.val σ W hW x hx⟩
  let loss := fun x => (F.card : ℝ) - ((F.filter fun W => x ∉ kill W).card : ℝ)
  have hsum : (∑ l ∈ Finset.Ici j, loss (σ.symm (e l))) = ∑ x ∈ R, loss x := by
    apply Finset.sum_bij (fun l _ => σ.symm (e l))
    · intro l hl
      simpa [R] using (Finset.mem_Ici.mp hl)
    · intro l hl m hm he
      exact e.injective (σ.symm.injective he)
    · intro x hx
      refine ⟨e.symm (σ x), ?_, ?_⟩
      · simpa [R] using hx
      · simp
    · intro l hl
      rfl
  have htotal := sum_count_loss_eq_sum_killing_card F R kill hkill
  calc
    _ = ∑ l ∈ Finset.Ici j, loss (σ.symm (e l)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Y_eq_countedW,Y_eq_countedW,next_family G e u k σ j l (Finset.mem_Ici.mp hl)]
    _ = ∑ W ∈ F, ((kill W).card : ℝ) := hsum.trans htotal
    _ = _ := by simp only [dsSum,Nat.cast_sum,F,kill,killers_card]

lemma terminal_loss_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) :
    dsSum G u k (n : ℝ) (ranks e u σ) = 0 := by
  unfold dsSum
  apply Finset.sum_eq_zero
  intro W hW
  rw [← killers_card]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := killing_position G e u k n σ W hW x hx
  exact (not_le_of_gt (e.symm (σ x)).isLt) hh
end PermutationTotalLoss

-- Source: Solutions.FiniteProfileDrift
open RGMISFast
set_option maxHeartbeats 1000000
namespace FiniteProfileDrift
open Classical RootArrivalProfile OrderMixture PermutationRankSwap PermutationGraphTransition
open PermutationTotalLoss ArrivalPolynomial
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
lemma countProfile_eq_ranks (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (hj : j ≤ n) (σ : Equiv.Perm V) :
    countProfile G u k (j : ℝ) (representative e σ) = (Y G u k (j : ℝ) (ranks e u σ) : ℝ) := by
  unfold countProfile
  congr 1
  apply PrefixOrderActivity.Y_congr
  exact pinned_activity_congr G u _ _ j j j n le_rfl (by exact_mod_cast hj)
    (fun _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
lemma lossProfile_eq_ranks (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (hj : j ≤ n) (σ : Equiv.Perm V) :
    lossProfile G u k (j : ℝ) (representative e σ) = (dsSum G u k (j : ℝ) (ranks e u σ) : ℝ) := by
  unfold lossProfile
  congr 1
  apply PrefixOrderActivity.dsSum_congr
  exact pinned_activity_congr G u _ _ j j j n le_rfl (by exact_mod_cast hj)
    (fun _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

lemma profile_loss_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (hj : j < n) :
    profile e (lossProfile G u k) j = (n-j : ℕ) *
      (profile e (countProfile G u k) j - profile e (countProfile G u k) (j+1)) := by
  let ij : Fin n := ⟨j,hj⟩
  have hs (l : Fin n) :
      (∑ σ : Equiv.Perm V, (Y G u k ((j : ℝ)+1) (ranks e u (swapRanks e ij l * σ)) : ℝ)) =
        ∑ σ : Equiv.Perm V, (Y G u k ((j : ℝ)+1) (ranks e u σ) : ℝ) := by
    apply Fintype.sum_equiv (Equiv.mulLeft (swapRanks e ij l))
    intro σ
    rfl
  unfold profile
  simp_rw [lossProfile_eq_ranks G e u k j hj.le,
    countProfile_eq_ranks G e u k j hj.le,
    countProfile_eq_ranks G e u k (j+1) (Nat.succ_le_of_lt hj)]
  simp only [Nat.cast_add,Nat.cast_one]
  have ht (σ : Equiv.Perm V) := total_loss G e u k σ ij
  simp only [ij] at ht
  simp_rw [← ht]
  rw [Finset.sum_comm]
  simp only [Finset.sum_sub_distrib]
  simp only [ij] at hs
  simp only [hs]
  simp only [Finset.sum_const,Fin.card_Ici,nsmul_eq_mul,ij]
  ring

lemma profile_loss_terminal (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) : profile e (lossProfile G u k) n = 0 := by
  unfold profile
  simp_rw [lossProfile_eq_ranks G e u k n le_rfl,terminal_loss_zero]
  simp

lemma loss_mixture_eq_drift (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (z : ℝ) :
    arrivalMixture n (profile e (lossProfile G u k)) z =
      arrivalDrift n (profile e (countProfile G u k)) z := by
  unfold arrivalMixture arrivalDrift
  rw [Finset.sum_range_succ,profile_loss_terminal]
  simp only [mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [profile_loss_identity G e u k j (Finset.mem_range.mp hj)]
  ring
end FiniteProfileDrift

-- Source: Solutions.ArrivalExpansionDerivative
set_option autoImplicit false

lemma arrival_expansion_derivative (n : ℕ) (coeff : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun z : ℝ => ∑ j ∈ Finset.range (n+1), coeff j * Real.exp (-(j:ℝ)*z))
      (-(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))) s := by
  have hd (j : ℕ) : HasDerivAt
      (fun z : ℝ => coeff j * Real.exp (-(j:ℝ)*z))
      (coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) s := by
    simpa using (((hasDerivAt_id s).const_mul (-(j:ℝ))).exp.const_mul (coeff j))
  have hh := HasDerivAt.fun_sum (u := Finset.range (n+1)) (fun j _ => hd j)
  have he : (∑ j ∈ Finset.range (n+1), coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) =
      -(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he] at hh
  exact hh

lemma derivative_from_arrival_expansion (f d : ℝ → ℝ) (n : ℕ) (coeff : ℕ → ℝ)
    (t : ℝ)
    (hf : ∀ s ∈ Set.Icc 0 t, f s = ∑ j ∈ Finset.range (n+1), coeff j*Real.exp (-(j:ℝ)*s))
    (hd : ∀ s ∈ Set.Icc 0 t, d s = ∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))
    (s : ℝ) (hs : s ∈ Set.Ico 0 t) : HasDerivWithinAt f (-d s) (Set.Icc 0 t) s := by
  have hs' : s ∈ Set.Icc 0 t := ⟨hs.1,hs.2.le⟩
  rw [hd s hs']
  exact (arrival_expansion_derivative n coeff s).hasDerivWithinAt.congr_of_mem hf hs'

-- Source: Solutions.ExponentialPolynomial
open scoped BigOperators
namespace ArrivalPolynomial

lemma exponential_mixture_derivative (n : ℕ) (g : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun z => arrivalMixture n g (1 - Real.exp (-z)))
      (-arrivalDrift n g (1 - Real.exp (-s))) s := by
  by_cases hn : n = 0
  · subst n
    simpa [arrivalMixture,arrivalWeight,bernsteinPolynomial,arrivalDrift] using
      (hasDerivAt_const s (g 0))
  · have hq : HasDerivAt (fun z : ℝ => 1 - Real.exp (-z)) (Real.exp (-s)) s := by
      simpa using ((hasDerivAt_id s).neg.exp.const_sub 1)
    have he := Real.exp_pos (-s)
    have hd := (hasDerivAt_arrivalMixture n g (1 - Real.exp (-s))
      (Nat.pos_of_ne_zero hn) (by linarith)).comp s hq
    convert! hd using 1 <;> field_simp <;> ring

/-- The permutation means are Bernstein coefficients. After substituting
1-exp(-s), conversion to monomials supplies the constant exponential coefficients
and simultaneously the weighted coefficients of the exact loss profile. -/
theorem exponential_mixture_expansion (n : ℕ) (g : ℕ → ℝ) :
    ∃ m : ℕ, ∃ coeff : ℕ → ℝ,
      (∀ s : ℝ, arrivalMixture n g (1 - Real.exp (-s)) =
        ∑ j ∈ Finset.range (m+1), coeff j * Real.exp (-(j:ℝ)*s)) ∧
      (∀ s : ℝ, arrivalDrift n g (1 - Real.exp (-s)) =
        ∑ j ∈ Finset.range (m+1), (j:ℝ)*coeff j * Real.exp (-(j:ℝ)*s)) := by
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (n+1),
    (bernsteinPolynomial ℝ n j).comp (1 - Polynomial.X) * Polynomial.C (g j)
  have hp (s : ℝ) : P.eval (Real.exp (-s)) = arrivalMixture n g (1 - Real.exp (-s)) := by
    simp [P,arrivalMixture,arrivalWeight,Polynomial.eval_finsetSum]
  have hf (s : ℝ) : arrivalMixture n g (1 - Real.exp (-s)) =
      ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * Real.exp (-(j:ℝ)*s) := by
    rw [← hp,Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine ⟨P.natDegree,P.coeff,hf,?_⟩
  intro s
  have hd := exponential_mixture_derivative n g s
  have he : (fun z => arrivalMixture n g (1 - Real.exp (-z))) =
      (fun z => ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * Real.exp (-(j:ℝ)*z)) := funext hf
  rw [he] at hd
  have hh := hd.unique (arrival_expansion_derivative P.natDegree P.coeff s)
  exact neg_injective hh
end ArrivalPolynomial

-- Source: Solutions.RootArrivalExpansionComplete
open MeasureTheory ProbabilityTheory RGMISFast
open RootArrivalProfile OrderMixture ArrivalPolynomial FiniteProfileDrift ExponentialArrivals

 theorem root_count_arrival_expansion_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (hk : 1 ≤ k)
    (t ρ : ℝ) (ht : 0 < t) (htρ : t ≤ ρ) :
    ∃ (m : ℕ) (coeff : ℕ → ℝ),
      (∀ s ∈ Set.Icc 0 t,
        (∫ r, (Y G u k s r : ℝ) ∂(rootLaw u ρ)) =
          ∑ j ∈ Finset.range (m+1), coeff j * Real.exp (-(j:ℝ)*s)) ∧
      (∀ s ∈ Set.Icc 0 t,
        (∫ r, (dsSum G u k s r : ℝ) ∂(rootLaw u ρ)) =
          ∑ j ∈ Finset.range (m+1), (j:ℝ)*coeff j * Real.exp (-(j:ℝ)*s)) := by
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  obtain ⟨m,coeff,hf,hd⟩ := exponential_mixture_expansion n (profile e (countProfile G u k))
  refine ⟨m,coeff,?_,?_⟩
  · intro s hs
    rw [count_integral_rootLaw G u k s ρ (hs.2.trans htρ),
      expectation_eq_mixture e (countProfile G u k) (count_prefix_invariant G u k) s hs.1
        (count_integrable G u k s _)]
    exact hf s
  · intro s hs
    rw [loss_integral_rootLaw G u k s ρ (hs.2.trans htρ),
      expectation_eq_mixture e (lossProfile G u k) (loss_prefix_invariant G u k) s hs.1
        (loss_integrable G u k s _),loss_mixture_eq_drift]
    exact hd s

-- Source: Solutions.Eq20Complete
open MeasureTheory ProbabilityTheory RGMISFast
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (hk : 1 ≤ k) (t ρ : ℝ) (ht : 0 < t) (htρ : t ≤ ρ) :
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (Y G u k s r : ℝ))) ∧
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (dsSum G u k s r : ℝ))) ∧
    ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s' : ℝ => ∫ r, (Y G u k s' r : ℝ) ∂(rootLaw u ρ))
        (-(∫ r, (dsSum G u k s r : ℝ) ∂(rootLaw u ρ))) (Set.Icc 0 t) s := by
  refine ⟨?_,?_,?_⟩
  · intro s
    have hm := Y_measurable_complete G u k s
    fun_prop
  · intro s
    have hm := dsSum_measurable_complete G u k s
    fun_prop
  · obtain ⟨n,coeff,hf,hd⟩ := root_count_arrival_expansion_complete G u k hk t ρ ht htρ
    exact derivative_from_arrival_expansion _ _ n coeff t hf hd

#print axioms solution
