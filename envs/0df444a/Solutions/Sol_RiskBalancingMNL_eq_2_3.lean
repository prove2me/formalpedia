-- Prove2me | solution 1 for RiskBalancingMNL.eq_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:40:19.218793+00:00
-- url     : https://prove2.me/submissions/ba09c35d-cffb-4675-8bf4-37d4db50f2ab

import Mathlib
import Definitions.Def_RiskBalancingMNL_randomProfit

open MeasureTheory ProbabilityTheory RiskBalancingMNL

theorem solution {n : ℕ} (N : ℕ) (ν : Measure (Fin n ⊕ Unit)) [IsProbabilityMeasure ν]
    (m : Fin n → ℝ) :
    (∫ ω, randomProfit m ω ∂(customerLaw N ν)) = (N : ℝ) * ∑ i, m i * choiceProb ν i ∧
    variance (randomProfit (N := N) m) (customerLaw N ν) =
      ∑ i, ∑ j, m i * m j * covariance (demand (N := N) i) (demand j) (customerLaw N ν) ∧
    variance (randomProfit (N := N) m) (customerLaw N ν) =
      (N : ℝ) * (∑ i, m i ^ 2 * choiceProb ν i * (1 - choiceProb ν i) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, m i * m j * choiceProb ν i * choiceProb ν j) ∧
    variance (randomProfit (N := N) m) (customerLaw N ν) =
      (N : ℝ) * (∑ i, m i ^ 2 * choiceProb ν i - (∑ i, m i * choiceProb ν i) ^ 2) := by
  have : DiscreteMeasurableSpace (Fin n ⊕ Unit) :=
    ⟨fun s => measurableSet_sum_iff.mpr ⟨.of_discrete, .of_discrete⟩⟩
  let ind : Fin n → (Fin n ⊕ Unit) → ℝ := fun i z => if z = Sum.inl i then 1 else 0
  have hdemand_eq : ∀ (i : Fin n) (ω : Fin N → Fin n ⊕ Unit),
      demand i ω = ∑ k : Fin N, ind i (ω k) := by
    intro i ω
    unfold demand ind
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hdemand_fun : ∀ i : Fin n,
      demand (N := N) i = fun ω => ∑ k : Fin N, ind i (ω k) := by
    intro i
    ext ω
    exact hdemand_eq i ω
  have hind_int : ∀ i : Fin n, ∫ z, ind i z ∂ν = choiceProb ν i := by
    intro i
    rw [integral_fintype ((MemLp.of_discrete (p := 2)).integrable one_le_two)]
    rw [Finset.sum_eq_single (Sum.inl i)]
    · simp [ind, choiceProb]
    · intro z _ hz
      simp [ind, hz]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hind_cov : ∀ i j : Fin n,
      covariance (ind i) (ind j) ν =
        (if i = j then choiceProb ν i else 0) - choiceProb ν i * choiceProb ν j := by
    intro i j
    rw [covariance_eq_sub MemLp.of_discrete MemLp.of_discrete, hind_int i, hind_int j]
    congr 1
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hsq : ind i * ind i = ind i := by
        ext z
        dsimp [ind]
        split_ifs <;> norm_num
      rw [hsq, hind_int i]
    · rw [if_neg hij]
      have hzero : ind i * ind j = 0 := by
        ext z
        dsimp [ind]
        split_ifs with h1 h2
        · exfalso
          exact hij (Sum.inl.inj (h1.symm.trans h2))
        · simp
        · simp
        · simp
      rw [hzero]
      simp
  have hμ_prob : IsProbabilityMeasure (customerLaw N ν) := by
    unfold customerLaw
    infer_instance
  have hmean_demand : ∀ i : Fin n,
      (∫ ω, demand i ω ∂(customerLaw N ν)) = (N : ℝ) * choiceProb ν i := by
    intro i
    simp_rw [hdemand_eq i]
    rw [integral_finsetSum Finset.univ
      (fun k _ => (MemLp.of_discrete (p := 2)).integrable one_le_two)]
    have hterm : ∀ k : Fin N,
        (∫ ω, ind i (ω k) ∂(customerLaw N ν)) = choiceProb ν i := by
      intro k
      unfold customerLaw
      rw [integral_comp_eval (MemLp.of_discrete (p := 2)).aestronglyMeasurable, hind_int i]
    simp_rw [hterm]
    simp
  have hmean : (∫ ω, randomProfit m ω ∂(customerLaw N ν)) =
      (N : ℝ) * ∑ i, m i * choiceProb ν i := by
    unfold randomProfit
    rw [integral_finsetSum Finset.univ
      (fun i _ => (MemLp.of_discrete (p := 2)).integrable one_le_two)]
    simp_rw [integral_const_mul, hmean_demand]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hvar_cov : variance (randomProfit (N := N) m) (customerLaw N ν) =
      ∑ i, ∑ j, m i * m j * covariance (demand (N := N) i) (demand j) (customerLaw N ν) := by
    unfold randomProfit
    rw [variance_fun_sum (fun _ => MemLp.of_discrete)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, mul_assoc]
  have hcov_eval : ∀ (i j : Fin n) (k l : Fin N),
      covariance (fun ω : Fin N → Fin n ⊕ Unit => ind i (ω k))
        (fun ω => ind j (ω l)) (customerLaw N ν) =
        if k = l then covariance (ind i) (ind j) ν else 0 := by
    intro i j k l
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      unfold customerLaw
      have hmp := measurePreserving_eval (fun _ : Fin N => ν) k
      change covariance ((ind i) ∘ (fun ω => ω k)) ((ind j) ∘ (fun ω => ω k))
        (Measure.pi fun _ => ν) = _
      rw [← covariance_map (hmp.map_eq.symm ▸ (MemLp.of_discrete (p := 2)).aestronglyMeasurable)
        (hmp.map_eq.symm ▸ (MemLp.of_discrete (p := 2)).aestronglyMeasurable) hmp.aemeasurable,
        hmp.map_eq]
    · rw [if_neg hkl]
      unfold customerLaw
      let f : Fin N → (Fin n ⊕ Unit) → ℝ := fun r => if r = k then ind i else ind j
      have hindep_all := iIndepFun_pi (μ := fun _ : Fin N => ν)
        (X := f) (fun r => Measurable.of_discrete.aemeasurable)
      have hindep := hindep_all.indepFun hkl
      have hfk : (fun ω : Fin N → Fin n ⊕ Unit => f k (ω k)) = fun ω => ind i (ω k) := by
        ext ω
        simp [f]
      have hfl : (fun ω : Fin N → Fin n ⊕ Unit => f l (ω l)) = fun ω => ind j (ω l) := by
        ext ω
        simp [f, Ne.symm hkl]
      rw [hfk, hfl] at hindep
      exact hindep.covariance_eq_zero MemLp.of_discrete MemLp.of_discrete
  have hcov_demand : ∀ i j : Fin n,
      covariance (demand (N := N) i) (demand (N := N) j) (customerLaw N ν) =
        (N : ℝ) * covariance (ind i) (ind j) ν := by
    intro i j
    rw [hdemand_fun i, hdemand_fun j]
    rw [covariance_fun_sum_fun_sum (fun _ => MemLp.of_discrete) (fun _ => MemLp.of_discrete)]
    simp_rw [hcov_eval i j]
    have hinner : ∀ k : Fin N,
        (∑ l : Fin N, if k = l then covariance (ind i) (ind j) ν else 0) =
          covariance (ind i) (ind j) ν := by
      intro k
      simp
    simp_rw [hinner]
    simp
  have hvar_split : variance (randomProfit (N := N) m) (customerLaw N ν) =
      (N : ℝ) * (∑ i, m i ^ 2 * choiceProb ν i * (1 - choiceProb ν i) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, m i * m j * choiceProb ν i * choiceProb ν j) := by
    rw [hvar_cov]
    simp_rw [hcov_demand, hind_cov]
    have hrow : ∀ i : Fin n,
        (∑ j : Fin n, m i * m j * ((N : ℝ) *
          ((if i = j then choiceProb ν i else 0) - choiceProb ν i * choiceProb ν j))) =
        (N : ℝ) * (m i ^ 2 * choiceProb ν i * (1 - choiceProb ν i) -
          ∑ j ∈ Finset.univ.erase i, m i * m j * choiceProb ν i * choiceProb ν j) := by
      intro i
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      rw [if_pos rfl]
      have herase :
          (∑ j ∈ Finset.univ.erase i, m i * m j * ((N : ℝ) *
            ((if i = j then choiceProb ν i else 0) - choiceProb ν i * choiceProb ν j))) =
          -(N : ℝ) * ∑ j ∈ Finset.univ.erase i, m i * m j * choiceProb ν i * choiceProb ν j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        rw [if_neg hji]
        ring
      rw [herase]
      ring
    simp_rw [hrow, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hvar_compact : variance (randomProfit (N := N) m) (customerLaw N ν) =
      (N : ℝ) * (∑ i, m i ^ 2 * choiceProb ν i - (∑ i, m i * choiceProb ν i) ^ 2) := by
    rw [hvar_split]
    congr 1
    have hsq : (∑ i, m i * choiceProb ν i) ^ 2 =
        ∑ i, (m i ^ 2 * choiceProb ν i ^ 2 +
          ∑ j ∈ Finset.univ.erase i, m i * m j * choiceProb ν i * choiceProb ν j) := by
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        ring
    rw [hsq, Finset.sum_add_distrib]
    have hsub : (∑ i, m i ^ 2 * choiceProb ν i * (1 - choiceProb ν i)) =
        (∑ i, m i ^ 2 * choiceProb ν i) - ∑ i, m i ^ 2 * choiceProb ν i ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsub]
    ring
  exact ⟨hmean, hvar_cov, hvar_split, hvar_compact⟩
