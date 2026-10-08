-- Prove2me | solution 1 for WardropTraffic.MinTime.min_average_time_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:06:57.907459+00:00
-- url     : https://prove2.me/submissions/4998e1f1-cf71-436d-8e9e-b99ce14f1c3f

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting
open WardropTraffic.MinTime WardropTraffic.EqualTimes
open Filter Set
open scoped Topology

-- Local restatement of the derivative fact; no theorem-module import.
private theorem route_derivative {D : ℕ} (b p : Fin D → ℝ) (i : Fin D) (x : ℝ)
    (hp : 0 < p i) (hx : x < p i) :
    HasDerivAt (fun u => u * routeTime b p i u) (b i / (1 - x / p i)^2) x := by
  have hd : 1 - x / p i ≠ 0 := ne_of_gt (sub_pos.mpr ((div_lt_one hp).mpr hx))
  have h := (hasDerivAt_id x).fun_mul
    ((hasDerivAt_const x (b i)).fun_div
      ((hasDerivAt_const x (1 : ℝ)).fun_sub ((hasDerivAt_id x).div_const (p i))) hd)
  convert h using 1 <;> try rfl
  dsimp
  field_simp
  <;> ring

private theorem marginal_le {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hp : ∀ k, 0 < p k) (hQ : 0 < Q) (q : Fin D → ℝ)
    (hmin : IsMinAvgTime b p Q q) (i j : Fin D) (hi : 0 < q i) :
    b i / (1 - q i / p i)^2 ≤ b j / (1 - q j / p j)^2 := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  let z : ℝ → Fin D → ℝ := fun u k =>
    q k + u * (if k = j then 1 else 0) - u * (if k = i then 1 else 0)
  let M : Fin D → ℝ := fun k => b k / (1 - q k / p k)^2
  have hz0 : z 0 = q := by ext k; simp [z]
  have hfeas : ∀ᶠ u in 𝓝[Set.Ici (0 : ℝ)] 0, IsFeasible p Q (z u) := by
    have hjcap : 0 < p j - q j := sub_pos.mpr (hmin.1.1 j).2
    have huv : ∀ᶠ u in 𝓝 (0 : ℝ), u < min (q i) (p j - q j) :=
      eventually_lt_nhds (lt_min hi hjcap)
    filter_upwards [huv.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hu0
    have hui := (lt_min_iff.mp hu).1
    have huj := (lt_min_iff.mp hu).2
    have hu0' : 0 ≤ u := hu0
    refine ⟨?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst k
        simp only [z, if_true, if_neg hij, mul_zero, mul_one, add_zero]
        constructor <;> linarith [(hmin.1.1 i).2]
      · by_cases hkj : k = j
        · subst k
          simp only [z, if_true, if_neg (Ne.symm hij), mul_one, mul_zero, sub_zero]
          constructor <;> linarith [(hmin.1.1 j).1]
        · simpa [z, hki, hkj] using hmin.1.1 k
    · simp only [z, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hmin.1.2]
      simp
  have hder : HasDerivAt (fun u => avgTime b p Q (z u)) ((M j - M i) / Q) 0 := by
    have hk : ∀ k : Fin D, HasDerivAt (fun u => z u k * routeTime b p k (z u k))
        (M k * ((if k = j then 1 else 0) - (if k = i then 1 else 0))) 0 := by
      intro k
      have hd : HasDerivAt (fun u => z u k)
          ((if k = j then 1 else 0) - (if k = i then 1 else 0)) 0 := by
        simpa [z] using
          (((hasDerivAt_const 0 (q k)).fun_add ((hasDerivAt_id 0).mul_const (if k = j then (1 : ℝ) else 0))).fun_sub
            ((hasDerivAt_id 0).mul_const (if k = i then (1 : ℝ) else 0)))
      have hr : HasDerivAt (fun u => u * routeTime b p k u) (M k) (z 0 k) := by
        simpa [z, M] using route_derivative b p k (q k) (hp k) (hmin.1.1 k).2
      have hc := hr.comp 0 hd
      simpa only [Function.comp_def] using hc
    have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hk k)).div_const Q
    convert hh using 1 <;> try rfl
    simp [mul_sub, Finset.sum_sub_distrib]
  have hloc : IsLocalMinOn (fun u => avgTime b p Q (z u)) (Set.Ici 0) 0 := by
    filter_upwards [hfeas] with u hu
    rw [hz0]
    exact hmin.2 (z u) hu
  have ht : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa using le_of_lt hu
  have hn := hloc.hasFDerivWithinAt_nonneg hder.hasFDerivAt.hasFDerivWithinAt ht
  have hn' : 0 ≤ (M j - M i) / Q := by simpa using hn
  have : 0 ≤ M j - M i := by
    have hm := mul_nonneg hn' hQ.le
    rwa [div_mul_cancel₀ _ hQ.ne'] at hm
  exact sub_nonneg.mp this




private theorem used_characterization {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) (ε : ℝ)
    (hε : ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε) :
    0 < ε ∧ ∀ i, (0 < q i ↔ b i < ε) ∧
      (0 < q i → 1 - q i / p i = Real.sqrt (b i / ε)) := by
  classical
  have hex : ∃ i, 0 < q i := by
    by_contra h
    have hz : ∀ i, q i = 0 := by
      intro i
      have := (hmin.1.1 i).1
      have hn : ¬ 0 < q i := fun hh => h ⟨i, hh⟩
      linarith
    have he := hmin.1.2
    simp [hz] at he
    linarith
  obtain ⟨j, hj⟩ := hex
  have hεpos : 0 < ε := by
    rw [← hε j hj]
    exact div_pos (hb j) (sq_pos_of_pos (sub_pos.mpr ((div_lt_one (hp j)).mpr (hmin.1.1 j).2)))
  refine ⟨hεpos, ?_⟩
  intro i
  constructor
  · constructor
    · intro hqi
      have hd0 : 0 < 1 - q i / p i := sub_pos.mpr ((div_lt_one (hp i)).mpr (hmin.1.1 i).2)
      have hd1 : 1 - q i / p i < 1 := by have := div_pos hqi (hp i); linarith
      have hm := (div_eq_iff (ne_of_gt (sq_pos_of_pos hd0))).mp (hε i hqi)
      have hsq : (1 - q i / p i)^2 < 1 := by nlinarith
      nlinarith
    · intro hbε
      by_contra h
      have hzero : q i = 0 := by have := (hmin.1.1 i).1; linarith
      have hh := marginal_le b p Q hp hQ q hmin j i hj
      rw [hε j hj, hzero] at hh
      simp at hh
      linarith
  · intro hqi
    have hd : 0 < 1 - q i / p i := sub_pos.mpr ((div_lt_one (hp i)).mpr (hmin.1.1 i).2)
    have hm := (div_eq_iff (ne_of_gt (sq_pos_of_pos hd))).mp (hε i hqi)
    have he : b i / ε = (1 - q i / p i)^2 := (div_eq_iff hεpos.ne').mpr (by nlinarith [hm])
    rw [he, Real.sqrt_sq hd.le]

private theorem common_marginal {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) :
    ∃ ε : ℝ, ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε := by
  classical
  have hex : ∃ i, 0 < q i := by
    by_contra h
    have hz : ∀ i, q i = 0 := by
      intro i
      have := (hmin.1.1 i).1
      have hn : ¬ 0 < q i := fun hh => h ⟨i, hh⟩
      linarith
    have he := hmin.1.2
    simp [hz] at he
    linarith
  obtain ⟨j, hj⟩ := hex
  refine ⟨b j / (1 - q j / p j)^2, ?_⟩
  intro i hi
  exact le_antisymm (marginal_le b p Q hp hQ q hmin i j hi)
    (marginal_le b p Q hp hQ q hmin j i hj)



theorem solution {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) :
    ∃ ε : ℝ, 0 < ε ∧ Q < ∑ i ∈ usedSet b ε, p i ∧
      (∀ h, q h = if b h < ε then
          p h * (1 - (∑ i ∈ usedSet b ε, p i - Q) * Real.sqrt (b h) /
            ∑ i ∈ usedSet b ε, p i * Real.sqrt (b i))
        else 0) ∧
      avgTime b p Q q = (1 / Q) * ((∑ i ∈ usedSet b ε, p i * Real.sqrt (b i)) ^ 2 /
          (∑ i ∈ usedSet b ε, p i - Q) - ∑ i ∈ usedSet b ε, p i * b i) := by
  classical
  obtain ⟨ε, hε⟩ := common_marginal b p Q hb hp hQ hQp q hmin
  obtain ⟨hepos, hu⟩ := used_characterization b p Q hb hp hQ hQp q hmin ε hε
  let U := usedSet b ε
  let S := ∑ i ∈ U, p i * Real.sqrt (b i)
  let R := (∑ i ∈ U, p i) - Q
  let k := Real.sqrt ε
  have hk : 0 < k := Real.sqrt_pos.mpr hepos
  have hq0 (i : Fin D) (hi : i ∉ U) : q i = 0 := by
    have hn : ¬ b i < ε := by simpa [U, usedSet] using hi
    have hnq : ¬ 0 < q i := fun hh => hn ((hu i).1.mp hh)
    linarith [(hmin.1.1 i).1]
  have hden (i : Fin D) (hi : i ∈ U) : 1 - q i / p i = Real.sqrt (b i) / k := by
    have hbε : b i < ε := by simpa [U, usedSet] using hi
    rw [(hu i).2 ((hu i).1.mpr hbε), Real.sqrt_div (hb i).le]
  have hcoord (i : Fin D) (hi : i ∈ U) : p i - q i = p i * Real.sqrt (b i) / k := by
    have hh := hden i hi
    field_simp [(hp i).ne', hk.ne'] at hh ⊢
    nlinarith
  have hsumq : ∑ i ∈ U, q i = Q := by
    rw [← hmin.1.2]
    exact Finset.sum_subset (Finset.subset_univ U) (fun i _ hi => hq0 i hi)
  have hr : R = S / k := by
    dsimp [R, S]
    rw [← hsumq, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl hcoord]
    rw [Finset.sum_div]
  have hRpos : 0 < R := by
    dsimp [R]
    rw [← hsumq, ← Finset.sum_sub_distrib]
    apply Finset.sum_pos'
    · intro i hi
      exact (sub_pos.mpr (hmin.1.1 i).2).le
    · have hex : ∃ i, 0 < q i := by
        by_contra hn
        have hz : ∀ i, q i = 0 := by
          intro i
          have hni : ¬ 0 < q i := fun hh => hn ⟨i, hh⟩
          linarith [(hmin.1.1 i).1]
        have hh := hmin.1.2
        simp [hz] at hh
        linarith
      obtain ⟨i, hi⟩ := hex
      refine ⟨i, ?_, sub_pos.mpr (hmin.1.1 i).2⟩
      simpa [U, usedSet] using (hu i).1.mp hi
  have hS : S = R * k := by rw [hr]; field_simp
  have hSpos : 0 < S := by rw [hS]; positivity
  have hinv : R / S = 1 / k := by rw [hS]; field_simp [hRpos.ne', hk.ne']
  refine ⟨ε, hepos, ?_, ?_, ?_⟩
  · change Q < ∑ i ∈ U, p i
    dsimp [R] at hRpos
    linarith
  · intro i
    split_ifs with hi
    · have hui : i ∈ U := by simpa [U, usedSet] using hi
      change q i = p i * (1 - R * Real.sqrt (b i) / S)
      have hh := hcoord i hui
      rw [show R * Real.sqrt (b i) / S = Real.sqrt (b i) / k by
        calc
          _ = (R / S) * Real.sqrt (b i) := by ring
          _ = _ := by rw [hinv]; ring]
      rw [mul_sub, mul_one, ← mul_div_assoc]
      linarith
    · exact hq0 i (by simpa [U, usedSet] using hi)
  · have hterm (i : Fin D) (hi : i ∈ U) :
        q i * routeTime b p i (q i) = p i * Real.sqrt (b i) * k - p i * b i := by
      rw [routeTime, hden i hi]
      have hsqi : 0 < Real.sqrt (b i) := Real.sqrt_pos.mpr (hb i)
      have hsq := Real.sq_sqrt (hb i).le
      have hh := hcoord i hi
      have hqi : q i = p i - p i * Real.sqrt (b i) / k := by linarith
      rw [hqi, ← hsq]
      rw [Real.sqrt_sq hsqi.le]
      field_simp [hk.ne', hsqi.ne']
      <;> ring
    have htotal : totalExtra b p q = S * k - ∑ i ∈ U, p i * b i := by
      unfold totalExtra
      rw [← Finset.sum_subset (Finset.subset_univ U) (fun i _ hi => by rw [hq0 i hi]; simp)]
      rw [Finset.sum_congr rfl hterm]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    change totalExtra b p q / Q = (1 / Q) * (S ^ 2 / R - ∑ i ∈ U, p i * b i)
    rw [htotal, hS]
    field_simp [hRpos.ne', hQ.ne']
    <;> ring

#print axioms solution
