-- Prove2me | solution 1 for WardropTraffic.MinTime.sum_eq_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:58:57.298021+00:00
-- url     : https://prove2.me/submissions/4005f781-e896-45bf-9585-d4656915ba4f

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


theorem solution {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) (ε : ℝ)
    (hε : ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε) :
    ∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i - Q = ∑ i ∈ WardropTraffic.EqualTimes.usedSet b ε, p i * Real.sqrt (b i / ε) := by
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
  have hsupport : ∀ i, b i < ε ↔ 0 < q i := by
    intro i
    constructor
    · intro hbε
      by_contra h
      have hzero : q i = 0 := by have := (hmin.1.1 i).1; linarith
      have hh := marginal_le b p Q hp hQ q hmin j i hj
      rw [hε j hj, hzero] at hh
      simp at hh
      linarith
    · intro hqi
      have hd0 : 0 < 1 - q i / p i := sub_pos.mpr ((div_lt_one (hp i)).mpr (hmin.1.1 i).2)
      have hd1 : 1 - q i / p i < 1 := by have := div_pos hqi (hp i); linarith
      have hm := (div_eq_iff (ne_of_gt (sq_pos_of_pos hd0))).mp (hε i hqi)
      have hsq : (1 - q i / p i)^2 < 1 := by nlinarith
      nlinarith
  have hcoord : ∀ i ∈ usedSet b ε, p i - q i = p i * Real.sqrt (b i / ε) := by
    intro i hi
    have hqi := (hsupport i).mp ((Finset.mem_filter.mp hi).2)
    have hd : 0 < 1 - q i / p i := sub_pos.mpr ((div_lt_one (hp i)).mpr (hmin.1.1 i).2)
    have hm := (div_eq_iff (ne_of_gt (sq_pos_of_pos hd))).mp (hε i hqi)
    have he : b i / ε = (1 - q i / p i)^2 := (div_eq_iff hεpos.ne').mpr (by nlinarith [hm])
    rw [he, Real.sqrt_sq hd.le]
    field_simp [(hp i).ne']
  have hsumq : ∑ i ∈ usedSet b ε, q i = Q := by
    rw [usedSet, Finset.sum_filter]
    calc
      _ = ∑ i, q i := by
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs with h
        · rfl
        · have hh : q i = 0 := by
            have hnp : ¬ 0 < q i := fun hh => h ((hsupport i).mpr hh)
            have := (hmin.1.1 i).1
            linarith
          exact hh.symm
      _ = Q := hmin.1.2
  calc
    _ = ∑ i ∈ usedSet b ε, (p i - q i) := by rw [Finset.sum_sub_distrib, hsumq]
    _ = _ := Finset.sum_congr rfl hcoord

#print axioms solution
