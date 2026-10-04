-- Prove2me | solution 1 for TeschlODE.IntervalMaps.chaotic_sensitiveDependence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:11:16.657311+00:00
-- url     : https://prove2.me/submissions/d8f99b89-f598-4c30-be7b-08a37618573c

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsChaotic
import Definitions.Def_TeschlODE_IntervalMaps_SensitiveDependence

open TeschlODE.Shared TeschlODE.IntervalMaps Function

theorem solution {M : Type*} [MetricSpace M] (f : M → M)
    (hf : TeschlODE.Shared.IsChaotic f) : SensitiveDependence f := by
  classical
  obtain ⟨hcont, hinf, htrans, hdense⟩ := hf
  -- the set of periodic points is infinite
  have hPinf : (periodicPts f).Infinite := by
    intro hfin
    have hcl : closure (periodicPts f) = periodicPts f := hfin.isClosed.closure_eq
    rw [hdense.closure_eq] at hcl
    have : (Set.univ : Set M).Finite := by rw [hcl]; exact hfin
    exact (Set.infinite_univ_iff.mpr hinf) this
  -- finite orbits
  let Orb : M → Finset M := fun q => (Finset.range (minimalPeriod f q)).image (fun i => f^[i] q)
  have hOrb : ∀ q ∈ periodicPts f, ∀ k, f^[k] q ∈ Orb q := by
    intro q hq k
    refine Finset.mem_image.mpr ⟨k % minimalPeriod f q, ?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hq))
    · exact (isPeriodicPt_minimalPeriod f q).iterate_mod_apply k
  obtain ⟨q1, hq1⟩ := hPinf.nonempty
  obtain ⟨q2, hq2, hq2n⟩ := (hPinf.diff (Orb q1).finite_toSet).nonempty
  have hdisj : ∀ a ∈ Orb q1, ∀ b ∈ Orb q2, a ≠ b := by
    intro a ha b hb hab
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    apply hq2n
    have hi' : i < minimalPeriod f q2 := Finset.mem_range.mp hi
    have hq : f^[minimalPeriod f q2 - i] (f^[i] q2) = q2 := by
      rw [← iterate_add_apply, Nat.sub_add_cancel hi'.le]
      exact (isPeriodicPt_minimalPeriod f q2).eq
    rw [← hq, ← hab, ← iterate_add_apply]
    exact hOrb q1 hq1 _
  have hne : ((Orb q1) ×ˢ (Orb q2)).Nonempty :=
    ⟨(q1, q2), Finset.mem_product.mpr ⟨by simpa using hOrb q1 hq1 0, by simpa using hOrb q2 hq2 0⟩⟩
  set δ0 : ℝ := ((Orb q1) ×ˢ (Orb q2)).inf' hne (fun pr => dist pr.1 pr.2) with hδ0
  have hδ0pos : 0 < δ0 := by
    rw [hδ0, Finset.lt_inf'_iff]
    rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact dist_pos.mpr (hdisj a ha b hb)
  have hδ0le : ∀ a ∈ Orb q1, ∀ b ∈ Orb q2, δ0 ≤ dist a b := by
    intro a ha b hb
    exact Finset.inf'_le (fun pr : M × M => dist pr.1 pr.2)
      (show (a, b) ∈ Orb q1 ×ˢ Orb q2 from Finset.mem_product.mpr ⟨ha, hb⟩)
  -- every point is far from one of the two orbits
  have hfar : ∀ x : M, ∃ q ∈ periodicPts f, ∀ k, δ0 / 2 ≤ dist x (f^[k] q) := by
    intro x
    by_contra hcon
    push Not at hcon
    obtain ⟨k1, hk1⟩ := hcon q1 hq1
    obtain ⟨k2, hk2⟩ := hcon q2 hq2
    have := hδ0le _ (hOrb q1 hq1 k1) _ (hOrb q2 hq2 k2)
    have := dist_triangle_left (f^[k1] q1) (f^[k2] q2) x
    linarith
  refine ⟨δ0 / 8, by positivity, fun x ε hε => ?_⟩
  set δ : ℝ := δ0 / 8 with hδ
  set ε' : ℝ := min ε δ with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  obtain ⟨p, hxp, hpP⟩ := Metric.dense_iff.mp hdense x ε' hε'pos
  rw [Metric.mem_ball, dist_comm] at hxp
  have hpP' : p ∈ periodicPts f := hpP
  set N := minimalPeriod f p with hN
  have hNpos : 0 < N := minimalPeriod_pos_of_mem_periodicPts hpP'
  obtain ⟨q, hqP, hq⟩ := hfar x
  set V : Set M := ⋂ i ∈ Finset.range (N + 1), (f^[i]) ⁻¹' Metric.ball (f^[i] q) δ with hV
  have hVopen : IsOpen V := by
    refine isOpen_biInter_finset fun i _ => ?_
    exact Metric.isOpen_ball.preimage (hcont.iterate i)
  have hqV : q ∈ V := by
    simp only [hV, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_self]
    intro i _
    positivity
  obtain ⟨k, hk1, z, ⟨y, hyU, rfl⟩, hzV⟩ :=
    htrans (Metric.ball x ε') V Metric.isOpen_ball hVopen ⟨x, Metric.mem_ball_self hε'pos⟩
      ⟨q, hqV⟩
  rw [Metric.mem_ball, dist_comm] at hyU
  -- the return time
  set m : ℕ := N - k % N with hm
  have hkmod : k % N < N := Nat.mod_lt _ hNpos
  have hm1 : 1 ≤ m := by omega
  have hmN : m ≤ N := by omega
  set T : ℕ := m + k with hT
  have hTmul : T = N * (k / N + 1) := by
    have := Nat.div_add_mod k N
    rw [hT, hm]
    rw [mul_add, mul_one]
    omega
  have hT1 : 1 ≤ T := by omega
  have hpT : f^[T] p = p := by
    rw [hTmul]
    exact ((isPeriodicPt_minimalPeriod f p).mul_const _).eq
  have hyT : dist (f^[T] y) (f^[m] q) < δ := by
    have hzV' := hzV
    simp only [hV, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball] at hzV'
    have := hzV' m (Finset.mem_range.mpr (by omega))
    rwa [hT, iterate_add_apply]
  have hxq := hq m
  have hpy : 2 * δ < dist (f^[T] p) (f^[T] y) := by
    rw [hpT]
    have h1 := dist_triangle x p (f^[m] q)
    have h2 := dist_triangle p (f^[T] y) (f^[m] q)
    have hxp' : dist x p < δ := lt_of_lt_of_le hxp (min_le_right ε δ)
    have : δ0 / 2 = 4 * δ := by rw [hδ]; ring
    linarith
  by_cases hcase : δ < dist (f^[T] x) (f^[T] y)
  · exact ⟨y, T, hT1, lt_of_lt_of_le hyU (min_le_left _ _), hcase⟩
  · refine ⟨p, T, hT1, lt_of_lt_of_le hxp (min_le_left _ _), ?_⟩
    push Not at hcase
    have := dist_triangle (f^[T] p) (f^[T] x) (f^[T] y)
    rw [dist_comm (f^[T] p) (f^[T] x)] at this
    linarith

#print axioms solution
