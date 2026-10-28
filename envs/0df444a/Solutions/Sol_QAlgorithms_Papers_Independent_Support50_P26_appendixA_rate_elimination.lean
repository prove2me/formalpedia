-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P26.appendixA_rate_elimination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:59:16.779027+00:00
-- url     : https://prove2.me/submissions/9771ee29-5c37-4786-8736-0aa5701ffa71

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

theorem S169_pointwise (p a b : ℝ) (hp : 0 ≤ p) (ha : p ≤ a) (hb : p ≤ b) :
    p - a * b ≤ p * Real.log p - p * Real.log a - p * Real.log b := by
  rcases eq_or_lt_of_le hp with h0 | h0
  · subst h0; simp; nlinarith
  · have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have := Real.log_le_sub_one_of_pos (show 0 < a * b / p by positivity)
    rw [Real.log_div (by positivity) h0.ne', Real.log_mul ha0.ne' hb0.ne'] at this
    have h2 : p * (Real.log a + Real.log b - Real.log p) ≤ p * (a * b / p - 1) :=
      mul_le_mul_of_nonneg_left this hp
    have e : p * (a * b / p - 1) = a * b - p := by field_simp
    rw [e] at h2
    nlinarith

theorem S169_auxMI_nonneg {X U V : Type} [Fintype X] [Fintype U] [Fintype V]
    (D : MartonData U V X) : 0 ≤ auxiliaryMI D := by
  set p := D.law.prob with hp
  set pu : U → ℝ := fun u => ∑ v, p (u, v) with hpu
  set pv : V → ℝ := fun v => ∑ u, p (u, v) with hpv
  have hpn : ∀ x, 0 ≤ p x := D.law.nonneg
  have hu : ∀ u v, p (u, v) ≤ pu u := fun u v =>
    Finset.single_le_sum (f := fun v => p (u, v)) (fun v _ => hpn _) (Finset.mem_univ v)
  have hv : ∀ u v, p (u, v) ≤ pv v := fun u v =>
    Finset.single_le_sum (f := fun u => p (u, v)) (fun u _ => hpn _) (Finset.mem_univ u)
  have htot : ∑ u, ∑ v, p (u, v) = 1 := by rw [← Fintype.sum_prod_type']; exact D.law.total
  have htot' : ∑ v, ∑ u, p (u, v) = 1 := by rw [Finset.sum_comm]; exact htot
  have hsum : 0 ≤ ∑ u, ∑ v, (p (u, v) * Real.log (p (u, v)) - p (u, v) * Real.log (pu u)
      - p (u, v) * Real.log (pv v)) := by
    have h1 : ∑ u, ∑ v, (p (u, v) - pu u * pv v) ≤ ∑ u, ∑ v, (p (u, v) * Real.log (p (u, v))
        - p (u, v) * Real.log (pu u) - p (u, v) * Real.log (pv v)) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
        S169_pointwise _ _ _ (hpn _) (hu u v) (hv u v)
    have h2 : ∑ u, ∑ v, (p (u, v) - pu u * pv v) = 0 := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [htot]
      have : ∑ v, pv v = 1 := htot'
      have : ∑ u, pu u = 1 := htot
      simp_all
    linarith
  have e1 : ∑ u, ∑ v, p (u, v) * Real.log (pu u) = ∑ u, pu u * Real.log (pu u) := by
    simp only [hpu, Finset.sum_mul]
  have e2 : ∑ u, ∑ v, p (u, v) * Real.log (pv v) = ∑ v, pv v * Real.log (pv v) := by
    rw [Finset.sum_comm]; simp only [hpv, Finset.sum_mul]
  have e3 : ∑ u, ∑ v, p (u, v) * Real.log (p (u, v)) = ∑ x, p x * Real.log (p x) := by
    rw [← Fintype.sum_prod_type']
  have hmain : 0 ≤ ∑ x, p x * Real.log (p x) - ∑ u, pu u * Real.log (pu u)
      - ∑ v, pv v * Real.log (pv v) := by
    rw [← e1, ← e2, ← e3]
    simp only [Finset.sum_sub_distrib] at hsum
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : auxiliaryMI D = (∑ x, p x * Real.log (p x) - ∑ u, pu u * Real.log (pu u)
      - ∑ v, pv v * Real.log (pv v)) / Real.log 2 := by
    simp only [auxiliaryMI, shannon, Real.logb, ← hp]
    rw [eq_div_iff hl2.ne']
    simp only [Finset.sum_mul, neg_mul, Finset.sum_neg_distrib, sub_mul, add_mul]
    have : ∀ y z : ℝ, y * (z / Real.log 2) * Real.log 2 = y * z := fun y z => by
      field_simp
    simp only [this]
    rw [← e1, ← e2]
    simp only [hpu, hpv]
    rw [Finset.sum_comm (s := (Finset.univ : Finset U)) (t := (Finset.univ : Finset V))
      (f := fun u v => p (u, v) * Real.log (∑ u', p (u', v)))]
    ring
  rw [key]
  exact div_nonneg hmain hl2.le

end QAlgorithms.Papers.Independent.Support50.P26

open QAlgorithms.Papers.Independent.Support50.P26 in
open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI) in
theorem solution {X B1 B2 U V : Type} [Fintype X] [Fintype B1] [Fintype B2] [Fintype U] [Fintype V]
    [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq U] [DecidableEq V]
    (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (r : ℝ × ℝ) (h1 : 0 ≤ r.1) (h2 : 0 ≤ r.2) :
    (∃ t1 t2 : ℝ, auxiliaryRateSystem
      (quantumMI (martonU1B1 C D)) (quantumMI (martonU2B2 C D)) (auxiliaryMI D) r t1 t2) ↔
    r ∈ MartonRegion C D := by
  have hc := S169_auxMI_nonneg D
  set a := quantumMI (martonU1B1 C D)
  set b := quantumMI (martonU2B2 C D)
  set c := auxiliaryMI D
  simp only [auxiliaryRateSystem, MartonRegion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t1, t2, k1, k2, k3, k4, k5, k6, k7⟩
    refine ⟨h1, h2, by linarith, by linarith, by linarith⟩
  · rintro ⟨-, -, k3, k4, k5⟩
    refine ⟨r.1 + min (a - r.1) c, r.2 + c - min (a - r.1) c, ?_⟩
    rcases min_cases (a - r.1) c with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;>
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith⟩

