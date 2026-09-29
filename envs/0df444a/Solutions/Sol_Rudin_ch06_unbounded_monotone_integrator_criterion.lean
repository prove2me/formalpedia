-- Prove2me | solution 1 for Rudin.ch06_unbounded_monotone_integrator_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T17:09:37.021349+00:00
-- url     : https://prove2.me/submissions/e9093221-970c-4aac-9abb-4327b68b58f2

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace RudinCriterionAux

open Rudin

/-- Division points of a partition increase with the index. -/
lemma x_mono {a b : ℝ} (P : Partition a b) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j hij hjn
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      simp [this]
  | succ k ih =>
      have hk : k < P.n := hjn
      rcases Nat.eq_or_lt_of_le hij with h | h
      · exact le_of_eq (by rw [h])
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        exact (ih hik (le_of_lt hk)).trans (P.mono k hk)

/-- Every division point lies in the interval. -/
lemma x_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have h := x_mono P (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := x_mono P hi (le_refl P.n)
    rwa [P.last] at h

/-- The trivial partition of `[0, 1]` with a single subinterval. -/
def trivPart : Partition (0:ℝ) 1 where
  n := 1
  x := fun i => if i = 0 then 0 else 1
  first := by simp
  last := by norm_num
  mono := by
    intro i hi
    interval_cases i
    norm_num

/-- The partition of `[0, 1]` with division points `0, u, v, 1`. -/
def fourPart {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) : Partition (0:ℝ) 1 where
  n := 3
  x := fun i => if i = 0 then 0 else if i = 1 then u else if i = 2 then v else 1
  first := by simp
  last := by norm_num
  mono := by
    intro i hi
    interval_cases i
    · simpa using hu
    · simpa using huv
    · simpa using hv

section

variable {g : ℝ → ℝ}

lemma sInf_nonneg (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) : 0 ≤ sInf (g '' Set.Icc u v) := by
  have hsub : Set.Icc u v ⊆ Set.Icc (0:ℝ) 1 := Set.Icc_subset_Icc hu hv
  refine le_csInf ⟨g u, u, ⟨le_rfl, huv⟩, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hnn x (hsub hx)

/-- Every upper sum of a nonnegative integrand (with `α = id`) is nonnegative. -/
lemma upperSum_nonneg (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x) (P : Partition (0:ℝ) 1) :
    0 ≤ upperSum g id P := by
  refine Finset.sum_nonneg ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
  have hmi : P.x i ∈ Set.Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
  have hsup : 0 ≤ sSup (g '' Set.Icc (P.x i) (P.x (i + 1))) := by
    by_cases hb : BddAbove (g '' Set.Icc (P.x i) (P.x (i + 1)))
    · exact le_trans (hnn _ hmi) (le_csSup hb ⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩)
    · simp [Real.sSup_of_not_bddAbove hb]
  have hfac : (0:ℝ) ≤ id (P.x (i + 1)) - id (P.x i) := by
    simpa using sub_nonneg.mpr hle
  exact mul_nonneg hsup hfac

/-- If a nonnegative integrand is unbounded above on `[0, 1]`, its upper integral is `0`. -/
lemma upperIntegral_eq_zero (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hunb : ¬ BddAbove (g '' Set.Icc (0:ℝ) 1)) : upperIntegral 0 1 g id = 0 := by
  have h0 : upperSum g id trivPart = 0 := by
    simp [upperSum, trivPart, Real.sSup_of_not_bddAbove hunb]
  have hmem : (0:ℝ) ∈ {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum g id P} := ⟨trivPart, h0.symm⟩
  have hlb : ∀ y ∈ {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum g id P}, (0:ℝ) ≤ y := by
    rintro y ⟨P, rfl⟩
    exact upperSum_nonneg hnn P
  exact le_antisymm (csInf_le ⟨0, fun y hy => hlb y hy⟩ hmem) (le_csInf ⟨0, hmem⟩ hlb)

end

/-- Every lower sum of the derivative of a monotone function is at most its total increment:
on each subinterval the mean value theorem produces a point where the derivative equals the
slope, and the infimum does not exceed it. -/
lemma lowerSum_le (α : ℝ → ℝ) (hdiff : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x)
    (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ deriv α x) (P : Partition (0:ℝ) 1) :
    lowerSum (deriv α) id P ≤ α 1 - α 0 := by
  have hterm : ∀ i ∈ Finset.range P.n,
      sInf (deriv α '' Set.Icc (P.x i) (P.x (i + 1))) * (id (P.x (i + 1)) - id (P.x i))
        ≤ α (P.x (i + 1)) - α (P.x i) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp hi
    have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
    have hmi : P.x i ∈ Set.Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
    have hmi1 : P.x (i + 1) ∈ Set.Icc (0:ℝ) 1 := x_mem P (Nat.succ_le_of_lt hi')
    rcases eq_or_lt_of_le hle with h | h
    · simp [h]
    · have hsub : Set.Icc (P.x i) (P.x (i + 1)) ⊆ Set.Icc (0:ℝ) 1 :=
        Set.Icc_subset_Icc hmi.1 hmi1.2
      have hcont : ContinuousOn α (Set.Icc (P.x i) (P.x (i + 1))) := by
        intro y hy
        exact ((hdiff y (hsub hy)).continuousAt).continuousWithinAt
      obtain ⟨c, hc, hslope⟩ :=
        exists_hasDerivAt_eq_slope α (deriv α) h hcont
          (fun y hy => hdiff y (hsub (Set.mem_Icc_of_Ioo hy)))
      have hbdd : BddBelow (deriv α '' Set.Icc (P.x i) (P.x (i + 1))) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        exact hnn x (hsub hx)
      have hmem : deriv α c ∈ deriv α '' Set.Icc (P.x i) (P.x (i + 1)) :=
        ⟨c, Set.mem_Icc_of_Ioo hc, rfl⟩
      have hInf : sInf (deriv α '' Set.Icc (P.x i) (P.x (i + 1))) ≤ deriv α c := csInf_le hbdd hmem
      have hpos : (0:ℝ) < P.x (i + 1) - P.x i := sub_pos.mpr h
      have : sInf (deriv α '' Set.Icc (P.x i) (P.x (i + 1))) * (P.x (i + 1) - P.x i)
          ≤ deriv α c * (P.x (i + 1) - P.x i) := by
        exact mul_le_mul_of_nonneg_right hInf (le_of_lt hpos)
      rw [hslope] at this
      field_simp at this
      simpa using this
  calc lowerSum (deriv α) id P
      ≤ ∑ i ∈ Finset.range P.n, (α (P.x (i + 1)) - α (P.x i)) :=
        Finset.sum_le_sum hterm
    _ = α 1 - α 0 := by
        rw [Finset.sum_range_sub (fun i => α (P.x i)), P.first, P.last]

end RudinCriterionAux

open Rudin RudinCriterionAux

/-- For a monotone, everywhere differentiable integrator whose derivative is unbounded above on
`[0,1]`, Riemann integrability of the derivative forces the integral to vanish and the derivative
to take arbitrarily small values on every nondegenerate subinterval. -/
theorem solution (α : ℝ → ℝ) (hmono : Monotone α)
    (hdiff : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x)
    (hunb : ∀ K : ℝ, ∃ x ∈ Set.Icc (0:ℝ) 1, K < deriv α x)
    (hint : RiemannIntegrable 0 1 (deriv α)) :
    RiemannIntegral 0 1 (deriv α) = 0 ∧
      ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, deriv α x < ε := by
  have hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ deriv α x := fun x _ => hmono.deriv_nonneg
  have hunb' : ¬ BddAbove (deriv α '' Set.Icc (0:ℝ) 1) := by
    rintro ⟨K, hK⟩
    obtain ⟨x, hx, hlt⟩ := hunb K
    exact absurd (hK ⟨x, hx, rfl⟩) (not_le.mpr hlt)
  have hup : upperIntegral 0 1 (deriv α) id = 0 := upperIntegral_eq_zero hnn hunb'
  have hlo : lowerIntegral 0 1 (deriv α) id = 0 := by
    have := hint
    unfold RiemannIntegrable RSIntegrable at this
    rw [hup] at this
    exact this.symm
  refine ⟨by unfold RiemannIntegral RSIntegral; exact hup, ?_⟩
  intro u v hu huv hv ε hε
  by_contra hcon
  push Not at hcon
  -- every value of the derivative on `[u,v]` is at least `ε`
  have hge : ∀ x ∈ Set.Icc u v, ε ≤ deriv α x := hcon
  -- the four-point partition `0, u, v, 1` has a strictly positive lower sum
  set P := fourPart hu (le_of_lt huv) hv with hP
  have hx0 : P.x 0 = 0 := rfl
  have hx1 : P.x 1 = u := rfl
  have hx2 : P.x 2 = v := rfl
  have hx3 : P.x 3 = 1 := rfl
  have hmid : ε ≤ sInf (deriv α '' Set.Icc u v) := by
    refine le_csInf ⟨deriv α u, u, ⟨le_rfl, le_of_lt huv⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hge x hx
  have hsum : lowerSum (deriv α) id P = sInf (deriv α '' Set.Icc 0 u) * (u - 0)
      + sInf (deriv α '' Set.Icc u v) * (v - u)
      + sInf (deriv α '' Set.Icc v 1) * (1 - v) := by
    simp [lowerSum, hP, fourPart, Finset.sum_range_succ]
  have h1 : 0 ≤ sInf (deriv α '' Set.Icc 0 u) * (u - 0) := by
    refine mul_nonneg (sInf_nonneg hnn le_rfl hu (le_trans (le_of_lt huv) hv)) ?_
    simpa using hu
  have h3 : 0 ≤ sInf (deriv α '' Set.Icc v 1) * (1 - v) := by
    refine mul_nonneg (sInf_nonneg hnn (le_trans hu (le_of_lt huv)) hv le_rfl) ?_
    simpa using hv
  have h2 : 0 < sInf (deriv α '' Set.Icc u v) * (v - u) :=
    mul_pos (lt_of_lt_of_le hε hmid) (sub_pos.mpr huv)
  have hpos : 0 < lowerSum (deriv α) id P := by
    rw [hsum]; linarith
  -- but every lower sum is at most the lower integral, which is `0`
  have hbddA : BddAbove {y : ℝ | ∃ Q : Partition (0:ℝ) 1, y = lowerSum (deriv α) id Q} := by
    refine ⟨α 1 - α 0, ?_⟩
    rintro y ⟨Q, rfl⟩
    exact lowerSum_le α hdiff hnn Q
  have hle : lowerSum (deriv α) id P ≤ lowerIntegral 0 1 (deriv α) id := by
    unfold lowerIntegral
    exact le_csSup hbddA ⟨P, rfl⟩
  rw [hlo] at hle
  linarith
