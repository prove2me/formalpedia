-- Prove2me | solution 1 for SelfishRouting.Potential.lemma_2_6_cost_eq
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T15:06:45.858929+00:00
-- url     : https://prove2.me/submissions/4e69d685-359c-4799-a30c-14521989b93d

import Definitions.Def_SelfishRouting_Potential_Model
set_option autoImplicit false
open Finset KellyStochasticNetworks SelfishRouting.Bicriteria
namespace RoutingUniqueness

lemma zero_shift {R : ℕ} (x : Fin R → ℝ) (r t : Fin R) :
    shiftFlow x r t 0 = x := by
  ext q
  simp [shiftFlow]

lemma wardrop_of_nash {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ) (x : Fin R → ℝ)
    (hx : SelfishRouting.Potential.IsNashFlow A s ℓ rate x) :
    IsWardropEquilibrium A s ℓ rate x := by
  refine ⟨hx.1, ?_⟩
  intro r t hst hr
  by_cases hrt : r = t
  · subst t; exact le_rfl
  have h := hx.2 r t hst.symm hrt hr 0 le_rfl hr.le
  simpa only [zero_shift,pathLatency] using h

lemma variational {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ) (x y : Fin R → ℝ)
    (hrate : ∀ i, 0 < rate i) (hx : IsWardropEquilibrium A s ℓ rate x)
    (hy : y ∈ wardropFeasible s rate) :
    (∑ r, pathLatency A ℓ x r * x r) ≤ ∑ r, pathLatency A ℓ x r * y r := by
  have hgroup (i : Fin Sd) :
      (∑ r ∈ univ.filter (fun r => s r = i), pathLatency A ℓ x r * x r) ≤
        ∑ r ∈ univ.filter (fun r => s r = i), pathLatency A ℓ x r * y r := by
    have hpos : 0 < ∑ r ∈ univ.filter (fun r => s r = i), x r := by
      rw [hx.1.2 i]; exact hrate i
    obtain ⟨r,hr,hxr⟩ := (sum_pos_iff_of_nonneg (fun t _ => hx.1.1 t)).mp hpos
    have hri : s r = i := (mem_filter.mp hr).2
    have hmin (t : Fin R) (ht : t ∈ univ.filter (fun r => s r = i)) :
        pathLatency A ℓ x r ≤ pathLatency A ℓ x t :=
      hx.2 r t ((mem_filter.mp ht).2.trans hri.symm) hxr
    have heq (t : Fin R) (ht : t ∈ univ.filter (fun r => s r = i)) :
        pathLatency A ℓ x t * x t = pathLatency A ℓ x r * x t := by
      by_cases hxt : x t = 0
      · simp [hxt]
      · have hxtp : 0 < x t := lt_of_le_of_ne (hx.1.1 t) (Ne.symm hxt)
        have hrev := hx.2 t r (hri.trans (mem_filter.mp ht).2.symm) hxtp
        change pathLatency A ℓ x t ≤ pathLatency A ℓ x r at hrev
        rw [le_antisymm hrev (hmin t ht)]
    calc
      _ = ∑ t ∈ univ.filter (fun r => s r = i), pathLatency A ℓ x r * x t :=
        sum_congr rfl heq
      _ = pathLatency A ℓ x r * rate i := by rw [← mul_sum,hx.1.2 i]
      _ = ∑ t ∈ univ.filter (fun r => s r = i), pathLatency A ℓ x r * y t := by
        rw [← mul_sum,hy.2 i]
      _ ≤ _ := sum_le_sum (fun t ht => mul_le_mul_of_nonneg_right (hmin t ht) (hy.1 t))
  have h := sum_le_sum (fun i (_ : i ∈ univ) => hgroup i)
  simpa only [sum_fiberwise] using h

lemma edge_form {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (x y : Fin R → ℝ) :
    (∑ r, pathLatency A ℓ x r * y r) =
      ∑ j, ℓ j (linkFlow A x j) * linkFlow A y j := by
  simp only [pathLatency,linkFlow,sum_mul,mul_sum,mul_assoc]
  exact sum_comm

lemma edge_nonneg {J R : ℕ} (A : Fin J → Fin R → ℝ) (x : Fin R → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hx : ∀ r, 0 ≤ x r) (j : Fin J) :
    0 ≤ linkFlow A x j := by
  apply sum_nonneg
  intro r _
  rcases hA j r with h | h <;> simp [h,hx r]

lemma same_latencies {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (hmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (x y : Fin R → ℝ) (hx : IsWardropEquilibrium A s ℓ rate x)
    (hy : IsWardropEquilibrium A s ℓ rate y) :
    ∀ j, ℓ j (linkFlow A x j) = ℓ j (linkFlow A y j) := by
  let f := linkFlow A x
  let g := linkFlow A y
  have hfg (j : Fin J) : 0 ≤ (ℓ j (f j)-ℓ j (g j))*(f j-g j) := by
    have hf := edge_nonneg A x hA hx.1.1 j
    have hg := edge_nonneg A y hA hy.1.1 j
    rcases le_total (f j) (g j) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hmono j hf hg h)) (sub_nonpos.mpr h)
    · exact mul_nonneg (sub_nonneg.mpr (hmono j hg hf h)) (sub_nonneg.mpr h)
  have hvx := variational A s rate ℓ x y hrate hx hy.1
  have hvy := variational A s rate ℓ y x hrate hy hx.1
  simp only [edge_form] at hvx hvy
  have hs : (∑ j, (ℓ j (f j)-ℓ j (g j))*(f j-g j)) ≤ 0 := by
    have he : (∑ j, (ℓ j (f j)-ℓ j (g j))*(f j-g j)) =
        (∑ j, ℓ j (f j)*f j) - (∑ j, ℓ j (f j)*g j) +
        (∑ j, ℓ j (g j)*g j) - (∑ j, ℓ j (g j)*f j) := by
      simp only [sub_mul,mul_sub,sum_sub_distrib]
      ring
    rw [he]
    change (∑ j, ℓ j (f j)*f j) ≤ ∑ j, ℓ j (f j)*g j at hvx
    change (∑ j, ℓ j (g j)*g j) ≤ ∑ j, ℓ j (g j)*f j at hvy
    linarith
  have hz : (∑ j, (ℓ j (f j)-ℓ j (g j))*(f j-g j)) = 0 :=
    le_antisymm hs (sum_nonneg (fun j _ => hfg j))
  have he := (sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ univ) => hfg j)).mp hz
  intro j
  change ℓ j (f j) = ℓ j (g j)
  rcases mul_eq_zero.mp (he j (mem_univ _)) with h | h
  · exact sub_eq_zero.mp h
  · rw [sub_eq_zero.mp h]

end RoutingUniqueness
theorem solution {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x x' : Fin R → ℝ) (hx : SelfishRouting.Potential.IsNashFlow A s ℓ rate x)
    (hx' : SelfishRouting.Potential.IsNashFlow A s ℓ rate x') :
    cost A ℓ x = cost A ℓ x' := by
  have hw := RoutingUniqueness.wardrop_of_nash A s rate ℓ x hx
  have hw' := RoutingUniqueness.wardrop_of_nash A s rate ℓ x' hx'
  have he := RoutingUniqueness.same_latencies A s rate ℓ hA hrate hℓmono x x' hw hw'
  have h1 := RoutingUniqueness.variational A s rate ℓ x x' hrate hw hx'.1
  have h2 := RoutingUniqueness.variational A s rate ℓ x' x hrate hw' hx.1
  have hp (r : Fin R) : pathLatency A ℓ x r = pathLatency A ℓ x' r := by
    unfold pathLatency; simp_rw [he]
  unfold cost
  apply le_antisymm
  · simpa only [hp] using h1
  · simpa only [← hp] using h2
#print axioms RoutingUniqueness.same_latencies
#print axioms solution
