-- Prove2me | solution 1 for SendSplit.DPEquations.theorem2_dp_equations
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T09:33:20.014906+00:00
-- url     : https://prove2.me/submissions/ffb23dd7-88be-49cb-96b9-62024b07470d

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_SendSplit_DPEquations_Equations
import Mathlib


section

open scoped BigOperators
open Finset

namespace SendSplit.DPEquations.SSFresh

def balance {n : ℕ} (x : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ j, x j i) - ∑ j, x i j

noncomputable def flowSupport {n : ℕ} (x : Fin n → Fin n → ℝ) :
    Finset (Fin n × Fin n) := Finset.univ.filter fun p => x p.1 p.2 ≠ 0

def IndependentSupport {n : ℕ} (s : Finset (Fin n × Fin n)) : Prop :=
  ∀ z : Fin n → Fin n → ℝ,
    (∀ i j, (i,j) ∉ s → z i j = 0) →
    (∀ i, balance z i = 0) → z = 0

lemma mem_flowSupport {n : ℕ} (x : Fin n → Fin n → ℝ) (i j : Fin n) :
    (i,j) ∈ flowSupport x ↔ x i j ≠ 0 := by
  classical
  simp [flowSupport]

lemma balance_add {n : ℕ} (x y : Fin n → Fin n → ℝ) (i : Fin n) :
    balance (x+y) i = balance x i + balance y i := by
  simp only [balance, Pi.add_apply, Finset.sum_add_distrib]
  ring

lemma balance_sub {n : ℕ} (x y : Fin n → Fin n → ℝ) (i : Fin n) :
    balance (x-y) i = balance x i - balance y i := by
  simp only [balance, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

lemma balance_smul {n : ℕ} (a : ℝ) (x : Fin n → Fin n → ℝ) (i : Fin n) :
    balance (a • x) i = a * balance x i := by
  simp only [balance, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma flow_balance {n : ℕ} {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {x : Fin n → Fin n → ℝ} (hx : IsFlow A r x) (i : Fin n) :
    balance x i = r i := by
  classical
  rw [balance, ← hx.2 i]
  congr 1
  · symm
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro j _ hj
      exact hx.1.2 j i (by simpa using hj))
  · symm
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro j _ hj
      exact hx.1.2 i j (by simpa using hj))

lemma flow_of_balance {n : ℕ} {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {x : Fin n → Fin n → ℝ} (hx : IsPreflow A x) (hb : ∀ i, balance x i = r i) :
    IsFlow A r x := by
  classical
  refine ⟨hx, fun i => ?_⟩
  rw [← hb i, balance]
  congr 1
  · exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro j _ hj
      exact hx.2 j i (by simpa using hj))
  · exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro j _ hj
      exact hx.2 i j (by simpa using hj))

lemma independent_support_unique {n : ℕ} {s : Finset (Fin n × Fin n)}
    (hs : IndependentSupport s) {x y : Fin n → Fin n → ℝ}
    (hx : ∀ i j, (i,j) ∉ s → x i j = 0)
    (hy : ∀ i j, (i,j) ∉ s → y i j = 0)
    (hb : ∀ i, balance x i = balance y i) : x = y := by
  have hz := hs (x-y) (by intro i j hij; simp [hx i j hij, hy i j hij])
    (by intro i; rw [balance_sub, hb i, sub_self])
  exact sub_eq_zero.mp hz

end SendSplit.DPEquations.SSFresh
end


section

open Set

namespace SendSplit.DPEquations.SSFresh

lemma concave_increment_bound {c : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici 0) c)
    {x d : ℝ} (hx : 1 ≤ x) (hd : 0 ≤ d) :
    c (x+d) - c x ≤ d * (c 1-c 0) := by
  rcases eq_or_lt_of_le hd with rfl | hd
  · simp
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ha := hc.slope_anti_adjacent (show (0:ℝ) ∈ Ici 0 by simp)
    (show x+d ∈ Ici 0 by change 0 ≤ x+d; linarith) hxp (by linarith : x < x+d)
  have hb : (c x-c 0)/x ≤ c 1-c 0 := by
    have hh := hc.antitoneOn_slope_gt (show (0:ℝ) ∈ Ici 0 by simp)
      (show 1 ∈ Ici (0:ℝ) ∩ Ioi 0 by simp)
      (show x ∈ Ici (0:ℝ) ∩ Ioi 0 by exact ⟨hxp.le,hxp⟩) hx
    simpa [slope_def_field] using hh
  have h := le_trans ha (by simpa using hb)
  have hh := (div_le_iff₀ hd).mp (by simpa using h)
  nlinarith

lemma concave_monotone_of_eventual_lower_bound {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Ici 0) f) (m R : ℝ)
    (hlow : ∀ t, R ≤ t → 0 ≤ t → m ≤ f t) : MonotoneOn f (Ici 0) := by
  intro x hx y hy hxy
  by_contra h
  have hgap : 0 < f x-f y := sub_pos.mpr (lt_of_not_ge h)
  have hxy' : x < y := lt_of_le_of_ne hxy (by intro he; subst y; exact h le_rfl)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((f y-m)/(f x-f y)))
  have hN0 : (0:ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN' : f y-m < N*(f x-f y) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_right _ _) hN)
  let z := max R (y+N*(y-x))
  have hzy : y+N*(y-x) ≤ z := le_max_right _ _
  have hyz : y < z := by nlinarith
  have hz : 0 ≤ z := le_trans hy hyz.le
  have hs := hf.slope_anti_adjacent hx hz hxy' hyz
  have hcross := (div_le_div_iff₀ (sub_pos.mpr hyz) (sub_pos.mpr hxy')).mp hs
  have hzlow := hlow z (le_max_left _ _) hz
  have hprod : 0 < (y-x)*(N*(f x-f y)-(f y-m)) :=
    mul_pos (sub_pos.mpr hxy') (sub_pos.mpr hN')
  have hp := mul_nonneg (sub_nonneg.mpr hzy) hgap.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hzlow) (sub_nonneg.mpr hxy)]

lemma concave_subadditive {c : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici 0) c)
    (h0 : c 0 = 0) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    c (x+y) ≤ c x+c y := by
  by_cases hxy : x+y=0
  · have : x=0 := by linarith
    have : y=0 := by linarith
    simp_all
  have hp : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hxy)
  have hsum : x/(x+y)+y/(x+y)=1 := by field_simp
  have h1 := hc.2 (show (0:ℝ) ∈ Ici 0 by simp) (show x+y ∈ Ici 0 from hp.le)
    (div_nonneg hy hp.le) (div_nonneg hx hp.le) (by linarith [hsum])
  have h2 := hc.2 (show (0:ℝ) ∈ Ici 0 by simp) (show x+y ∈ Ici 0 from hp.le)
    (div_nonneg hx hp.le) (div_nonneg hy hp.le) hsum
  simp only [smul_eq_mul, mul_zero, zero_add, h0] at h1 h2
  have hxx : x/(x+y)*(x+y)=x := div_mul_cancel₀ x hxy
  have hyy : y/(x+y)*(x+y)=y := div_mul_cancel₀ y hxy
  rw [hxx] at h1
  rw [hyy] at h2
  nlinarith [show x/(x+y)*c (x+y)+y/(x+y)*c (x+y)=c (x+y) by
    rw [← add_mul,hsum,one_mul]]

end SendSplit.DPEquations.SSFresh
end


section

open scoped BigOperators
open Set

namespace SendSplit.DPEquations.SSFresh

def rayCost {ι : Type*} [Fintype ι] (c : ι → ℝ → ℝ) (a y : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i (a i+t*y i)

lemma rayCost_concave {ι : Type*} [Fintype ι] {c : ι → ℝ → ℝ} {a y : ι → ℝ}
    (hc : ∀ i, ConcaveOn ℝ (Ici 0) (c i)) (ha : ∀ i, 0 ≤ a i)
    (hy : ∀ i, 0 ≤ y i) : ConcaveOn ℝ (Ici 0) (rayCost c a y) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro s hs t ht u v hu hv huv
  simp only [rayCost, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := (hc i).2 (show a i+s*y i ∈ Ici 0 from add_nonneg (ha i) (mul_nonneg hs (hy i)))
    (show a i+t*y i ∈ Ici 0 from add_nonneg (ha i) (mul_nonneg ht (hy i))) hu hv huv
  simp only [smul_eq_mul] at h
  convert h using 1
  congr 1
  nlinarith [congrArg (fun z : ℝ => z*a i) huv]

lemma finite_nonnegative_upper {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, f i ≤ M := by
  classical
  refine ⟨∑ i, max 0 (f i), Finset.sum_nonneg (fun _ _ => le_max_left _ _), ?_⟩
  intro i
  exact (le_max_right _ _).trans (Finset.single_le_sum
    (fun j _ => le_max_left (0:ℝ) (f j)) (Finset.mem_univ i))

lemma rayCost_compare_bases {ι : Type*} [Fintype ι] {c : ι → ℝ → ℝ}
    (hc : ∀ i, ConcaveOn ℝ (Ici 0) (c i)) (a b y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    ∃ T R K : ℝ, 0 ≤ T ∧ 0 ≤ R ∧
      ∀ t, R ≤ t → rayCost c b y (t+T) ≤ rayCost c a y t+K := by
  classical
  obtain ⟨T,hT0,hT⟩ := finite_nonnegative_upper (fun i => (a i-b i)/y i)
  obtain ⟨R,hR0,hR⟩ := finite_nonnegative_upper (fun i => (1-a i)/y i)
  let d : ι → ℝ := fun i => b i+T*y i-a i
  let k : ι → ℝ := fun i => if y i=0 then c i (b i)-c i (a i)
    else d i*(c i 1-c i 0)
  refine ⟨T,R,∑ i, k i,hT0,hR0,?_⟩
  intro t ht
  rw [rayCost,rayCost,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : y i=0
  · simp [hi,k]
  · have hyp : 0 < y i := lt_of_le_of_ne (hy i) (Ne.symm hi)
    have hd : 0 ≤ d i := by
      have h := (div_le_iff₀ hyp).mp (hT i)
      dsimp [d]
      linarith
    have ha1 : 1 ≤ a i+t*y i := by
      have h := (div_le_iff₀ hyp).mp ((hR i).trans ht)
      linarith
    have h := concave_increment_bound (hc i) ha1 hd
    have he : a i+t*y i+d i=b i+(t+T)*y i := by dsimp [d]; ring
    rw [he] at h
    dsimp [k]
    rw [if_neg hi]
    linarith

lemma rayCost_monotone_from_one_bounded_ray {ι : Type*} [Fintype ι]
    {c : ι → ℝ → ℝ} (hc : ∀ i, ConcaveOn ℝ (Ici 0) (c i))
    (a b y : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hy : ∀ i, 0 ≤ y i)
    (m : ℝ) (hb : ∀ t, 0 ≤ t → m ≤ rayCost c b y t) :
    MonotoneOn (rayCost c a y) (Ici 0) := by
  obtain ⟨T,R,K,hT,hR,hcomp⟩ := rayCost_compare_bases hc a b y hy
  apply concave_monotone_of_eventual_lower_bound (rayCost_concave hc ha hy) (m-K) R
  intro t ht ht0
  have h1 := hb (t+T) (add_nonneg ht0 hT)
  have h2 := hcomp t ht
  linarith

end SendSplit.DPEquations.SSFresh
end


section

open scoped BigOperators
open Set

namespace SendSplit.DPEquations.SSFresh

lemma preflow_add_nonnegative {n : ℕ} {A : Finset (Fin n × Fin n)}
    {x y : Fin n → Fin n → ℝ} (hx : IsPreflow A x) (hy : IsPreflow A y)
    {t : ℝ} (ht : 0 ≤ t) : IsPreflow A (x+t • y) := by
  refine ⟨fun i j => ?_, fun i j hij => ?_⟩
  · exact add_nonneg (hx.1 i j) (mul_nonneg ht (hy.1 i j))
  · simp [hx.2 i j hij,hy.2 i j hij]

lemma flow_add_circulation {n : ℕ} {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {x y : Fin n → Fin n → ℝ} (hx : IsFlow A r x) (hy : IsFlow A 0 y)
    {t : ℝ} (ht : 0 ≤ t) : IsFlow A r (x+t • y) := by
  apply flow_of_balance (preflow_add_nonnegative hx.1 hy.1 ht)
  intro i
  rw [balance_add,balance_smul,flow_balance hx,flow_balance hy]
  simp

lemma flowCost_eq_rayCost {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (x y : Fin n → Fin n → ℝ) (t : ℝ) :
    flowCost A c (x+t • y) =
      rayCost (fun p : A => c p.1.1 p.1.2)
        (fun p : A => x p.1.1 p.1.2) (fun p : A => y p.1.1 p.1.2) t := by
  classical
  exact (A.sum_coe_sort (fun p => c p.1 p.2 (x p.1 p.2+t*y p.1 p.2))).symm

lemma native_circulation_ray_monotone {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {x y : Fin n → Fin n → ℝ} (hx : IsPreflow A x) (hy : IsFlow A 0 y) :
    MonotoneOn (fun t : ℝ => flowCost A c (x+t • y)) (Ici 0) := by
  classical
  obtain ⟨b,hb,hbm⟩ := hmin
  have h := rayCost_monotone_from_one_bounded_ray
    (fun p : A => (hc p.1 p.2).1)
    (fun p : A => x p.1.1 p.1.2) (fun p : A => b p.1.1 p.1.2)
    (fun p : A => y p.1.1 p.1.2)
    (fun p => hx.1 _ _) (fun p => hy.1.1 _ _) (flowCost A c b)
    (by
      intro t ht
      rw [← flowCost_eq_rayCost]
      exact hbm _ (flow_add_circulation hb hy ht))
  intro s hs t ht hst
  change flowCost A c (x+s • y) ≤ flowCost A c (x+t • y)
  rw [flowCost_eq_rayCost,flowCost_eq_rayCost]
  exact h hs ht hst

lemma native_circulation_cost_nonnegative {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {y : Fin n → Fin n → ℝ} (hy : IsFlow A 0 y) : 0 ≤ flowCost A c y := by
  have h := native_circulation_ray_monotone hc hmin
    (x:=0) (by exact ⟨fun _ _ => le_rfl, fun _ _ _ => rfl⟩) hy
    (show (0:ℝ) ∈ Ici 0 by simp) (show (1:ℝ) ∈ Ici 0 by simp) zero_le_one
  have hzero : flowCost A c 0=0 := Finset.sum_eq_zero (fun p hp => (hc p hp).2)
  simpa only [zero_smul,one_smul,zero_add,hzero] using h

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

lemma positive_endpoint {ι : Type*} [Fintype ι] (x z : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, z i ≠ 0 → 0 < x i)
    (hneg : ∃ i, z i < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ x i+t*z i) ∧
      ∃ i, x i ≠ 0 ∧ x i+t*z i=0 := by
  classical
  let s : Finset ι := Finset.univ.filter fun i => z i < 0
  have hne : s.Nonempty := by
    obtain ⟨i,hi⟩ := hneg
    exact ⟨i,by simp [s,hi]⟩
  obtain ⟨i,hi,hmin⟩ := s.exists_min_image (fun i => x i/(-z i)) hne
  have hzi : z i < 0 := (Finset.mem_filter.mp hi).2
  let t := x i/(-z i)
  have ht : 0 < t := div_pos (hs i hzi.ne) (neg_pos.mpr hzi)
  refine ⟨t,ht,?_,i,(hs i hzi.ne).ne',?_⟩
  · intro j
    by_cases hj : z j < 0
    · have h := hmin j (by simp [s,hj])
      have h' := (le_div_iff₀ (neg_pos.mpr hj)).mp h
      change 0 ≤ x j+t*z j
      dsimp [t] at *
      nlinarith
    · exact add_nonneg (hx j) (mul_nonneg ht.le (le_of_not_gt hj))
  · dsimp [t]
    have h := div_mul_cancel₀ (x i) (neg_ne_zero.mpr hzi.ne)
    nlinarith

end SendSplit.DPEquations.SSFresh
end


section

open scoped BigOperators
open Set

namespace SendSplit.DPEquations.SSFresh

lemma native_cost_concave {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} (hc : IsConcaveArcCost A c) :
    ConcaveOn ℝ {x : Fin n → Fin n → ℝ | ∀ i j, 0 ≤ x i j} (flowCost A c) := by
  classical
  constructor
  · intro x hx y hy a b ha hb _ i j
    exact add_nonneg (mul_nonneg ha (hx i j)) (mul_nonneg hb (hy i j))
  · intro x hx y hy a b ha hb hab
    simp only [flowCost, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    exact (hc p hp).1.2 (hx p.1 p.2) (hy p.1 p.2) ha hb hab

lemma native_cost_endpoint_choice {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} (hc : IsConcaveArcCost A c)
    (x z : Fin n → Fin n → ℝ) {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hp : ∀ i j, 0 ≤ (x+t • z) i j) (hm : ∀ i j, 0 ≤ (x-u • z) i j) :
    flowCost A c (x+t • z) ≤ flowCost A c x ∨
      flowCost A c (x-u • z) ≤ flowCost A c x := by
  have htu : 0 < t+u := add_pos ht hu
  have ha : 0 ≤ u/(t+u) := div_nonneg hu.le htu.le
  have hb : 0 ≤ t/(t+u) := div_nonneg ht.le htu.le
  have hab : u/(t+u)+t/(t+u)=1 := by field_simp; ring
  have he : (u/(t+u)) • (x+t • z)+(t/(t+u)) • (x-u • z)=x := by
    funext i j
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    field_simp
    ring
  have h := (native_cost_concave hc).2 hp hm ha hb hab
  rw [he] at h
  simp only [smul_eq_mul] at h
  by_contra hh
  push Not at hh
  have h1 := mul_lt_mul_of_pos_left hh.1 (div_pos hu htu)
  have h2 := mul_lt_mul_of_pos_left hh.2 (div_pos ht htu)
  have h3 : u/(t+u)*flowCost A c x+t/(t+u)*flowCost A c x=flowCost A c x := by
    rw [← add_mul,hab,one_mul]
  linarith

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

lemma supported_direction_flow {n : ℕ} {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {x z : Fin n → Fin n → ℝ} (hx : IsFlow A r x)
    (hz : ∀ i j, (i,j) ∉ flowSupport x → z i j=0)
    (hb : ∀ i, balance z i=0) (t : ℝ)
    (hn : ∀ i j, 0 ≤ (x+t • z) i j) : IsFlow A r (x+t • z) := by
  apply flow_of_balance ⟨hn,?_⟩
  · intro i
    rw [balance_add,balance_smul,hb i,flow_balance hx]
    simp
  · intro i j hij
    have hxi := hx.1.2 i j hij
    have hzi := hz i j (by simp [flowSupport,hxi])
    simp [hxi,hzi]

lemma direction_support_subset {n : ℕ} (x z : Fin n → Fin n → ℝ)
    (hz : ∀ i j, (i,j) ∉ flowSupport x → z i j=0) (t : ℝ) :
    flowSupport (x+t • z) ⊆ flowSupport x := by
  intro p hp
  by_contra h
  have hx0 : x p.1 p.2=0 := by simpa [flowSupport] using h
  have hz0 := hz p.1 p.2 h
  simp [flowSupport,hx0,hz0] at hp

lemma direction_support_strict {n : ℕ} (x z : Fin n → Fin n → ℝ)
    (hz : ∀ i j, (i,j) ∉ flowSupport x → z i j=0) (t : ℝ)
    (he : ∃ i j, x i j≠0 ∧ (x+t • z) i j=0) :
    flowSupport (x+t • z) ⊂ flowSupport x := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨direction_support_subset x z hz t,?_⟩
  intro hh
  obtain ⟨i,j,hx,hzero⟩ := he
  have hmem : (i,j) ∈ flowSupport (x+t • z) := by rw [hh]; exact (mem_flowSupport _ _ _).mpr hx
  exact (mem_flowSupport _ _ _).mp hmem hzero

lemma negative_direction_reduction {n : ℕ} {A : Finset (Fin n × Fin n)}
    {r : Fin n → ℝ} {c : Fin n → Fin n → ℝ → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {d : Fin n → ℝ} {x z : Fin n → Fin n → ℝ} (hx : IsFlow A d x)
    (hz : ∀ i j, (i,j) ∉ flowSupport x → z i j=0)
    (hb : ∀ i, balance z i=0) (hneg : ∃ i j, z i j<0) :
    ∃ x', IsFlow A d x' ∧ flowCost A c x' ≤ flowCost A c x ∧
      flowSupport x' ⊂ flowSupport x := by
  classical
  have hposx : ∀ p : Fin n × Fin n, z p.1 p.2≠0 → 0<x p.1 p.2 := by
    intro p hp
    apply lt_of_le_of_ne (hx.1.1 _ _)
    intro he
    exact hp (hz _ _ (by simp [flowSupport,← he]))
  obtain ⟨t,ht,htn,i,hi,hte⟩ := positive_endpoint
    (fun p : Fin n × Fin n => x p.1 p.2) (fun p => z p.1 p.2)
    (fun _ => hx.1.1 _ _) hposx (by obtain ⟨i,j,h⟩ := hneg; exact ⟨(i,j),h⟩)
  have htf := supported_direction_flow hx hz hb t (fun i j => htn (i,j))
  have hts := direction_support_strict x z hz t ⟨i.1,i.2,hi,hte⟩
  by_cases hpositive : ∃ i j, 0<z i j
  · obtain ⟨u,hu,hun,j,hj,hue⟩ := positive_endpoint
      (fun p : Fin n × Fin n => x p.1 p.2) (fun p => -z p.1 p.2)
      (fun _ => hx.1.1 _ _) (by intro p hp; exact hposx p (neg_ne_zero.mp hp))
      (by obtain ⟨i,j,h⟩ := hpositive; exact ⟨(i,j),neg_neg_of_pos h⟩)
    have hun' : ∀ i j, 0≤(x-u • z) i j := fun i j => by simpa using hun (i,j)
    have huf := supported_direction_flow hx hz hb (-u) (by intro i j; simpa using hun' i j)
    have hus := direction_support_strict x z hz (-u) ⟨j.1,j.2,hj,by simpa using hue⟩
    rcases native_cost_endpoint_choice hc x z ht hu (fun i j => htn (i,j)) hun' with h|h
    · exact ⟨_,htf,h,hts⟩
    · refine ⟨x+(-u) • z,huf,?_,hus⟩
      simpa [sub_eq_add_neg] using h
  · push Not at hpositive
    have hzn : ∀ i j, 0≤(-z) i j := by intro i j; exact neg_nonneg.mpr (hpositive i j)
    have hzflow : IsFlow A 0 (-z) := by
      apply flow_of_balance ⟨hzn,?_⟩
      · intro i
        have h := balance_smul (-1) z i
        simpa [hb i] using h
      · intro i j hij
        have hxi := hx.1.2 i j hij
        simp [hz i j (by simp [flowSupport,hxi])]
    have hmono := native_circulation_ray_monotone hc hmin htf.1 hzflow
      (show (0:ℝ) ∈ Set.Ici 0 by simp) (show t ∈ Set.Ici 0 from ht.le) ht.le
    have he : x+t • z+t • (-z)=x := by module
    simp only [zero_smul,add_zero,he] at hmono
    exact ⟨_,htf,hmono,hts⟩

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

lemma dependent_support_reduction {n : ℕ} {A : Finset (Fin n × Fin n)}
    {r : Fin n → ℝ} {c : Fin n → Fin n → ℝ → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {d : Fin n → ℝ} {x : Fin n → Fin n → ℝ} (hx : IsFlow A d x)
    (hdep : ¬IndependentSupport (flowSupport x)) :
    ∃ x', IsFlow A d x' ∧ flowCost A c x' ≤ flowCost A c x ∧
      flowSupport x' ⊂ flowSupport x := by
  classical
  simp only [IndependentSupport] at hdep
  push Not at hdep
  obtain ⟨z,hz,hb,hne⟩ := hdep
  by_cases hneg : ∃ i j, z i j<0
  · exact negative_direction_reduction hc hmin hx hz hb hneg
  · push Not at hneg
    have hex : ∃ i j, z i j≠0 := by
      by_contra h
      push Not at h
      apply hne
      funext i j
      exact h i j
    obtain ⟨i,j,hij⟩ := hex
    have hp : 0<z i j := lt_of_le_of_ne (hneg i j) (Ne.symm hij)
    apply negative_direction_reduction hc hmin hx (z:=-z)
    · intro i j h
      simp [hz i j h]
    · intro i
      have h := balance_smul (-1) z i
      simpa [hb i] using h
    · exact ⟨i,j,neg_neg_of_pos hp⟩

lemma independent_flow_below {n : ℕ} {A : Finset (Fin n × Fin n)}
    {r : Fin n → ℝ} {c : Fin n → Fin n → ℝ → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {d : Fin n → ℝ} (x : Fin n → Fin n → ℝ) (hx : IsFlow A d x) :
    ∃ y, IsFlow A d y ∧ IndependentSupport (flowSupport y) ∧
      flowCost A c y ≤ flowCost A c x := by
  classical
  suffices H : ∀ k : ℕ, ∀ x : Fin n → Fin n → ℝ, (flowSupport x).card=k →
      IsFlow A d x → ∃ y, IsFlow A d y ∧ IndependentSupport (flowSupport y) ∧
        flowCost A c y ≤ flowCost A c x from H _ x rfl hx
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hcard hx
    by_cases hi : IndependentSupport (flowSupport x)
    · exact ⟨x,hx,hi,le_rfl⟩
    · obtain ⟨y,hy,hcost,hs⟩ := dependent_support_reduction hc hmin hx hi
      obtain ⟨z,hz,hzi,hzc⟩ := ih (flowSupport y).card
        (by rw [← hcard]; exact Finset.card_lt_card hs) y rfl hy
      exact ⟨z,hz,hzi,hzc.trans hcost⟩

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

lemma minimum_flow_exists_for_every_feasible_demand {n : ℕ}
    {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ} {c : Fin n → Fin n → ℝ → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {d : Fin n → ℝ} (hfeas : ∃ x, IsFlow A d x) :
    ∃ x, IsMinCostFlow A c d x ∧ IndependentSupport (flowSupport x) := by
  classical
  obtain ⟨x,hx⟩ := hfeas
  obtain ⟨x0,hx0,hi0,_⟩ := independent_flow_below hc hmin x hx
  let P := fun (s : Finset (Fin n × Fin n)) (y : Fin n → Fin n → ℝ) =>
    IsFlow A d y ∧ IndependentSupport (flowSupport y) ∧ flowSupport y=s
  have hchoose : ∀ s : Finset (Fin n × Fin n),
      ∃ y, IsFlow A d y ∧ IndependentSupport (flowSupport y) ∧
        ((∃ z, P s z) → P s y) := by
    intro s
    by_cases h : ∃ z, P s z
    · obtain ⟨z,hz⟩ := h
      exact ⟨z,hz.1,hz.2.1,fun _ => hz⟩
    · exact ⟨x0,hx0,hi0,fun he => (h he).elim⟩
  choose cand hcand hci hcp using hchoose
  obtain ⟨s,_,hs⟩ := Finset.univ.exists_min_image
    (fun s : Finset (Fin n × Fin n) => flowCost A c (cand s)) (Finset.univ_nonempty)
  refine ⟨cand s,⟨hcand s,?_⟩,hci s⟩
  intro y hy
  obtain ⟨z,hz,hiz,hcost⟩ := independent_flow_below hc hmin y hy
  have hp : P (flowSupport z) (cand (flowSupport z)) :=
    hcp _ ⟨z,hz,hiz,rfl⟩
  have he : cand (flowSupport z)=z := by
    apply independent_support_unique hiz
    · intro i j hij
      have hnot : (i,j) ∉ flowSupport (cand (flowSupport z)) := by rw [hp.2.2]; exact hij
      simpa [mem_flowSupport] using hnot
    · intro i j hij
      simpa [mem_flowSupport] using hij
    · intro i
      rw [flow_balance hp.1,flow_balance hz]
  have hle := hs (flowSupport z) (Finset.mem_univ _)
  rw [he] at hle
  exact hle.trans hcost

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

lemma native_minCost_le_flow {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ} {i : Fin n} {I : Finset (Fin n)}
    {x : Fin n → Fin n → ℝ} (hx : IsFlow A (subDemand r i I) x) :
    minCost A c r i I ≤ (flowCost A c x : EReal) :=
  iInf_le_of_le x (iInf_le_of_le hx le_rfl)

lemma native_minCost_eq_of_minimum {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ} {i : Fin n} {I : Finset (Fin n)}
    {x : Fin n → Fin n → ℝ} (hx : IsMinCostFlow A c (subDemand r i I) x) :
    minCost A c r i I = (flowCost A c x : EReal) := by
  apply le_antisymm (native_minCost_le_flow hx.1)
  exact le_iInf fun y => le_iInf fun hy => by exact_mod_cast hx.2 y hy

lemma native_minCost_eq_top_of_infeasible {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ} {i : Fin n} {I : Finset (Fin n)}
    (h : ¬∃ x, IsFlow A (subDemand r i I) x) : minCost A c r i I=⊤ := by
  simp only [not_exists] at h
  simp [minCost,h]

lemma native_minCost_ne_bot {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    (i : Fin n) (I : Finset (Fin n)) : minCost A c r i I≠⊥ := by
  by_cases hf : ∃ x, IsFlow A (subDemand r i I) x
  · obtain ⟨x,hx,_⟩ := minimum_flow_exists_for_every_feasible_demand hc hmin hf
    rw [native_minCost_eq_of_minimum hx]
    exact EReal.coe_ne_bot _
  · rw [native_minCost_eq_top_of_infeasible hf]
    exact top_ne_bot

lemma native_zero_minimum {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b) :
    IsMinCostFlow A c 0 0 := by
  have hz : flowCost A c 0=0 := Finset.sum_eq_zero (fun p hp => (hc p hp).2)
  refine ⟨?_,?_⟩
  · apply flow_of_balance ⟨fun _ _ => le_rfl, fun _ _ _ => rfl⟩
    intro i
    simp [balance]
  · intro y hy
    rw [hz]
    exact native_circulation_cost_nonnegative hc hmin hy

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

def arcUnit (u v : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = u then if j = v then 1 else 0 else 0

theorem balance_arcUnit (u v k : Fin n) :
    balance (arcUnit u v) k = (if k = v then 1 else 0) - (if k = u then 1 else 0) := by
  classical
  by_cases hk : k = v <;> by_cases hu : k = u <;>
    simp [balance, arcUnit, hk, hu]

theorem independentSupport_mono {s t : Finset (Fin n × Fin n)}
    (ht : IndependentSupport t) (hst : s ⊆ t) : IndependentSupport s := by
  intro z hz hb
  exact ht z (fun i j hij => hz i j (fun h => hij (hst h))) hb

theorem independentSupport_no_opposite {s : Finset (Fin n × Fin n)}
    (hs : IndependentSupport s) {u v : Fin n} (huv : u ≠ v)
    (h : (u,v) ∈ s) : (v,u) ∉ s := by
  classical
  intro hr
  have hz := hs (arcUnit u v + arcUnit v u) (by
    intro i j hij
    by_cases hi : i = u
    · subst i
      have hj : j ≠ v := by intro he; subst j; exact hij h
      simp [arcUnit, hj, huv]
    · by_cases hiv : i = v
      · subst i
        have hj : j ≠ u := by intro he; subst j; exact hij hr
        simp [arcUnit, hi, hj]
      · simp [arcUnit, hi, hiv]) (by
    intro k
    rw [balance_add, balance_arcUnit, balance_arcUnit]
    ring)
  have he := congrFun (congrFun hz u) v
  simp [arcUnit, huv] at he

noncomputable def supportGraph (s : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u,v) ∈ s ∨ (v,u) ∈ s)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def signedArc (s : Finset (Fin n × Fin n)) (u v : Fin n) :
    Fin n → Fin n → ℝ :=
  if (u,v) ∈ s then arcUnit u v else -(arcUnit v u)

theorem balance_signedArc (s : Finset (Fin n × Fin n)) (u v k : Fin n) :
    balance (signedArc s u v) k =
      (if k = v then 1 else 0) - (if k = u then 1 else 0) := by
  classical
  by_cases huv : (u,v) ∈ s
  · rw [signedArc, if_pos huv]
    exact balance_arcUnit u v k
  · rw [signedArc, if_neg huv]
    simp only [balance, Pi.neg_apply, Finset.sum_neg_distrib]
    have h := balance_arcUnit v u k
    dsimp [balance] at h
    linarith

theorem signedArc_supported {s : Finset (Fin n × Fin n)} {u v : Fin n}
    (h : (supportGraph s).Adj u v) :
    ∀ i j, (i,j) ∉ s → signedArc s u v i j = 0 := by
  classical
  intro i j hij
  unfold signedArc
  split_ifs with huv
  · have hn : ¬(i = u ∧ j = v) := by rintro ⟨rfl,rfl⟩; exact hij huv
    simp only [arcUnit]
    split_ifs <;> simp_all
  · have hvu : (v,u) ∈ s := h.2.resolve_left huv
    have hn : ¬(i = v ∧ j = u) := by rintro ⟨rfl,rfl⟩; exact hij hvu
    simp only [Pi.neg_apply, arcUnit]
    split_ifs <;> simp_all

noncomputable def walkFlow (s : Finset (Fin n × Fin n))
    {u v : Fin n} : (supportGraph s).Walk u v → (Fin n → Fin n → ℝ)
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ a b c _ p => signedArc s a b + walkFlow s p

theorem balance_walkFlow (s : Finset (Fin n × Fin n)) {u v : Fin n}
    (p : (supportGraph s).Walk u v) (k : Fin n) :
    balance (walkFlow s p) k = (if k = v then 1 else 0) - (if k = u then 1 else 0) := by
  induction p with
  | nil => simp [walkFlow, balance]
  | @cons a b c h p ih =>
    rw [walkFlow, balance_add, balance_signedArc, ih]
    ring

theorem walkFlow_supported (s : Finset (Fin n × Fin n)) {u v : Fin n}
    (p : (supportGraph s).Walk u v) :
    ∀ i j, (i,j) ∉ s → walkFlow s p i j = 0 := by
  induction p with
  | nil => simp [walkFlow]
  | @cons a b c h p ih =>
    intro i j hij
    simp only [walkFlow, Pi.add_apply, signedArc_supported h i j hij, ih i j hij, add_zero]

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ} (r : Fin n → ℝ)

theorem demandSum_singleton (i : Fin n) : demandSum r {i} = r i := by
  simp [demandSum]

theorem demandSum_erase (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I) :
    demandSum r (I.erase j) = demandSum r I - r j := by
  have h := Finset.sum_erase_add I r hj
  dsimp [demandSum]
  linarith

theorem demandSum_partition (I J : Finset (Fin n)) (hJ : J ⊆ I) :
    demandSum r J + demandSum r (I \ J) = demandSum r I := by
  simpa only [demandSum, Finset.inter_eq_right.mpr hJ] using I.sum_inter_add_sum_sdiff J r

theorem subDemand_singleton (i : Fin n) : subDemand r i {i} = 0 := by
  funext k
  by_cases hk : k = i
  · subst k; simp [subDemand, demandSum]
  · simp [subDemand, hk]

theorem subDemand_partition (i : Fin n) (I J : Finset (Fin n)) (hJ : J ⊆ I) :
    subDemand r i J + subDemand r i (I \ J) = subDemand r i I := by
  have hs := demandSum_partition r I J hJ
  funext k
  simp only [Pi.add_apply, subDemand]
  by_cases hk : k ∈ J
  · have hi := hJ hk
    simp only [hk, hi, Finset.mem_sdiff, not_true_eq_false, and_false, ↓reduceIte]
    split_ifs <;> linarith
  · by_cases hi : k ∈ I
    · simp only [hk, hi, Finset.mem_sdiff, not_false_eq_true, and_self, ↓reduceIte]
      split_ifs <;> linarith
    · simp only [hk, hi, Finset.mem_sdiff, false_and, ↓reduceIte]
      split_ifs <;> linarith

theorem subDemand_erase_root (i : Fin n) (I : Finset (Fin n)) (hi : i ∈ I) :
    subDemand r i (I.erase i) = subDemand r i I := by
  have hs := demandSum_erase r I i hi
  funext k
  by_cases hk : k = i
  · subst k
    simp [subDemand, hs, hi]
  · simp [subDemand, hk]

theorem subDemand_zero_sum_erase (i j : Fin n) (I : Finset (Fin n))
    (hj : j ∈ I) (hs : demandSum r I = 0) :
    subDemand r i I = subDemand r j (I.erase j) := by
  have he := demandSum_erase r I j hj
  funext k
  by_cases hk : k = j
  · subst k
    simp [subDemand, hs, he, hj]
  · simp [subDemand, hs, hk]

theorem admissible_member_ne_zero {I : Finset (Fin n)} (hI : IsAdmissible r I)
    {j : Fin n} (hj : j ∈ I) : r j ≠ 0 := by
  simpa [demandNodes] using hI.2 hj

theorem admissible_subset {I J : Finset (Fin n)} (hI : IsAdmissible r I)
    (hJ : J.Nonempty) (hJI : J ⊆ I) : IsAdmissible r J :=
  ⟨hJ, hJI.trans hI.2⟩

theorem admissible_zero_sum_erase {I : Finset (Fin n)} (hI : IsAdmissible r I)
    (hs : demandSum r I = 0) {j : Fin n} (hj : j ∈ I) :
    IsAdmissible r (I.erase j) := by
  apply admissible_subset r hI _ (Finset.erase_subset _ _)
  by_contra h
  have he : I.erase j = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hsum := demandSum_erase r I j hj
  have hr := admissible_member_ne_zero r hI hj
  simp only [he, demandSum, Finset.sum_empty] at hsum
  dsimp [demandSum] at hs
  exact hr (by linarith)

end SendSplit.DPEquations.SSFresh
end


section

open scoped BigOperators

namespace SendSplit.DPEquations.SSFresh

lemma flow_add {n : ℕ} {A : Finset (Fin n × Fin n)} {r s : Fin n → ℝ}
    {x y : Fin n → Fin n → ℝ} (hx : IsFlow A r x) (hy : IsFlow A s y) :
    IsFlow A (r+s) (x+y) := by
  apply flow_of_balance
  · simpa only [one_smul] using preflow_add_nonnegative hx.1 hy.1 (t:=1) zero_le_one
  · intro i
    rw [balance_add,flow_balance hx,flow_balance hy]
    rfl

lemma flowCost_subadditive {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} (hc : IsConcaveArcCost A c)
    {x y : Fin n → Fin n → ℝ} (hx : ∀ i j, 0 ≤ x i j) (hy : ∀ i j, 0 ≤ y i j) :
    flowCost A c (x+y) ≤ flowCost A c x+flowCost A c y := by
  simp only [flowCost,Pi.add_apply,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun p hp => concave_subadditive (hc p hp).1 (hc p hp).2
    (hx p.1 p.2) (hy p.1 p.2)

lemma arcUnit_preflow {n : ℕ} {A : Finset (Fin n × Fin n)} {u v : Fin n}
    (hA : (u,v) ∈ A) {t : ℝ} (ht : 0 ≤ t) : IsPreflow A (t • arcUnit u v) := by
  refine ⟨?_,?_⟩
  · intro i j
    dsimp [arcUnit]
    split_ifs <;> positivity
  · intro i j hij
    by_cases hi : i=u
    · subst i
      have hj : j≠v := by intro he; subst j; exact hij hA
      simp [arcUnit,hj]
    · simp [arcUnit,hi]

lemma arcUnit_cost {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} (hc : IsConcaveArcCost A c)
    {u v : Fin n} (hA : (u,v) ∈ A) (t : ℝ) :
    flowCost A c (t • arcUnit u v)=c u v t := by
  classical
  unfold flowCost
  rw [Finset.sum_eq_single_of_mem (u,v) hA]
  · simp [arcUnit]
  · intro p hp hne
    have hp' : p.1≠u ∨ p.2≠v := by
      by_contra hh
      push Not at hh
      exact hne (Prod.ext hh.1 hh.2)
    rcases hp' with h|h <;> simp [arcUnit,h,(hc p hp).2]

lemma subDemand_send_difference {n : ℕ} (r : Fin n → ℝ) (I : Finset (Fin n))
    (i j k : Fin n) :
    subDemand r j I k+demandSum r I*balance (arcUnit i j) k=subDemand r i I k := by
  rw [balance_arcUnit]
  simp only [subDemand]
  split_ifs <;> ring

lemma forward_send_flow_pos {n : ℕ} {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {I : Finset (Fin n)} {i j : Fin n} (hA : (i,j) ∈ A) (hr : 0 ≤ demandSum r I)
    {x : Fin n → Fin n → ℝ} (hx : IsFlow A (subDemand r j I) x) :
    IsFlow A (subDemand r i I) (x+demandSum r I • arcUnit i j) := by
  apply flow_of_balance
  · have ha := arcUnit_preflow hA hr
    simpa only [one_smul] using preflow_add_nonnegative hx.1 ha (t:=1) zero_le_one
  · intro k
    rw [balance_add,balance_smul,flow_balance hx]
    exact subDemand_send_difference r I i j k

lemma forward_send_flow_neg {n : ℕ} {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {I : Finset (Fin n)} {i j : Fin n} (hA : (j,i) ∈ A) (hr : demandSum r I ≤ 0)
    {x : Fin n → Fin n → ℝ} (hx : IsFlow A (subDemand r j I) x) :
    IsFlow A (subDemand r i I) (x+(-demandSum r I) • arcUnit j i) := by
  apply flow_of_balance
  · have ha := arcUnit_preflow hA (neg_nonneg.mpr hr)
    simpa only [one_smul] using preflow_add_nonnegative hx.1 ha (t:=1) zero_le_one
  · intro k
    rw [balance_add,balance_smul,flow_balance hx,balance_arcUnit]
    have h := subDemand_send_difference r I i j k
    rw [balance_arcUnit] at h
    linarith

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

lemma sendCost_ne_bot {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ) (I : Finset (Fin n)) (i j : Fin n) :
    sendCost A c r I i j≠⊥ := by
  unfold sendCost
  split_ifs <;> simp

lemma native_forward_send {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    (i j : Fin n) (I : Finset (Fin n)) :
    minCost A c r i I ≤ sendCost A c r I i j+minCost A c r j I := by
  classical
  by_cases hf : ∃ x, IsFlow A (subDemand r j I) x
  · obtain ⟨x,hx,_⟩ := minimum_flow_exists_for_every_feasible_demand hc hmin hf
    rw [native_minCost_eq_of_minimum hx]
    unfold sendCost
    split_ifs with hp hn
    · have hfl := forward_send_flow_pos hp.2 hp.1.le hx.1
      have hcost := flowCost_subadditive hc hx.1.1.1 (arcUnit_preflow hp.2 hp.1.le).1
      rw [arcUnit_cost hc hp.2] at hcost
      calc
        minCost A c r i I ≤ (flowCost A c (x+demandSum r I • arcUnit i j):EReal) :=
          native_minCost_le_flow hfl
        _ ≤ (c i j (demandSum r I):EReal)+(flowCost A c x:EReal) := by
          rw [← EReal.coe_add]
          exact_mod_cast (by linarith : flowCost A c (x+demandSum r I • arcUnit i j) ≤
            c i j (demandSum r I)+flowCost A c x)
    · have hfl := forward_send_flow_neg hn.2 hn.1.le hx.1
      have hcost := flowCost_subadditive hc hx.1.1.1
        (arcUnit_preflow hn.2 (neg_nonneg.mpr hn.1.le)).1
      rw [arcUnit_cost hc hn.2] at hcost
      calc
        minCost A c r i I ≤ (flowCost A c (x+(-demandSum r I) • arcUnit j i):EReal) :=
          native_minCost_le_flow hfl
        _ ≤ (c j i (-demandSum r I):EReal)+(flowCost A c x:EReal) := by
          rw [← EReal.coe_add]
          exact_mod_cast (by linarith : flowCost A c (x+(-demandSum r I) • arcUnit j i) ≤
            c j i (-demandSum r I)+flowCost A c x)
    · simp
  · rw [native_minCost_eq_top_of_infeasible hf,
      EReal.add_top_of_ne_bot (sendCost_ne_bot A c r I i j)]
    exact le_top

lemma native_forward_partition {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    (i : Fin n) (I J : Finset (Fin n)) (hJ : J ⊆ I) :
    minCost A c r i I ≤ minCost A c r i J+minCost A c r i (I\J) := by
  classical
  by_cases hf : ∃ x, IsFlow A (subDemand r i J) x
  · by_cases hg : ∃ y, IsFlow A (subDemand r i (I\J)) y
    · obtain ⟨x,hx,_⟩ := minimum_flow_exists_for_every_feasible_demand hc hmin hf
      obtain ⟨y,hy,_⟩ := minimum_flow_exists_for_every_feasible_demand hc hmin hg
      have hfl := flow_add hx.1 hy.1
      rw [subDemand_partition r i I J hJ] at hfl
      rw [native_minCost_eq_of_minimum hx,native_minCost_eq_of_minimum hy,← EReal.coe_add]
      exact (native_minCost_le_flow hfl).trans
        (by exact_mod_cast flowCost_subadditive hc hx.1.1.1 hy.1.1.1)
    · rw [native_minCost_eq_top_of_infeasible hg,
        EReal.add_top_of_ne_bot (native_minCost_ne_bot hc hmin i J)]
      exact le_top
  · rw [native_minCost_eq_top_of_infeasible hf,
      EReal.top_add_of_ne_bot (native_minCost_ne_bot hc hmin i (I\J))]
    exact le_top

lemma native_forward_split {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    (i : Fin n) (I : Finset (Fin n)) :
    minCost A c r i I ≤ splitCost (minCost A c r) i I := by
  classical
  unfold splitCost
  split_ifs with hcard heq
  · subst I
    have hzero := native_zero_minimum hc hmin
    have hsub : IsMinCostFlow A c (subDemand r i {i}) 0 := by
      rw [subDemand_singleton]; exact hzero
    rw [native_minCost_eq_of_minimum hsub]
    have hz : flowCost A c 0=0 := Finset.sum_eq_zero (fun p hp => (hc p hp).2)
    simp [hz]
  · exact le_top
  · apply Finset.le_inf
    intro J hJ
    exact native_forward_partition hc hmin i I J
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hJ).1)

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

noncomputable def eraseArc (x : Fin n → Fin n → ℝ) (a b : Fin n) :
    Fin n → Fin n → ℝ := fun i j => if i = a ∧ j = b then 0 else x i j

theorem eraseArc_add (x : Fin n → Fin n → ℝ) (a b : Fin n) :
    eraseArc x a b + x a b • arcUnit a b = x := by
  classical
  funext i j
  by_cases hi : i = a <;> by_cases hj : j = b <;>
    simp [eraseArc, arcUnit, hi, hj]

theorem eraseArc_preflow {A : Finset (Fin n × Fin n)}
    {x : Fin n → Fin n → ℝ} (hx : IsPreflow A x) (a b : Fin n) :
    IsPreflow A (eraseArc x a b) := by
  classical
  constructor
  · intro i j
    unfold eraseArc
    split_ifs
    · exact le_rfl
    · exact hx.1 i j
  · intro i j hij
    simp [eraseArc, hx.2 i j hij]

theorem balance_eraseArc (x : Fin n → Fin n → ℝ) (a b k : Fin n) :
    balance (eraseArc x a b) k = balance x k -
      x a b * ((if k = b then 1 else 0) - (if k = a then 1 else 0)) := by
  have h := balance_add (eraseArc x a b) (x a b • arcUnit a b) k
  rw [eraseArc_add, balance_smul, balance_arcUnit] at h
  linarith

theorem flowSupport_eraseArc (x : Fin n → Fin n → ℝ) (a b : Fin n) :
    flowSupport (eraseArc x a b) = (flowSupport x).erase (a,b) := by
  classical
  ext p
  rcases p with ⟨i,j⟩
  simp [flowSupport, eraseArc, Prod.mk.injEq]

theorem independentSupport_eraseArc {x : Fin n → Fin n → ℝ}
    (hx : IndependentSupport (flowSupport x)) (a b : Fin n) :
    IndependentSupport (flowSupport (eraseArc x a b)) := by
  rw [flowSupport_eraseArc]
  exact independentSupport_mono hx (Finset.erase_subset _ _)

theorem flowSupport_eraseArc_card_lt {x : Fin n → Fin n → ℝ}
    {a b : Fin n} (hab : x a b ≠ 0) :
    (flowSupport (eraseArc x a b)).card < (flowSupport x).card := by
  rw [flowSupport_eraseArc]
  exact Finset.card_erase_lt_of_mem ((mem_flowSupport x a b).mpr hab)

theorem flowCost_eraseArc {A : Finset (Fin n × Fin n)}
    (c : Fin n → Fin n → ℝ → ℝ) (hc : ∀ p ∈ A, c p.1 p.2 0 = 0)
    (x : Fin n → Fin n → ℝ) {a b : Fin n} (hab : (a,b) ∈ A) :
    flowCost A c x = c a b (x a b) + flowCost A c (eraseArc x a b) := by
  classical
  have hx := Finset.sum_erase_add A (fun p => c p.1 p.2 (x p.1 p.2)) hab
  have hy := Finset.sum_erase_add A
    (fun p => c p.1 p.2 (eraseArc x a b p.1 p.2)) hab
  have he : (∑ p ∈ A.erase (a,b), c p.1 p.2 (x p.1 p.2)) =
      ∑ p ∈ A.erase (a,b), c p.1 p.2 (eraseArc x a b p.1 p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hn : ¬(p.1 = a ∧ p.2 = b) := by
      rintro ⟨ha,hb⟩
      exact (Finset.mem_erase.mp hp).1 (Prod.ext ha hb)
    simp [eraseArc, hn]
  simp only [eraseArc, and_self, ↓reduceIte, hc (a,b) hab, add_zero] at hy
  dsimp [flowCost, eraseArc] at hx he ⊢
  linarith

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem unique_neighbor_zero {A : Finset (Fin n × Fin n)}
    {x : Fin n → Fin n → ℝ} (hA : IsGraph A) (hx : IsPreflow A x)
    (root j : Fin n)
    (hu : ∀ k, (supportGraph (flowSupport x)).Adj root k → k = j)
    {k : Fin n} (hkj : k ≠ j) : x root k = 0 ∧ x k root = 0 := by
  by_cases hkr : k = root
  · subst k
    have hz := hx.2 root root (fun h => hA (root,root) h rfl)
    exact ⟨hz,hz⟩
  · constructor
    · by_contra h
      exact hkj (hu k ⟨Ne.symm hkr, Or.inl ((mem_flowSupport x root k).mpr h)⟩)
    · by_contra h
      exact hkj (hu k ⟨Ne.symm hkr, Or.inr ((mem_flowSupport x k root).mpr h)⟩)

theorem unique_neighbor_balance {A : Finset (Fin n × Fin n)}
    {x : Fin n → Fin n → ℝ} (hA : IsGraph A) (hx : IsPreflow A x)
    (root j : Fin n)
    (hu : ∀ k, (supportGraph (flowSupport x)).Adj root k → k = j) :
    balance x root = x j root - x root j := by
  unfold balance
  congr 1
  · apply Finset.sum_eq_single j
    · intro k _ hkj
      exact (unique_neighbor_zero hA hx root j hu hkj).2
    · simp
  · apply Finset.sum_eq_single j
    · intro k _ hkj
      exact (unique_neighbor_zero hA hx root j hu hkj).1
    · simp

theorem positive_send_erase {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root j : Fin n} {I : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hx : IsFlow A (subDemand r root I) x)
    (he : x root j = demandSum r I) :
    IsFlow A (subDemand r j I) (eraseArc x root j) := by
  apply flow_of_balance (eraseArc_preflow hx.1 root j)
  intro k
  rw [balance_eraseArc, flow_balance hx, he]
  simp only [subDemand]
  split_ifs <;> ring

theorem negative_send_erase {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root j : Fin n} {I : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hx : IsFlow A (subDemand r root I) x)
    (he : x j root = -demandSum r I) :
    IsFlow A (subDemand r j I) (eraseArc x j root) := by
  apply flow_of_balance (eraseArc_preflow hx.1 j root)
  intro k
  rw [balance_eraseArc, flow_balance hx, he]
  simp only [subDemand]
  split_ifs <;> ring

theorem one_neighbor_send {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root j : Fin n} {I : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hA : IsGraph A) (hx : IsFlow A (subDemand r root I) x)
    (hs : IndependentSupport (flowSupport x)) (hr : root ∉ I)
    (hq : demandSum r I ≠ 0)
    (hj : (supportGraph (flowSupport x)).Adj root j)
    (hu : ∀ k, (supportGraph (flowSupport x)).Adj root k → k = j) :
    ∃ y : Fin n → Fin n → ℝ,
      IsFlow A (subDemand r j I) y ∧ IndependentSupport (flowSupport y) ∧
      (flowSupport y).card < (flowSupport x).card ∧ IsSendArc A r I root j ∧
      ∀ c : Fin n → Fin n → ℝ → ℝ, (∀ p ∈ A, c p.1 p.2 0 = 0) →
        (flowCost A c x : EReal) = sendCost A c r I root j + (flowCost A c y : EReal) := by
  classical
  have hb := unique_neighbor_balance hA hx.1 root j hu
  rw [flow_balance hx] at hb
  simp only [subDemand, hr, ↓reduceIte, zero_sub] at hb
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · have hxp : 0 < x j root := by linarith [hx.1.1 root j]
    have hmem := (mem_flowSupport x j root).mpr (ne_of_gt hxp)
    have hn := independentSupport_no_opposite hs hj.ne.symm hmem
    have hz : x root j = 0 := by
      by_contra h
      exact hn ((mem_flowSupport x root j).mpr h)
    have he : x j root = -demandSum r I := by linarith
    have ha : (j,root) ∈ A := by
      by_contra h
      exact (ne_of_gt hxp) (hx.1.2 j root h)
    refine ⟨eraseArc x j root, negative_send_erase hx he,
      independentSupport_eraseArc hs j root, flowSupport_eraseArc_card_lt (ne_of_gt hxp),
      Or.inr ⟨hneg,ha⟩, ?_⟩
    intro c hc
    rw [flowCost_eraseArc c hc x ha, he]
    simp [sendCost, not_lt.mpr (le_of_lt hneg), hneg, ha]
  · have hxp : 0 < x root j := by linarith [hx.1.1 j root]
    have hmem := (mem_flowSupport x root j).mpr (ne_of_gt hxp)
    have hn := independentSupport_no_opposite hs hj.ne hmem
    have hz : x j root = 0 := by
      by_contra h
      exact hn ((mem_flowSupport x j root).mpr h)
    have he : x root j = demandSum r I := by linarith
    have ha : (root,j) ∈ A := by
      by_contra h
      exact (ne_of_gt hxp) (hx.1.2 root j h)
    refine ⟨eraseArc x root j, positive_send_erase hx he,
      independentSupport_eraseArc hs root j, flowSupport_eraseArc_card_lt (ne_of_gt hxp),
      Or.inl ⟨hpos,ha⟩, ?_⟩
    intro c hc
    rw [flowCost_eraseArc c hc x ha, he]
    simp [sendCost, hpos, ha]

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem supportGraph_delete_le (s : Finset (Fin n × Fin n)) (u v : Fin n) :
    (supportGraph s).deleteEdges {Sym2.mk u v} ≤
      supportGraph ((s.erase (u,v)).erase (v,u)) := by
  classical
  intro a b hab
  rcases SimpleGraph.deleteEdges_adj.mp hab with ⟨hab, hn⟩
  change a ≠ b ∧ ((a,b) ∈ s ∨ (b,a) ∈ s) at hab
  change a ≠ b ∧ _
  refine ⟨hab.1, ?_⟩
  have h1 : (a,b) ≠ (u,v) := by
    intro he
    cases he
    exact hn (by simp)
  have h2 : (a,b) ≠ (v,u) := by
    intro he
    cases he
    exact hn (by simp [Sym2.eq_swap])
  have h3 : (b,a) ≠ (u,v) := by
    intro he
    have ha : a = v := congrArg Prod.snd he
    have hb : b = u := congrArg Prod.fst he
    subst a b
    exact hn (by simp [Sym2.eq_swap])
  have h4 : (b,a) ≠ (v,u) := by
    intro he
    have ha : a = u := congrArg Prod.snd he
    have hb : b = v := congrArg Prod.fst he
    subst a b
    exact hn (by simp)
  rcases hab.2 with h | h
  · exact Or.inl (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, h⟩⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨h4, Finset.mem_erase.mpr ⟨h3, h⟩⟩)

theorem independentSupport_isBridge {s : Finset (Fin n × Fin n)}
    (hs : IndependentSupport s) {u v : Fin n}
    (huv : (supportGraph s).Adj u v) :
    (supportGraph s).IsBridge (Sym2.mk u v) := by
  classical
  rw [SimpleGraph.isBridge_iff]
  intro hr
  obtain ⟨p⟩ := hr.mono (supportGraph_delete_le s u v)
  let t := (s.erase (u,v)).erase (v,u)
  have hts : t ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have heq : walkFlow t p = signedArc s u v := independent_support_unique hs
    (fun i j hij => walkFlow_supported t p i j (fun h => hij (hts h)))
    (signedArc_supported huv)
    (fun k => by rw [balance_walkFlow, balance_signedArc])
  have hz : walkFlow t p u v = 0 := walkFlow_supported t p u v (by simp [t])
  have hzr : walkFlow t p v u = 0 := walkFlow_supported t p v u (by simp [t])
  by_cases h : (u,v) ∈ s
  · have hh := congrFun (congrFun heq u) v
    rw [hz] at hh
    simp [signedArc, h, arcUnit] at hh
  · have hh := congrFun (congrFun heq v) u
    rw [hzr] at hh
    simp [signedArc, h, arcUnit] at hh

theorem independentSupport_isAcyclic {s : Finset (Fin n × Fin n)}
    (hs : IndependentSupport s) : (supportGraph s).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ h => independentSupport_isBridge hs h

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

noncomputable def rootComponent (G : SimpleGraph (Fin n)) (root u : Fin n) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun v => (G.deleteIncidenceSet root).Reachable u v

theorem mem_rootComponent (G : SimpleGraph (Fin n)) (root u v : Fin n) :
    v ∈ rootComponent G root u ↔ (G.deleteIncidenceSet root).Reachable u v := by
  classical
  simp [rootComponent]

theorem self_mem_rootComponent (G : SimpleGraph (Fin n)) (root u : Fin n) :
    u ∈ rootComponent G root u := by
  exact (mem_rootComponent G root u u).mpr (SimpleGraph.Reachable.refl u)

theorem root_not_mem_rootComponent (G : SimpleGraph (Fin n)) (root u : Fin n)
    (hu : u ≠ root) : root ∉ rootComponent G root u := by
  rw [mem_rootComponent]
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hu
  ext v
  simp [SimpleGraph.mem_neighborSet, SimpleGraph.deleteIncidenceSet_adj]

theorem rootComponent_closed (G : SimpleGraph (Fin n)) (root u : Fin n)
    (hu : u ≠ root) {a b : Fin n} (ha : a ∈ rootComponent G root u)
    (hab : G.Adj a b) (hb : b ≠ root) : b ∈ rootComponent G root u := by
  rw [mem_rootComponent] at ha ⊢
  have har : a ≠ root := by
    intro he
    subst a
    exact root_not_mem_rootComponent G root u hu ((mem_rootComponent G root u root).mpr ha)
  exact ha.trans (SimpleGraph.Adj.reachable
    (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab, har, hb⟩))

theorem deleteIncidenceSet_le_delete_single (G : SimpleGraph (Fin n))
    {root u : Fin n} (hu : G.Adj root u) :
    G.deleteIncidenceSet root ≤ G.deleteEdges {Sym2.mk root u} := by
  apply SimpleGraph.deleteEdges_anti
  intro e he
  have heq : e = Sym2.mk root u := Set.mem_singleton_iff.mp he
  subst e
  exact (SimpleGraph.mk'_mem_incidenceSet_iff G).mpr ⟨hu, Or.inl rfl⟩

theorem acyclic_other_neighbor_not_mem (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    {root u v : Fin n} (hu : G.Adj root u) (hv : G.Adj root v) (huv : u ≠ v) :
    v ∉ rootComponent G root u := by
  rw [mem_rootComponent]
  intro hr
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG) hu
  rw [SimpleGraph.isBridge_iff] at hb
  apply hb
  have hv' : (G.deleteEdges {Sym2.mk root u}).Adj root v := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hv, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (h | h)
    · exact huv h.2.symm
    · exact hu.ne h.1
  exact hv'.reachable.trans (hr.symm.mono (deleteIncidenceSet_le_delete_single G hu))

theorem rootComponent_flow_cut (x : Fin n → Fin n → ℝ)
    (root u : Fin n) (hu : u ≠ root) :
    ∀ i ∈ rootComponent (supportGraph (flowSupport x)) root u,
      ∀ j, j ∉ rootComponent (supportGraph (flowSupport x)) root u → j ≠ root →
        x i j = 0 ∧ x j i = 0 := by
  classical
  intro i hi j hj hjr
  have hij : i ≠ j := by rintro rfl; exact hj hi
  constructor
  · by_contra hz
    have hadj : (supportGraph (flowSupport x)).Adj i j :=
      ⟨hij, Or.inl ((mem_flowSupport x i j).mpr hz)⟩
    exact hj (rootComponent_closed _ root u hu hi hadj hjr)
  · by_contra hz
    have hadj : (supportGraph (flowSupport x)).Adj i j :=
      ⟨hij, Or.inr ((mem_flowSupport x j i).mpr hz)⟩
    exact hj (rootComponent_closed _ root u hu hi hadj hjr)

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem sum_balance (x : Fin n → Fin n → ℝ) : (∑ i, balance x i) = 0 := by
  simp only [balance, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (Finset.sum_comm)

noncomputable def cutPart (x : Fin n → Fin n → ℝ) (U : Finset (Fin n)) :
    Fin n → Fin n → ℝ :=
  fun i j => if i ∈ U ∨ j ∈ U then x i j else 0

noncomputable def cutRest (x : Fin n → Fin n → ℝ) (U : Finset (Fin n)) :
    Fin n → Fin n → ℝ :=
  fun i j => if i ∈ U ∨ j ∈ U then 0 else x i j

theorem cutPart_add_cutRest (x : Fin n → Fin n → ℝ) (U : Finset (Fin n)) :
    cutPart x U + cutRest x U = x := by
  classical
  funext i j
  simp only [cutPart, cutRest, Pi.add_apply]
  split_ifs <;> simp

theorem cutPart_preflow {A : Finset (Fin n × Fin n)}
    {x : Fin n → Fin n → ℝ} (hx : IsPreflow A x) (U : Finset (Fin n)) :
    IsPreflow A (cutPart x U) := by
  classical
  constructor
  · intro i j
    unfold cutPart
    split_ifs
    · exact hx.1 i j
    · exact le_rfl
  · intro i j hij
    simp [cutPart, hx.2 i j hij]

theorem cutRest_preflow {A : Finset (Fin n × Fin n)}
    {x : Fin n → Fin n → ℝ} (hx : IsPreflow A x) (U : Finset (Fin n)) :
    IsPreflow A (cutRest x U) := by
  classical
  constructor
  · intro i j
    unfold cutRest
    split_ifs
    · exact le_rfl
    · exact hx.1 i j
  · intro i j hij
    simp [cutRest, hx.2 i j hij]

theorem cutPart_balance_mem (x : Fin n → Fin n → ℝ) (U : Finset (Fin n))
    {k : Fin n} (hk : k ∈ U) : balance (cutPart x U) k = balance x k := by
  simp [balance, cutPart, hk]

theorem cutPart_balance_outside (x : Fin n → Fin n → ℝ) (U : Finset (Fin n))
    (root : Fin n)
    (hcut : ∀ i ∈ U, ∀ j, j ∉ U → j ≠ root → x i j = 0 ∧ x j i = 0)
    {k : Fin n} (hk : k ∉ U) (hkr : k ≠ root) :
    balance (cutPart x U) k = 0 := by
  have hin : ∀ j, cutPart x U j k = 0 := by
    intro j
    by_cases hj : j ∈ U
    · simp [cutPart, hj, (hcut j hj k hk hkr).1]
    · simp [cutPart, hj, hk]
  have hout : ∀ j, cutPart x U k j = 0 := by
    intro j
    by_cases hj : j ∈ U
    · simp [cutPart, hj, (hcut j hj k hk hkr).2]
    · simp [cutPart, hj, hk]
  simp [balance, hin, hout]

theorem cutPart_balance_root (x : Fin n → Fin n → ℝ) (U : Finset (Fin n))
    (root : Fin n) (hroot : root ∉ U)
    (hcut : ∀ i ∈ U, ∀ j, j ∉ U → j ≠ root → x i j = 0 ∧ x j i = 0) :
    balance (cutPart x U) root = -(∑ i ∈ U, balance x i) := by
  classical
  have he : ∀ k, balance (cutPart x U) k =
      (if k ∈ U then balance x k else 0) +
        (if k = root then balance (cutPart x U) root else 0) := by
    intro k
    by_cases hk : k ∈ U
    · have hkr : k ≠ root := by rintro rfl; exact hroot hk
      simp [hk, hkr, cutPart_balance_mem x U hk]
    · by_cases hkr : k = root
      · subst k; simp [hroot]
      · simp [hk, hkr, cutPart_balance_outside x U root hcut hk hkr]
  have hz := sum_balance (cutPart x U)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => he k)
  rw [hsum] at hz
  simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.univ_inter] at hz
  linarith

theorem flowCost_cut_add {A : Finset (Fin n × Fin n)}
    (c : Fin n → Fin n → ℝ → ℝ) (hc : ∀ p ∈ A, c p.1 p.2 0 = 0)
    (x : Fin n → Fin n → ℝ) (U : Finset (Fin n)) :
    flowCost A c (cutPart x U) + flowCost A c (cutRest x U) = flowCost A c x := by
  classical
  unfold flowCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [cutPart, cutRest]
  split_ifs <;> simp [hc p hp]

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem cutPart_subproblem {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root : Fin n} {I U : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hx : IsFlow A (subDemand r root I) x) (hroot : root ∉ U)
    (hcut : ∀ i ∈ U, ∀ j, j ∉ U → j ≠ root → x i j = 0 ∧ x j i = 0) :
    IsFlow A (subDemand r root (I ∩ U)) (cutPart x U) := by
  classical
  apply flow_of_balance (cutPart_preflow hx.1 U)
  intro k
  by_cases hkr : k = root
  · subst k
    rw [cutPart_balance_root x U root hroot hcut]
    have hs : (∑ i ∈ U, balance x i) = demandSum r (I ∩ U) := by
      calc
        (∑ i ∈ U, balance x i) = ∑ i ∈ U, if i ∈ I then r i else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hir : i ≠ root := by rintro rfl; exact hroot hi
          rw [flow_balance hx]
          simp [subDemand, hir]
        _ = demandSum r (I ∩ U) := by
          simp [demandSum, Finset.sum_ite_mem, Finset.inter_comm]
    rw [hs]
    simp [subDemand, hroot]
  · by_cases hk : k ∈ U
    · rw [cutPart_balance_mem x U hk, flow_balance hx]
      simp [subDemand, hk, hkr]
    · rw [cutPart_balance_outside x U root hcut hk hkr]
      simp [subDemand, hk, hkr]

theorem cutRest_subproblem {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root : Fin n} {I U : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hx : IsFlow A (subDemand r root I) x) (hroot : root ∉ U)
    (hcut : ∀ i ∈ U, ∀ j, j ∉ U → j ≠ root → x i j = 0 ∧ x j i = 0) :
    IsFlow A (subDemand r root (I \ (I ∩ U))) (cutRest x U) := by
  classical
  have hp := cutPart_subproblem hx hroot hcut
  apply flow_of_balance (cutRest_preflow hx.1 U)
  intro k
  have hb := balance_add (cutPart x U) (cutRest x U) k
  rw [cutPart_add_cutRest, flow_balance hx, flow_balance hp] at hb
  have hd := congrFun (subDemand_partition r root I (I ∩ U) Finset.inter_subset_left) k
  simp only [Pi.add_apply] at hd
  linarith

theorem flowSupport_cutPart_subset (x : Fin n → Fin n → ℝ) (U : Finset (Fin n)) :
    flowSupport (cutPart x U) ⊆ flowSupport x := by
  classical
  intro p hp
  rcases p with ⟨i,j⟩
  rw [mem_flowSupport] at hp ⊢
  contrapose! hp
  simp [cutPart, hp]

theorem flowSupport_cutRest_subset (x : Fin n → Fin n → ℝ) (U : Finset (Fin n)) :
    flowSupport (cutRest x U) ⊆ flowSupport x := by
  classical
  intro p hp
  rcases p with ⟨i,j⟩
  rw [mem_flowSupport] at hp ⊢
  contrapose! hp
  simp [cutRest, hp]

theorem independentSupport_cutPart {x : Fin n → Fin n → ℝ}
    (hx : IndependentSupport (flowSupport x)) (U : Finset (Fin n)) :
    IndependentSupport (flowSupport (cutPart x U)) :=
  independentSupport_mono hx (flowSupport_cutPart_subset x U)

theorem independentSupport_cutRest {x : Fin n → Fin n → ℝ}
    (hx : IndependentSupport (flowSupport x)) (U : Finset (Fin n)) :
    IndependentSupport (flowSupport (cutRest x U)) :=
  independentSupport_mono hx (flowSupport_cutRest_subset x U)

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem independent_zero_demand {A : Finset (Fin n × Fin n)}
    {x : Fin n → Fin n → ℝ} (hx : IsFlow A 0 x)
    (hs : IndependentSupport (flowSupport x)) : x = 0 := by
  apply hs x
  · intro i j hij
    by_contra h
    exact hij ((mem_flowSupport x i j).mpr h)
  · intro i
    simpa using flow_balance hx i

theorem cutPart_ne_zero_of_neighbor (x : Fin n → Fin n → ℝ)
    (U : Finset (Fin n)) {root u : Fin n}
    (hu : (supportGraph (flowSupport x)).Adj root u) (hU : u ∈ U) :
    cutPart x U ≠ 0 := by
  intro hz
  rcases hu.2 with h | h
  · have he := congrFun (congrFun hz root) u
    have hn := (mem_flowSupport x root u).mp h
    exact hn (by simpa [cutPart, hU] using he)
  · have he := congrFun (congrFun hz u) root
    have hn := (mem_flowSupport x u root).mp h
    exact hn (by simpa [cutPart, hU] using he)

theorem cutRest_ne_zero_of_neighbor (x : Fin n → Fin n → ℝ)
    (U : Finset (Fin n)) {root u : Fin n}
    (hu : (supportGraph (flowSupport x)).Adj root u)
    (hr : root ∉ U) (hU : u ∉ U) : cutRest x U ≠ 0 := by
  intro hz
  rcases hu.2 with h | h
  · have he := congrFun (congrFun hz root) u
    have hn := (mem_flowSupport x root u).mp h
    exact hn (by simpa [cutRest, hr, hU] using he)
  · have he := congrFun (congrFun hz u) root
    have hn := (mem_flowSupport x u root).mp h
    exact hn (by simpa [cutRest, hr, hU] using he)

theorem two_neighbor_split {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root : Fin n} {I : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hx : IsFlow A (subDemand r root I) x)
    (hs : IndependentSupport (flowSupport x))
    {u v : Fin n} (hu : (supportGraph (flowSupport x)).Adj root u)
    (hv : (supportGraph (flowSupport x)).Adj root v) (huv : u ≠ v) :
    ∃ J : Finset (Fin n), J.Nonempty ∧ J ⊂ I ∧
      ∃ x₁ x₂ : Fin n → Fin n → ℝ,
        IsFlow A (subDemand r root J) x₁ ∧
        IsFlow A (subDemand r root (I \ J)) x₂ ∧
        IndependentSupport (flowSupport x₁) ∧ IndependentSupport (flowSupport x₂) ∧
        x₁ + x₂ = x ∧
        ∀ c : Fin n → Fin n → ℝ → ℝ,
          (∀ p ∈ A, c p.1 p.2 0 = 0) →
          flowCost A c x₁ + flowCost A c x₂ = flowCost A c x := by
  classical
  let G := supportGraph (flowSupport x)
  let U := rootComponent G root u
  have hr : root ∉ U := root_not_mem_rootComponent G root u hu.ne.symm
  have huU : u ∈ U := self_mem_rootComponent G root u
  have hvU : v ∉ U := acyclic_other_neighbor_not_mem G
    (independentSupport_isAcyclic hs) hu hv huv
  have hcut := rootComponent_flow_cut x root u hu.ne.symm
  have hp := cutPart_subproblem hx hr hcut
  have hq := cutRest_subproblem hx hr hcut
  have hip := independentSupport_cutPart hs U
  have hiq := independentSupport_cutRest hs U
  have hpn := cutPart_ne_zero_of_neighbor x U hu huU
  have hqn := cutRest_ne_zero_of_neighbor x U hv hr hvU
  have hd0 : subDemand r root ∅ = 0 := by
    funext k
    simp [subDemand, demandSum]
  have hJ : (I ∩ U).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hzflow : IsFlow A 0 (cutPart x U) := by
      simpa only [he, hd0] using hp
    exact hpn (independent_zero_demand hzflow hip)
  have hrest : (I \ (I ∩ U)).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hzflow : IsFlow A 0 (cutRest x U) := by
      simpa only [he, hd0] using hq
    exact hqn (independent_zero_demand hzflow hiq)
  refine ⟨I ∩ U, hJ, ?_, cutPart x U, cutRest x U, hp, hq, hip, hiq,
    cutPart_add_cutRest x U, ?_⟩
  · apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro he
    simp [he] at hrest
  · intro c hc
    exact flowCost_cut_add c hc x U

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem root_has_neighbor {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root : Fin n} {I : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hA : IsGraph A) (hx : IsFlow A (subDemand r root I) x)
    (hr : root ∉ I) (hq : demandSum r I ≠ 0) :
    ∃ j, (supportGraph (flowSupport x)).Adj root j := by
  classical
  by_contra h
  push Not at h
  have hz : ∀ k, x root k = 0 ∧ x k root = 0 := by
    intro k
    by_cases hk : k = root
    · subst k
      have he := hx.1.2 root root (fun ha => hA (root,root) ha rfl)
      exact ⟨he,he⟩
    · constructor
      · by_contra he
        exact h k ⟨Ne.symm hk, Or.inl ((mem_flowSupport x root k).mpr he)⟩
      · by_contra he
        exact h k ⟨Ne.symm hk, Or.inr ((mem_flowSupport x k root).mpr he)⟩
  have hb := flow_balance hx root
  simp [balance, fun k => (hz k).1, fun k => (hz k).2, subDemand, hr] at hb
  exact hq hb

theorem forest_send_or_split {A : Finset (Fin n × Fin n)} {r : Fin n → ℝ}
    {root : Fin n} {I : Finset (Fin n)} {x : Fin n → Fin n → ℝ}
    (hA : IsGraph A) (hx : IsFlow A (subDemand r root I) x)
    (hs : IndependentSupport (flowSupport x)) (hr : root ∉ I)
    (hq : demandSum r I ≠ 0) :
    (∃ (j : Fin n) (y : Fin n → Fin n → ℝ),
      IsFlow A (subDemand r j I) y ∧ IndependentSupport (flowSupport y) ∧
      (flowSupport y).card < (flowSupport x).card ∧ IsSendArc A r I root j ∧
      ∀ c : Fin n → Fin n → ℝ → ℝ, (∀ p ∈ A, c p.1 p.2 0 = 0) →
        (flowCost A c x : EReal) = sendCost A c r I root j + (flowCost A c y : EReal)) ∨
    (∃ J : Finset (Fin n), J.Nonempty ∧ J ⊂ I ∧
      ∃ x₁ x₂ : Fin n → Fin n → ℝ,
        IsFlow A (subDemand r root J) x₁ ∧
        IsFlow A (subDemand r root (I \ J)) x₂ ∧
        IndependentSupport (flowSupport x₁) ∧ IndependentSupport (flowSupport x₂) ∧
        x₁ + x₂ = x ∧
        ∀ c : Fin n → Fin n → ℝ → ℝ, (∀ p ∈ A, c p.1 p.2 0 = 0) →
          flowCost A c x₁ + flowCost A c x₂ = flowCost A c x) := by
  classical
  obtain ⟨j,hj⟩ := root_has_neighbor hA hx hr hq
  by_cases hu : ∀ k, (supportGraph (flowSupport x)).Adj root k → k = j
  · exact Or.inl ⟨j, one_neighbor_send hA hx hs hr hq hj hu⟩
  · push Not at hu
    obtain ⟨k,hk,hkj⟩ := hu
    exact Or.inr (two_neighbor_split hx hs hj hk hkj.symm)

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ} {A : Finset (Fin n × Fin n)} {c : Fin n → Fin n → ℝ → ℝ}
  {r : Fin n → ℝ} {C : Fin n → Finset (Fin n) → EReal}

theorem solution_send_le (hC : IsSolution A c r C) (i j : Fin n)
    {I : Finset (Fin n)} (hI : IsAdmissible r I) (hq : demandSum r I ≠ 0) :
    C i I ≤ sendCost A c r I i j + C j I := by
  rw [(hC.2 i I hI).2 hq]
  exact inf_le_left.trans (Finset.inf_le (Finset.mem_univ j))

theorem solution_split_le (hC : IsSolution A c r C) (i : Fin n)
    {I : Finset (Fin n)} (hI : IsAdmissible r I) (hq : demandSum r I ≠ 0) :
    C i I ≤ splitCost C i I := by
  rw [(hC.2 i I hI).2 hq]
  exact inf_le_right

theorem splitCost_le_partition (C : Fin n → Finset (Fin n) → EReal)
    (i : Fin n) {I J : Finset (Fin n)} (hJ : J.Nonempty) (hJI : J ⊂ I) :
    splitCost C i I ≤ C i J + C i (I \ J) := by
  classical
  have hcard : I.card ≠ 1 := by
    have hlt := Finset.card_lt_card hJI
    have hp := Finset.card_pos.mpr hJ
    omega
  rw [splitCost, if_neg hcard]
  apply Finset.inf_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.trans
    (Finset.Subset.refl J) (Finset.ssubset_iff_subset_ne.mp hJI).1),
    hJ, (Finset.ssubset_iff_subset_ne.mp hJI).2⟩

theorem solution_partition_le (hC : IsSolution A c r C) (i : Fin n)
    {I J : Finset (Fin n)} (hI : IsAdmissible r I) (hq : demandSum r I ≠ 0)
    (hJ : J.Nonempty) (hJI : J ⊂ I) : C i I ≤ C i J + C i (I \ J) :=
  (solution_split_le hC i hI hq).trans (splitCost_le_partition C i hJ hJI)

theorem solution_singleton_le_zero (hC : IsSolution A c r C) (i : Fin n)
    (hi : r i ≠ 0) : C i {i} ≤ 0 := by
  have hI : IsAdmissible r {i} := by
    refine ⟨Finset.singleton_nonempty i, ?_⟩
    intro j hj
    have he : j = i := Finset.mem_singleton.mp hj
    subst j
    simp [demandNodes, hi]
  have h := solution_split_le hC i hI (by simpa [demandSum] using hi)
  simpa [splitCost] using h

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

lemma native_singleton_minCost {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b) (i : Fin n) :
    minCost A c r i {i}=0 := by
  have hx : IsMinCostFlow A c (subDemand r i {i}) 0 := by
    rw [subDemand_singleton]; exact native_zero_minimum hc hmin
  rw [native_minCost_eq_of_minimum hx]
  have hz : flowCost A c 0=0 := Finset.sum_eq_zero (fun p hp => (hc p hp).2)
  simp [hz]

lemma native_split_le_minCost_of_mem {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {i : Fin n} {I : Finset (Fin n)} (hi : i ∈ I) :
    splitCost (minCost A c r) i I ≤ minCost A c r i I := by
  classical
  by_cases he : I={i}
  · subst I
    simp [splitCost,native_singleton_minCost hc hmin i]
  · have hsub : ({i}:Finset (Fin n)) ⊂ I :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hi,Ne.symm he⟩
    have h := splitCost_le_partition (minCost A c r) i (Finset.singleton_nonempty i) hsub
    rw [native_singleton_minCost hc hmin i,zero_add,Finset.sdiff_singleton_eq_erase] at h
    have heq : minCost A c r i (I.erase i)=minCost A c r i I := by
      unfold minCost
      rw [subDemand_erase_root r i I hi]
    simpa only [heq] using h

lemma native_rhs_le_forest_cost {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hA : IsGraph A) (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    {i : Fin n} {I : Finset (Fin n)} (hq : demandSum r I≠0)
    {x : Fin n → Fin n → ℝ} (hx : IsFlow A (subDemand r i I) x)
    (hs : IndependentSupport (flowSupport x)) :
    ((Finset.univ.inf fun j => sendCost A c r I i j+minCost A c r j I) ⊓
      splitCost (minCost A c r) i I) ≤ (flowCost A c x:EReal) := by
  classical
  by_cases hi : i ∈ I
  · exact inf_le_right.trans ((native_split_le_minCost_of_mem hc hmin hi).trans
      (native_minCost_le_flow hx))
  · rcases forest_send_or_split hA hx hs hi hq with hsend|hsplit
    · obtain ⟨j,y,hy,_,_,_,he⟩ := hsend
      rw [he c (fun p hp => (hc p hp).2)]
      exact (inf_le_left.trans (Finset.inf_le (Finset.mem_univ j))).trans
        (add_le_add le_rfl (native_minCost_le_flow hy))
    · obtain ⟨J,hJ,hJI,x1,x2,h1,h2,_,_,_,he⟩ := hsplit
      have hle := splitCost_le_partition (minCost A c r) i hJ hJI
      have hp := add_le_add (native_minCost_le_flow (c:=c) h1) (native_minCost_le_flow (c:=c) h2)
      rw [← EReal.coe_add,he c (fun p hp => (hc p hp).2)] at hp
      exact inf_le_right.trans (hle.trans hp)

lemma native_minCost_isSolution {n : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hA : IsGraph A) (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b) :
    IsSolution A c r (minCost A c r) := by
  classical
  refine ⟨fun j I _ => native_minCost_ne_bot hc hmin j I,?_⟩
  intro i I _
  constructor
  · intro hzero j hj
    unfold minCost
    rw [subDemand_zero_sum_erase r i j I hj hzero]
  · intro hq
    apply le_antisymm
    · apply le_inf
      · apply Finset.le_inf
        intro j _
        exact native_forward_send hc hmin i j I
      · exact native_forward_split hc hmin i I
    · by_cases hf : ∃ x, IsFlow A (subDemand r i I) x
      · obtain ⟨x,hx,hs⟩ := minimum_flow_exists_for_every_feasible_demand hc hmin hf
        rw [native_minCost_eq_of_minimum hx]
        exact native_rhs_le_forest_cost hA hc hmin hq hx.1 hs
      · rw [native_minCost_eq_top_of_infeasible hf]
        exact le_top

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem splitCost_congr_proper (C D : Fin n → Finset (Fin n) → EReal)
    (I : Finset (Fin n))
    (h : ∀ J, J.Nonempty → J ⊂ I → ∀ i, C i J = D i J) (i : Fin n) :
    splitCost C i I = splitCost D i I := by
  classical
  unfold splitCost
  split_ifs
  · rfl
  · rfl
  · apply Finset.inf_congr rfl
    intro J hJ
    rcases Finset.mem_filter.mp hJ with ⟨hsub,hne,hneq⟩
    have hJI := Finset.mem_powerset.mp hsub
    have hp : J ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨hJI,hneq⟩
    have hr := Finset.sdiff_nonempty_of_card_lt_card (Finset.card_lt_card hp)
    rw [h J hne hp i, h (I \ J) hr (Finset.sdiff_ssubset hJI hne) i]

theorem sendCost_ne_top_isSendArc {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ} {I : Finset (Fin n)}
    {i j : Fin n} (h : sendCost A c r I i j ≠ ⊤) : IsSendArc A r I i j := by
  unfold sendCost at h
  split_ifs at h with hp hn
  · exact Or.inl hp
  · exact Or.inr hn
  · exact False.elim (h rfl)

theorem bad_node_successor {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    {C : Fin n → Finset (Fin n) → EReal}
    (hc : IsConcaveArcCost A c) (hmin : ∃ b, IsMinCostFlow A c r b)
    (hC : IsSolution A c r C) {I : Finset (Fin n)} (hI : IsAdmissible r I)
    (hq : demandSum r I ≠ 0)
    (hsmall : ∀ J, J.Nonempty → J ⊂ I → ∀ i, C i J = minCost A c r i J)
    {i : Fin n} (hbad : C i I < minCost A c r i I) :
    ∃ j : Fin n, C j I < minCost A c r j I ∧ IsSendArc A r I i j ∧
      C i I = sendCost A c r I i j + C j I := by
  classical
  have hsplit : C i I < splitCost C i I := by
    rw [splitCost_congr_proper C (minCost A c r) I hsmall i]
    exact hbad.trans_le (native_forward_split hc hmin i I)
  let F := Finset.univ.inf (fun j => sendCost A c r I i j + C j I)
  have heq : C i I = F := by
    have h := (hC.2 i I hI).2 hq
    change C i I = F ⊓ splitCost C i I at h
    rcases le_total F (splitCost C i I) with hl | hr
    · simpa only [inf_eq_left.mpr hl] using h
    · rw [inf_eq_right.mpr hr] at h
      exact False.elim ((ne_of_lt hsplit) h)
  obtain ⟨j,_hj,hj⟩ := Finset.exists_mem_eq_inf Finset.univ ⟨i,Finset.mem_univ i⟩
    (fun j => sendCost A c r I i j + C j I)
  have ht : C i I = sendCost A c r I i j + C j I := heq.trans hj
  have htop : C i I ≠ ⊤ := ne_top_of_lt hbad
  have ha : sendCost A c r I i j ≠ ⊤ := by
    intro he
    rw [he, EReal.top_add_of_ne_bot (hC.1 j I hI)] at ht
    exact htop ht
  have hbj : C j I < minCost A c r j I := by
    by_contra h
    have hjle : minCost A c r j I ≤ C j I := le_of_not_gt h
    have hle : minCost A c r i I ≤ C i I := by
      rw [ht]
      exact (native_forward_send hc hmin i j I).trans (add_le_add le_rfl hjle)
    exact (not_le_of_gt hbad) hle
  exact ⟨j,hbj,sendCost_ne_top_isSendArc ha,ht⟩

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

theorem finite_map_has_periodic_point {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    ∃ x : α, ∃ m : ℕ, 0 < m ∧ Function.IsPeriodicPt f m x := by
  classical
  let x : α := Classical.arbitrary α
  obtain ⟨i,j,hij,he⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k] x)
  have make : ∀ a b : ℕ, a < b → f^[a] x = f^[b] x →
      ∃ y : α, ∃ m : ℕ, 0 < m ∧ Function.IsPeriodicPt f m y := by
    intro a b hab habf
    refine ⟨f^[a] x, b-a, Nat.sub_pos_of_lt hab, ?_⟩
    change f^[b-a] (f^[a] x) = f^[a] x
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
    exact habf.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact make i j h he
  · exact make j i h he.symm

theorem finite_map_injective_cycle {α : Type*} [Finite α] [Nonempty α]
    (f : α → α) (hfix : ∀ x, f x ≠ x) :
    ∃ (m : ℕ) (v : Fin m → α), 2 ≤ m ∧ Function.Injective v ∧
      ∀ k, f (v k) = v (finRotate m k) := by
  classical
  obtain ⟨x,l,hl,hper⟩ := finite_map_has_periodic_point f
  let m := Function.minimalPeriod f x
  have hm : 0 < m := hper.minimalPeriod_pos hl
  have hm1 : m ≠ 1 := by
    intro he
    have hf : Function.IsFixedPt f x := Function.minimalPeriod_eq_one_iff_isFixedPt.mp he
    exact hfix x hf
  have hm2 : 2 ≤ m := by omega
  let v : Fin m → α := fun k => f^[k.val] x
  refine ⟨m,v,hm2,?_,?_⟩
  · intro a b hab
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod a.isLt b.isLt hab
  · intro k
    let : NeZero m := ⟨Nat.ne_of_gt hm⟩
    have hr : (finRotate m k).val = (k.val+1) % m := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < m)]
    change f (f^[k.val] x) = f^[(finRotate m k).val] x
    rw [hr, Function.iterate_mod_minimalPeriod_eq]
    exact (Function.iterate_succ_apply' f k.val x).symm

end SendSplit.DPEquations.SSFresh
end


section

open scoped BigOperators

namespace SendSplit.DPEquations.SSFresh

lemma cycle_cost_positive {n m : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} (hzero : ∀ e∈A, c e.1 e.2 0=0)
    (hcirc : ∀ y, IsSimpleCirculation A y → 0 < flowCost A c y)
    (hm : 2 ≤ m) (v : Fin m → Fin n) (hv : Function.Injective v)
    (hedge : ∀ k, (v k,v (finRotate m k)) ∈ A) {θ : ℝ} (hθ : 0 < θ) :
    0 < ∑ k, c (v k) (v (finRotate m k)) θ := by
  classical
  let e : Fin m → Fin n × Fin n := fun k => (v k,v (finRotate m k))
  let E : Finset (Fin n × Fin n) := Finset.univ.image e
  let y : Fin n → Fin n → ℝ := fun i j => if (i,j)∈E then θ else 0
  have hE : E ⊆ A := by
    intro p hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    exact hedge k
  have hy : IsSimpleCirculation A y := by
    refine ⟨m,v,θ,hm,hv,hθ,hedge,?_⟩
    intro i j
    dsimp [y]
    congr 1
    simp [E,e,Prod.ext_iff]
  have hcost : flowCost A c y=∑ k, c (v k) (v (finRotate m k)) θ := by
    calc
      flowCost A c y = ∑ p∈E, c p.1 p.2 (y p.1 p.2) := by
        symm
        exact Finset.sum_subset hE (by
          intro p hp hnot
          simpa [y,hnot] using hzero p hp)
      _ = ∑ p∈E, c p.1 p.2 θ := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [y,hp]
      _ = ∑ k, c (v k) (v (finRotate m k)) θ := by
        rw [Finset.sum_image]
        intro k _ l _ he
        exact hv (congrArg Prod.fst he)
  rw [← hcost]
  exact hcirc y hy

lemma cycle_potential_sum {m : ℕ} (p : Fin m → ℝ) :
    ∑ k, (p k-p (finRotate m k))=0 := by
  rw [Finset.sum_sub_distrib,Equiv.sum_comp (finRotate m) p,sub_self]

lemma no_tight_send_cycle {n m : ℕ} {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ} {I : Finset (Fin n)}
    (_hA : IsGraph A) (hzero : ∀ e∈A, c e.1 e.2 0=0)
    (hcirc : ∀ y, IsSimpleCirculation A y → 0 < flowCost A c y)
    (hq : demandSum r I≠0) (hm : 2 ≤ m) (v : Fin m → Fin n)
    (hv : Function.Injective v)
    (hedge : ∀ k, IsSendArc A r I (v k) (v (finRotate m k)))
    (p : Fin m → ℝ)
    (htight : ∀ k, (p k:EReal)=sendCost A c r I (v k) (v (finRotate m k))+
      (p (finRotate m k):EReal)) : False := by
  classical
  let : NeZero m := ⟨by omega⟩
  rcases lt_or_gt_of_ne hq with hneg|hpos
  · have hed : ∀ k, (v (finRotate m k),v k) ∈ A := by
      intro k
      rcases hedge k with h|h
      · linarith [h.1]
      · exact h.2
    have heq : ∀ k, c (v (finRotate m k)) (v k) (-demandSum r I)=p k-p (finRotate m k) := by
      intro k
      have h := htight k
      rw [sendCost,if_neg (by intro h; linarith [h.1]),if_pos ⟨hneg,hed k⟩,
        ← EReal.coe_add] at h
      have hh : p k=c (v (finRotate m k)) (v k) (-demandSum r I)+p (finRotate m k) :=
        EReal.coe_injective h
      linarith
    let w : Fin m → Fin n := fun k => v (-k)
    have hrot : ∀ k : Fin m, finRotate m (-(finRotate m k)) = -k := by
      intro k
      simp only [finRotate_apply]
      abel
    have hw : Function.Injective w := hv.comp neg_injective
    have hwe : ∀ k, (w k,w (finRotate m k)) ∈ A := by
      intro k
      have h := hed (-(finRotate m k))
      simpa only [hrot,w] using h
    have hp := cycle_cost_positive hzero hcirc hm w hw hwe (neg_pos.mpr hneg)
    have hz : ∑ k, c (w k) (w (finRotate m k)) (-demandSum r I)=0 := by
      have hsum : ∀ k, c (w k) (w (finRotate m k)) (-demandSum r I)=
          (-p (-k))-(-p (-(finRotate m k))) := by
        intro k
        have h := heq (-(finRotate m k))
        simp only [hrot] at h
        dsimp [w]
        linarith
      simp_rw [hsum]
      exact cycle_potential_sum (fun k => -p (-k))
    linarith
  · have hed : ∀ k, (v k,v (finRotate m k)) ∈ A := by
      intro k
      rcases hedge k with h|h
      · exact h.2
      · linarith [h.1]
    have heq : ∀ k, c (v k) (v (finRotate m k)) (demandSum r I)=p k-p (finRotate m k) := by
      intro k
      have h := htight k
      rw [sendCost,if_pos ⟨hpos,hed k⟩,← EReal.coe_add] at h
      have hh := EReal.coe_injective h
      linarith
    have hp := cycle_cost_positive hzero hcirc hm v hv hed hpos
    have hz : ∑ k, c (v k) (v (finRotate m k)) (demandSum r I)=0 := by
      simp_rw [heq]
      exact cycle_potential_sum p
    linarith

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem admissible_proper_partition {r : Fin n → ℝ} {I J : Finset (Fin n)}
    (hI : IsAdmissible r I) (hJ : J.Nonempty) (hJI : J ⊂ I) :
    IsAdmissible r J ∧ IsAdmissible r (I \ J) := by
  have hsub := (Finset.ssubset_iff_subset_ne.mp hJI).1
  exact ⟨admissible_subset r hI hJ hsub,
    admissible_subset r hI (Finset.sdiff_nonempty_of_card_lt_card (Finset.card_lt_card hJI))
      Finset.sdiff_subset⟩

theorem solution_le_forest {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    {C : Fin n → Finset (Fin n) → EReal}
    (hA : IsGraph A) (hc0 : ∀ p ∈ A, c p.1 p.2 0 = 0)
    (hC : IsSolution A c r C) :
    ∀ I : Finset (Fin n), IsAdmissible r I → ∀ (i : Fin n) (x : Fin n → Fin n → ℝ),
      IsFlow A (subDemand r i I) x → IndependentSupport (flowSupport x) →
      C i I ≤ (flowCost A c x : EReal) := by
  classical
  intro I
  refine Finset.strongInductionOn I ?_
  intro I ih hI
  suffices h : ∀ m : ℕ, ∀ (i : Fin n) (x : Fin n → Fin n → ℝ),
      (flowSupport x).card = m → IsFlow A (subDemand r i I) x →
      IndependentSupport (flowSupport x) → C i I ≤ (flowCost A c x : EReal) by
    intro i x hx hs
    exact h _ i x rfl hx hs
  intro m
  induction m using Nat.strong_induction_on with
  | h m im =>
    intro i x hm hx hs
    by_cases hq : demandSum r I = 0
    · obtain ⟨j,hj⟩ := hI.1
      have hjI := admissible_zero_sum_erase r hI hq hj
      have hflow : IsFlow A (subDemand r j (I.erase j)) x := by
        rw [← subDemand_zero_sum_erase r i j I hj hq]
        exact hx
      rw [(hC.2 i I hI).1 hq j hj]
      exact ih (I.erase j) (Finset.erase_ssubset hj) hjI j x hflow hs
    · by_cases hi : i ∈ I
      · by_cases hsingle : I = {i}
        · subst I
          have hflow : IsFlow A 0 x := by simpa only [subDemand_singleton] using hx
          have hz := independent_zero_demand hflow hs
          have hc : flowCost A c x = 0 := by
            rw [hz]
            exact Finset.sum_eq_zero (fun p hp => hc0 p hp)
          rw [hc]
          exact solution_singleton_le_zero hC i (admissible_member_ne_zero r hI (by simp))
        · have hJ : ({i} : Finset (Fin n)) ⊂ I :=
            Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hi, Ne.symm hsingle⟩
          have hparts := admissible_proper_partition hI (Finset.singleton_nonempty i) hJ
          have hflow : IsFlow A (subDemand r i (I \ {i})) x := by
            simpa only [Finset.sdiff_singleton_eq_erase, subDemand_erase_root r i I hi] using hx
          have hrest := ih (I \ {i})
            (Finset.sdiff_ssubset (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_nonempty i))
            hparts.2 i x hflow hs
          have hsingle0 := solution_singleton_le_zero hC i (admissible_member_ne_zero r hI hi)
          have hb := solution_partition_le hC i hI hq (Finset.singleton_nonempty i) hJ
          exact hb.trans (by simpa using add_le_add hsingle0 hrest)
      · rcases forest_send_or_split hA hx hs hi hq with
          ⟨j,y,hy,hsy,hlt,_ha,hcost⟩ | ⟨J,hJ,hJI,x₁,x₂,hx₁,hx₂,hs₁,hs₂,_hadd,hcost⟩
        · have hltm : (flowSupport y).card < m := by simpa only [hm] using hlt
          have hrest := im _ hltm j y rfl hy hsy
          calc
            C i I ≤ sendCost A c r I i j + C j I := solution_send_le hC i j hI hq
            _ ≤ sendCost A c r I i j + (flowCost A c y : EReal) := add_le_add le_rfl hrest
            _ = (flowCost A c x : EReal) := (hcost c hc0).symm
        · have hp := admissible_proper_partition hI hJ hJI
          have h₁ := ih J hJI hp.1 i x₁ hx₁ hs₁
          have h₂ := ih (I \ J) (Finset.sdiff_ssubset (Finset.ssubset_iff_subset_ne.mp hJI).1 hJ)
            hp.2 i x₂ hx₂ hs₂
          calc
            C i I ≤ C i J + C i (I \ J) := solution_partition_le hC i hI hq hJ hJI
            _ ≤ (flowCost A c x₁ : EReal) + (flowCost A c x₂ : EReal) := add_le_add h₁ h₂
            _ = (flowCost A c x : EReal) := by exact_mod_cast hcost c hc0

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem native_greatest_solution {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x)
    {C : Fin n → Finset (Fin n) → EReal} (hC : IsSolution A c r C)
    (i : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I) :
    C i I ≤ minCost A c r i I := by
  by_cases hf : ∃ x, IsFlow A (subDemand r i I) x
  · obtain ⟨x,hx,hs⟩ := minimum_flow_exists_for_every_feasible_demand hc hmin hf
    rw [native_minCost_eq_of_minimum hx]
    exact solution_le_forest hA (fun p hp => (hc p hp).2) hC I hI i x hx.1 hs
  · rw [native_minCost_eq_top_of_infeasible hf]
    exact le_top

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations.SSFresh

variable {n : ℕ}

theorem no_bad_node_of_proper_equality {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x)
    (hpos : ∀ y, IsSimpleCirculation A y → 0 < flowCost A c y)
    {C : Fin n → Finset (Fin n) → EReal} (hC : IsSolution A c r C)
    {I : Finset (Fin n)} (hI : IsAdmissible r I) (hq : demandSum r I ≠ 0)
    (hsmall : ∀ J, J.Nonempty → J ⊂ I → ∀ i, C i J = minCost A c r i J) :
    ∀ i, ¬ C i I < minCost A c r i I := by
  classical
  intro i hi
  let B := {j : Fin n // C j I < minCost A c r j I}
  let : Nonempty B := ⟨⟨i,hi⟩⟩
  have hnext (b : B) := bad_node_successor hc hmin hC hI hq hsmall b.property
  let f : B → B := fun b => ⟨(hnext b).choose, (hnext b).choose_spec.1⟩
  have hstep : ∀ b : B, IsSendArc A r I b.val (f b).val ∧
      C b.val I = sendCost A c r I b.val (f b).val + C (f b).val I := by
    intro b
    exact (hnext b).choose_spec.2
  have hfix : ∀ b : B, f b ≠ b := by
    intro b he
    have ha := (hstep b).1
    have hv := congrArg Subtype.val he
    rw [hv] at ha
    rcases ha with ha | ha
    · exact hA (b.val,b.val) ha.2 rfl
    · exact hA (b.val,b.val) ha.2 rfl
  obtain ⟨m,v,hm,hv,hcycle⟩ := finite_map_injective_cycle f hfix
  let w : Fin m → Fin n := fun k => (v k).val
  have hw : Function.Injective w := Subtype.val_injective.comp hv
  have hedge : ∀ k, IsSendArc A r I (w k) (w (finRotate m k)) := by
    intro k
    have h := (hstep (v k)).1
    rw [hcycle k] at h
    exact h
  let p : Fin m → ℝ := fun k => (C (w k) I).toReal
  have hp : ∀ k, (p k : EReal) = C (w k) I := by
    intro k
    exact EReal.coe_toReal (ne_top_of_lt (v k).property) (hC.1 (w k) I hI)
  have htight : ∀ k, (p k : EReal) = sendCost A c r I (w k) (w (finRotate m k)) +
      (p (finRotate m k) : EReal) := by
    intro k
    rw [hp k, hp (finRotate m k)]
    have h := (hstep (v k)).2
    rw [hcycle k] at h
    exact h
  exact no_tight_send_cycle hA (fun a ha => (hc a ha).2) hpos hq hm w hw hedge p htight

theorem native_unique_solution {A : Finset (Fin n × Fin n)}
    {c : Fin n → Fin n → ℝ → ℝ} {r : Fin n → ℝ}
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x)
    (hpos : ∀ y, IsSimpleCirculation A y → 0 < flowCost A c y)
    {C : Fin n → Finset (Fin n) → EReal} (hC : IsSolution A c r C) :
    ∀ I : Finset (Fin n), IsAdmissible r I → ∀ i, C i I = minCost A c r i I := by
  classical
  intro I
  refine Finset.strongInductionOn I ?_
  intro I ih hI i
  by_cases hq : demandSum r I = 0
  · obtain ⟨j,hj⟩ := hI.1
    have hJ := admissible_zero_sum_erase r hI hq hj
    rw [(hC.2 i I hI).1 hq j hj]
    rw [ih (I.erase j) (Finset.erase_ssubset hj) hJ j]
    unfold minCost
    rw [subDemand_zero_sum_erase r i j I hj hq]
  · apply le_antisymm (native_greatest_solution hA hc hmin hC i I hI)
    apply le_of_not_gt
    exact no_bad_node_of_proper_equality hA hc hmin hpos hC hI hq
      (fun J hJ hJI j => ih J hJI (admissible_subset r hI hJ
        (Finset.ssubset_iff_subset_ne.mp hJI).1) j) i

end SendSplit.DPEquations.SSFresh
end


section

namespace SendSplit.DPEquations

theorem theorem2_dp_equations {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x) :
    IsSolution A c r (minCost A c r) ∧
      (∀ C' : Fin n → Finset (Fin n) → EReal, IsSolution A c r C' →
        ∀ j I, IsAdmissible r I → C' j I ≤ minCost A c r j I) ∧
      ((∀ y, IsSimpleCirculation A y → 0 < flowCost A c y) →
        ∀ C' : Fin n → Finset (Fin n) → EReal, IsSolution A c r C' →
          ∀ j I, IsAdmissible r I → C' j I = minCost A c r j I) := by
  refine ⟨SSFresh.native_minCost_isSolution hA hc hmin, ?_, ?_⟩
  · intro C hC j I hI
    exact SSFresh.native_greatest_solution hA hc hmin hC j I hI
  · intro hpos C hC j I hI
    exact SSFresh.native_unique_solution hA hc hmin hpos hC I hI j

end SendSplit.DPEquations
end


theorem solution {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : SendSplit.DPEquations.IsGraph A) (hc : SendSplit.DPEquations.IsConcaveArcCost A c)
    (hmin : ∃ x, SendSplit.DPEquations.IsMinCostFlow A c r x) :
    SendSplit.DPEquations.IsSolution A c r (SendSplit.DPEquations.minCost A c r) ∧
      (∀ C' : Fin n → Finset (Fin n) → EReal, SendSplit.DPEquations.IsSolution A c r C' →
        ∀ j I, SendSplit.DPEquations.IsAdmissible r I → C' j I ≤ SendSplit.DPEquations.minCost A c r j I) ∧
      ((∀ y, SendSplit.DPEquations.IsSimpleCirculation A y → 0 < SendSplit.DPEquations.flowCost A c y) →
        ∀ C' : Fin n → Finset (Fin n) → EReal, SendSplit.DPEquations.IsSolution A c r C' →
          ∀ j I, SendSplit.DPEquations.IsAdmissible r I → C' j I = SendSplit.DPEquations.minCost A c r j I) := by
  exact SendSplit.DPEquations.theorem2_dp_equations A c r hA hc hmin
