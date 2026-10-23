-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P03.feasible_laws_two_point_convex_hull
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:38:10.57198+00:00
-- url     : https://prove2.me/submissions/6c2aff30-1314-4452-9978-55344c2f2bf5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P03

open QAlgorithms.Papers.Independent.Frontier18.P03

namespace X6F03

variable {X : Type*}

theorem mass_eq (p : X →₀ ℝ) (T : Finset X) (h : p.support ⊆ T) :
    p.sum (fun _ w => w) = ∑ x ∈ T, p x :=
  Finsupp.sum_of_support_subset p h _ (fun _ _ => rfl)

theorem cost_eq (c : X → ℝ) (p : X →₀ ℝ) (T : Finset X) (h : p.support ⊆ T) :
    meanCost c p = ∑ x ∈ T, p x * c x :=
  Finsupp.sum_of_support_subset p h _ (fun _ _ => by simp)

theorem supp_add (p q : X →₀ ℝ) (a b : ℝ) (T : Finset X) (hp : p.support ⊆ T)
    (hq : q.support ⊆ T) : (a • p + b • q).support ⊆ T := by
  classical
  intro x hx
  rw [Finsupp.mem_support_iff] at hx
  by_contra hT
  apply hx
  have h1 : p x = 0 := Finsupp.notMem_support_iff.1 (fun h => hT (hp h))
  have h2 : q x = 0 := Finsupp.notMem_support_iff.1 (fun h => hT (hq h))
  simp [h1, h2]

/-- convexity of feasible laws -/
theorem feasible_convex (c : X → ℝ) (gamma : ℝ) : Convex ℝ (feasibleLaws c gamma) := by
  classical
  intro p hp q hq a b ha hb hab
  set T := p.support ∪ q.support
  have hpT : p.support ⊆ T := Finset.subset_union_left
  have hqT : q.support ⊆ T := Finset.subset_union_right
  have hT := supp_add p q a b T hpT hqT
  obtain ⟨⟨hp0, hp1⟩, hpc⟩ := hp
  obtain ⟨⟨hq0, hq1⟩, hqc⟩ := hq
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have := hp0 x; have := hq0 x; positivity
  · rw [mass_eq _ T hT]
    rw [mass_eq _ T hpT] at hp1
    rw [mass_eq _ T hqT] at hq1
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    linarith
  · rw [cost_eq c _ T hT]
    rw [cost_eq c _ T hpT] at hpc
    rw [cost_eq c _ T hqT] at hqc
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left hpc ha
    have h2 := mul_le_mul_of_nonneg_left hqc hb
    have h3 : a * gamma + b * gamma = gamma := by rw [← add_mul, hab, one_mul]
    linarith

/-- the two-point decomposition -/
theorem decomp [DecidableEq X] (c : X → ℝ) (T : Finset X) (m : ℝ) :
    ∀ n : ℕ, ∀ p : X →₀ ℝ, p.support.card = n → IsFiniteLaw p → p.support ⊆ T →
      meanCost c p = m →
      p ∈ convexHull ℝ {q : X →₀ ℝ | IsFiniteLaw q ∧ q.support.card ≤ 2 ∧
        q.support ⊆ T ∧ meanCost c q = m} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hcard hlaw hT hm
  set S := {q : X →₀ ℝ | IsFiniteLaw q ∧ q.support.card ≤ 2 ∧
        q.support ⊆ T ∧ meanCost c q = m}
  obtain ⟨hp0, hp1⟩ := hlaw
  have hmass := hp1
  rw [mass_eq p p.support subset_rfl] at hmass
  have hcost := hm
  rw [cost_eq c p p.support subset_rfl] at hcost
  by_cases hall : ∀ x ∈ p.support, c x = m
  · -- convex combination of point masses
    have hp : p = ∑ x ∈ p.support, p x • Finsupp.single x (1 : ℝ) := by
      conv_lhs => rw [← Finsupp.sum_single p]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finsupp.smul_single_one]
    rw [hp]
    refine (convex_convexHull ℝ S).sum_mem (fun x _ => hp0 x) hmass fun x hx => ?_
    apply subset_convexHull
    refine ⟨⟨fun y => ?_, ?_⟩, ?_, ?_, ?_⟩
    · by_cases h : x = y <;> simp [Finsupp.single_apply, h]
    · simp
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero]; simp
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero]
      exact Finset.singleton_subset_iff.2 (hT hx)
    · simp [meanCost, hall x hx]
  push Not at hall
  -- find points on both sides of m
  have hlo : ∃ x ∈ p.support, c x < m := by
    by_contra h
    push Not at h
    obtain ⟨z, hz, hcz⟩ := hall
    have hgt : m < c z := lt_of_le_of_ne (h z hz) (Ne.symm hcz)
    have hpz : 0 < p z := lt_of_le_of_ne (hp0 z) (Ne.symm (Finsupp.mem_support_iff.1 hz))
    have : ∑ x ∈ p.support, p x * m < ∑ x ∈ p.support, p x * c x := by
      apply Finset.sum_lt_sum
      · intro x hx; exact mul_le_mul_of_nonneg_left (h x hx) (hp0 x)
      · exact ⟨z, hz, mul_lt_mul_of_pos_left hgt hpz⟩
    rw [← Finset.sum_mul, hmass, hcost] at this
    linarith
  have hhi : ∃ y ∈ p.support, m < c y := by
    by_contra h
    push Not at h
    obtain ⟨z, hz, hcz⟩ := hall
    have hlt : c z < m := lt_of_le_of_ne (h z hz) hcz
    have hpz : 0 < p z := lt_of_le_of_ne (hp0 z) (Ne.symm (Finsupp.mem_support_iff.1 hz))
    have : ∑ x ∈ p.support, p x * c x < ∑ x ∈ p.support, p x * m := by
      apply Finset.sum_lt_sum
      · intro x hx; exact mul_le_mul_of_nonneg_left (h x hx) (hp0 x)
      · exact ⟨z, hz, mul_lt_mul_of_pos_left hlt hpz⟩
    rw [← Finset.sum_mul, hmass, hcost] at this
    linarith
  obtain ⟨x, hx, hcx⟩ := hlo
  obtain ⟨y, hy, hcy⟩ := hhi
  have hxy : x ≠ y := by rintro rfl; linarith
  have hpx : 0 < p x := lt_of_le_of_ne (hp0 x) (Ne.symm (Finsupp.mem_support_iff.1 hx))
  have hpy : 0 < p y := lt_of_le_of_ne (hp0 y) (Ne.symm (Finsupp.mem_support_iff.1 hy))
  set lam := (c y - m) / (c y - c x)
  have hlam0 : 0 < lam := div_pos (by linarith) (by linarith)
  have hlam1 : lam < 1 := by rw [div_lt_one (by linarith)]; linarith
  set q : X →₀ ℝ := Finsupp.single x lam + Finsupp.single y (1 - lam)
  have hqx : q x = lam := by simp [q, Finsupp.single_apply, hxy, Ne.symm hxy]
  have hqy : q y = 1 - lam := by simp [q, Finsupp.single_apply, hxy, Ne.symm hxy]
  have hqo : ∀ z, z ≠ x → z ≠ y → q z = 0 := by
    intro z h1 h2; simp [q, Finsupp.single_apply, Ne.symm h1, Ne.symm h2]
  have hqsupp : q.support ⊆ {x, y} := by
    intro z hz
    rw [Finsupp.mem_support_iff] at hz
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact hz (hqo z h.1 h.2)
  have hxyT : ({x, y} : Finset X) ⊆ p.support := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hqsum : ∀ f : X → ℝ, ∑ z ∈ p.support, q z * f z = lam * f x + (1 - lam) * f y := by
    intro f
    rw [← Finset.sum_subset hxyT (fun z _ hz => by
      rw [hqo z (fun h => hz (by simp [h])) (fun h => hz (by simp [h])), zero_mul])]
    rw [Finset.sum_pair hxy, hqx, hqy]
  have hqlaw : IsFiniteLaw q := by
    refine ⟨fun z => ?_, ?_⟩
    · by_cases h1 : z = x
      · rw [h1, hqx]; exact hlam0.le
      by_cases h2 : z = y
      · rw [h2, hqy]; linarith
      rw [hqo z h1 h2]
    · rw [mass_eq q p.support (hqsupp.trans hxyT)]
      have := hqsum (fun _ => 1); simp only [mul_one] at this; rw [this]; ring
  have hqm : meanCost c q = m := by
    rw [cost_eq c q p.support (hqsupp.trans hxyT), hqsum c]
    simp only [lam]
    have hne : c y - c x ≠ 0 := by linarith
    field_simp
    ring
  have hqS : q ∈ S := by
    refine ⟨hqlaw, (Finset.card_le_card hqsupp).trans Finset.card_le_two, ?_, hqm⟩
    exact (hqsupp.trans hxyT).trans hT
  -- the step size
  set θ := min (p x / lam) (p y / (1 - lam))
  have hθ0 : 0 < θ := lt_min (div_pos hpx hlam0) (div_pos hpy (by linarith))
  have hle : ∀ z, θ * q z ≤ p z := by
    intro z
    by_cases h1 : z = x
    · subst h1; rw [hqx]
      have := min_le_left (p z / lam) (p y / (1 - lam))
      rw [le_div_iff₀ hlam0] at this; linarith
    by_cases h2 : z = y
    · subst h2; rw [hqy]
      have := min_le_right (p x / lam) (p z / (1 - lam))
      rw [le_div_iff₀ (by linarith)] at this; linarith
    rw [hqo z h1 h2, mul_zero]; exact hp0 z
  -- some point is killed
  have hkill : ∃ w ∈ ({x, y} : Finset X), θ * q w = p w := by
    rcases min_choice (p x / lam) (p y / (1 - lam)) with h | h
    · refine ⟨x, by simp, ?_⟩
      rw [hqx, show θ = p x / lam from h]; field_simp
    · refine ⟨y, by simp, ?_⟩
      rw [hqy, show θ = p y / (1 - lam) from h]
      have : (1 - lam) ≠ 0 := by linarith
      field_simp
  obtain ⟨w, hw, hθw⟩ := hkill
  have hθ1 : θ ≤ 1 := by
    have h1 : ∑ z ∈ p.support, θ * q z ≤ ∑ z ∈ p.support, p z := Finset.sum_le_sum fun z _ => hle z
    rw [← Finset.mul_sum, hmass] at h1
    have := hqsum (fun _ => 1); simp only [mul_one] at this
    rw [this] at h1; linarith
  rcases hθ1.lt_or_eq with hθ1 | hθ1
  · set r : X →₀ ℝ := (1 - θ)⁻¹ • (p - θ • q)
    have hr : p = θ • q + (1 - θ) • r := by
      ext z
      simp only [r, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]
      have : (1 - θ) ≠ 0 := by linarith
      field_simp
      ring
    have hrsupp : r.support ⊆ p.support.erase w := by
      intro z hz
      rw [Finsupp.mem_support_iff] at hz
      simp only [r, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul] at hz
      rw [Finset.mem_erase]
      constructor
      · rintro rfl; apply hz; rw [hθw, sub_self, mul_zero]
      · rw [Finsupp.mem_support_iff]; intro h0; apply hz
        have := hle z
        have hq0 : q z = 0 := by
          by_contra hq
          have : 0 < q z := by
            have h1 := hqlaw.1 z
            exact lt_of_le_of_ne h1 (Ne.symm hq)
          nlinarith
        rw [h0, hq0]; ring
    have hrT : r.support ⊆ p.support := hrsupp.trans (Finset.erase_subset _ _)
    have hwsupp : w ∈ p.support := hxyT hw
    have hcard : r.support.card < n := by
      rw [← hcard]
      exact lt_of_le_of_lt (Finset.card_le_card hrsupp) (Finset.card_erase_lt_of_mem hwsupp)
    have hrlaw : IsFiniteLaw r := by
      refine ⟨fun z => ?_, ?_⟩
      · simp only [r, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]
        have := hle z
        have : 0 < (1 - θ)⁻¹ := inv_pos.2 (by linarith)
        nlinarith
      · rw [mass_eq r p.support hrT]
        simp only [r, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, ← Finset.mul_sum,
          Finset.sum_sub_distrib, hmass]
        have := hqsum (fun _ => 1); simp only [mul_one] at this
        rw [this]
        have : (1 - θ) ≠ 0 := by linarith
        field_simp; ring
    have hrm : meanCost c r = m := by
      rw [cost_eq c r p.support hrT]
      simp only [r, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, sub_mul, mul_assoc,
        ← Finset.mul_sum, Finset.sum_sub_distrib, hcost]
      rw [hqsum c]
      have h2 : lam * c x + (1 - lam) * c y = m := by
        rw [cost_eq c q p.support (hqsupp.trans hxyT), hqsum c] at hqm; exact hqm
      rw [h2]
      have : (1 - θ) ≠ 0 := by linarith
      field_simp
    have hrS := ih _ hcard r rfl hrlaw (hrT.trans hT) hrm
    rw [hr]
    exact (convex_convexHull ℝ S) (subset_convexHull ℝ S hqS) hrS hθ0.le (by linarith)
      (by ring)
  · -- θ = 1 : p = q
    have hpq : p = q := by
      have hdiff : ∀ z ∈ p.support, p z - q z = 0 := by
        have hsum : ∑ z ∈ p.support, (p z - q z) = 0 := by
          rw [Finset.sum_sub_distrib, hmass]
          have := hqsum (fun _ => 1); simp only [mul_one] at this; rw [this]; ring
        have hnn : ∀ z ∈ p.support, 0 ≤ p z - q z := fun z _ => by
          have := hle z; rw [hθ1] at this; linarith
        exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
      ext z
      by_cases hz : z ∈ p.support
      · linarith [hdiff z hz]
      · have h1 : p z = 0 := Finsupp.notMem_support_iff.1 hz
        have := hle z; rw [hθ1, one_mul, h1] at this
        have h2 := hqlaw.1 z
        rw [h1]; linarith
    rw [hpq]; exact subset_convexHull ℝ S hqS

end X6F03

open X6F03 in
theorem solution
    {X : Type*} (c : X → ℝ) (gamma : ℝ) :
    feasibleLaws c gamma =
      convexHull ℝ {p : X →₀ ℝ | p ∈ feasibleLaws c gamma ∧ p.support.card ≤ 2} ∧
    ∀ p ∈ feasibleLaws c gamma,
      p ∈ convexHull ℝ {q : X →₀ ℝ |
        q ∈ feasibleLaws c gamma ∧ q.support.card ≤ 2 ∧
        q.support ⊆ p.support ∧ meanCost c q = meanCost c p} := by
  classical
  have h2 : ∀ p ∈ feasibleLaws c gamma,
      p ∈ convexHull ℝ {q : X →₀ ℝ |
        q ∈ feasibleLaws c gamma ∧ q.support.card ≤ 2 ∧
        q.support ⊆ p.support ∧ meanCost c q = meanCost c p} := by
    intro p hp
    have := decomp c p.support (meanCost c p) _ p rfl hp.1 subset_rfl rfl
    refine convexHull_mono ?_ this
    rintro q ⟨hq1, hq2, hq3, hq4⟩
    exact ⟨⟨hq1, hq4 ▸ hp.2⟩, hq2, hq3, hq4⟩
  refine ⟨Set.Subset.antisymm ?_ ?_, h2⟩
  · intro p hp
    refine convexHull_mono ?_ (h2 p hp)
    rintro q ⟨hq1, hq2, -, -⟩
    exact ⟨hq1, hq2⟩
  · exact convexHull_min (fun q hq => hq.1) (feasible_convex c gamma)
