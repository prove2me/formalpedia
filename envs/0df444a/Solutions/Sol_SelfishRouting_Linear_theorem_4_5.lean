-- Prove2me | solution 1 for SelfishRouting.Linear.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T18:46:38.14659+00:00
-- url     : https://prove2.me/submissions/cc45a5eb-0f3e-4075-9a1a-56b1904ad09f

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

set_option autoImplicit false

open SelfishRouting.Bicriteria KellyStochasticNetworks

lemma srb_pair {J R : ℕ} (A : Fin J → Fin R → ℝ) (a : Fin J → ℝ) (z : Fin R → ℝ) :
    ∑ r, (∑ j, a j * A j r) * z r = ∑ j, a j * linkFlow A z j := by
  unfold linkFlow
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => by ring

lemma srb_cost_eq {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ) (x : Fin R → ℝ) :
    cost A ℓ x = ∑ j, ℓ j (linkFlow A x j) * linkFlow A x j := by
  unfold cost pathLatency
  exact srb_pair A (fun j => ℓ j (linkFlow A x j)) x

lemma srb_A_nn {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (j : Fin J) (r : Fin R) : 0 ≤ A j r := by
  rcases hA j r with h | h <;> rw [h] <;> norm_num

lemma srb_lf_nn {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin J) : 0 ≤ linkFlow A x j :=
  Finset.sum_nonneg fun r _ => mul_nonneg (srb_A_nn A hA j r) (hx r)

lemma srb_shift_lf {J R : ℕ} (A : Fin J → Fin R → ℝ) (x : Fin R → ℝ) (r₁ r₂ : Fin R)
    (h : r₁ ≠ r₂) (δ : ℝ) (j : Fin J) :
    linkFlow A (shiftFlow x r₁ r₂ δ) j = linkFlow A x j + δ * (A j r₂ - A j r₁) := by
  unfold linkFlow shiftFlow
  have : ∀ r, A j r * (if r = r₁ then x r - δ else if r = r₂ then x r + δ else x r)
      = A j r * x r + δ * ((if r = r₂ then A j r else 0) - (if r = r₁ then A j r else 0)) := by
    intro r
    by_cases h1 : r = r₁
    · simp [h1, h, h.symm]
      ring
    · by_cases h2 : r = r₂
      · simp [h1, h2, h, h.symm]
        ring
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun r _ => this r, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  simp

lemma srb_wardrop {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) (hx : IsNashFlow A s ℓ rate x) (r₁ r₂ : Fin R) (hs : s r₁ = s r₂)
    (hpos : 0 < x r₁) : pathLatency A ℓ x r₁ ≤ pathLatency A ℓ x r₂ := by
  by_cases h : r₁ = r₂
  · subst h; exact le_rfl
  have hnn : ∀ r, 0 ≤ x r := hx.1.1
  set b := x r₁ with hb
  let g : ℝ → ℝ := fun δ => ∑ j, ℓ j (linkFlow A x j + δ * (A j r₂ - A j r₁)) * A j r₂
  have hsh : ∀ δ, pathLatency A ℓ (shiftFlow x r₁ r₂ δ) r₂ = g δ := by
    intro δ
    unfold pathLatency
    exact Finset.sum_congr rfl fun j _ => by rw [srb_shift_lf A x r₁ r₂ h]
  have hsingle : ∀ j, A j r₁ * x r₁ ≤ linkFlow A x j := by
    intro j
    exact Finset.single_le_sum (f := fun r => A j r * x r)
      (fun r _ => mul_nonneg (srb_A_nn A hA j r) (hnn r)) (Finset.mem_univ r₁)
  have hmaps : ∀ j, ∀ δ ∈ Set.Icc (0:ℝ) b, 0 ≤ linkFlow A x j + δ * (A j r₂ - A j r₁) := by
    intro j δ hδ
    have h1 := hsingle j
    have h2 := srb_lf_nn A hA x hnn j
    have hb' : δ ≤ x r₁ := hδ.2
    rcases hA j r₁ with e1 | e1 <;> rcases hA j r₂ with e2 | e2 <;> rw [e1] at h1 <;>
      rw [e1, e2] <;> nlinarith [hδ.1, hb']
  have hcont : ContinuousOn g (Set.Icc 0 b) := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    refine (hℓcont j).comp (f := fun δ : ℝ => linkFlow A x j + δ * (A j r₂ - A j r₁)) ?_ ?_
    · fun_prop
    · intro δ hδ; exact hmaps j δ hδ
  have hcl : (0:ℝ) ∈ closure (Set.Ioc 0 b) := by
    rw [closure_Ioc hpos.ne]; exact ⟨le_rfl, hpos.le⟩
  have key := ContinuousWithinAt.closure_le (f := fun _ => pathLatency A ℓ x r₁) (g := g)
    (s := Set.Ioc 0 b) hcl continuousWithinAt_const
    ((hcont 0 ⟨le_rfl, hpos.le⟩).mono (fun δ hδ => ⟨hδ.1.le, hδ.2⟩))
    (fun δ hδ => by
      rw [← hsh]; exact hx.2 r₁ r₂ hs h δ hδ.1 hδ.2)
  have g0 : g 0 = pathLatency A ℓ x r₂ := by
    simp only [g, zero_mul, add_zero]; rfl
  simpa [g0] using key

open SelfishRouting.Linear SelfishRouting.Bicriteria KellyStochasticNetworks in
theorem solution {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (x : Fin R → ℝ) (hx : SelfishRouting.Bicriteria.IsNashFlow A s (linLatency a b) rate x)
    (y : Fin R → ℝ) (hy : y ∈ wardropFeasible s rate) :
    SelfishRouting.Bicriteria.cost A (linLatency a b) x ≤ 4 / 3 * SelfishRouting.Bicriteria.cost A (linLatency a b) y := by
  have hℓcont : ∀ j, ContinuousOn (linLatency a b j) (Set.Ici 0) := by
    intro j
    have : linLatency a b j = fun t => a j * t + b j := rfl
    rw [this]
    fun_prop
  have hxfeas := hx.1
  have hxnn : ∀ r, 0 ≤ x r := hxfeas.1
  have hynn : ∀ r, 0 ≤ y r := hy.1
  have hex : ∀ σ, ∃ r0, s r0 = σ ∧ 0 < x r0 := by
    intro σ
    by_contra hcon
    push Not at hcon
    have h0 : ∑ r ∈ Finset.univ.filter (fun r => s r = σ), x r = 0 :=
      Finset.sum_eq_zero fun r hr =>
        le_antisymm (hcon r (Finset.mem_filter.1 hr).2) (hxnn r)
    have h1 := hxfeas.2 σ
    linarith [hrate σ]
  choose r0 hr0s hr0pos using hex
  set L : Fin Sd → ℝ := fun σ => pathLatency A (linLatency a b) x (r0 σ) with hLdef
  have hL_le : ∀ r, L (s r) ≤ pathLatency A (linLatency a b) x r := fun r =>
    srb_wardrop A s (linLatency a b) rate hA hℓcont x hx (r0 (s r)) r (hr0s _) (hr0pos _)
  have hL_eq : ∀ r, 0 < x r → pathLatency A (linLatency a b) x r = L (s r) := fun r hr =>
    le_antisymm (srb_wardrop A s (linLatency a b) rate hA hℓcont x hx r (r0 (s r)) (by rw [hr0s]) hr) (hL_le r)
  have hfib : ∀ (z : Fin R → ℝ) (g : Fin Sd → ℝ), z ∈ wardropFeasible s g →
      ∑ r, L (s r) * z r = ∑ σ, L σ * g σ := by
    intro z g hz
    rw [← Finset.sum_fiberwise Finset.univ s (fun r => L (s r) * z r)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← hz.2 σ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.1 hr).2]
  have hA1 : ∑ r, pathLatency A (linLatency a b) x r * x r = ∑ σ, L σ * rate σ := by
    rw [← hfib x rate hxfeas]
    refine Finset.sum_congr rfl fun r _ => ?_
    rcases (hxnn r).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · rw [hL_eq r h0]
  have hB : ∑ σ, L σ * rate σ ≤ ∑ r, pathLatency A (linLatency a b) x r * y r := by
    rw [← hfib y _ hy]
    exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hL_le r) (hynn r)
  have hcx : cost A (linLatency a b) x = ∑ σ, L σ * rate σ := by
    unfold cost; exact hA1
  have hC : ∑ r, pathLatency A (linLatency a b) x r * y r
      = ∑ j, linLatency a b j (linkFlow A x j) * linkFlow A y j := by
    unfold pathLatency
    exact srb_pair A (fun j => linLatency a b j (linkFlow A x j)) y
  have hxl : ∀ j, 0 ≤ linkFlow A x j := srb_lf_nn A hA x hxnn
  have hedge : ∀ j, linLatency a b j (linkFlow A x j) * linkFlow A y j
      ≤ linLatency a b j (linkFlow A y j) * linkFlow A y j
        + 1 / 4 * (linLatency a b j (linkFlow A x j) * linkFlow A x j) := by
    intro j
    simp only [linLatency]
    nlinarith [mul_nonneg (ha j) (sq_nonneg (linkFlow A y j - linkFlow A x j / 2)),
      mul_nonneg (hb j) (hxl j)]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hedge j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← srb_cost_eq, ← srb_cost_eq] at hsum
  have hxc : cost A (linLatency a b) x ≤ ∑ j, linLatency a b j (linkFlow A x j) * linkFlow A y j := by
    rw [hcx, ← hC]; exact hB
  have hsum2 : ∑ j, linLatency a b j (linkFlow A x j) * linkFlow A x j = cost A (linLatency a b) x :=
    (srb_cost_eq A (linLatency a b) x).symm
  linarith
