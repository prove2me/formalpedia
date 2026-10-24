-- Prove2me | solution 1 for SensitivityPoA.Lipschitz.poa_eq_one_of_const
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T08:39:17.24017+00:00
-- url     : https://prove2.me/submissions/607993b9-8acd-4b3f-8980-ee599fbdff39

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Lipschitz_Setting
import Definitions.Def_SensitivityPoA_Lipschitz_SpecialCosts

namespace PoA3
open SensitivityPoA.Lipschitz KellyStochasticNetworks

variable {N : Network}

lemma A01 (hN : N.Standing) (j : Fin N.J) (r : Fin N.R) : 0 ≤ N.A j r ∧ N.A j r ≤ 1 := by
  rcases hN.1 j r with h | h <;> rw [h] <;> norm_num

lemma sum_fiber {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsFlow Γ f) (φ : Fin N.Sd → ℝ) :
    ∑ r, f r * φ (N.s r) = ∑ k, Γ.d k * φ k := by
  rw [← Finset.sum_fiberwise Finset.univ N.s (fun r => f r * φ (N.s r))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hf.2 k, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [Finset.mem_filter] at hr
  rw [hr.2]

lemma sum_flow {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsFlow Γ f) :
    ∑ r, f r = totalDemand Γ.d := by
  have := sum_fiber hf (fun _ => 1)
  simpa [totalDemand] using this

lemma linkFlow_nonneg (hN : N.Standing) {f : Fin N.R → ℝ} (hf : ∀ r, 0 ≤ f r) (j : Fin N.J) :
    0 ≤ linkFlow N.A f j :=
  Finset.sum_nonneg fun r _ => mul_nonneg (A01 hN j r).1 (hf r)

lemma linkFlow_le_sum (hN : N.Standing) {f : Fin N.R → ℝ} (hf : ∀ r, 0 ≤ f r) (j : Fin N.J) :
    linkFlow N.A f j ≤ ∑ r, f r :=
  Finset.sum_le_sum fun r _ => by
    have := A01 hN j r
    nlinarith [hf r]

lemma linkFlow_le (hN : N.Standing) {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsFlow Γ f)
    (j : Fin N.J) : linkFlow N.A f j ≤ totalDemand Γ.d :=
  (sum_flow hf) ▸ linkFlow_le_sum hN hf.1 j

lemma linkFlow_add (f g : Fin N.R → ℝ) (j : Fin N.J) :
    linkFlow N.A (f + g) j = linkFlow N.A f j + linkFlow N.A g j := by
  simp [linkFlow, mul_add, Finset.sum_add_distrib]

lemma linkFlow_sub (f g : Fin N.R → ℝ) (j : Fin N.J) :
    linkFlow N.A (f - g) j = linkFlow N.A f j - linkFlow N.A g j := by
  simp [linkFlow, mul_sub, Finset.sum_sub_distrib]

lemma abs_linkFlow_sub_le (hN : N.Standing) (f g : Fin N.R → ℝ) (j : Fin N.J) :
    |linkFlow N.A f j - linkFlow N.A g j| ≤ ∑ r, |f r - g r| := by
  rw [← linkFlow_sub]
  unfold linkFlow
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [abs_mul, Pi.sub_apply]
  have := A01 hN j r
  rw [abs_of_nonneg this.1]
  nlinarith [abs_nonneg (f r - g r)]

lemma cost_eq_path (Γ : Game N) (f : Fin N.R → ℝ) :
    cost Γ f = ∑ r, f r * pathCost Γ f r := by
  unfold cost pathCost linkFlow
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma sum_tau_mul_linkFlow (Γ : Game N) (f h : Fin N.R → ℝ) :
    ∑ j, Γ.τ j (linkFlow N.A f j) * linkFlow N.A h j = ∑ r, h r * pathCost Γ f r := by
  unfold pathCost linkFlow
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Each O/D pair has a path. -/
lemma exists_path (hN : N.Standing) (k : Fin N.Sd) : ∃ r, N.s r = k := by
  have h := hN.2.2.2.2 k
  have : (Finset.univ.filter fun r => N.s r = k).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨r, hr⟩ := this
  exact ⟨r, (Finset.mem_filter.mp hr).2⟩

lemma fiber_nonempty (hN : N.Standing) (k : Fin N.Sd) :
    (Finset.univ.filter fun r => N.s r = k).Nonempty := by
  obtain ⟨r, hr⟩ := exists_path hN k
  exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩

/-- Minimal path cost of pair `k` for path costs `c`. -/
noncomputable def minCost (hN : N.Standing) (c : Fin N.R → ℝ) (k : Fin N.Sd) : ℝ :=
  (Finset.univ.filter fun r => N.s r = k).inf' (fiber_nonempty hN k) c

lemma minCost_le (hN : N.Standing) (c : Fin N.R → ℝ) (r : Fin N.R) :
    minCost hN c (N.s r) ≤ c r := by
  unfold minCost
  have hr : r ∈ Finset.univ.filter fun r' => N.s r' = N.s r :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩
  exact Finset.inf'_le c hr

lemma exists_minCost (hN : N.Standing) (c : Fin N.R → ℝ) (k : Fin N.Sd) :
    ∃ r, N.s r = k ∧ c r = minCost hN c k := by
  obtain ⟨r, hr, h⟩ := Finset.exists_mem_eq_inf' (fiber_nonempty hN k) c
  exact ⟨r, (Finset.mem_filter.mp hr).2, h.symm⟩

lemma le_minCost (hN : N.Standing) (c : Fin N.R → ℝ) (k : Fin N.Sd) (x : ℝ)
    (h : ∀ r, N.s r = k → x ≤ c r) : x ≤ minCost hN c k :=
  (Finset.le_inf'_iff _ _).mpr fun r hr => h r (Finset.mem_filter.mp hr).2

/-- On a WE flow, every used path has the minimal cost. -/
lemma WE_used (hN : N.Standing) {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsWE Γ f) (r : Fin N.R)
    (hr : 0 < f r) : pathCost Γ f r = minCost hN (pathCost Γ f) (N.s r) :=
  le_antisymm (le_minCost hN _ _ _ fun r' hr' => hf.2 r r' hr' hr) (minCost_le hN _ r)

lemma WE_cost_eq (hN : N.Standing) {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsWE Γ f) :
    cost Γ f = ∑ k, Γ.d k * minCost hN (pathCost Γ f) k := by
  rw [cost_eq_path, ← sum_fiber hf.1]
  refine Finset.sum_congr rfl fun r _ => ?_
  rcases (hf.1.1 r).lt_or_eq with h | h
  · rw [WE_used hN hf r h]
  · rw [← h]; ring

/-- Variational inequality for WE flows. -/
lemma WE_VI (hN : N.Standing) {Γ : Game N} {f h : Fin N.R → ℝ} (hf : IsWE Γ f)
    (hh : IsFlow Γ h) :
    0 ≤ ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A h j - linkFlow N.A f j) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sum_tau_mul_linkFlow, sum_tau_mul_linkFlow, ← cost_eq_path, WE_cost_eq hN hf,
    ← sum_fiber hh]
  rw [sub_nonneg]
  exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (minCost_le hN _ r) (hh.1 r)


/-! ### Flows exist; SO/WE cost bounds -/

lemma exists_flow (hN : N.Standing) (Γ : Game N) (hd : ∀ k, 0 ≤ Γ.d k) :
    ∃ f, IsFlow Γ f := by
  choose q hq using exists_path hN
  refine ⟨fun r => if q (N.s r) = r then Γ.d (N.s r) else 0, fun r => ?_, fun k => ?_⟩
  · dsimp only; split_ifs <;> simp [hd]
  · have : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k),
        (if q (N.s r) = r then Γ.d (N.s r) else 0) = if q k = r then Γ.d k else 0 := by
      intro r hr; rw [(Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [hq k]

lemma cost_nonneg (hN : N.Standing) {Γ : Game N} (hG : Γ.IsGeneralized) {f : Fin N.R → ℝ}
    (hf : IsFlow Γ f) : 0 ≤ cost Γ f :=
  Finset.sum_nonneg fun j _ => mul_nonneg (linkFlow_nonneg hN hf.1 j)
    ((hG.1 j).2.2 _ (linkFlow_nonneg hN hf.1 j))

lemma cost_le_bound (hN : N.Standing) {Γ : Game N} (hG : Γ.IsGeneralized) {f : Fin N.R → ℝ}
    (hf : IsFlow Γ f) :
    cost Γ f ≤ ∑ j, totalDemand Γ.d * Γ.τ j (totalDemand Γ.d) := by
  refine Finset.sum_le_sum fun j _ => ?_
  have h0 := linkFlow_nonneg hN hf.1 j
  have h1 := linkFlow_le hN hf j
  have hτ0 := (hG.1 j).2.2 _ h0
  have hmono := (hG.1 j).2.1 (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr (h0.trans h1)) h1
  exact mul_le_mul h1 hmono hτ0 (h0.trans h1)

lemma SOCost_le (hN : N.Standing) {Γ : Game N} (hG : Γ.IsGeneralized) {f : Fin N.R → ℝ}
    (hf : IsFlow Γ f) : SOCost Γ ≤ cost Γ f := by
  refine csInf_le ⟨0, ?_⟩ ⟨f, hf, rfl⟩
  rintro _ ⟨g, hg, rfl⟩; exact cost_nonneg hN hG hg

lemma le_SOCost (hN : N.Standing) {Γ : Game N} (hd : ∀ k, 0 ≤ Γ.d k) {c : ℝ}
    (h : ∀ f, IsFlow Γ f → c ≤ cost Γ f) : c ≤ SOCost Γ := by
  obtain ⟨f, hf⟩ := exists_flow hN Γ hd
  refine le_csInf ⟨_, f, hf, rfl⟩ ?_
  rintro _ ⟨g, hg, rfl⟩; exact h g hg

lemma SOCost_nonneg (hN : N.Standing) {Γ : Game N} (hG : Γ.IsGeneralized) : 0 ≤ SOCost Γ :=
  le_SOCost hN hG.2 fun _ hf => cost_nonneg hN hG hf

lemma le_WECost (hN : N.Standing) {Γ : Game N} (hG : Γ.IsGeneralized) {f : Fin N.R → ℝ}
    (hf : IsWE Γ f) : cost Γ f ≤ WECost Γ := by
  refine le_csSup ⟨∑ j, totalDemand Γ.d * Γ.τ j (totalDemand Γ.d), ?_⟩ ⟨f, hf, rfl⟩
  rintro _ ⟨g, hg, rfl⟩; exact cost_le_bound hN hG hg.1

lemma WECost_le {Γ : Game N} (hex : ∃ f, IsWE Γ f) {c : ℝ}
    (h : ∀ f, IsWE Γ f → cost Γ f ≤ c) : WECost Γ ≤ c := by
  obtain ⟨f, hf⟩ := hex
  refine csSup_le ⟨_, f, hf, rfl⟩ ?_
  rintro _ ⟨g, hg, rfl⟩; exact h g hg

/-! ### Existence of a WE (Beckmann potential) -/

noncomputable def pot (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  ∑ j, ∫ u in (0:ℝ)..(linkFlow N.A f j), Γ.τ j (max u 0)

lemma cont_ext {Γ : Game N} (hG : Γ.IsGeneralized) (j : Fin N.J) :
    Continuous fun u : ℝ => Γ.τ j (max u 0) :=
  (hG.1 j).1.comp_continuous (continuous_id.max continuous_const)
    fun u => Set.mem_Ici.mpr (le_max_right u 0)

lemma continuous_linkFlow (j : Fin N.J) : Continuous fun f : Fin N.R → ℝ => linkFlow N.A f j :=
  continuous_finsetSum _ fun r _ => continuous_const.mul (continuous_apply r)

lemma continuous_pot {Γ : Game N} (hG : Γ.IsGeneralized) : Continuous (pot Γ) := by
  unfold pot
  refine continuous_finsetSum _ fun j _ => ?_
  have h := intervalIntegral.continuous_primitive
    (μ := MeasureTheory.volume) (fun a b => (cont_ext hG j).intervalIntegrable a b) (0:ℝ)
  exact h.comp (continuous_linkFlow j)

lemma isCompact_flows (hN : N.Standing) (Γ : Game N) : IsCompact {f | IsFlow Γ f} := by
  have hcl : IsClosed {f | IsFlow Γ f} := by
    have : {f | IsFlow Γ f} = (⋂ r, {f : Fin N.R → ℝ | 0 ≤ f r}) ∩
        ⋂ k, {f : Fin N.R → ℝ | (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r) = Γ.d k} := by
      ext f; simp [IsFlow, wardropFeasible]
    rw [this]
    refine (isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)).inter
      (isClosed_iInter fun k => isClosed_eq ?_ continuous_const)
    exact continuous_finsetSum _ fun r _ => continuous_apply r
  refine (isCompact_Icc (a := (0 : Fin N.R → ℝ)) (b := fun _ => totalDemand Γ.d)).of_isClosed_subset
    hcl fun f hf => ⟨fun r => hf.1 r, fun r => ?_⟩
  have := sum_flow hf
  rw [← this]
  exact Finset.single_le_sum (fun r _ => hf.1 r) (Finset.mem_univ r)

lemma exists_WE (hN : N.Standing) {Γ : Game N} (hG : Γ.IsGeneralized) : ∃ f, IsWE Γ f := by
  obtain ⟨f0, hf0⟩ := exists_flow hN Γ hG.2
  obtain ⟨f, hf, hmin⟩ := (isCompact_flows hN Γ).exists_isMinOn ⟨f0, hf0⟩
    (continuous_pot hG).continuousOn
  refine ⟨f, hf, fun r r' hs hr => ?_⟩
  by_contra hlt
  push Not at hlt
  have hne : r ≠ r' := by rintro rfl; exact lt_irrefl _ hlt
  -- perturbation
  set e : Fin N.R → ℝ := fun x => (if x = r' then 1 else 0) - (if x = r then 1 else 0) with he
  set ft : ℝ → Fin N.R → ℝ := fun t => f + t • e with hft
  have hlink : ∀ t j, linkFlow N.A (ft t) j = linkFlow N.A f j + t * (N.A j r' - N.A j r) := by
    intro t j
    simp only [hft, linkFlow_add]
    congr 1
    simp [linkFlow, he, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  have hflow : ∀ t, 0 ≤ t → t ≤ f r → IsFlow Γ (ft t) := by
    intro t ht0 ht1
    refine ⟨fun x => ?_, fun k => ?_⟩
    · simp only [hft, he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h1 : x = r
      · subst h1; simp [hne]; linarith
      · by_cases h2 : x = r'
        · subst h2; simp [h1]; linarith [hf.1 x]
        · simp [h1, h2]; exact hf.1 x
    · simp only [hft, he, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
      rw [hf.2 k]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp [hs]
  -- derivative of the potential along the perturbation
  have hderiv : HasDerivAt (fun t => pot Γ (ft t))
      (∑ j, Γ.τ j (max (linkFlow N.A f j) 0) * (N.A j r' - N.A j r)) 0 := by
    have : (fun t => pot Γ (ft t)) = fun t => ∑ j, ∫ u in (0:ℝ)..(linkFlow N.A f j +
        t * (N.A j r' - N.A j r)), Γ.τ j (max u 0) := by
      funext t; unfold pot; simp only [hlink]
    rw [this]
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := ((cont_ext hG j).integral_hasStrictDerivAt 0
      (linkFlow N.A f j)).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => linkFlow N.A f j + t * (N.A j r' - N.A j r))
        (N.A j r' - N.A j r) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (N.A j r' - N.A j r)).const_add
        (linkFlow N.A f j)
    exact h1.comp_of_eq (0:ℝ) h2 (by simp)
  have hval : (∑ j, Γ.τ j (max (linkFlow N.A f j) 0) * (N.A j r' - N.A j r)) =
      pathCost Γ f r' - pathCost Γ f r := by
    unfold pathCost
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [max_eq_left (linkFlow_nonneg hN hf.1 j)]; ring
  rw [hval] at hderiv
  have hneg : pathCost Γ f r' - pathCost Γ f r < 0 := by unfold pathCost; linarith
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hderiv).mono_left
    (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => ne_of_gt hx))
  have hev1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), slope (fun t => pot Γ (ft t)) 0 t < 0 :=
    hslope (Iio_mem_nhds hneg)
  have hev2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < f r :=
    nhdsWithin_le_nhds (Iio_mem_nhds hr)
  have hev3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  have hft0 : ft 0 = f := by simp [hft]
  rw [slope_def_field, hft0] at h1
  have hlt2 : pot Γ (ft t) < pot Γ f := by
    have : (pot Γ (ft t) - pot Γ f) < 0 := by
      have h3' : 0 < t - 0 := by linarith
      exact (div_neg_iff.mp h1).elim (fun h => absurd h.1 (by linarith [h.2])) (fun h => h.1)
    linarith
  exact absurd (hmin (hflow t h3.le h2.le)) (not_le.mpr hlt2)


/-! ### Facts about the distance -/

lemma dist_d (Γ Γ' : Game N) (k : Fin N.Sd) : |Γ.d k - Γ'.d k| ≤ gameDist Γ Γ' := by
  unfold gameDist
  refine le_trans ?_ (le_max_left _ _)
  have := norm_le_pi_norm (Γ.d - Γ'.d) k
  simpa [Real.norm_eq_abs] using this

lemma dist_end (Γ Γ' : Game N) (j : Fin N.J) :
    |Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)| ≤ gameDist Γ Γ' := by
  unfold gameDist
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_right _ _)
  have := norm_le_pi_norm (fun j => Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)) j
  simpa [Real.norm_eq_abs] using this

lemma dist_tau {Γ Γ' : Game N} (hG : Γ.IsGeneralized) (hG' : Γ'.IsGeneralized) (j : Fin N.J)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ totalDemand Γ.d) (hx2 : x ≤ totalDemand Γ'.d) :
    |Γ.τ j x - Γ'.τ j x| ≤ gameDist Γ Γ' := by
  unfold gameDist
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_left _ _)
  refine le_csSup ⟨∑ i, (Γ.τ i (totalDemand Γ.d) + Γ'.τ i (totalDemand Γ'.d)), ?_⟩
    ⟨(j, x), ⟨Set.mem_univ _, hx0, le_min hx1 hx2⟩, rfl⟩
  rintro _ ⟨⟨i, y⟩, ⟨-, hy0, hy1⟩, rfl⟩
  have hy1' := le_min_iff.mp hy1
  have a1 := (hG.1 i).2.2 y hy0
  have a2 := (hG'.1 i).2.2 y hy0
  have a3 := (hG.1 i).2.1 (Set.mem_Ici.mpr hy0) (Set.mem_Ici.mpr (hy0.trans hy1'.1)) hy1'.1
  have a4 := (hG'.1 i).2.1 (Set.mem_Ici.mpr hy0) (Set.mem_Ici.mpr (hy0.trans hy1'.2)) hy1'.2
  have hle : |Γ.τ i y - Γ'.τ i y| ≤ Γ.τ i (totalDemand Γ.d) + Γ'.τ i (totalDemand Γ'.d) := by
    rw [abs_le]; constructor <;> linarith
  refine hle.trans (Finset.single_le_sum (f := fun i => Γ.τ i (totalDemand Γ.d) +
    Γ'.τ i (totalDemand Γ'.d)) (fun i' _ => ?_) (Finset.mem_univ i))
  have b1 := (hG.1 i').2.2 _ (hy0.trans hy1'.1)
  have b2 := (hG'.1 i').2.2 _ (hy0.trans hy1'.2)
  linarith

lemma dist_nonneg (Γ Γ' : Game N) (hSd : 0 < N.Sd) : 0 ≤ gameDist Γ Γ' :=
  (abs_nonneg _).trans (dist_d Γ Γ' ⟨0, hSd⟩)

lemma dist_T (Γ Γ' : Game N) :
    |totalDemand Γ.d - totalDemand Γ'.d| ≤ N.Sd * gameDist Γ Γ' := by
  unfold totalDemand
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_sum (s := Finset.univ) fun k _ => dist_d Γ Γ' k
  simpa using this

/-- Comparison of `σ` with `τ` clamped to `[0, T]`. -/
lemma dist_clamp {Γ Γ' : Game N} (hG : Γ.IsGeneralized) (hG' : Γ'.IsGeneralized) (j : Fin N.J)
    (hT : 0 ≤ totalDemand Γ.d) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ totalDemand Γ'.d) :
    |Γ'.τ j x - Γ.τ j (min x (totalDemand Γ.d))| ≤ gameDist Γ Γ' := by
  rcases le_or_gt x (totalDemand Γ.d) with h | h
  · rw [min_eq_left h, abs_sub_comm]; exact dist_tau hG hG' j hx0 h hx1
  · rw [min_eq_right h.le]
    have e1 := dist_tau hG hG' j hT le_rfl (h.le.trans hx1)
    have e2 := dist_end Γ Γ' j
    have m1 := (hG'.1 j).2.1 (Set.mem_Ici.mpr hT) (Set.mem_Ici.mpr hx0) h.le
    have m2 := (hG'.1 j).2.1 (Set.mem_Ici.mpr hx0) (Set.mem_Ici.mpr (hx0.trans hx1)) hx1
    rw [abs_le] at e1 e2 ⊢
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]


/-! ### Games with near-constant costs -/

def constPath (c : Fin N.J → ℝ) (r : Fin N.R) : ℝ := ∑ j, c j * N.A j r

lemma pathCost_near (hN : N.Standing) {Γ : Game N} (c : Fin N.J → ℝ) {η : ℝ}
    (hc : ∀ j x, 0 ≤ x → x ≤ totalDemand Γ.d → |Γ.τ j x - c j| ≤ η)
    {f : Fin N.R → ℝ} (hf : IsFlow Γ f) (r : Fin N.R) :
    |pathCost Γ f r - constPath c r| ≤ N.J * η := by
  unfold pathCost constPath
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ j ∈ (Finset.univ : Finset (Fin N.J)),
      |Γ.τ j (linkFlow N.A f j) * N.A j r - c j * N.A j r| ≤ η := by
    intro j _
    rw [← sub_mul, abs_mul, abs_of_nonneg (A01 hN j r).1]
    have h1 := hc j _ (linkFlow_nonneg hN hf.1 j) (linkFlow_le hN hf j)
    have h2 := A01 hN j r
    nlinarith [abs_nonneg (Γ.τ j (linkFlow N.A f j) - c j)]
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma near_const_lower (hN : N.Standing) {Γ : Game N} (c : Fin N.J → ℝ) {η : ℝ}
    (hc : ∀ j x, 0 ≤ x → x ≤ totalDemand Γ.d → |Γ.τ j x - c j| ≤ η)
    {f : Fin N.R → ℝ} (hf : IsFlow Γ f) :
    (∑ k, Γ.d k * minCost hN (constPath c) k) - N.J * η * totalDemand Γ.d ≤ cost Γ f := by
  have e1 := sum_fiber hf (fun k => minCost hN (constPath c) k - N.J * η)
  have e2 := sum_flow hf
  have : (∑ k, Γ.d k * minCost hN (constPath c) k) - N.J * η * totalDemand Γ.d =
      ∑ r, f r * (minCost hN (constPath c) (N.s r) - N.J * η) := by
    rw [e1]; unfold totalDemand
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, cost_eq_path]
  refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (hf.1 r)
  have h1 := pathCost_near hN c hc hf r
  have h2 := minCost_le hN (constPath c) r
  rw [abs_le] at h1; linarith [h1.1]

lemma near_const_upper (hN : N.Standing) {Γ : Game N} (c : Fin N.J → ℝ) {η : ℝ}
    (hc : ∀ j x, 0 ≤ x → x ≤ totalDemand Γ.d → |Γ.τ j x - c j| ≤ η)
    {g : Fin N.R → ℝ} (hg : IsWE Γ g) :
    cost Γ g ≤ (∑ k, Γ.d k * minCost hN (constPath c) k) + N.J * η * totalDemand Γ.d := by
  rw [WE_cost_eq hN hg]
  have : (∑ k, Γ.d k * minCost hN (constPath c) k) + N.J * η * totalDemand Γ.d =
      ∑ k, Γ.d k * (minCost hN (constPath c) k + N.J * η) := by
    unfold totalDemand
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hg.1.1 |> fun _ => ?_)
  · obtain ⟨q, hq, hqe⟩ := exists_minCost hN (constPath c) k
    have h1 := pathCost_near hN c hc hg.1 q
    have h2 := minCost_le hN (pathCost Γ g) q
    rw [hq] at h2
    rw [abs_le] at h1; linarith [h1.2]
  · -- demand nonneg from the flow
    have := hg.1.2 k
    rw [← this]
    exact Finset.sum_nonneg fun r _ => hg.1.1 r

lemma constPath_pos (hN : N.Standing) (c : Fin N.J → ℝ) (hc : ∀ j, 0 < c j) (r : Fin N.R) :
    0 < constPath c r := by
  obtain ⟨j, hj⟩ := hN.2.1 r
  unfold constPath
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => c j * N.A j r)
    (fun i _ => mul_nonneg (hc i).le (A01 hN i r).1) (Finset.mem_univ j))
  simp [hj, hc j]

lemma minCost_pos (hN : N.Standing) (c : Fin N.R → ℝ) (hc : ∀ r, 0 < c r) (k : Fin N.Sd) :
    0 < minCost hN c k := by
  obtain ⟨r, -, h⟩ := exists_minCost hN c k
  rw [← h]; exact hc r

lemma exists_d_pos {Γ : Game N} (hT : 0 < totalDemand Γ.d) : ∃ k, 0 < Γ.d k := by
  by_contra h
  push Not at h
  have : totalDemand Γ.d ≤ 0 := Finset.sum_nonpos fun k _ => h k
  linarith

lemma weighted_pos {Γ : Game N} (hd : ∀ k, 0 ≤ Γ.d k) (hT : 0 < totalDemand Γ.d)
    (φ : Fin N.Sd → ℝ) (hφ : ∀ k, 0 < φ k) : 0 < ∑ k, Γ.d k * φ k := by
  obtain ⟨k, hk⟩ := exists_d_pos hT
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hd i) (hφ i).le)
    ⟨k, Finset.mem_univ _, mul_pos hk (hφ k)⟩

lemma tau0_pos {Γ : Game N} (hΓ : Γ ∈ gameSpace N) (hc : ConstOnDemand Γ) (j : Fin N.J) :
    0 < Γ.τ j 0 := by
  have hT := hΓ.2.1
  have := hΓ.2.2 j (totalDemand Γ.d) hT le_rfl
  rwa [hc j _ ⟨hT.le, le_rfl⟩] at this

/-- For constant costs: SO = WE = M. -/
lemma const_costs (hN : N.Standing) {Γ : Game N} (hΓ : Γ ∈ gameSpace N) (hc : ConstOnDemand Γ) :
    SOCost Γ = ∑ k, Γ.d k * minCost hN (constPath fun j => Γ.τ j 0) k ∧
    WECost Γ = ∑ k, Γ.d k * minCost hN (constPath fun j => Γ.τ j 0) k := by
  have hc' : ∀ j x, 0 ≤ x → x ≤ totalDemand Γ.d → |Γ.τ j x - Γ.τ j 0| ≤ 0 := by
    intro j x h0 h1; rw [hc j x ⟨h0, h1⟩]; simp
  obtain ⟨g, hg⟩ := exists_WE hN hΓ.1
  have l1 := le_SOCost hN hΓ.1.2 fun f hf => near_const_lower hN _ hc' hf
  have u1 := WECost_le ⟨g, hg⟩ fun f hf => near_const_upper hN _ hc' hf
  have m1 := SOCost_le hN hΓ.1 hg.1
  have m2 := le_WECost hN hΓ.1 hg
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at l1 u1
  exact ⟨by linarith, by linarith⟩

theorem poa_eq_one_of_const (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (hc : ConstOnDemand Γ) : PoA Γ = 1 := by
  obtain ⟨h1, h2⟩ := const_costs hN hΓ hc
  have hpos : 0 < ∑ k, Γ.d k * minCost hN (constPath fun j => Γ.τ j 0) k :=
    weighted_pos hΓ.1.2 hΓ.2.1 _ fun k => minCost_pos hN _
      (constPath_pos hN _ (tau0_pos hΓ hc)) k
  unfold PoA; rw [h1, h2, div_self hpos.ne']

end PoA3

open SensitivityPoA.Lipschitz KellyStochasticNetworks

theorem solution (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (hc : ConstOnDemand Γ) : PoA Γ = 1 :=
  PoA3.poa_eq_one_of_const N hN Γ hΓ hc
