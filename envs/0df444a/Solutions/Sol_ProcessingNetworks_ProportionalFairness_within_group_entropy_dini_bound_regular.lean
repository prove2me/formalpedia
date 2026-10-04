-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.within_group_entropy_dini_bound_regular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:20:25.870867+00:00
-- url     : https://prove2.me/submissions/016edbc3-5f9c-46ed-8df9-08c06b78d6b9

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

open Filter Topology

open ProcessingNetworks.ProportionalFairness in
theorem solution
    {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i)
    (hZlip : ∃ Kc : ℝ, ∀ i (s t : ℝ), 0 ≤ s → s ≤ t → |Zh t i - Zh s i| ≤ Kc * (t - s))
    (t : ℝ) (ht : 0 < t)
    (hreg : ∀ i, DifferentiableAt ℝ (fun s => Zh s i) t) :
    diniUpperRight (withinGroupEntropy grp Zh) t ≤
      ((∑ i, if Zh t i = 0 then 0 else
        deriv (fun s => Zh s i) t * Real.log (Zh t i / groupAggregate grp (Zh t) (grp i)) : ℝ) :
          EReal) := by
  classical
  set z' : Fin I → ℝ := fun i => deriv (fun s => Zh s i) t with hz'
  have hZd : ∀ i, HasDerivAt (fun s => Zh s i) (z' i) t := fun i => (hreg i).hasDerivAt
  set Y : ℝ → Fin L → ℝ := fun s ℓ => groupAggregate grp (Zh s) ℓ with hY
  set Y' : Fin L → ℝ := fun ℓ => ∑ j ∈ Finset.univ.filter (fun j => grp j = ℓ), z' j with hY'
  have hYd : ∀ ℓ, HasDerivAt (fun s => Y s ℓ) (Y' ℓ) t := fun ℓ =>
    HasDerivAt.fun_sum fun j _ => hZd j
  have hev : ∀ᶠ s in 𝓝 t, 0 ≤ s := (lt_mem_nhds ht).mono fun s hs => hs.le
  have hYge : ∀ s, 0 ≤ s → ∀ i, Zh s i ≤ Y s (grp i) := fun s hs i =>
    Finset.single_le_sum (f := fun j => Zh s j) (fun j _ => hZnn s hs j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
  -- zero coordinates have zero derivative
  have hz0 : ∀ i, Zh t i = 0 → z' i = 0 := by
    intro i h0
    have hmin : IsLocalMin (fun s => Zh s i) t :=
      hev.mono fun s hs => by simp only; rw [h0]; exact hZnn s hs i
    exact hmin.hasDerivAt_eq_zero (hZd i)
  set F : Fin I → ℝ → ℝ := fun i s =>
    if Zh s i = 0 then 0 else Zh s i * Real.log (Zh s i / Y s (grp i)) with hF
  have hf : ∀ s, withinGroupEntropy grp Zh s = ∑ i, F i s := fun s => rfl
  -- positive coordinates: differentiable terms
  set d : Fin I → ℝ := fun i =>
    z' i * Real.log (Zh t i / Y t (grp i)) + z' i - Zh t i * Y' (grp i) / Y t (grp i) with hd
  have hFd : ∀ i, 0 < Zh t i → HasDerivAt (F i) (d i) t := by
    intro i hpos
    have hYpos : 0 < Y t (grp i) := lt_of_lt_of_le hpos (hYge t ht.le i)
    have hq : HasDerivAt (fun s => Zh s i / Y s (grp i))
        ((z' i * Y t (grp i) - Zh t i * Y' (grp i)) / Y t (grp i) ^ 2) t :=
      (hZd i).div (hYd (grp i)) hYpos.ne'
    have hqpos : Zh t i / Y t (grp i) ≠ 0 := (div_pos hpos hYpos).ne'
    have hm := (hZd i).mul (hq.log hqpos)
    have hloc : (fun s => Zh s i * Real.log (Zh s i / Y s (grp i))) =ᶠ[𝓝 t] F i := by
      have hc : ContinuousAt (fun s => Zh s i) t := (hZd i).continuousAt
      filter_upwards [hc.eventually (lt_mem_nhds hpos)] with s hs
      simp only [hF, if_neg hs.ne']
    refine (hm.congr_of_eventuallyEq hloc.symm).congr_deriv ?_
    simp only [hd]
    field_simp
    ring
  -- zero coordinates: nonpositive increments
  have hFneg : ∀ i, Zh t i = 0 → ∀ s, 0 ≤ s → F i s ≤ F i t := by
    intro i h0 s hs
    have hFt : F i t = 0 := by simp [hF, h0]
    rw [hFt]
    simp only [hF]
    split_ifs with hs0
    · exact le_rfl
    · have hp : 0 < Zh s i := lt_of_le_of_ne (hZnn s hs i) (Ne.symm hs0)
      have hYs : 0 < Y s (grp i) := lt_of_lt_of_le hp (hYge s hs i)
      exact mul_nonpos_of_nonneg_of_nonpos hp.le
        (Real.log_nonpos (div_nonneg hp.le hYs.le) ((div_le_one hYs).mpr (hYge s hs i)))
  -- the comparison function
  set q : ℝ → ℝ := fun h => ∑ i, if 0 < Zh t i then (F i (t + h) - F i t) / h else 0 with hq
  set Lsum : ℝ := ∑ i, if 0 < Zh t i then d i else 0 with hL
  have hqlim : Tendsto q (𝓝[>] 0) (𝓝 Lsum) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    split_ifs with hpos
    · have := (hFd i hpos).tendsto_slope_zero_right
      refine this.congr fun h => ?_
      simp [smul_eq_mul, div_eq_inv_mul]
    · exact tendsto_const_nhds
  have hle : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (((withinGroupEntropy grp Zh (t + h) - withinGroupEntropy grp Zh t) / h : ℝ) : EReal) ≤
        ((q h : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    rw [EReal.coe_le_coe_iff, hf, hf, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hpos
    · exact le_rfl
    · have h0 : Zh t i = 0 := le_antisymm (not_lt.mp hpos) (hZnn t ht.le i)
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hFneg i h0 (t + h) (by linarith))) hh'.le
  have hlimq : Tendsto (fun h => ((q h : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (Lsum : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hqlim
  have hstep : diniUpperRight (withinGroupEntropy grp Zh) t ≤ (Lsum : EReal) := by
    unfold diniUpperRight
    calc limsup (fun h : ℝ => (((withinGroupEntropy grp Zh (t + h) -
          withinGroupEntropy grp Zh t) / h : ℝ) : EReal)) (𝓝[>] 0)
        ≤ limsup (fun h => ((q h : ℝ) : EReal)) (𝓝[>] 0) := limsup_le_limsup hle
      _ = (Lsum : EReal) := hlimq.limsup_eq
  refine hstep.trans (le_of_eq ?_)
  congr 1
  -- algebra: the correction terms cancel within each group
  have hcancel : ∑ i, (if 0 < Zh t i then z' i - Zh t i * Y' (grp i) / Y t (grp i) else 0) = 0 := by
    have e1 : ∀ i, (if 0 < Zh t i then z' i - Zh t i * Y' (grp i) / Y t (grp i) else 0) =
        z' i - Zh t i * (Y' (grp i) / Y t (grp i)) := by
      intro i
      split_ifs with hpos
      · ring
      · have h0 : Zh t i = 0 := le_antisymm (not_lt.mp hpos) (hZnn t ht.le i)
        rw [h0, hz0 i h0]; ring
    rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_sub_distrib]
    have e2 : ∑ i, Zh t i * (Y' (grp i) / Y t (grp i)) = ∑ ℓ, Y' ℓ := by
      rw [← Finset.sum_fiberwise Finset.univ grp (fun i => Zh t i * (Y' (grp i) / Y t (grp i)))]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      have e3 : ∑ i ∈ Finset.univ.filter (fun i => grp i = ℓ), Zh t i * (Y' (grp i) / Y t (grp i)) =
          Y t ℓ * (Y' ℓ / Y t ℓ) := by
        rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), ← Finset.sum_mul]
        rfl
      rw [e3]
      by_cases hY0 : Y t ℓ = 0
      · have hall : ∀ j ∈ Finset.univ.filter (fun j => grp j = ℓ), Zh t j = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hZnn t ht.le j).mp hY0
        have : Y' ℓ = 0 := Finset.sum_eq_zero fun j hj => hz0 j (hall j hj)
        rw [hY0, this]; simp
      · field_simp
    have e4 : ∑ ℓ, Y' ℓ = ∑ i, z' i := Finset.sum_fiberwise Finset.univ grp z'
    rw [e2, e4, sub_self]
  rw [hL]
  have e5 : ∀ i, (if 0 < Zh t i then d i else 0) =
      (if Zh t i = 0 then 0 else z' i * Real.log (Zh t i / Y t (grp i))) +
        (if 0 < Zh t i then z' i - Zh t i * Y' (grp i) / Y t (grp i) else 0) := by
    intro i
    by_cases hpos : 0 < Zh t i
    · rw [if_pos hpos, if_neg hpos.ne', if_pos hpos, hd]; ring
    · have h0 : Zh t i = 0 := le_antisymm (not_lt.mp hpos) (hZnn t ht.le i)
      rw [if_neg hpos, if_pos h0, if_neg hpos]; ring
  rw [Finset.sum_congr rfl fun i _ => e5 i, Finset.sum_add_distrib, hcancel, add_zero]


