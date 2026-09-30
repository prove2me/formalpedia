-- Prove2me | solution 1 for WeierstrassEllipticZeta.frobenius_stickelberger
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T01:36:28.809474+00:00
-- url     : https://prove2.me/submissions/3be7a8a3-a1a7-4e5d-bfa8-2288ef4c0a77

import Theorems.Thm_WeierstrassEllipticZeta_hasSumLocallyUniformly_zetaSeries
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

theorem weierstrassZeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  classical
  have hsum : (∑' l : L.lattice, if -l = 0 then (0 : ℂ) else
      1 / (-z - ((-l : L.lattice) : ℂ)) + 1 / ((-l : L.lattice) : ℂ) +
        -z / ((-l : L.lattice) : ℂ) ^ 2) =
      ∑' l : L.lattice, -(if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
    apply tsum_congr
    intro l
    by_cases hl : l = 0
    · simp [hl]
    · simp only [neg_eq_zero, if_neg hl, NegMemClass.coe_neg, even_two, Even.neg_pow]
      rw [show -z - -(l : ℂ) = -(z - (l : ℂ)) by ring]
      simp only [div_neg, neg_div]
      ring
  unfold weierstrassZeta
  conv_lhs => arg 2; rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, hsum, tsum_neg, div_neg]
  ring

private lemma differentiableOn_weierstrassZeta (L : PeriodPair) :
    DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ :=
  fun z hz ↦ (hasDerivAt_weierstrassZeta L z hz).differentiableAt.differentiableWithinAt

private def zetaTail (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l = 0 then 0 else
    1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2

private lemma zetaTail_zero (L : PeriodPair) : zetaTail L 0 = 0 := by
  simp [zetaTail]

private lemma differentiableOn_zetaTail (L : PeriodPair) :
    DifferentiableOn ℂ (zetaTail L) (L.lattice \ {0})ᶜ := by
  refine (hasSumLocallyUniformly_zetaSeries L).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) L.isOpen_compl_lattice_sdiff
  by_cases hl : l = 0
  · simp only [hl, if_true]
    fun_prop
  simp only [if_neg hl]
  refine .add (.add (.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)) (by fun_prop)
  intro z hz h
  apply hz
  have heq := sub_eq_zero.mp h
  exact ⟨heq ▸ l.property, fun hz0 ↦ hl (Subtype.ext (heq.symm.trans hz0))⟩

private lemma hasDerivAt_zetaTail_zero (L : PeriodPair) :
    HasDerivAt (zetaTail L) 0 0 := by
  have h0 : (0 : ℂ) ∈ ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ := by simp
  have hd := ((hasSumLocallyUniformly_zetaSeries L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) L.isOpen_compl_lattice_sdiff).tendsto_at h0
  · have hs (l : L.lattice) : HasDerivAt (fun w : ℂ ↦ if l = 0 then 0 else
        1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) 0 0 := by
      by_cases hl : l = 0
      · simpa only [if_pos hl] using hasDerivAt_const (0 : ℂ) (0 : ℂ)
      simp only [if_neg hl]
      have hlc : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
      convert! ((((hasDerivAt_id (0 : ℂ)).sub_const (l : ℂ)).inv
        (by simpa using hlc)).add_const (1 / (l : ℂ))).add
          ((hasDerivAt_id (0 : ℂ)).div_const ((l : ℂ) ^ 2)) using 1
      · ext w
        simp [one_div]
      · simp [one_div, neg_div]
    have heq : (fun s : Finset L.lattice ↦ deriv (fun w : ℂ ↦ ∑ l ∈ s,
        if l = 0 then 0 else 1 / (w - (l : ℂ)) + 1 / (l : ℂ) +
          w / (l : ℂ) ^ 2) 0) = fun _ ↦ (0 : ℂ) := by
      funext s
      simpa using (HasDerivAt.fun_sum fun l _ ↦ hs l).deriv
    change Tendsto (fun s : Finset L.lattice ↦ deriv (fun w : ℂ ↦ ∑ l ∈ s,
      if l = 0 then 0 else 1 / (w - (l : ℂ)) + 1 / (l : ℂ) +
        w / (l : ℂ) ^ 2) 0) atTop (𝓝 (deriv (zetaTail L) 0)) at hd
    rw [heq] at hd
    have hder := tendsto_nhds_unique hd tendsto_const_nhds
    simpa only [hder] using ((differentiableOn_zetaTail L).differentiableAt
      (L.isOpen_compl_lattice_sdiff.mem_nhds h0)).hasDerivAt
  · by_cases hl : l = 0
    · simp only [hl, if_true]
      fun_prop
    simp only [if_neg hl]
    refine .add (.add (.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)) (by fun_prop)
    intro z hz h
    apply hz
    have heq := sub_eq_zero.mp h
    exact ⟨heq ▸ l.property, fun hz0 ↦ hl (Subtype.ext (heq.symm.trans hz0))⟩

private def fsRelation (L : PeriodPair) (v z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if z ∈ L.lattice ∨ z + v ∈ L.lattice then 0 else
    (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) ^ 2 -
      L.weierstrassP z - L.weierstrassP v - L.weierstrassP (z + v)

private lemma fsRelation_add_period (L : PeriodPair) (v z ω : ℂ) (hω : ω ∈ L.lattice) :
    fsRelation L v (z + ω) = fsRelation L v z := by
  have hmem (w : ℂ) : w + ω ∈ L.lattice ↔ w ∈ L.lattice :=
    ⟨fun h ↦ by simpa using L.lattice.sub_mem h hω, fun h ↦ L.lattice.add_mem h hω⟩
  have hswap : z + ω + v = (z + v) + ω := by ring
  unfold fsRelation
  rw [hswap, hmem, hmem]
  by_cases hz : z ∈ L.lattice ∨ z + v ∈ L.lattice
  · simp [hz]
  · rw [if_neg hz, if_neg hz, weierstrassZeta_add_period L ω z hω
        (fun h ↦ hz (Or.inl h)), weierstrassZeta_add_period L ω (z + v) hω
        (fun h ↦ hz (Or.inr h)), L.weierstrassP_add_coe z ⟨ω, hω⟩,
        L.weierstrassP_add_coe (z + v) ⟨ω, hω⟩]
    ring

private lemma fsRelation_reflection (L : PeriodPair) (v z : ℂ) :
    fsRelation L v (-v - z) = fsRelation L v z := by
  classical
  have h1 : -v - z = -(z + v) := by ring
  have h2 : -v - z + v = -z := by ring
  unfold fsRelation
  rw [h2, h1]
  simp only [neg_mem_iff, weierstrassZeta_neg, L.weierstrassP_neg]
  simp only [or_comm (a := z + v ∈ L.lattice)]
  split_ifs <;> ring

private lemma analyticAt_fsRelation_zero (L : PeriodPair) (v : ℂ) (hv : v ∉ L.lattice) :
    AnalyticAt ℂ (fsRelation L v) 0 := by
  let a : ℂ → ℂ := fun z ↦ weierstrassZeta L (z + v) - weierstrassZeta L v - zetaTail L z
  let b := dslope a 0
  have htail : AnalyticAt ℂ (zetaTail L) 0 :=
    (differentiableOn_zetaTail L).analyticOnNhd L.isOpen_compl_lattice_sdiff 0 (by simp)
  have hza : AnalyticAt ℂ (weierstrassZeta L) v :=
    (differentiableOn_weierstrassZeta L).analyticOnNhd L.isClosed_lattice.isOpen_compl v hv
  have hzcomp : AnalyticAt ℂ (fun z ↦ weierstrassZeta L (z + v)) 0 := by
    have hh : AnalyticAt ℂ (weierstrassZeta L) (0 + v) := by simpa using hza
    exact hh.comp (f := fun z : ℂ ↦ z + v) (by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ z + v) 0)
  have ha : AnalyticAt ℂ a 0 := (hzcomp.sub analyticAt_const).sub htail
  have ha0 : a 0 = 0 := by simp [a, zetaTail_zero]
  have had : HasDerivAt a (-L.weierstrassP v) 0 := by
    have hzcompd : HasDerivAt (fun z ↦ weierstrassZeta L (z + v)) (-L.weierstrassP v) 0 := by
      have hh : HasDerivAt (weierstrassZeta L) (-L.weierstrassP v) (0 + v) :=
        by simpa using hasDerivAt_weierstrassZeta L v hv
      convert! hh.comp 0
        ((hasDerivAt_id (0 : ℂ)).add_const v) using 1
      simp
    convert! (hzcompd.sub_const (weierstrassZeta L v)).sub
      (hasDerivAt_zetaTail_zero L) using 1
    simp
  have hb : AnalyticAt ℂ b 0 := by
    obtain ⟨p, hp⟩ := ha
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hb0 : b 0 = -L.weierstrassP v := by simp only [b, dslope_same, had.deriv]
  have hab (z : ℂ) : z * b z = a z := by
    simpa only [b, sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero ha0 z
  have hpa : AnalyticAt ℂ (fun z ↦ L.weierstrassP (z + v)) 0 := by
    have hh : AnalyticAt ℂ L.weierstrassP (0 + v) := by
      simpa using L.analyticOnNhd_weierstrassP v hv
    exact hh.comp (f := fun z : ℂ ↦ z + v) (by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ z + v) 0)
  let g : ℂ → ℂ := fun z ↦ (z * b z) ^ 2 - 2 * b z - L.weierstrassPExcept 0 z -
    L.weierstrassP v - L.weierstrassP (z + v)
  have hg : AnalyticAt ℂ g 0 := by
    have hp0 := L.analyticAt_weierstrassPExcept 0
    dsimp [g]
    fun_prop
  apply hg.congr
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z + v ∉ L.lattice := by
    have hh : Tendsto (fun z : ℂ ↦ z + v) (𝓝 0) (𝓝 v) := by
      convert! (continuousAt_id.add continuousAt_const :
        ContinuousAt (fun z : ℂ ↦ z + v) 0).tendsto using 1
      simp
    exact hh.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hv)
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0, hnear] with z hz hzv
  by_cases hz0 : z = 0
  · subst z
    simp [g, fsRelation, hb0]
    ring
  · have hzreg : z ∉ L.lattice := by simpa [hz0] using hz
    have hP := L.weierstrassPExcept_add (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at hP
    simp only [g, fsRelation, hzreg, hzv, or_self, if_false]
    rw [← hP]
    have haeq := hab z
    dsimp [a] at haeq
    change z * b z = weierstrassZeta L (z + v) - weierstrassZeta L v - zetaTail L z at haeq
    change _ = ((weierstrassZeta L (z + v) - (1 / z + zetaTail L z) -
      weierstrassZeta L v) ^ 2 - (L.weierstrassPExcept 0 z + 1 / z ^ 2) -
      L.weierstrassP v - L.weierstrassP (z + v))
    rw [show weierstrassZeta L (z + v) - (1 / z + zetaTail L z) -
      weierstrassZeta L v = z * b z - 1 / z by linear_combination -haeq]
    field_simp
    ring

private lemma analyticAt_fsRelation (L : PeriodPair) (v : ℂ) (hv : v ∉ L.lattice) (z : ℂ) :
    AnalyticAt ℂ (fsRelation L v) z := by
  have hzero := analyticAt_fsRelation_zero L v hv
  by_cases hz : z ∈ L.lattice
  · have hcomp : AnalyticAt ℂ (fun w ↦ fsRelation L v (w - z)) z := by
      have hh : AnalyticAt ℂ (fsRelation L v) (z - z) := by simpa using hzero
      exact hh.comp (f := fun w : ℂ ↦ w - z) (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - z) z)
    convert! hcomp using 1
    ext w
    simpa using fsRelation_add_period L v (w - z) z hz
  by_cases hzv : z + v ∈ L.lattice
  · have hnegv : AnalyticAt ℂ (fsRelation L v) (-v) := by
      have hc : AnalyticAt ℂ (fun w ↦ fsRelation L v (-v - w)) (-v) := by
        have hh : AnalyticAt ℂ (fsRelation L v) (-v - -v) := by simpa using hzero
        exact hh.comp (f := fun w : ℂ ↦ -v - w) (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ -v - w) (-v))
      simpa only [fsRelation_reflection] using hc
    have hc : AnalyticAt ℂ (fun w ↦ fsRelation L v (w - (z + v))) z := by
      have hh : AnalyticAt ℂ (fsRelation L v) (z - (z + v)) := by simpa using hnegv
      exact hh.comp (f := fun w : ℂ ↦ w - (z + v)) (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - (z + v)) z)
    convert! hc using 1
    ext w
    simpa using fsRelation_add_period L v (w - (z + v)) (z + v) hzv
  · have hZ := (differentiableOn_weierstrassZeta L).analyticOnNhd L.isClosed_lattice.isOpen_compl
    have hZz := hZ z hz
    have hZv := hZ (z + v) hzv
    have hPz := L.analyticOnNhd_weierstrassP z hz
    have hPv := L.analyticOnNhd_weierstrassP (z + v) hzv
    have ha : AnalyticAt ℂ (fun w ↦
        (weierstrassZeta L (w + v) - weierstrassZeta L w - weierstrassZeta L v) ^ 2 -
          L.weierstrassP w - L.weierstrassP v - L.weierstrassP (w + v)) z := by fun_prop
    apply ha.congr
    have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz
    have hnearv : ∀ᶠ w in 𝓝 z, w + v ∉ L.lattice :=
      (continuousAt_id.add continuousAt_const).eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hzv)
    filter_upwards [hnear, hnearv] with w hw hwv
    simp [fsRelation, hw, hwv]

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) ^ 2 =
      L.weierstrassP z + L.weierstrassP v + L.weierstrassP (z + v) := by
  have hd : Differentiable ℂ (fsRelation L v) :=
    fun w ↦ (analyticAt_fsRelation L v hv w).differentiableAt
  have hconst := hd.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hd.continuous
      (fun w ω hω ↦ fsRelation_add_period L v w ω hω)).isBounded z 0
  simp only [fsRelation, hz, hzv, or_self, if_false, zero_mem,
    true_or, if_true] at hconst
  linear_combination hconst
