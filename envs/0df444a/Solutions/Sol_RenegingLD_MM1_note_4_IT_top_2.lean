-- Prove2me | solution 2 for RenegingLD.MM1.note_4_IT_top
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:03:18.169847+00:00
-- url     : https://prove2.me/submissions/830fd6c1-3476-465e-8e16-e665a53a36a6

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

open RenegingLD.MM1
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace RenegN4

/-- If every increment of `f` over a pair of points of `[a,b]` is dominated by an increment of the
absolutely continuous `g` over a sub-pair, then `f` is absolutely continuous. -/
theorem ac_of_dom {f g : ℝ → ℝ} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, ∃ p ∈ uIcc x y, ∃ q ∈ uIcc x y,
      dist (f x) (f y) ≤ dist (g p) (g q)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := hg ε hε
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨n, I⟩ ⟨hI1, hI2⟩ hlen
  have hch : ∀ i, ∃ pq : ℝ × ℝ, (i ∈ Finset.range n →
      pq.1 ∈ uIcc (I i).1 (I i).2 ∧ pq.2 ∈ uIcc (I i).1 (I i).2 ∧
      dist (f (I i).1) (f (I i).2) ≤ dist (g pq.1) (g pq.2)) := by
    intro i
    by_cases hi : i ∈ Finset.range n
    · obtain ⟨p, hp, q, hq, hd⟩ := h _ (hI1 i hi).1 _ (hI1 i hi).2
      exact ⟨(p, q), fun _ => ⟨hp, hq, hd⟩⟩
    · exact ⟨(0, 0), fun h' => absurd h' hi⟩
  choose J hJ using hch
  have hsub : ∀ i ∈ Finset.range n, uIcc (J i).1 (J i).2 ⊆ uIcc (I i).1 (I i).2 := fun i hi =>
    uIcc_subset_uIcc (hJ i hi).1 (hJ i hi).2.1
  have hsubIoc : ∀ i ∈ Finset.range n, uIoc (J i).1 (J i).2 ⊆ uIoc (I i).1 (I i).2 := by
    intro i hi
    have h1 := (hJ i hi).1
    have h2 := (hJ i hi).2.1
    simp only [uIcc, mem_Icc] at h1 h2
    intro z hz
    simp only [uIoc, mem_Ioc] at hz ⊢
    constructor
    · have : min (I i).1 (I i).2 ≤ min (J i).1 (J i).2 := le_min h1.1 h2.1
      linarith [hz.1]
    · have : max (J i).1 (J i).2 ≤ max (I i).1 (I i).2 := max_le h1.2 h2.2
      linarith [hz.2]
  have hmem : (n, J) ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
    refine ⟨fun i hi => ⟨?_, ?_⟩, ?_⟩
    · exact uIcc_subset_uIcc (hI1 i hi).1 (hI1 i hi).2 (hJ i hi).1
    · exact uIcc_subset_uIcc (hI1 i hi).1 (hI1 i hi).2 (hJ i hi).2.1
    · intro i hi j hj hij
      exact (hI2 hi hj hij).mono (hsubIoc i hi) (hsubIoc j hj)
  have hlen' : ∑ i ∈ Finset.range n, dist (J i).1 (J i).2 < δ := by
    refine lt_of_le_of_lt (Finset.sum_le_sum fun i hi => ?_) hlen
    have h1 := (hJ i hi).1
    have h2 := (hJ i hi).2.1
    simp only [uIcc, mem_Icc] at h1 h2
    simp only [Real.dist_eq]
    rw [abs_le]
    constructor <;>
    · rcases le_total (I i).1 (I i).2 with hh | hh
      · rw [min_eq_left hh, max_eq_right hh] at h1 h2
        cases abs_cases ((I i).1 - (I i).2) <;> linarith
      · rw [min_eq_right hh, max_eq_left hh] at h1 h2
        cases abs_cases ((I i).1 - (I i).2) <;> linarith
  calc ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)
      ≤ ∑ i ∈ Finset.range n, dist (g (J i).1) (g (J i).2) :=
        Finset.sum_le_sum fun i hi => (hJ i hi).2.2
    _ < ε := hgδ (n, J) hmem hlen'

/-- Absolute continuity only depends on the values on `uIcc a b`. -/
theorem ac_congr {f g : ℝ → ℝ} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, f x = g x) : AbsolutelyContinuousOnInterval f a b :=
  ac_of_dom hg fun x hx y hy => ⟨x, left_mem_uIcc, y, right_mem_uIcc, by rw [h x hx, h y hy]⟩

/-- The running minimum `m(t) = inf_{s ∈ [0,t]} min(ψ s, 0)` of a continuous function is attained. -/
theorem runmin_attained {ψ : ℝ → ℝ} {T : ℝ} (hψ : ContinuousOn ψ (Icc 0 T)) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ∃ r ∈ Icc 0 t, (⨅ s : Icc (0 : ℝ) t, min (ψ s) 0) = min (ψ r) 0 ∧
      ∀ s ∈ Icc 0 t, min (ψ r) 0 ≤ min (ψ s) 0 := by
  have hc : ContinuousOn (fun s => min (ψ s) 0) (Icc 0 t) :=
    ContinuousOn.inf (hψ.mono (Icc_subset_Icc le_rfl ht.2)) continuousOn_const
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht.1) hc
  refine ⟨r, hr, ?_, fun s hs => hmin hs⟩
  have hne : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht.1⟩⟩
  apply le_antisymm
  · have hbdd : BddBelow (Set.range fun s : Icc (0 : ℝ) t => min (ψ s) 0) :=
      ⟨min (ψ r) 0, fun y hy => by obtain ⟨s, rfl⟩ := hy; exact hmin s.2⟩
    exact ciInf_le hbdd ⟨r, hr⟩
  · exact le_ciInf fun s => hmin s.2

theorem runmin_ac {ψ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hψ : AbsolutelyContinuousOnInterval ψ 0 T) :
    AbsolutelyContinuousOnInterval (fun t => ⨅ s : Icc (0 : ℝ) t, min (ψ s) 0) 0 T := by
  have hu : uIcc 0 T = Icc 0 T := uIcc_of_le hT
  have hcont : ContinuousOn ψ (Icc 0 T) := hu ▸ hψ.continuousOn
  refine ac_of_dom hψ ?_
  -- the key estimate for `s ≤ t`
  have key : ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → ∃ q ∈ Icc s t,
      dist (⨅ u : Icc (0 : ℝ) s, min (ψ u) 0) (⨅ u : Icc (0 : ℝ) t, min (ψ u) 0) ≤
        dist (ψ s) (ψ q) := by
    intro s t hs ht hst
    obtain ⟨rs, hrs, es, ms⟩ := runmin_attained hcont hs
    obtain ⟨rt, hrt, et, mt⟩ := runmin_attained hcont ht
    rw [es, et]
    have h1 : min (ψ rt) 0 ≤ min (ψ rs) 0 := mt rs ⟨hrs.1, hrs.2.trans hst⟩
    rcases le_or_gt rt s with hle | hlt
    · have h2 : min (ψ rs) 0 ≤ min (ψ rt) 0 := ms rt ⟨hrt.1, hle⟩
      refine ⟨s, ⟨le_rfl, hst⟩, ?_⟩
      rw [le_antisymm h1 h2, dist_self]; exact dist_nonneg
    · refine ⟨rt, ⟨hlt.le, hrt.2⟩, ?_⟩
      have h3 : min (ψ rs) 0 ≤ min (ψ s) 0 := ms s ⟨hs.1, le_rfl⟩
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith)]
      have h4 : min (ψ s) 0 - min (ψ rt) 0 ≤ |ψ s - ψ rt| := by
        have a1 := le_abs_self (ψ s - ψ rt)
        have a2 := neg_abs_le (ψ s - ψ rt)
        rcases le_total (ψ s) 0 with h5 | h5 <;> rcases le_total (ψ rt) 0 with h6 | h6
        · rw [min_eq_left h5, min_eq_left h6]; linarith
        · rw [min_eq_left h5, min_eq_right h6]; linarith
        · rw [min_eq_right h5, min_eq_left h6]; linarith
        · rw [min_eq_right h5, min_eq_right h6]; linarith [abs_nonneg (ψ s - ψ rt)]
      linarith
  intro x hx y hy
  rw [hu] at hx hy
  rcases le_total x y with hxy | hyx
  · obtain ⟨q, hq, hd⟩ := key x y hx hy hxy
    refine ⟨x, left_mem_uIcc, q, ?_, hd⟩
    rw [uIcc_of_le hxy]; exact hq
  · obtain ⟨q, hq, hd⟩ := key y x hy hx hyx
    refine ⟨y, right_mem_uIcc, q, ?_, by rw [dist_comm]; exact hd⟩
    rw [uIcc_of_ge hyx]; exact hq

end RenegN4

open RenegN4 in
theorem solution (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T)
    (ξ ζ : ℝ → ℝ) (h : ¬ InCT x0 T ξ ζ) :
    IT lam mu θ x0 T ξ ζ = ⊤ := by
  by_contra hne
  apply h
  have hpath : IsPath T ξ ζ := by
    by_contra hp; apply hne; simp [IT, hp]
  obtain ⟨ϕ, hϕ⟩ : (U lam mu θ x0 T ξ ζ).Nonempty := by
    by_contra hU
    rw [Set.not_nonempty_iff_eq_empty] at hU
    apply hne; simp [IT, hU]
  obtain ⟨hm1, hm2, hm3, hnn, hi1, hi2, hi3, heq⟩ := hϕ
  obtain ⟨hcξ, hcζ, hpnn⟩ := hpath
  have hu : uIcc 0 T = Icc 0 T := uIcc_of_le hT.le
  have h0u : (0 : ℝ) ∈ uIcc 0 T := left_mem_uIcc
  set F1 : ℝ → ℝ := fun r => ∫ s in (0)..r, ϕ.1 s with hF1
  set F2 : ℝ → ℝ := fun r => ∫ s in (0)..r, ϕ.2.1 s with hF2
  set F3 : ℝ → ℝ := fun r => ∫ s in (0)..r, ϕ.2.2 s * ξ s with hF3
  set ψ : ℝ → ℝ := fun r => x0 + lam * F1 r - mu * F2 r - θ * F3 r with hψ
  have ac1 : AbsolutelyContinuousOnInterval F1 0 T :=
    hi1.absolutelyContinuousOnInterval_intervalIntegral h0u
  have ac2 : AbsolutelyContinuousOnInterval F2 0 T :=
    hi2.absolutelyContinuousOnInterval_intervalIntegral h0u
  have ac3 : AbsolutelyContinuousOnInterval F3 0 T :=
    hi3.absolutelyContinuousOnInterval_intervalIntegral h0u
  have acc : AbsolutelyContinuousOnInterval (fun _ : ℝ => x0) 0 T :=
    (LipschitzWith.const x0).lipschitzOnWith.absolutelyContinuousOnInterval
  have acψ : AbsolutelyContinuousOnInterval ψ 0 T :=
    ((acc.add (ac1.const_mul lam)).sub (ac2.const_mul mu)).sub (ac3.const_mul θ)
  have hξeq : ∀ t ∈ Icc 0 T, ξ t = ψ t - ⨅ s : Icc (0 : ℝ) t, min (ψ s) 0 := fun t ht =>
    (heq t ht).1
  have hζeq : ∀ t ∈ Icc 0 T, ζ t = θ * F3 t := fun t ht => (heq t ht).2
  refine ⟨⟨hcξ, hcζ, hpnn⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ξ 0 = x0
    rw [hξeq 0 ⟨le_rfl, hT.le⟩]
    have hψ0 : ψ 0 = x0 := by simp [hψ, hF1, hF2, hF3]
    have hfun : (fun s : Icc (0 : ℝ) 0 => min (ψ s) 0) = fun _ => 0 := by
      funext s
      have : (s : ℝ) = 0 := le_antisymm s.2.2 s.2.1
      rw [this, hψ0]; exact min_eq_right hx0
    have hne : Nonempty (Icc (0 : ℝ) 0) := ⟨⟨0, le_rfl, le_rfl⟩⟩
    rw [hfun, ciInf_const, hψ0, sub_zero]
  · rw [hζeq 0 ⟨le_rfl, hT.le⟩]; simp [hF3]
  · -- ξ absolutely continuous
    have acm := runmin_ac hT.le acψ
    refine ac_congr (acψ.sub acm) ?_
    intro t ht
    rw [hu] at ht
    exact hξeq t ht
  · refine ac_congr (ac3.const_mul θ) ?_
    intro t ht; rw [hu] at ht; exact hζeq t ht
  · -- ζ' = 0 a.e. where ξ = 0
    have hd := hi3.ae_hasDerivAt_integral
    have hIoo : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), t ∈ Ioo 0 T := by
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T))] with t h ht
      exact h.mpr ht
    filter_upwards [hIoo, ae_restrict_of_ae hd] with t ht hdt hz
    have ht' : t ∈ uIcc 0 T := by rw [hu]; exact Ioo_subset_Icc_self ht
    have hder : HasDerivAt F3 (ϕ.2.2 t * ξ t) t := hdt ht' 0 h0u
    have hev : ζ =ᶠ[𝓝 t] fun r => θ * F3 r := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr using hζeq r hr
    have : HasDerivAt ζ (θ * (ϕ.2.2 t * ξ t)) t := (hder.const_mul θ).congr_of_eventuallyEq hev
    rw [this.deriv, hz]; ring
  · -- ζ monotone
    intro s hs t ht hst
    rw [hζeq s hs, hζeq t ht]
    apply mul_le_mul_of_nonneg_left _ hθ.le
    have hsub : uIcc 0 t ⊆ uIcc 0 T := by
      rw [hu, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
    have hi3t : IntervalIntegrable (fun s => ϕ.2.2 s * ξ s) volume 0 t := hi3.mono_set hsub
    have hi3s : IntervalIntegrable (fun s => ϕ.2.2 s * ξ s) volume 0 s :=
      hi3.mono_set (by rw [hu, uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)
    have hst' : IntervalIntegrable (fun s => ϕ.2.2 s * ξ s) volume s t :=
      hi3s.symm.trans hi3t
    have := intervalIntegral.integral_add_adjacent_intervals hi3s hst'
    simp only [hF3]
    rw [← this]
    have hnn' : 0 ≤ ∫ u in s..t, ϕ.2.2 u * ξ u := by
      apply intervalIntegral.integral_nonneg hst
      intro u hu'
      have hu'' : u ∈ Icc 0 T := ⟨hs.1.trans hu'.1, hu'.2.trans ht.2⟩
      exact mul_nonneg (hnn u hu'').2.2 (hpnn u hu'').1
    linarith
