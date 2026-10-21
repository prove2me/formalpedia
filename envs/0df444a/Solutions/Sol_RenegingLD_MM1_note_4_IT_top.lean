-- Prove2me | solution 1 for RenegingLD.MM1.note_4_IT_top
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:52:28.689317+00:00
-- url     : https://prove2.me/submissions/6113c7de-9ea1-44b9-9959-635d8ac2dc83

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open RenegingLD.MM1

lemma rld_min_sub (a b : ℝ) : min a 0 - min b 0 ≤ |a - b| := by
  simp only [min_def]
  split_ifs <;> linarith [le_abs_self (a - b), abs_nonneg (a - b)]

lemma rld_ac_of_bound {f G : ℝ → ℝ} {T : ℝ} (hT0 : 0 ≤ T)
    (hG : AbsolutelyContinuousOnInterval G 0 T)
    (hb : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → |f t - f s| ≤ 2 * |G t - G s|) :
    AbsolutelyContinuousOnInterval f 0 T := by
  rw [absolutelyContinuousOnInterval_iff] at hG ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hG (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have h1 := H E hE hlen
  have h2 : ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, 2 * dist (G (E.2 i).1) (G (E.2 i).2) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hi1, hi2⟩ := hE.1 i hi
    rw [Set.uIcc_of_le hT0] at hi1 hi2
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total (E.2 i).1 (E.2 i).2 with hle | hle
    · rw [abs_sub_comm, abs_sub_comm (G _)]
      exact hb _ _ hi1.1 hle hi2.2
    · exact hb _ _ hi2.1 hle hi1.2
  calc _ ≤ _ := h2
    _ = 2 * ∑ i ∈ Finset.range E.1, dist (G (E.2 i).1) (G (E.2 i).2) := by rw [Finset.mul_sum]
    _ < ε := by linarith

lemma rld_ac_congr {f g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hfg : ∀ t ∈ Set.Icc 0 T, f t = g t) (hg : AbsolutelyContinuousOnInterval g 0 T) :
    AbsolutelyContinuousOnInterval f 0 T := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have h1 := H E hE hlen
  have : ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
      = ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi1, hi2⟩ := hE.1 i hi
    rw [Set.uIcc_of_le hT] at hi1 hi2
    rw [hfg _ hi1, hfg _ hi2]
  rw [this]; exact h1

lemma rld_sk_bound (ψ h : ℝ → ℝ) (T x0 : ℝ) (hT : 0 ≤ T)
    (hh : IntervalIntegrable h volume 0 T)
    (hψ : ∀ r ∈ Set.Icc 0 T, ψ r = x0 + ∫ s in (0:ℝ)..r, h s)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    |skorokhod ψ t - skorokhod ψ s| ≤ 2 * ∫ u in s..t, |h u| := by
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IntervalIntegrable h volume a b := by
    intro a b ha hab hb
    exact hh.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc ha hb)
  have hint' : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      IntervalIntegrable (fun u => |h u|) volume a b := fun a b ha hab hb => (hint a b ha hab hb).abs
  -- difference bound
  have hdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → |ψ b - ψ a| ≤ ∫ u in a..b, |h u| := by
    intro a b ha hab hb
    have e : ψ b - ψ a = ∫ u in a..b, h u := by
      rw [hψ b ⟨ha.trans hab, hb⟩, hψ a ⟨ha, hab.trans hb⟩]
      rw [← intervalIntegral.integral_interval_sub_left (hint 0 b le_rfl (ha.trans hab) hb)
        (hint 0 a le_rfl ha (hab.trans hb))]
      ring
    rw [e]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  have hmono : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ T →
      ∫ u in a..b, |h u| ≤ ∫ u in a..c, |h u| := by
    intro a b c ha hab hbc hc
    exact intervalIntegral.integral_mono_interval le_rfl hab hbc
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hint' a c ha (hab.trans hbc) hc)
  have hnn : ∀ a b : ℝ, a ≤ b → 0 ≤ ∫ u in a..b, |h u| := fun a b hab =>
    intervalIntegral.integral_nonneg hab (fun _ _ => abs_nonneg _)
  have hψ0 : ψ 0 = x0 := by rw [hψ 0 ⟨le_rfl, hT⟩]; simp
  have hbdd : ∀ r : ℝ, 0 ≤ r → r ≤ T →
      BddBelow (Set.range fun u : Set.Icc (0:ℝ) r => min (ψ u) 0) := by
    intro r hr hrT
    refine ⟨-(|x0| + ∫ u in (0:ℝ)..T, |h u|), ?_⟩
    rintro _ ⟨u, rfl⟩
    have h2 := hdiff 0 u le_rfl u.2.1 (u.2.2.trans hrT)
    have h3 := hmono 0 u T le_rfl u.2.1 (u.2.2.trans hrT) le_rfl
    have h4 := abs_le.mp h2
    have h5 := neg_abs_le x0
    refine le_min ?_ (by
      have := hnn 0 T hT
      have := abs_nonneg x0
      linarith)
    linarith [h4.1, h3, hψ0]
  set m : ℝ → ℝ := fun r => ⨅ u : Set.Icc (0:ℝ) r, min (ψ u) 0 with hm
  have hskm : ∀ r, skorokhod ψ r = ψ r - m r := fun r => rfl
  have hne : ∀ r : ℝ, 0 ≤ r → Nonempty (Set.Icc (0:ℝ) r) := fun r hr => ⟨⟨0, le_rfl, hr⟩⟩
  have hm_mono : m t ≤ m s := by
    haveI := hne s hs
    refine le_ciInf fun u => ?_
    exact ciInf_le (hbdd t (hs.trans hst) htT) ⟨u, u.2.1, u.2.2.trans hst⟩
  have hm_low : m s - ∫ u in s..t, |h u| ≤ m t := by
    haveI := hne t (hs.trans hst)
    have hL0 := hnn s t hst
    refine le_ciInf fun u => ?_
    by_cases hu : (u : ℝ) ≤ s
    · have : m s ≤ min (ψ u) 0 := ciInf_le (hbdd s hs (hst.trans htT)) ⟨u, u.2.1, hu⟩
      linarith
    · push_neg at hu
      have h1 : m s ≤ min (ψ s) 0 := ciInf_le (hbdd s hs (hst.trans htT)) ⟨s, hs, le_rfl⟩
      have h2 := rld_min_sub (ψ s) (ψ u)
      have h3 := hdiff s u hs hu.le (u.2.2.trans htT)
      have h4 := hmono s u t hs hu.le u.2.2 htT
      rw [abs_sub_comm] at h2
      linarith
  have h5 := abs_le.mp (hdiff s t hs hst htT)
  rw [hskm, hskm, abs_le]
  constructor <;> linarith [h5.1, h5.2]

lemma rld_sk_zero (ψ : ℝ → ℝ) (h : 0 ≤ ψ 0) : skorokhod ψ 0 = ψ 0 := by
  unfold skorokhod
  have hu : ∀ u : Set.Icc (0:ℝ) 0, (u : ℝ) = 0 := fun u => le_antisymm u.2.2 u.2.1
  have : (fun u : Set.Icc (0:ℝ) 0 => min (ψ u) 0) = fun _ => 0 :=
    funext fun u => by rw [hu u]; exact min_eq_right h
  rw [this, ciInf_const]; simp

lemma rld_main (lam mu θ x0 T : ℝ) (hθ : 0 < θ) (hx0 : 0 ≤ x0) (hT : 0 < T) (ξ ζ : ℝ → ℝ)
    (hp : IsPath T ξ ζ) (ϕ : (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ))
    (hϕ : ϕ ∈ U lam mu θ x0 T ξ ζ) : InCT x0 T ξ ζ := by
  obtain ⟨m1, m2, m3, hnn, i1, i2, i3, hU⟩ := hϕ
  set g : ℝ → ℝ := fun s => ϕ.2.2 s * ξ s with hg
  set h : ℝ → ℝ := fun s => lam * ϕ.1 s - mu * ϕ.2.1 s - θ * g s with hh_def
  set ψ : ℝ → ℝ := fun r => x0 + lam * (∫ s in (0)..r, ϕ.1 s)
              - mu * (∫ s in (0)..r, ϕ.2.1 s) - θ * (∫ s in (0)..r, ϕ.2.2 s * ξ s) with hψdef
  have hTT : (0:ℝ) ≤ T := hT.le
  have hsub : ∀ r ∈ Set.Icc (0:ℝ) T, Set.uIcc 0 r ⊆ Set.uIcc 0 T := by
    intro r hr
    rw [Set.uIcc_of_le hr.1, Set.uIcc_of_le hTT]
    exact Set.Icc_subset_Icc le_rfl hr.2
  have hi1 : IntervalIntegrable (fun s => lam * ϕ.1 s) volume 0 T := i1.const_mul lam
  have hi2 : IntervalIntegrable (fun s => mu * ϕ.2.1 s) volume 0 T := i2.const_mul mu
  have hi3 : IntervalIntegrable (fun s => θ * g s) volume 0 T := i3.const_mul θ
  have hhi : IntervalIntegrable h volume 0 T := (hi1.sub hi2).sub hi3
  have hψ : ∀ r ∈ Set.Icc (0:ℝ) T, ψ r = x0 + ∫ s in (0:ℝ)..r, h s := by
    intro r hr
    have a1 := i1.mono_set (hsub r hr)
    have a2 := i2.mono_set (hsub r hr)
    have a3 := i3.mono_set (hsub r hr)
    have : ∫ s in (0:ℝ)..r, h s = lam * (∫ s in (0)..r, ϕ.1 s)
              - mu * (∫ s in (0)..r, ϕ.2.1 s) - θ * (∫ s in (0)..r, ϕ.2.2 s * ξ s) := by
      simp only [hh_def]
      rw [intervalIntegral.integral_sub ((a1.const_mul lam).sub (a2.const_mul mu)) (a3.const_mul θ),
        intervalIntegral.integral_sub (a1.const_mul lam) (a2.const_mul mu),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [this]; simp only [hψdef]; ring
  have hξ : ∀ t ∈ Set.Icc (0:ℝ) T, ξ t = skorokhod ψ t := fun t ht => (hU t ht).1
  have hζ : ∀ t ∈ Set.Icc (0:ℝ) T, ζ t = θ * ∫ s in (0:ℝ)..t, g s := fun t ht => (hU t ht).2
  have h0T : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_rfl, hTT⟩
  have hψ0 : ψ 0 = x0 := by rw [hψ 0 h0T]; simp
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hξ 0 h0T, rld_sk_zero ψ (by rw [hψ0]; exact hx0), hψ0]
  · rw [hζ 0 h0T]; simp
  · refine rld_ac_of_bound (G := fun t => ∫ v in (0:ℝ)..t, |h v|) hTT
      (hhi.abs.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc) ?_
    intro s t hs hst htT
    rw [hξ t ⟨hs.trans hst, htT⟩, hξ s ⟨hs, hst.trans htT⟩]
    have hb := rld_sk_bound ψ h T x0 hTT hhi hψ hs hst htT
    have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IntervalIntegrable (fun u => |h u|) volume a b := by
      intro a b ha hab hb
      exact hhi.abs.mono_set (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le hTT]; exact Set.Icc_subset_Icc ha hb)
    have e : (∫ v in (0:ℝ)..t, |h v|) - (∫ v in (0:ℝ)..s, |h v|) = ∫ v in s..t, |h v| :=
      intervalIntegral.integral_interval_sub_left (hint 0 t le_rfl (hs.trans hst) htT)
        (hint 0 s le_rfl hs (hst.trans htT))
    have hn : 0 ≤ ∫ v in s..t, |h v| :=
      intervalIntegral.integral_nonneg hst (fun _ _ => abs_nonneg _)
    simp only [e, abs_of_nonneg hn]
    exact hb
  · exact rld_ac_congr hTT hζ (AbsolutelyContinuousOnInterval.const_mul θ
      (i3.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc))
  · rw [ae_restrict_iff' measurableSet_Icc]
    have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]; simp
    have hTn : ∀ᵐ t : ℝ, t ≠ T := by
      rw [ae_iff]; simp
    filter_upwards [i3.ae_hasDerivAt_integral, h0, hTn] with t ht h0 hTn htI hξt
    have htI' : t ∈ Set.Ioo 0 T := ⟨lt_of_le_of_ne htI.1 (Ne.symm h0), lt_of_le_of_ne htI.2 hTn⟩
    have hd := ht (by rw [Set.uIcc_of_le hTT]; exact htI) 0 (by rw [Set.uIcc_of_le hTT]; exact h0T)
    have hd2 : HasDerivAt ζ (θ * g t) t := by
      refine (hd.const_mul θ).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds htI'.1 htI'.2] with r hr
      exact hζ r ⟨hr.1.le, hr.2.le⟩
    rw [hd2.deriv]
    simp [hg, hξt]
  · intro a ha b hb hab
    rw [hζ a ha, hζ b hb]
    apply mul_le_mul_of_nonneg_left _ hθ.le
    refine intervalIntegral.integral_mono_interval le_rfl ha.1 hab ?_ (i3.mono_set (hsub b hb))
    show ∀ᵐ s ∂(volume.restrict (Set.Ioc (0:ℝ) b)), (0:ℝ → ℝ) s ≤ g s
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun s hs =>
      mul_nonneg (hnn s ⟨hs.1.le, hs.2.trans hb.2⟩).2.2 (hp.2.2 s ⟨hs.1.le, hs.2.trans hb.2⟩).1

theorem solution (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T)
    (ξ ζ : ℝ → ℝ) (h : ¬ InCT x0 T ξ ζ) :
    IT lam mu θ x0 T ξ ζ = ⊤ := by
  unfold IT
  rw [iInf_eq_top]
  intro hp
  rw [iInf_eq_top]
  intro ϕ
  rw [iInf_eq_top]
  intro hϕ
  exact absurd (rld_main lam mu θ x0 T hθ hx0 hT ξ ζ hp ϕ hϕ) h
