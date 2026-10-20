-- Prove2me | solution 1 for SupplyFlex.SupplierLed.qo_lt_qc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:46:54.922786+00:00
-- url     : https://prove2.me/submissions/57a202e6-c5d7-4efe-821a-8df341ff5ade

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

open MeasureTheory SupplyFlex.SupplierLed

namespace T6Fbar

lemma f_nonneg (M : Model) (hM : M.Std) (x : ℝ) : 0 ≤ M.f x := by
  by_cases h : x ∈ supp M.abar
  · exact (hM.f_pos x h).le
  · rw [hM.f_zero x h]

lemma f_neg (M : Model) (hM : M.Std) (x : ℝ) (hx : x < 0) : M.f x = 0 :=
  hM.f_zero x (fun h => by linarith [h.1])

lemma r_pos (M : Model) (hM : M.Std) : 0 < M.r := by
  have := hM.assm1_r
  have : 0 < M.c / M.p := div_pos hM.c_pos hM.p_pos
  linarith

lemma Iic0 (M : Model) (hM : M.Std) : ∫ x in Set.Iic (0:ℝ), M.f x = 0 := by
  rw [integral_Iic_eq_integral_Iio]
  exact setIntegral_eq_zero_of_forall_eq_zero (fun x hx => f_neg M hM x hx)

/-- `F̄(x) = 1 − ∫₀ˣ f`. -/
lemma Fbar_eq (M : Model) (hM : M.Std) (x : ℝ) :
    Fbar M.f x = 1 - ∫ t in (0:ℝ)..x, M.f t := by
  have hi := hM.f_int.1
  have h1 := intervalIntegral.integral_Iic_add_Ioi (b := x) hi.integrableOn hi.integrableOn
  have h2 := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x) hi.integrableOn
    hi.integrableOn
  rw [Iic0 M hM, sub_zero] at h2
  unfold Fbar
  rw [hM.f_int.2] at h1
  linarith

lemma Fbar_cont (M : Model) (hM : M.Std) : Continuous (Fbar M.f) := by
  have : Fbar M.f = fun x => 1 - ∫ t in (0:ℝ)..x, M.f t := funext (Fbar_eq M hM)
  rw [this]
  exact continuous_const.sub (intervalIntegral.continuous_primitive
    (fun a b => hM.f_int.1.intervalIntegrable) 0)

lemma Fbar_zero (M : Model) (hM : M.Std) : Fbar M.f 0 = 1 := by
  rw [Fbar_eq M hM]; simp

lemma Fbar_nonneg (M : Model) (hM : M.Std) (x : ℝ) : 0 ≤ Fbar M.f x :=
  setIntegral_nonneg measurableSet_Ioi (fun t _ => f_nonneg M hM t)

lemma Fbar_tendsto (M : Model) (hM : M.Std) :
    Filter.Tendsto (Fbar M.f) Filter.atTop (nhds 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := M.f) (s := fun x : ℝ => Set.Ioi x)
    (fun _ => measurableSet_Ioi) (fun a b hab => Set.Ioi_subset_Ioi hab)
    ⟨0, hM.f_int.1.integrableOn⟩
  have he : (⋂ n : ℝ, Set.Ioi n) = ∅ := by
    ext x; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact ⟨x, le_rfl⟩
  rw [he, Measure.restrict_empty, integral_zero_measure] at h
  exact h

/-- There are points of the support where `F̄` is arbitrarily small. -/
lemma exists_supp_Fbar_lt (M : Model) (hM : M.Std) (ε : ℝ) (hε : 0 < ε) :
    ∃ b, b ∈ supp M.abar ∧ Fbar M.f b < ε := by
  by_cases htop : M.abar = ⊤
  · obtain ⟨b, hb⟩ := Filter.eventually_atTop.1
      ((Fbar_tendsto M hM).eventually (gt_mem_nhds hε))
    refine ⟨max b 0, ⟨le_max_right _ _, by rw [htop]; exact ENNReal.ofReal_lt_top⟩,
      hb _ (le_max_left _ _)⟩
  · set a := M.abar.toReal with ha
    have hofa : ENNReal.ofReal a = M.abar := ENNReal.ofReal_toReal htop
    have hapos : 0 < a := ENNReal.toReal_pos hM.abar_pos.ne' htop
    have hFa : Fbar M.f a = 0 := by
      unfold Fbar
      refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => hM.f_zero t (fun h => ?_))
      have : ENNReal.ofReal a < ENNReal.ofReal t :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hapos.le).2 ht
      rw [hofa] at this
      exact absurd h.2 (not_lt.2 this.le)
    have hc := (Fbar_cont M hM).continuousAt (x := a)
    rw [ContinuousAt, hFa] at hc
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hε))
    set b := max 0 (a - δ / 2)
    have hb0 : 0 ≤ b := le_max_left _ _
    have hba : b < a := max_lt hapos (by linarith)
    refine ⟨b, ⟨hb0, ?_⟩, hball ?_⟩
    · rw [← hofa]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb0).2 hba
    · rw [Real.dist_eq, abs_lt]
      constructor
      · have : a - δ / 2 ≤ b := le_max_right _ _
        linarith
      · linarith

end T6Fbar

namespace T6Psi
open T6Fbar

lemma Fbar_anti (M : Model) (hM : M.Std) {x y : ℝ} (hxy : x ≤ y) : Fbar M.f y ≤ Fbar M.f x := by
  unfold Fbar
  refine setIntegral_mono_set hM.f_int.1.integrableOn
    (Filter.Eventually.of_forall (fun t => f_nonneg M hM t))
    (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hxy))

lemma Fbar_le_one (M : Model) (hM : M.Std) (x : ℝ) : Fbar M.f x ≤ 1 := by
  unfold Fbar
  rw [← hM.f_int.2]
  exact setIntegral_le_integral hM.f_int.1 (Filter.Eventually.of_forall (f_nonneg M hM))

/-- Beyond the support, `F̄ = 0`. -/
lemma Fbar_out (M : Model) (hM : M.Std) (q : ℝ) (hq : M.abar ≤ ENNReal.ofReal q) :
    Fbar M.f q = 0 := by
  unfold Fbar
  refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => hM.f_zero t (fun h => ?_))
  exact absurd (lt_of_lt_of_le h.2 (le_trans hq (ENNReal.ofReal_le_ofReal ht.le))) (lt_irrefl _)

/-- On the support, `F̄ > 0`. -/
lemma Fbar_pos (M : Model) (hM : M.Std) (q : ℝ) (hq : q ∈ supp M.abar) : 0 < Fbar M.f q := by
  rcases (Fbar_nonneg M hM q).lt_or_eq with h | h
  · exact h
  exfalso
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi q)] M.f :=
    Filter.Eventually.of_forall (fun t => f_nonneg M hM t)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hM.f_int.1.integrableOn).1 h.symm
  obtain ⟨t, ht0, hqt, hta⟩ := ENNReal.lt_iff_exists_real_btwn.1 hq.2
  have hqt' : q < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq.1).1 hqt
  have hvol : volume (Set.Ioo q t) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    have := (ae_restrict_iff' measurableSet_Ioi).1 hae
    filter_upwards [this] with d hd
    intro hdI
    have hsupp : d ∈ supp M.abar :=
      ⟨by linarith [hq.1, hdI.1], lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hdI.2.le) hta⟩
    have := hd hdI.1
    simp only [Pi.zero_apply] at this
    exact absurd this (hM.f_pos d hsupp).ne'
  rw [Real.volume_Ioo] at hvol
  exact absurd hvol (ENNReal.ofReal_pos.2 (by linarith)).ne'

lemma hasDerivAt_Fbar (M : Model) (hM : M.Std) (q : ℝ) (hq0 : 0 < q)
    (hqa : ENNReal.ofReal q < M.abar) : HasDerivAt (Fbar M.f) (-(M.f q)) q := by
  have hF : Fbar M.f = fun x => 1 - ∫ t in (0:ℝ)..x, M.f t := funext (Fbar_eq M hM)
  rw [hF]
  have hnhds : supp M.abar ∈ nhds q := by
    have hopen : IsOpen {x : ℝ | 0 < x ∧ ENNReal.ofReal x < M.abar} :=
      (isOpen_lt continuous_const continuous_id).inter
        (isOpen_lt ENNReal.continuous_ofReal continuous_const)
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨hq0, hqa⟩) (fun x hx => ⟨hx.1.le, hx.2⟩)
  have hca : ContinuousAt M.f q := hM.f_cont.continuousAt hnhds
  exact (intervalIntegral.integral_hasDerivAt_right hM.f_int.1.intervalIntegrable
    hM.f_meas.stronglyMeasurable.stronglyMeasurableAtFilter hca).const_sub 1

/-- `G(q) ≤ s/r` past `q̂*` (IGFR). -/
lemma G_le (M : Model) (hM : M.Std) (qh q : ℝ) (hqh : qh ∈ supp M.abar) (hq : q ∈ supp M.abar)
    (hle : qh ≤ q) (hGpos : 0 < G M.f qh) : G M.f q ≤ G M.f qh := by
  have hg := hM.igfr hqh hq hle
  simp only at hg
  have hFh := Fbar_pos M hM qh hqh
  have hFq := Fbar_pos M hM q hq
  set gh := qh * M.f qh / Fbar M.f qh
  set gq := q * M.f q / Fbar M.f q
  have eh : G M.f qh = Fbar M.f qh * (1 - gh) := by
    unfold G; simp only [gh]; field_simp
  have eq' : G M.f q = Fbar M.f q * (1 - gq) := by
    unfold G; simp only [gq]; field_simp
  have hgh : 0 < 1 - gh := by
    rw [eh] at hGpos; exact (pos_iff_pos_of_mul_pos hGpos).1 hFh
  have hanti := Fbar_anti M hM hle
  rw [eh, eq']
  rcases le_or_gt (1 - gq) 0 with h | h
  · nlinarith
  · calc Fbar M.f q * (1 - gq) ≤ Fbar M.f qh * (1 - gq) := mul_le_mul_of_nonneg_right hanti h.le
      _ ≤ Fbar M.f qh * (1 - gh) := mul_le_mul_of_nonneg_left (by linarith) hFh.le

/-- `ψ(q) = q (r F̄(q) − s)` is antitone on `[q̂*, ∞)`. -/
lemma psi_anti (M : Model) (hM : M.Std) (qh : ℝ) (hqh0 : 0 ≤ qh)
    (hqhe : M.r * G M.f qh = M.s) (hs0 : 0 < M.s) :
    AntitoneOn (fun q => q * (M.r * Fbar M.f q - M.s)) (Set.Ici qh) := by
  have hr := r_pos M hM
  have hGpos : 0 < G M.f qh := by
    by_contra hc; push_neg at hc; nlinarith
  have hqh_supp : qh ∈ supp M.abar := by
    refine ⟨hqh0, lt_of_not_ge (fun h => ?_)⟩
    have h1 := Fbar_out M hM qh h
    have h2 : M.f qh = 0 := hM.f_zero qh (fun hh => absurd hh.2 (not_lt.2 h))
    unfold G at hGpos; rw [h1, h2] at hGpos; simp at hGpos
  set ψ := fun q => q * (M.r * Fbar M.f q - M.s) with hψ
  have hψc : Continuous ψ := by
    have := Fbar_cont M hM; simp only [hψ]; fun_prop
  -- derivative inside the support
  have hderiv : ∀ x, qh < x → ENNReal.ofReal x < M.abar →
      HasDerivAt ψ ((M.r * Fbar M.f x - M.s) + x * (M.r * (-(M.f x)))) x := by
    intro x hx hxa
    have := hasDerivAt_Fbar M hM x (by linarith) hxa
    have h2 : HasDerivAt (fun y => y * (M.r * Fbar M.f y - M.s))
        (1 * (M.r * Fbar M.f x - M.s) + x * (M.r * -M.f x)) x :=
      HasDerivAt.fun_mul (hasDerivAt_id' x) ((this.const_mul M.r).sub_const M.s)
    rw [one_mul] at h2
    exact h2
  have hdnp : ∀ x, qh < x → ENNReal.ofReal x < M.abar →
      (M.r * Fbar M.f x - M.s) + x * (M.r * (-(M.f x))) ≤ 0 := by
    intro x hx hxa
    have hG := G_le M hM qh x hqh_supp ⟨by linarith, hxa⟩ hx.le hGpos
    unfold G at hG hqhe
    have : M.r * (Fbar M.f x - x * M.f x) ≤ M.r * (Fbar M.f qh - qh * M.f qh) :=
      mul_le_mul_of_nonneg_left hG hr.le
    linarith
  -- antitone on any convex set whose interior lies in the support
  have hanti : ∀ D : Set ℝ, Convex ℝ D → (∀ x ∈ interior D, qh < x ∧ ENNReal.ofReal x < M.abar) →
      AntitoneOn ψ D := by
    intro D hD hint
    refine antitoneOn_of_deriv_nonpos hD hψc.continuousOn
      (fun x hx => (hderiv x (hint x hx).1 (hint x hx).2).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [(hderiv x (hint x hx).1 (hint x hx).2).deriv]
    exact hdnp x (hint x hx).1 (hint x hx).2
  by_cases htop : M.abar = ⊤
  · refine hanti _ (convex_Ici qh) (fun x hx => ?_)
    rw [interior_Ici] at hx
    exact ⟨hx, by rw [htop]; exact ENNReal.ofReal_lt_top⟩
  · set A := M.abar.toReal
    have hofa : ENNReal.ofReal A = M.abar := ENNReal.ofReal_toReal htop
    have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
    have hqhA : qh < A := by
      have := hqh_supp.2; rw [← hofa] at this
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hqh0).1 this
    have h1 : AntitoneOn ψ (Set.Icc qh A) := by
      refine hanti _ (convex_Icc qh A) (fun x hx => ?_)
      rw [interior_Icc] at hx
      refine ⟨hx.1, ?_⟩
      rw [← hofa]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith [hx.1])).2 hx.2
    have hout : ∀ x, A ≤ x → ψ x = -(M.s * x) := by
      intro x hx
      simp only [hψ]
      rw [Fbar_out M hM x (by rw [← hofa]; exact ENNReal.ofReal_le_ofReal hx)]; ring
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    by_cases hyA : y ≤ A
    · exact h1 ⟨hx, le_trans hxy hyA⟩ ⟨hy, hyA⟩ hxy
    · push_neg at hyA
      by_cases hxA : A ≤ x
      · rw [hout x hxA, hout y (by linarith)]; nlinarith
      · push_neg at hxA
        calc ψ y = -(M.s * y) := hout y hyA.le
          _ ≤ -(M.s * A) := by nlinarith
          _ = ψ A := (hout A le_rfl).symm
          _ ≤ ψ x := h1 ⟨hx, hxA.le⟩ ⟨hqhA.le, le_rfl⟩ hxA.le

end T6Psi

open T6Fbar T6Psi in
theorem solution (M : Model) (hM : M.Std) (qo qh qc : ℝ)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hs : M.s < wo M qo qh)
    (hqc : qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh)) :
    qo < qc := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hs0 : 0 < M.s := by
    have := hM.assm1_s; have : 0 < M.c / M.p := div_pos hM.c_pos hp; linarith
  -- `q° > 0`
  have hqo_pos : 0 < qo := by
    rcases hqo.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := hqo.2
      rw [← h] at h2
      unfold G at h2
      rw [Fbar_zero M hM] at h2
      have := hM.assm1_r
      rw [div_lt_iff₀ hp] at this
      nlinarith
  by_cases hsr : M.s ≤ M.r
  · obtain ⟨hqh0, hqhe⟩ := hqh.1 hsr
    have hD : 0 < M.p * qo + (1 - M.p) * qh := by nlinarith
    have hφo : M.s * (M.p * qo + (1 - M.p) * qh) <
        M.r * (M.p * qo * Fbar M.f qo + (1 - M.p) * qh * Fbar M.f qh) := by
      unfold wo at hs
      rwa [lt_div_iff₀ hD] at hs
    by_contra hcon
    push_neg at hcon
    have hanti := psi_anti M hM qh hqh0 hqhe hs0 (show qc ∈ Set.Ici qh from hqc.1)
      (show qo ∈ Set.Ici qh from le_trans hqc.1 hcon) hcon
    simp only at hanti
    nlinarith [hqc.2]
  · exfalso
    have hrs : M.r < M.s := lt_of_not_ge hsr
    have h0 := hqh.2 hrs
    rw [h0] at hs
    unfold wo at hs
    simp only [mul_zero, zero_mul, add_zero] at hs
    rw [show M.r * (M.p * qo * Fbar M.f qo) / (M.p * qo) = M.r * Fbar M.f qo by
      field_simp] at hs
    nlinarith [Fbar_le_one M hM qo]
