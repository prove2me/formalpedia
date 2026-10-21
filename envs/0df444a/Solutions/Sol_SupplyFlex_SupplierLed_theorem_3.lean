-- Prove2me | solution 1 for SupplyFlex.SupplierLed.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:51:29.640291+00:00
-- url     : https://prove2.me/submissions/deb4797b-06cf-486a-9bef-10ffb482f4dd

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting
import Theorems.Thm_SupplyFlex_SupplierLed_qo_lt_qc

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
lemma psi_anti (M : Model) (hM : M.Std) (k : ℝ) (qh : ℝ) (hqh0 : 0 ≤ qh)
    (hqhe : M.r * G M.f qh = k) (hs0 : 0 < k) :
    AntitoneOn (fun q => q * (M.r * Fbar M.f q - k)) (Set.Ici qh) := by
  have hr := r_pos M hM
  have hGpos : 0 < G M.f qh := by
    by_contra hc; push_neg at hc; nlinarith
  have hqh_supp : qh ∈ supp M.abar := by
    refine ⟨hqh0, lt_of_not_ge (fun h => ?_)⟩
    have h1 := Fbar_out M hM qh h
    have h2 : M.f qh = 0 := hM.f_zero qh (fun hh => absurd hh.2 (not_lt.2 h))
    unfold G at hGpos; rw [h1, h2] at hGpos; simp at hGpos
  set ψ := fun q => q * (M.r * Fbar M.f q - k) with hψ
  have hψc : Continuous ψ := by
    have := Fbar_cont M hM; simp only [hψ]; fun_prop
  -- derivative inside the support
  have hderiv : ∀ x, qh < x → ENNReal.ofReal x < M.abar →
      HasDerivAt ψ ((M.r * Fbar M.f x - k) + x * (M.r * (-(M.f x)))) x := by
    intro x hx hxa
    have := hasDerivAt_Fbar M hM x (by linarith) hxa
    have h2 : HasDerivAt (fun y => y * (M.r * Fbar M.f y - k))
        (1 * (M.r * Fbar M.f x - k) + x * (M.r * -M.f x)) x :=
      HasDerivAt.fun_mul (hasDerivAt_id' x) ((this.const_mul M.r).sub_const k)
    rw [one_mul] at h2
    exact h2
  have hdnp : ∀ x, qh < x → ENNReal.ofReal x < M.abar →
      (M.r * Fbar M.f x - k) + x * (M.r * (-(M.f x))) ≤ 0 := by
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
    have hout : ∀ x, A ≤ x → ψ x = -(k * x) := by
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
        calc ψ y = -(k * y) := hout y hyA.le
          _ ≤ -(k * A) := by nlinarith
          _ = ψ A := (hout A le_rfl).symm
          _ ≤ ψ x := h1 ⟨hx, hxA.le⟩ ⟨hqhA.le, le_rfl⟩ hxA.le

end T6Psi

namespace T6Aux
open T6Fbar T6Psi

/-- Integrals against the demand law are integrals against `f`. -/
lemma integral_demandLaw (M : Model) (hM : M.Std) (g : ℝ → ℝ) :
    ∫ d, g d ∂(demandLaw M.f) = ∫ d, M.f d * g d := by
  unfold demandLaw
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (M.f x))
    hM.f_meas.ennreal_ofReal (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun d => ?_))
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (f_nonneg M hM d)]

lemma integrable_fmin (M : Model) (hM : M.Std) (z : ℝ) :
    Integrable (fun d => M.f d * min z d) := by
  have hb : Integrable (fun d => |z| * M.f d + |d * M.f d|) :=
    (hM.f_int.1.const_mul _).add hM.mean_fin.abs
  refine hb.mono' ?_ (Filter.Eventually.of_forall (fun d => ?_))
  · exact (hM.f_meas.mul (measurable_const.min measurable_id)).aestronglyMeasurable
  · have h0 := f_nonneg M hM d
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_mul, abs_of_nonneg h0]
    have : |min z d| ≤ |z| + |d| := by
      rcases le_total z d with h | h
      · rw [min_eq_left h]; linarith [abs_nonneg d]
      · rw [min_eq_right h]; linarith [abs_nonneg z]
    nlinarith

/-- `buyerExPost` as `r E[f · min(q, ·)] − w q`. -/
lemma buyerExPost_E (M : Model) (hM : M.Std) (w q : ℝ) :
    buyerExPost M w q = M.r * (∫ d, M.f d * min q d) - w * q := by
  unfold buyerExPost SupplyChainTheory.expSales; rw [integral_demandLaw M hM]

lemma kink_nonneg (a b d : ℝ) (hab : a < b) :
    0 ≤ 2 * min ((a + b) / 2) d - min a d - min b d := by
  simp only [min_def]; split_ifs <;> linarith

lemma kink_pos (a b d : ℝ) (h1 : a < d) (h2 : d < b) :
    0 < 2 * min ((a + b) / 2) d - min a d - min b d := by
  simp only [min_def]; split_ifs <;> linarith

lemma buyer_unique_aux (M : Model) (hM : M.Std) (w : ℝ) (hw : 0 < w) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (hma : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w a)
    (hmb : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w b) : False := by
  have hr := r_pos M hM
  set m := (a + b) / 2 with hm
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have e1 := hma m hm0
  have e2 := hmb a ha
  have e3 := hma b (by linarith)
  simp only [buyerExPost_E M hM] at e1 e2 e3
  set Ea := ∫ d, M.f d * min a d
  set Eb := ∫ d, M.f d * min b d
  set Em := ∫ d, M.f d * min m d
  have hk : ∫ d, M.f d * (2 * min m d - min a d - min b d) = 2 * Em - Ea - Eb := by
    have : (fun d => M.f d * (2 * min m d - min a d - min b d)) =
        fun d => (2 * (M.f d * min m d) - M.f d * min a d) - M.f d * min b d := by
      funext d; ring
    have i1 : Integrable (fun d => 2 * (M.f d * min m d)) := (integrable_fmin M hM m).const_mul 2
    have i2 : Integrable (fun d => 2 * (M.f d * min m d) - M.f d * min a d) :=
      i1.sub (integrable_fmin M hM a)
    rw [this, integral_sub i2 (integrable_fmin M hM b), integral_sub i1 (integrable_fmin M hM a),
      integral_const_mul]
  have hint : Integrable (fun d => M.f d * (2 * min m d - min a d - min b d)) := by
    have : (fun d => M.f d * (2 * min m d - min a d - min b d)) =
        fun d => (2 * (M.f d * min m d) - M.f d * min a d) - M.f d * min b d := by
      funext d; ring
    rw [this]
    exact (((integrable_fmin M hM m).const_mul 2).sub (integrable_fmin M hM a)).sub
      (integrable_fmin M hM b)
  have hnn : 0 ≤ fun d => M.f d * (2 * min m d - min a d - min b d) :=
    fun d => mul_nonneg (f_nonneg M hM d) (kink_nonneg a b d hab)
  have hle : 2 * Em - Ea - Eb ≤ 0 := by
    have : M.r * (2 * Em - Ea - Eb) ≤ 0 := by nlinarith
    by_contra hc; push_neg at hc; nlinarith
  have hzero : ∫ d, M.f d * (2 * min m d - min a d - min b d) = 0 := by
    rw [hk]; exact le_antisymm hle (hk ▸ integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 hzero
  -- the support ends at or before `a`
  have habar : M.abar ≤ ENNReal.ofReal a := by
    by_contra hc
    push_neg at hc
    obtain ⟨t, ht0, hat, htb⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
    have hat' : a < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).1 hat
    set d0 := min t b
    have had0 : a < d0 := lt_min hat' hab
    have hvol : volume (Set.Ioo a d0) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with d hd
      intro hdI
      have hsupp : d ∈ supp M.abar := by
        refine ⟨by linarith [hdI.1], ?_⟩
        calc ENNReal.ofReal d ≤ ENNReal.ofReal t :=
              ENNReal.ofReal_le_ofReal (le_trans hdI.2.le (min_le_left _ _))
          _ < M.abar := htb
      have := mul_pos (hM.f_pos d hsupp)
        (kink_pos a b d hdI.1 (lt_of_lt_of_le hdI.2 (min_le_right _ _)))
      simp only [Pi.zero_apply] at hd
      linarith
    rw [Real.volume_Ioo] at hvol
    have : 0 < d0 - a := by linarith
    exact absurd hvol (ENNReal.ofReal_pos.2 this).ne'
  have hfz : ∀ d, a ≤ d → M.f d = 0 := by
    intro d hd
    refine hM.f_zero d (fun h => ?_)
    have := h.2
    have : ENNReal.ofReal a ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal hd
    exact absurd (lt_of_lt_of_le h.2 (le_trans habar this)) (lt_irrefl _)
  have hEab : Eb = Ea := by
    have : ∀ d, M.f d * min b d = M.f d * min a d := by
      intro d
      rcases le_or_gt d a with h | h
      · rw [min_eq_right h, min_eq_right (by linarith)]
      · rw [hfz d h.le, zero_mul, zero_mul]
    simp only [Eb, Ea, this]
  rw [hEab] at e2 e3
  nlinarith

lemma buyer_unique (M : Model) (hM : M.Std) (w : ℝ) (hw : 0 < w) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hma : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w a)
    (hmb : ∀ q, 0 ≤ q → buyerExPost M w q ≤ buyerExPost M w b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact (buyer_unique_aux M hM w hw a b ha h hma hmb).elim
  · exact h
  · exact (buyer_unique_aux M hM w hw b a hb h hmb hma).elim

/-- With guaranteed fraction `1` the delivery equals the order. -/
lemma Z_b1 (M : Model) (k : Regime) (σ : Profile) (h : IsSPE M k σ) (w q y : ℝ) (α : Bool)
    (hadm : Admissible k w 1) (hq : 0 ≤ q) (hy : 0 ≤ y) : σ.Z w 1 q y α = q := by
  have := (h.1 w 1 q y α hadm hq hy).1.1
  rw [one_mul] at this
  exact le_antisymm this.2 this.1

lemma orderValue_b1 (M : Model) (k : Regime) (σ : Profile) (h : IsSPE M k σ) (w q : ℝ)
    (hadm : Admissible k w 1) (hq : 0 ≤ q) : orderValue M σ w 1 q = buyerExPost M w q := by
  unfold orderValue Eα
  have hy := (h.2.1 w 1 q hadm hq).1
  beta_reduce
  rw [Z_b1 M k σ h w q _ true hadm hq hy, Z_b1 M k σ h w q _ false hadm hq hy]
  ring

lemma prodValue_b1 (M : Model) (k : Regime) (σ : Profile) (h : IsSPE M k σ) (w q y : ℝ)
    (hadm : Admissible k w 1) (hq : 0 ≤ q) (hy : 0 ≤ y) :
    prodValue M σ w 1 q y = Eα M.p (fun α => supplierExPost M w y q α) := by
  unfold prodValue Eα
  beta_reduce
  rw [Z_b1 M k σ h w q y true hadm hq hy, Z_b1 M k σ h w q y false hadm hq hy]

end T6Aux

namespace T2
open T6Fbar T6Psi T6Aux

lemma T_nonneg (M : Model) (hM : M.Std) (z : ℝ) : 0 ≤ ∫ x in Set.Ioc 0 z, x * M.f x :=
  setIntegral_nonneg measurableSet_Ioc (fun x hx => mul_nonneg hx.1.le (f_nonneg M hM x))

lemma T_mono (M : Model) (hM : M.Std) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc 0 a, x * M.f x ≤ ∫ x in Set.Ioc 0 b, x * M.f x := by
  refine setIntegral_mono_set hM.mean_fin.integrableOn ?_
    (Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_right hab))
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall (fun x hx => ?_))
  exact mul_nonneg hx.1.le (f_nonneg M hM x)

lemma T_zero (M : Model) : ∫ x in Set.Ioc 0 (0:ℝ), x * M.f x = 0 := by simp



lemma supp_lower (M : Model) {x q : ℝ} (hx : 0 ≤ x) (hxq : x ≤ q) (hq : q ∈ supp M.abar) :
    x ∈ supp M.abar :=
  ⟨hx, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hxq) hq.2⟩

lemma Fbar_strict (M : Model) (hM : M.Std) {x q : ℝ} (hx : 0 ≤ x) (hxq : x < q)
    (hq : q ∈ supp M.abar) : Fbar M.f q < Fbar M.f x := by
  rw [Fbar_eq M hM x, Fbar_eq M hM q]
  have h := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := x) (c := q)
    (μ := volume) (f := M.f) hM.f_int.1.intervalIntegrable hM.f_int.1.intervalIntegrable
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (f := M.f)
    hM.f_int.1.intervalIntegrable
    (fun t ht => hM.f_pos t (supp_lower M (by linarith [ht.1]) ht.2.le hq)) hxq
  linarith

lemma root_supp (M : Model) (hM : M.Std) (k q0 : ℝ) (hk : 0 < k) (hq00 : 0 ≤ q0)
    (hq0e : M.r * G M.f q0 = k) : q0 ∈ supp M.abar := by
  have hr := r_pos M hM
  have hGpos : 0 < G M.f q0 := by
    by_contra hc; push_neg at hc; nlinarith
  refine ⟨hq00, lt_of_not_ge (fun h => ?_)⟩
  have h1 := Fbar_out M hM q0 h
  have h2 : M.f q0 = 0 := hM.f_zero q0 (fun hh => absurd hh.2 (not_lt.2 h))
  unfold G at hGpos; rw [h1, h2] at hGpos; simp at hGpos

lemma G_fac (M : Model) (hM : M.Std) (x : ℝ) (hx : x ∈ supp M.abar) :
    G M.f x = Fbar M.f x * (1 - x * M.f x / Fbar M.f x) := by
  have := Fbar_pos M hM x hx
  unfold G; field_simp

lemma G_ge (M : Model) (hM : M.Std) {x q : ℝ} (hx : x ∈ supp M.abar) (hq : q ∈ supp M.abar)
    (hxq : x ≤ q) (hGq : 0 < G M.f q) : G M.f q ≤ G M.f x := by
  have hg := hM.igfr hx hq hxq
  simp only at hg
  have hFx := Fbar_pos M hM x hx
  have hFq := Fbar_pos M hM q hq
  have hanti := Fbar_anti M hM hxq
  rw [G_fac M hM x hx, G_fac M hM q hq] at *
  have h1 : 0 < 1 - q * M.f q / Fbar M.f q := (pos_iff_pos_of_mul_pos hGq).1 hFq
  calc Fbar M.f q * (1 - q * M.f q / Fbar M.f q)
      ≤ Fbar M.f x * (1 - q * M.f q / Fbar M.f q) := mul_le_mul_of_nonneg_right hanti h1.le
    _ ≤ Fbar M.f x * (1 - x * M.f x / Fbar M.f x) :=
        mul_le_mul_of_nonneg_left (by linarith) hFx.le

lemma G_strict (M : Model) (hM : M.Std) {x q : ℝ} (hx : x ∈ supp M.abar) (hq : q ∈ supp M.abar)
    (hxq : x < q) (hGq : 0 < G M.f q) : G M.f q < G M.f x := by
  have hg := hM.igfr hx hq hxq.le
  simp only at hg
  have hFx := Fbar_pos M hM x hx
  have hFq := Fbar_pos M hM q hq
  have hstr := Fbar_strict M hM hx.1 hxq hq
  rw [G_fac M hM x hx, G_fac M hM q hq] at *
  have h1 : 0 < 1 - q * M.f q / Fbar M.f q := (pos_iff_pos_of_mul_pos hGq).1 hFq
  calc Fbar M.f q * (1 - q * M.f q / Fbar M.f q)
      < Fbar M.f x * (1 - q * M.f q / Fbar M.f q) := mul_lt_mul_of_pos_right hstr h1
    _ ≤ Fbar M.f x * (1 - x * M.f x / Fbar M.f x) :=
        mul_le_mul_of_nonneg_left (by linarith) hFx.le

lemma hderiv_psi (M : Model) (hM : M.Std) (k x : ℝ) (hx0 : 0 < x)
    (hxa : ENNReal.ofReal x < M.abar) :
    HasDerivAt (fun q => q * (M.r * Fbar M.f q - k)) (M.r * G M.f x - k) x := by
  have := hasDerivAt_Fbar M hM x hx0 hxa
  have h2 : HasDerivAt (fun y => y * (M.r * Fbar M.f y - k))
      (1 * (M.r * Fbar M.f x - k) + x * (M.r * -M.f x)) x :=
    HasDerivAt.fun_mul (hasDerivAt_id' x) ((this.const_mul M.r).sub_const k)
  convert h2 using 1
  unfold G; ring

lemma psi_mono (M : Model) (hM : M.Std) (k q0 : ℝ) (hk : 0 < k) (hq00 : 0 ≤ q0)
    (hq0e : M.r * G M.f q0 = k) :
    MonotoneOn (fun q => q * (M.r * Fbar M.f q - k)) (Set.Icc 0 q0) := by
  have hr := r_pos M hM
  have hq0s := root_supp M hM k q0 hk hq00 hq0e
  have hGq0 : 0 < G M.f q0 := by
    by_contra hc; push_neg at hc; nlinarith
  have hc : Continuous (fun q => q * (M.r * Fbar M.f q - k)) := by
    have := Fbar_cont M hM; fun_prop
  have hint : ∀ x ∈ interior (Set.Icc (0:ℝ) q0), 0 < x ∧ x ∈ supp M.abar := by
    intro x hx
    rw [interior_Icc] at hx
    exact ⟨hx.1, supp_lower M hx.1.le hx.2.le hq0s⟩
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 q0) hc.continuousOn
    (fun x hx => (hderiv_psi M hM k x (hint x hx).1
      (hint x hx).2.2).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
  rw [(hderiv_psi M hM k x (hint x hx).1 (hint x hx).2.2).deriv]
  have := G_ge M hM (hint x hx).2 hq0s (by rw [interior_Icc] at hx; exact hx.2.le) hGq0
  nlinarith

lemma psi_unique (M : Model) (hM : M.Std) (k q0 : ℝ) (hk : 0 < k) (hq0 : 0 < q0)
    (hq0e : M.r * G M.f q0 = k) (q : ℝ) (hq : 0 ≤ q)
    (heq : q * (M.r * Fbar M.f q - k) = q0 * (M.r * Fbar M.f q0 - k)) : q = q0 := by
  have hr := r_pos M hM
  set ψ := fun q => q * (M.r * Fbar M.f q - k) with hψ
  have hq0s := root_supp M hM k q0 hk hq0.le hq0e
  have hanti := psi_anti M hM k q0 hq0.le hq0e hk
  have hmono := psi_mono M hM k q0 hk hq0.le hq0e
  -- on an open interval where `ψ` is constant, `rG = k`
  have hconst : ∀ a b : ℝ, (∀ m ∈ Set.Ioo a b, ψ m = ψ q0) → ∀ m ∈ Set.Ioo a b, 0 < m →
      ENNReal.ofReal m < M.abar → M.r * G M.f m = k := by
    intro a b hab m hm hm0 hma
    have hev : ψ =ᶠ[nhds m] fun _ => ψ q0 :=
      Filter.eventually_of_mem (Ioo_mem_nhds hm.1 hm.2) (fun x hx => hab x hx)
    have h0 : HasDerivAt ψ 0 m := (hasDerivAt_const m (ψ q0)).congr_of_eventuallyEq hev
    have h1 := hderiv_psi M hM k m hm0 hma
    have := h1.unique h0
    linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `q < q0`
    have hc : ∀ m ∈ Set.Ioo q q0, ψ m = ψ q0 := by
      intro m hm
      have h1 := hmono ⟨hq, hlt.le⟩ ⟨by linarith [hm.1], hm.2.le⟩ hm.1.le
      have h2 := hmono ⟨by linarith [hm.1], hm.2.le⟩ ⟨hq0.le, le_rfl⟩ hm.2.le
      simp only [hψ] at h1 h2 heq ⊢
      linarith
    set m1 := q + (q0 - q) / 3
    set m2 := q + 2 * (q0 - q) / 3
    have hm1 : m1 ∈ Set.Ioo q q0 := ⟨by simp only [m1]; linarith, by simp only [m1]; linarith⟩
    have hm2 : m2 ∈ Set.Ioo q q0 := ⟨by simp only [m2]; linarith, by simp only [m2]; linarith⟩
    have hs1 := supp_lower M (by linarith [hm1.1]) hm1.2.le hq0s
    have hs2 := supp_lower M (by linarith [hm2.1]) hm2.2.le hq0s
    have e1 := hconst q q0 hc m1 hm1 (by linarith [hm1.1]) hs1.2
    have e2 := hconst q q0 hc m2 hm2 (by linarith [hm2.1]) hs2.2
    have hG2 : 0 < G M.f m2 := by
      by_contra h; push_neg at h; nlinarith
    have := G_strict M hM hs1 hs2 (by simp only [m1, m2]; linarith) hG2
    nlinarith
  · -- `q > q0`
    obtain ⟨t, ht0, hqt, hta⟩ := ENNReal.lt_iff_exists_real_btwn.1 hq0s.2
    have hqt' : q0 < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq0.le).1 hqt
    set u := min q t
    have hu : q0 < u := lt_min hgt hqt'
    have hc : ∀ m ∈ Set.Ioo q0 u, ψ m = ψ q0 := by
      intro m hm
      have hmq : m ≤ q := le_trans hm.2.le (min_le_left _ _)
      have h1 := hanti (show q0 ∈ Set.Ici q0 from Set.mem_Ici.2 le_rfl) (show m ∈ Set.Ici q0 from hm.1.le)
        hm.1.le
      have h2 := hanti (show m ∈ Set.Ici q0 from hm.1.le) (show q ∈ Set.Ici q0 from hgt.le) hmq
      simp only [hψ] at h1 h2 heq ⊢
      linarith
    have hus : ∀ m, m < u → ENNReal.ofReal m < M.abar := fun m hm =>
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_trans hm.le (min_le_right _ _))) hta
    set m1 := q0 + (u - q0) / 3
    set m2 := q0 + 2 * (u - q0) / 3
    have hm1 : m1 ∈ Set.Ioo q0 u := ⟨by simp only [m1]; linarith, by simp only [m1]; linarith⟩
    have hm2 : m2 ∈ Set.Ioo q0 u := ⟨by simp only [m2]; linarith, by simp only [m2]; linarith⟩
    have hs1 : m1 ∈ supp M.abar := ⟨by linarith [hm1.1], hus m1 hm1.2⟩
    have hs2 : m2 ∈ supp M.abar := ⟨by linarith [hm2.1], hus m2 hm2.2⟩
    have e1 := hconst q0 u hc m1 hm1 (by linarith [hm1.1]) hs1.2
    have e2 := hconst q0 u hc m2 hm2 (by linarith [hm2.1]) hs2.2
    have hG2 : 0 < G M.f m2 := by
      by_contra h; push_neg at h; nlinarith
    have := G_strict M hM hs1 hs2 (by simp only [m1, m2]; linarith) hG2
    nlinarith

lemma Fbar_lt_one (M : Model) (hM : M.Std) (q : ℝ) (hq : 0 < q) : Fbar M.f q < 1 := by
  obtain ⟨t, ht0, h0t, hta⟩ := ENNReal.lt_iff_exists_real_btwn.1 hM.abar_pos
  have ht : 0 < t := ENNReal.ofReal_pos.1 h0t
  set u := min q t
  have hu0 : 0 < u := lt_min hq ht
  have hus : u ∈ supp M.abar :=
    ⟨hu0.le, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_right _ _)) hta⟩
  have h1 := Fbar_strict M hM le_rfl hu0 hus
  rw [Fbar_zero M hM] at h1
  exact lt_of_le_of_lt (Fbar_anti M hM (min_le_left q t)) h1

/-- Supporting line of the expected sales. -/
lemma E_support (M : Model) (hM : M.Std) (q q' : ℝ) :
    (∫ d, M.f d * min q' d) - ∫ d, M.f d * min q d ≤ (q' - q) * Fbar M.f q := by
  rw [← integral_sub (integrable_fmin M hM q') (integrable_fmin M hM q)]
  have hR : (q' - q) * Fbar M.f q =
      ∫ d, (Set.Ioi q).indicator (fun d => (q' - q) * M.f d) d := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul]; rfl
  rw [hR]
  refine integral_mono ((integrable_fmin M hM q').sub (integrable_fmin M hM q))
    ((hM.f_int.1.const_mul _).indicator measurableSet_Ioi) (fun d => ?_)
  have hf := f_nonneg M hM d
  by_cases hd : d ∈ Set.Ioi q
  · rw [Set.indicator_of_mem hd]
    simp only [Set.mem_Ioi] at hd
    rw [min_eq_left hd.le]
    have : min q' d - q ≤ q' - q := by linarith [min_le_left q' d]
    nlinarith
  · rw [Set.indicator_of_notMem hd]
    simp only [Set.mem_Ioi, not_lt] at hd
    rw [min_eq_right hd]
    have : min q' d - d ≤ 0 := by linarith [min_le_right q' d]
    nlinarith

lemma bEP_support (M : Model) (hM : M.Std) (w q q' : ℝ) :
    buyerExPost M w q' ≤ buyerExPost M w q + (q' - q) * (M.r * Fbar M.f q - w) := by
  rw [buyerExPost_E M hM, buyerExPost_E M hM]
  have := mul_le_mul_of_nonneg_left (E_support M hM q q') (r_pos M hM).le
  nlinarith

lemma BR_zero (M : Model) (hM : M.Std) (w : ℝ) (hw : M.r ≤ w) :
    ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w 0 := by
  intro q' hq'
  have := bEP_support M hM w 0 q'
  rw [Fbar_zero M hM] at this
  nlinarith

lemma exists_Fbar_eq (M : Model) (hM : M.Std) (w : ℝ) (hw : 0 < w) (hwr : w < M.r) :
    ∃ q, 0 ≤ q ∧ M.r * Fbar M.f q = w := by
  have hr := r_pos M hM
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1
    ((Fbar_tendsto M hM).eventually (gt_mem_nhds (div_pos hw hr)))
  set b' := max b 0
  have hb' := hb b' (le_max_left _ _)
  have hcont : ContinuousOn (fun q => M.r * Fbar M.f q) (Set.Icc 0 b') :=
    (continuous_const.mul (Fbar_cont M hM)).continuousOn
  have hlo : M.r * Fbar M.f b' ≤ w := by
    rw [lt_div_iff₀ hr] at hb'; linarith
  obtain ⟨q, hq, hqw⟩ := intermediate_value_Icc' (le_max_right b 0) hcont
    ⟨hlo, by rw [Fbar_zero M hM]; linarith⟩
  exact ⟨q, hq.1, hqw⟩

lemma BR_exists (M : Model) (hM : M.Std) (w : ℝ) (hw : 0 < w) :
    ∃ q, 0 ≤ q ∧ ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w q := by
  by_cases hwr : M.r ≤ w
  · exact ⟨0, le_rfl, BR_zero M hM w hwr⟩
  · obtain ⟨q, hq, hqw⟩ := exists_Fbar_eq M hM w hw (lt_of_not_ge hwr)
    refine ⟨q, hq, fun q' _ => ?_⟩
    have := bEP_support M hM w q q'
    rw [hqw, sub_self, mul_zero, add_zero] at this
    exact this

lemma BR_char (M : Model) (hM : M.Std) (w : ℝ) (hw : 0 < w) (q : ℝ) (hq : 0 ≤ q)
    (hmax : ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w q) :
    (M.r ≤ w → q = 0) ∧ (w < M.r → M.r * Fbar M.f q = w) := by
  constructor
  · intro hwr
    exact buyer_unique M hM w hw q 0 hq le_rfl hmax (BR_zero M hM w hwr)
  · intro hwr
    obtain ⟨q1, hq1, hq1w⟩ := exists_Fbar_eq M hM w hw hwr
    have hm1 : ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w q1 := fun q' _ => by
      have := bEP_support M hM w q1 q'
      rw [hq1w, sub_self, mul_zero, add_zero] at this
      exact this
    rw [buyer_unique M hM w hw q q1 hq hq1 hmax hm1]
    exact hq1w

/-- Expected supplier profit from input `y` when the delivery is `q`. -/
lemma prod_eq (M : Model) (w q y : ℝ) (hq : 0 ≤ q) :
    Eα M.p (fun α => supplierExPost M w y q α) =
      w * q - M.c * y - M.s * (M.p * max (q - y) 0 + (1 - M.p) * q) := by
  unfold Eα supplierExPost
  simp only [if_true, Bool.false_eq_true, if_false, sub_zero, max_eq_left hq]
  ring

lemma prod_lt (M : Model) (hM : M.Std) (w q y : ℝ) (hq : 0 ≤ q) (hne : y ≠ q) :
    Eα M.p (fun α => supplierExPost M w y q α) < Eα M.p (fun α => supplierExPost M w q q α) := by
  rw [prod_eq M w q y hq, prod_eq M w q q hq, sub_self, max_eq_left le_rfl]
  have hc := hM.c_pos
  have hps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hM.p_pos] at this; linarith
  rcases lt_or_gt_of_ne hne with h | h
  · rw [max_eq_left (by linarith)]; nlinarith
  · rw [max_eq_right (by linarith)]; nlinarith

lemma Y_eq (M : Model) (hM : M.Std) (σ : Profile) (h : IsSPE M .priceOnly σ) (w q : ℝ)
    (hw : 0 < w) (hq : 0 ≤ q) : σ.Y w 1 q = q := by
  have hadm : Admissible .priceOnly w 1 := ⟨hw, rfl⟩
  obtain ⟨hY0, hY⟩ := h.2.1 w 1 q hadm hq
  by_contra hne
  have h1 := hY q hq
  rw [prodValue_b1 M _ σ h w q q hadm hq hq, prodValue_b1 M _ σ h w q _ hadm hq hY0] at h1
  exact absurd h1 (not_le.2 (prod_lt M hM w q _ hq hne))

lemma CV_eq (M : Model) (hM : M.Std) (σ : Profile) (h : IsSPE M .priceOnly σ) (w : ℝ)
    (hw : 0 < w) :
    contractValue M σ w 1 = σ.Q w 1 * (w - (M.c + (1 - M.p) * M.s)) := by
  have hadm : Admissible .priceOnly w 1 := ⟨hw, rfl⟩
  have hQ0 := (h.2.2.1 w 1 hadm).1
  unfold contractValue
  rw [Y_eq M hM σ h w _ hw hQ0, prodValue_b1 M _ σ h w _ _ hadm hQ0 hQ0, prod_eq M w _ _ hQ0,
    sub_self, max_eq_left le_rfl]
  ring

end T2


namespace Flex
open T6Fbar T6Psi T6Aux T2

/-- The continuation clauses of a subgame-perfect equilibrium of the flexibility game. -/
def ContOK (M : Model) (σ : Profile) : Prop :=
  (∀ w b q y : ℝ, ∀ α : Bool, Admissible .flex w b → 0 ≤ q → 0 ≤ y →
      IsLeast {z | z ∈ Set.Icc (b * q) q ∧
                   ∀ z' ∈ Set.Icc (b * q) q, supplierExPost M w y z' α ≤ supplierExPost M w y z α}
        (σ.Z w b q y α)) ∧
  (∀ w b q : ℝ, Admissible .flex w b → 0 ≤ q →
      0 ≤ σ.Y w b q ∧ ∀ y', 0 ≤ y' → prodValue M σ w b q y' ≤ prodValue M σ w b q (σ.Y w b q)) ∧
  (∀ w b : ℝ, Admissible .flex w b →
      0 ≤ σ.Q w b ∧ ∀ q', 0 ≤ q' → orderValue M σ w b q' ≤ orderValue M σ w b (σ.Q w b))

lemma contOK_of (M : Model) (σ : Profile) (h : IsSPE M .flex σ) : ContOK M σ :=
  ⟨h.1, h.2.1, h.2.2.1⟩



lemma Z_false (M : Model) (σ : Profile) (h : ContOK M σ) (w b q y : ℝ)
    (hadm : Admissible .flex w b) (hq : 0 ≤ q) (hy : 0 ≤ y) :
    σ.Z w b q y false = if M.s < w then q else b * q := by
  obtain ⟨⟨hmem, hmax⟩, hlow⟩ := h.1 w b q y false hadm hq hy
  have hb0 := hadm.2.1
  have hb1 := hadm.2.2
  have hbq : b * q ≤ q := by nlinarith
  have hbq0 : 0 ≤ b * q := mul_nonneg hb0 hq
  have hπ : ∀ z', 0 ≤ z' → supplierExPost M w y z' false = (w - M.s) * z' - M.c * y := by
    intro z' hz'
    unfold supplierExPost
    simp only [Bool.false_eq_true, if_false, sub_zero, max_eq_left hz']
    ring
  have hz0 : 0 ≤ σ.Z w b q y false := le_trans hbq0 hmem.1
  split_ifs with hsw
  · have h1 := hmax q ⟨hbq, le_rfl⟩
    rw [hπ q hq, hπ _ hz0] at h1
    have : q ≤ σ.Z w b q y false := by
      by_contra hc; push_neg at hc; nlinarith
    exact le_antisymm hmem.2 this
  · push_neg at hsw
    have hS : b * q ∈ {z | z ∈ Set.Icc (b * q) q ∧ ∀ z' ∈ Set.Icc (b * q) q,
        supplierExPost M w y z' false ≤ supplierExPost M w y z false} := by
      refine ⟨⟨le_rfl, hbq⟩, fun z' hz' => ?_⟩
      rw [hπ z' (le_trans hbq0 hz'.1), hπ _ hbq0]
      nlinarith [hz'.1]
    exact le_antisymm (hlow hS) hmem.1

lemma Z_true (M : Model) (σ : Profile) (h : ContOK M σ) (w b q y : ℝ)
    (hadm : Admissible .flex w b) (hq : 0 ≤ q) (hy : 0 ≤ y) :
    σ.Z w b q y true = if M.s < w then q else max (b * q) (min y q) := by
  obtain ⟨⟨hmem, hmax⟩, hlow⟩ := h.1 w b q y true hadm hq hy
  have hw := hadm.1
  have hb0 := hadm.2.1
  have hb1 := hadm.2.2
  have hbq : b * q ≤ q := by nlinarith
  have hbq0 : 0 ≤ b * q := mul_nonneg hb0 hq
  have hπ : ∀ z', supplierExPost M w y z' true = w * z' - M.c * y - M.s * max (z' - y) 0 := by
    intro z'; unfold supplierExPost; simp
  set z := σ.Z w b q y true with hz
  split_ifs with hsw
  · by_contra hne
    have hlt : z < q := lt_of_le_of_ne hmem.2 hne
    have h1 := hmax q ⟨hbq, le_rfl⟩
    rw [hπ, hπ] at h1
    have hm : max (q - y) 0 - max (z - y) 0 ≤ q - z := by
      simp only [max_def]; split_ifs <;> linarith
    have hm' : 0 ≤ max (q - y) 0 - max (z - y) 0 := by
      simp only [max_def]; split_ifs <;> linarith
    rcases le_or_gt 0 M.s with h0 | h0
    · nlinarith
    · nlinarith
  · push_neg at hsw
    set m := max (b * q) (min y q) with hmdef
    have hm1 : b * q ≤ m := le_max_left _ _
    have hm2 : m ≤ q := max_le hbq (min_le_right _ _)
    have hmax_m : ∀ z' ∈ Set.Icc (b * q) q,
        supplierExPost M w y z' true ≤ supplierExPost M w y m true := by
      intro z' hz'
      rw [hπ, hπ]
      obtain ⟨hz1, hz2⟩ := hz'
      simp only [hmdef, max_def, min_def]
      split_ifs <;> nlinarith
    have hS : m ∈ {z | z ∈ Set.Icc (b * q) q ∧ ∀ z' ∈ Set.Icc (b * q) q,
        supplierExPost M w y z' true ≤ supplierExPost M w y z true} := ⟨⟨hm1, hm2⟩, hmax_m⟩
    have hzm : z ≤ m := hlow hS
    refine le_antisymm hzm ?_
    by_contra hlt
    push_neg at hlt
    have h1 := hmax m ⟨hm1, hm2⟩
    rw [hπ, hπ] at h1
    have hzy : z < y := by
      have : z < min y q := by
        rcases le_total (b * q) (min y q) with hh | hh
        · rw [hmdef, max_eq_right hh] at hlt; exact hlt
        · rw [hmdef, max_eq_left hh] at hlt; linarith [hmem.1]
      exact lt_of_lt_of_le this (min_le_left _ _)
    have hmy : m ≤ y := by
      rcases le_total (b * q) (min y q) with hh | hh
      · rw [hmdef, max_eq_right hh]; exact min_le_left _ _
      · rw [hmdef, max_eq_left hh] at hlt ⊢; linarith [hmem.1]
    rw [max_eq_right (by linarith : z - y ≤ 0), max_eq_right (by linarith : m - y ≤ 0)] at h1
    nlinarith

/-- The supplier's expected profit from input `y` under the equilibrium delivery rule. -/
noncomputable def pv (M : Model) (w b q y : ℝ) : ℝ :=
  M.p * (w * (if M.s < w then q else max (b * q) (min y q)) - M.c * y -
      M.s * max ((if M.s < w then q else max (b * q) (min y q)) - y) 0) +
    (1 - M.p) * (w * (if M.s < w then q else b * q) - M.c * y -
      M.s * max (if M.s < w then q else b * q) 0)

lemma prodValue_eq (M : Model) (σ : Profile) (h : ContOK M σ) (w b q y : ℝ)
    (hadm : Admissible .flex w b) (hq : 0 ≤ q) (hy : 0 ≤ y) :
    prodValue M σ w b q y = pv M w b q y := by
  unfold prodValue Eα pv
  beta_reduce
  rw [Z_true M σ h w b q y hadm hq hy, Z_false M σ h w b q y hadm hq hy]
  unfold supplierExPost
  simp only [if_true, Bool.false_eq_true, if_false, sub_zero]

lemma pv_hi (M : Model) (w b q y : ℝ) (hsw : M.s < w) (hq : 0 ≤ q) :
    pv M w b q y = w * q - M.c * y - M.s * (M.p * max (q - y) 0 + (1 - M.p) * q) := by
  unfold pv; simp only [if_pos hsw, max_eq_left hq]; ring

lemma pv_mid (M : Model) (w b q y : ℝ) (hsw : ¬ M.s < w) (hq : 0 ≤ q) (hb0 : 0 ≤ b) :
    pv M w b q y = M.p * (w * max (b * q) (min y q) - M.c * y -
      M.s * max (max (b * q) (min y q) - y) 0) +
      (1 - M.p) * (w * (b * q) - M.c * y - M.s * (b * q)) := by
  unfold pv; simp only [if_neg hsw, max_eq_left (mul_nonneg hb0 hq)]

/-- Above `s`, input `q` is strictly optimal. -/
lemma pv_hi_lt (M : Model) (hM : M.Std) (w b q y : ℝ) (hsw : M.s < w) (hq : 0 ≤ q) (hne : y ≠ q) :
    pv M w b q y < pv M w b q q := by
  rw [pv_hi M w b q y hsw hq, pv_hi M w b q q hsw hq, sub_self, max_eq_left le_rfl]
  have hc := hM.c_pos
  have hps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hM.p_pos] at this; linarith
  rcases lt_or_gt_of_ne hne with h | h
  · rw [max_eq_left (by linarith)]; nlinarith
  · rw [max_eq_right (by linarith)]; nlinarith

lemma pv_hi_q (M : Model) (w b q : ℝ) (hsw : M.s < w) (hq : 0 ≤ q) :
    pv M w b q q = q * (w - (M.c + (1 - M.p) * M.s)) := by
  rw [pv_hi M w b q q hsw hq, sub_self, max_eq_left le_rfl]; ring

lemma pv_mid_q (M : Model) (w b q : ℝ) (hsw : ¬ M.s < w) (hq : 0 ≤ q) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) :
    pv M w b q q = M.p * (w * q - M.c * q) + (1 - M.p) * (w * (b * q) - M.c * q - M.s * (b * q)) := by
  rw [pv_mid M w b q q hsw hq hb0, min_self, max_eq_right (by nlinarith), sub_self,
    max_eq_left le_rfl]
  ring

/-- Between `c/p` and `s`, input `q` is optimal, strictly when `w > c/p`. -/
lemma pv_mid_le (M : Model) (hM : M.Std) (w b q y : ℝ) (hsw : ¬ M.s < w) (hcw : M.c / M.p ≤ w)
    (hq : 0 ≤ q) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hy : 0 ≤ y) :
    pv M w b q y ≤ pv M w b q q ∧ (M.c / M.p < w → y ≠ q → pv M w b q y < pv M w b q q) := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hc := hM.c_pos
  have hps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hpw : M.c ≤ M.p * w := by rw [div_le_iff₀ hp] at hcw; linarith
  have hbq : b * q ≤ q := by nlinarith
  have hbq0 : 0 ≤ b * q := mul_nonneg hb0 hq
  rw [pv_mid M w b q y hsw hq hb0, pv_mid M w b q q hsw hq hb0, min_self,
    max_eq_right hbq, sub_self, max_eq_left le_rfl]
  push_neg at hsw
  rcases le_total y (b * q) with h1 | h1
  · -- `y ≤ b q`
    rw [min_eq_left (le_trans h1 hbq), max_eq_left h1, max_eq_left (by linarith)]
    constructor
    · nlinarith
    · intro hcw' hne
      have : y < q ∨ b * q < q := by
        rcases lt_or_eq_of_le h1 with h | h
        · left; linarith
        · right; rw [← h]; exact lt_of_le_of_ne (le_trans h1 hbq) hne
      rcases lt_or_eq_of_le h1 with h | h
      · nlinarith
      · have hpw' : M.c < M.p * w := by rw [div_lt_iff₀ hp] at hcw'; linarith
        rw [h] at hne ⊢
        have : b * q < q := lt_of_le_of_ne hbq hne
        nlinarith
  · rcases le_total y q with h2 | h2
    · -- `b q ≤ y ≤ q`
      rw [min_eq_left h2, max_eq_right h1, sub_self, max_eq_left le_rfl]
      constructor
      · nlinarith
      · intro hcw' hne
        have hpw' : M.c < M.p * w := by rw [div_lt_iff₀ hp] at hcw'; linarith
        have : y < q := lt_of_le_of_ne h2 hne
        nlinarith
    · -- `y ≥ q`
      rw [min_eq_right h2, max_eq_right hbq, max_eq_right (by linarith)]
      constructor
      · nlinarith
      · intro _ hne
        have : q < y := lt_of_le_of_ne h2 (Ne.symm hne)
        nlinarith

/-- At or below `c/p` the supplier earns at most `0`. -/
lemma pv_low (M : Model) (hM : M.Std) (w b q y : ℝ) (hsw : ¬ M.s < w) (hcw : w ≤ M.c / M.p)
    (hq : 0 ≤ q) (hb0 : 0 ≤ b) (hy : 0 ≤ y) (hw : 0 < w) : pv M w b q y ≤ 0 := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hpw : M.p * w ≤ M.c := by rw [le_div_iff₀ hp] at hcw; linarith
  rw [pv_mid M w b q y hsw hq hb0]
  push_neg at hsw
  have hbq0 : 0 ≤ b * q := mul_nonneg hb0 hq
  set Z1 := max (b * q) (min y q)
  have hZ1 : 0 ≤ Z1 := le_trans hbq0 (le_max_left _ _)
  -- `w Z1 − s (Z1 − y)⁺ ≤ w min(Z1, y) ≤ w y`
  have h1 : w * Z1 - M.s * max (Z1 - y) 0 ≤ w * y := by
    rcases le_total Z1 y with h | h
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith
  have h2 : (1 - M.p) * (w * (b * q) - M.c * y - M.s * (b * q)) ≤ (1 - M.p) * (-(M.c * y)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have hc := hM.c_pos
  nlinarith

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

/-- Buyer's expected profit in the region `w ≤ s` when the input equals the order. -/
noncomputable def Bv (M : Model) (w b q : ℝ) : ℝ :=
  M.p * buyerExPost M w q + (1 - M.p) * buyerExPost M w (b * q)

/-- Marginal value of the order. -/
noncomputable def hv (M : Model) (w b q : ℝ) : ℝ :=
  M.p * (M.r * Fbar M.f q - w) + (1 - M.p) * b * (M.r * Fbar M.f (b * q) - w)

lemma bEP_lower (M : Model) (hM : M.Std) (w q q' : ℝ) :
    buyerExPost M w q + (q' - q) * (M.r * Fbar M.f q' - w) ≤ buyerExPost M w q' := by
  have := bEP_support M hM w q' q
  linarith

lemma Bv_support (M : Model) (hM : M.Std) (w b q q' : ℝ) (hp1 : M.p ≤ 1) (hp : 0 ≤ M.p) :
    Bv M w b q' ≤ Bv M w b q + (q' - q) * hv M w b q := by
  unfold Bv hv
  have h1 := mul_le_mul_of_nonneg_left (bEP_support M hM w q q') hp
  have h2 := mul_le_mul_of_nonneg_left (bEP_support M hM w (b * q) (b * q'))
    (by linarith : (0:ℝ) ≤ 1 - M.p)
  nlinarith

lemma Bv_lower (M : Model) (hM : M.Std) (w b q q' : ℝ) (hp1 : M.p ≤ 1) (hp : 0 ≤ M.p) :
    Bv M w b q + (q' - q) * hv M w b q' ≤ Bv M w b q' := by
  unfold Bv hv
  have h1 := mul_le_mul_of_nonneg_left (bEP_lower M hM w q q') hp
  have h2 := mul_le_mul_of_nonneg_left (bEP_lower M hM w (b * q) (b * q'))
    (by linarith : (0:ℝ) ≤ 1 - M.p)
  nlinarith

lemma hv_cont (M : Model) (hM : M.Std) (w b : ℝ) : Continuous (fun q => hv M w b q) := by
  unfold hv
  have := Fbar_cont M hM
  fun_prop

lemma hv_anti (M : Model) (hM : M.Std) (w b : ℝ) (hb : 0 ≤ b) {q1 q2 : ℝ} (h12 : q1 ≤ q2) :
    hv M w b q2 ≤ hv M w b q1 := by
  unfold hv
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have a1 := Fbar_anti M hM h12
  have a2 := Fbar_anti M hM (mul_le_mul_of_nonneg_left h12 hb)
  have hr := r_pos M hM
  have e1 : M.p * (M.r * Fbar M.f q2 - w) ≤ M.p * (M.r * Fbar M.f q1 - w) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hp.le
  have e2 : (1 - M.p) * b * (M.r * Fbar M.f (b * q2) - w) ≤
      (1 - M.p) * b * (M.r * Fbar M.f (b * q1) - w) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by linarith) hb)
  linarith

lemma hv_strict (M : Model) (hM : M.Std) (w b : ℝ) (hb : 0 ≤ b) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (h12 : q1 < q2) (hq2 : q2 ∈ supp M.abar) : hv M w b q2 < hv M w b q1 := by
  unfold hv
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have a1 := Fbar_strict M hM hq1 h12 hq2
  have a2 := Fbar_anti M hM (mul_le_mul_of_nonneg_left h12.le hb)
  have hr := r_pos M hM
  have e1 : M.p * (M.r * Fbar M.f q2 - w) < M.p * (M.r * Fbar M.f q1 - w) :=
    mul_lt_mul_of_pos_left (by nlinarith) hp
  have e2 : (1 - M.p) * b * (M.r * Fbar M.f (b * q2) - w) ≤
      (1 - M.p) * b * (M.r * Fbar M.f (b * q1) - w) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by linarith) hb)
  linarith

/-- First-order conditions at a maximiser of `Bv`. -/
lemma Bv_foc (M : Model) (hM : M.Std) (w b Q : ℝ) (hQ : 0 ≤ Q)
    (hmax : ∀ q', 0 ≤ q' → Bv M w b q' ≤ Bv M w b Q) :
    hv M w b Q ≤ 0 ∧ (0 < Q → 0 ≤ hv M w b Q) := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hc := hv_cont M hM w b
  constructor
  · have hr : ∀ q', Q < q' → hv M w b q' ≤ 0 := by
      intro q' hq'
      have h1 := Bv_lower M hM w b Q q' hp1 hp.le
      have h2 := hmax q' (by linarith)
      by_contra hc'; push_neg at hc'
      nlinarith [mul_pos (sub_pos.2 hq') hc']
    have ht : Filter.Tendsto (fun q => hv M w b q) (nhdsWithin Q (Set.Ioi Q))
        (nhds (hv M w b Q)) := hc.continuousAt.continuousWithinAt.tendsto
    exact le_of_tendsto ht (Filter.eventually_of_mem self_mem_nhdsWithin (fun q hq => hr q hq))
  · intro hQ0
    have hl : ∀ q', 0 ≤ q' → q' < Q → 0 ≤ hv M w b q' := by
      intro q' hq0 hq'
      have h1 := Bv_lower M hM w b Q q' hp1 hp.le
      have h2 := hmax q' hq0
      by_contra hc'; push_neg at hc'
      nlinarith [mul_pos (sub_pos.2 hq') (neg_pos.2 hc')]
    have ht : Filter.Tendsto (fun q => hv M w b q) (nhdsWithin Q (Set.Ioo 0 Q))
        (nhds (hv M w b Q)) := hc.continuousAt.continuousWithinAt.tendsto
    haveI : (nhdsWithin Q (Set.Ioo 0 Q)).NeBot := right_nhdsWithin_Ioo_neBot hQ0
    exact ge_of_tendsto ht (Filter.eventually_of_mem self_mem_nhdsWithin
      (fun q hq => hl q hq.1.le hq.2))

/-- `Q · h(Q) = 0`, i.e. the price identity `w (pQ + (1−p) bQ) = r (pQF̄(Q) + (1−p) bQ F̄(bQ))`. -/
lemma Bv_price (M : Model) (hM : M.Std) (w b Q : ℝ) (hQ : 0 ≤ Q)
    (hmax : ∀ q', 0 ≤ q' → Bv M w b q' ≤ Bv M w b Q) :
    w * (M.p * Q + (1 - M.p) * (b * Q)) =
      M.r * (M.p * Q * Fbar M.f Q + (1 - M.p) * (b * Q) * Fbar M.f (b * Q)) := by
  obtain ⟨h1, h2⟩ := Bv_foc M hM w b Q hQ hmax
  rcases hQ.lt_or_eq with h | h
  · have : hv M w b Q = 0 := le_antisymm h1 (h2 h)
    unfold hv at this
    have := congrArg (· * Q) this
    simp only [zero_mul] at this
    linarith
  · rw [← h]; ring

/-- Uniqueness of the order from the first-order conditions. -/
lemma Bv_unique (M : Model) (hM : M.Std) (w b Q κ : ℝ) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hfoc : hv M w b Q ≤ 0 ∧ (0 < Q → 0 ≤ hv M w b Q)) (hκ : 0 < κ)
    (hκs : κ ∈ supp M.abar) (hκ0 : hv M w b κ = 0) : Q = κ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hv_strict M hM w b hb hQ hlt hκs
    linarith [hfoc.1]
  · obtain ⟨t, ht0, hκt, hta⟩ := ENNReal.lt_iff_exists_real_btwn.1 hκs.2
    have hκt' : κ < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hκ.le).1 hκt
    set m := (κ + min Q t) / 2
    have hm1 : κ < m := by have := lt_min hgt hκt'; simp only [m]; linarith
    have hm2 : m < min Q t := by have := lt_min hgt hκt'; simp only [m]; linarith
    have hms : m ∈ supp M.abar :=
      ⟨by linarith, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_trans hm2.le (min_le_right _ _)))
        hta⟩
    have e1 := hv_strict M hM w b hb hκ.le hm1 hms
    have e2 := hv_anti M hM w b hb (le_trans hm2.le (min_le_left _ _))
    have := hfoc.2 (by linarith)
    linarith

/-- Sufficiency: a zero of `h` maximises `Bv`. -/
lemma Bv_suff (M : Model) (hM : M.Std) (w b κ : ℝ) (hκ0 : hv M w b κ = 0) :
    ∀ q', 0 ≤ q' → Bv M w b q' ≤ Bv M w b κ := by
  intro q' _
  have := Bv_support M hM w b κ q' hM.p_le_one hM.p_pos.le
  rw [hκ0, mul_zero, add_zero] at this
  exact this

/-! ### Problem (A2.8) -/

lemma obj_eq (M : Model) (hp : 0 < M.p) (q qh : ℝ) :
    a28Obj M (q, qh) = M.p * (q * (M.r * Fbar M.f q - M.c / M.p)) +
      (1 - M.p) * (qh * (M.r * Fbar M.f qh - M.s)) := by
  unfold a28Obj; simp only; field_simp; ring

/-- Strict decrease of `ψ_k` beyond its peak. -/
lemma psi_strict_anti (M : Model) (hM : M.Std) (k q0 : ℝ) (hk : 0 < k) (hq00 : 0 ≤ q0)
    (hq0e : M.r * G M.f q0 = k) {a b : ℝ} (ha : q0 ≤ a) (hab : a < b) :
    b * (M.r * Fbar M.f b - k) < a * (M.r * Fbar M.f a - k) := by
  have hr := r_pos M hM
  have hanti := psi_anti M hM k q0 hq00 hq0e hk
  have hle := hanti (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (by linarith)) hab.le
  simp only at hle
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  exfalso
  have hq0s := root_supp M hM k q0 hk hq00 hq0e
  have hc : ∀ m ∈ Set.Ioo a b, (fun q => q * (M.r * Fbar M.f q - k)) m =
      (fun q => q * (M.r * Fbar M.f q - k)) a := by
    intro m hm
    have h1 := hanti (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (by linarith [hm.1])) hm.1.le
    have h2 := hanti (Set.mem_Ici.2 (by linarith [hm.1])) (Set.mem_Ici.2 (by linarith)) hm.2.le
    simp only at h1 h2 ⊢
    linarith
  by_cases has : ENNReal.ofReal a < M.abar
  · obtain ⟨t, ht0, hat, hta⟩ := ENNReal.lt_iff_exists_real_btwn.1 has
    have ha0 : 0 ≤ a := le_trans hq00 ha
    have hat' : a < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0).1 hat
    set u := min b t
    have hu : a < u := lt_min hab hat'
    have hus : ∀ m, m < u → ENNReal.ofReal m < M.abar := fun m hm =>
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_trans hm.le (min_le_right _ _))) hta
    have hconst : ∀ m ∈ Set.Ioo a u, M.r * G M.f m = k := by
      intro m hm
      have hm0 : 0 < m := by
        rcases ha0.lt_or_eq with h' | h'
        · linarith [hm.1]
        · linarith [hm.1]
      have hev : (fun q => q * (M.r * Fbar M.f q - k)) =ᶠ[nhds m]
          fun _ => (fun q => q * (M.r * Fbar M.f q - k)) a :=
        Filter.eventually_of_mem (Ioo_mem_nhds hm.1 (lt_of_lt_of_le hm.2 (min_le_left _ _)))
          (fun x hx => hc x hx)
      have h0 : HasDerivAt (fun q => q * (M.r * Fbar M.f q - k)) 0 m :=
        (hasDerivAt_const m _).congr_of_eventuallyEq hev
      have h1 := hderiv_psi M hM k m hm0 (hus m hm.2)
      have := h1.unique h0
      linarith
    set m1 := a + (u - a) / 3
    set m2 := a + 2 * (u - a) / 3
    have hm1 : m1 ∈ Set.Ioo a u := ⟨by simp only [m1]; linarith, by simp only [m1]; linarith⟩
    have hm2 : m2 ∈ Set.Ioo a u := ⟨by simp only [m2]; linarith, by simp only [m2]; linarith⟩
    have hs1 : m1 ∈ supp M.abar := ⟨by linarith [hm1.1], hus m1 hm1.2⟩
    have hs2 : m2 ∈ supp M.abar := ⟨by linarith [hm2.1], hus m2 hm2.2⟩
    have e1 := hconst m1 hm1
    have e2 := hconst m2 hm2
    have hG2 : 0 < G M.f m2 := by
      by_contra h'; push_neg at h'; nlinarith
    have := G_strict M hM hs1 hs2 (by simp only [m1, m2]; linarith) hG2
    nlinarith
  · push_neg at has
    have hFa := Fbar_out M hM a has
    have hFb := Fbar_out M hM b (le_trans has (ENNReal.ofReal_le_ofReal hab.le))
    rw [hFa, hFb] at h
    nlinarith

/-- `ψ_k` is maximised exactly at its root `q₀ > 0`. -/
lemma psi_max (M : Model) (hM : M.Std) (k q0 : ℝ) (hk : 0 < k) (hq0 : 0 < q0)
    (hq0e : M.r * G M.f q0 = k) (q : ℝ) (hq : 0 ≤ q) :
    q * (M.r * Fbar M.f q - k) ≤ q0 * (M.r * Fbar M.f q0 - k) ∧
      (q * (M.r * Fbar M.f q - k) = q0 * (M.r * Fbar M.f q0 - k) → q = q0) := by
  refine ⟨?_, psi_unique M hM k q0 hk hq0 hq0e q hq⟩
  rcases le_total q0 q with hle | hle
  · exact psi_anti M hM k q0 hq0.le hq0e hk (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hle) hle
  · exact psi_mono M hM k q0 hk hq0.le hq0e ⟨hq, hle⟩ ⟨hq0.le, le_rfl⟩ hle

/-- `ψ_s` is maximised exactly at `q̂*`. -/
lemma psi_s_max (M : Model) (hM : M.Std) (qh : ℝ)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (q : ℝ) (hq : 0 ≤ q) :
    q * (M.r * Fbar M.f q - M.s) ≤ qh * (M.r * Fbar M.f qh - M.s) ∧
      (q * (M.r * Fbar M.f q - M.s) = qh * (M.r * Fbar M.f qh - M.s) → q = qh) := by
  have hr := r_pos M hM
  have hs0 : 0 < M.s := by
    have := hM.assm1_s; have : 0 < M.c / M.p := div_pos hM.c_pos hM.p_pos; linarith
  -- the cases where `q̂* = 0` and `ψ_s < 0` off `0`
  have hzero : qh = 0 → M.r ≤ M.s → (q * (M.r * Fbar M.f q - M.s) ≤ qh * (M.r * Fbar M.f qh - M.s) ∧
      (q * (M.r * Fbar M.f q - M.s) = qh * (M.r * Fbar M.f qh - M.s) → q = qh)) := by
    intro h0 hrs
    rw [h0, zero_mul]
    rcases hq.lt_or_eq with hqp | hqz
    · have := Fbar_lt_one M hM q hqp
      have : M.r * Fbar M.f q - M.s < 0 := by nlinarith
      have hneg := mul_neg_of_pos_of_neg hqp this
      exact ⟨hneg.le, fun h => absurd h hneg.ne⟩
    · rw [← hqz]; simp
  by_cases hsr : M.s ≤ M.r
  · obtain ⟨hqh0, hqhe⟩ := hqh.1 hsr
    rcases hqh0.lt_or_eq with hpos | hz
    · exact psi_max M hM M.s qh hs0 hpos hqhe q hq
    · have hrs : M.r ≤ M.s := by
        rw [← hz] at hqhe; unfold G at hqhe; rw [Fbar_zero M hM] at hqhe; linarith
      exact hzero hz.symm hrs
  · exact hzero (hqh.2 (lt_of_not_ge hsr)) (le_of_lt (lt_of_not_ge hsr))

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

lemma root_unique (M : Model) (hM : M.Std) (k q1 q2 : ℝ) (hk : 0 < k) (h10 : 0 ≤ q1)
    (h1 : M.r * G M.f q1 = k) (h20 : 0 ≤ q2) (h2 : M.r * G M.f q2 = k) : q1 = q2 := by
  have hr := r_pos M hM
  have s1 := root_supp M hM k q1 hk h10 h1
  have s2 := root_supp M hM k q2 hk h20 h2
  have g1 : 0 < G M.f q1 := by by_contra h; push_neg at h; nlinarith
  have g2 : 0 < G M.f q2 := by by_contra h; push_neg at h; nlinarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := G_strict M hM s1 s2 h g2; nlinarith
  · have := G_strict M hM s2 s1 h g1; nlinarith

lemma root_pos (M : Model) (hM : M.Std) (k q : ℝ) (hkr : k < M.r) (hq0 : 0 ≤ q)
    (hq : M.r * G M.f q = k) : 0 < q := by
  rcases hq0.lt_or_eq with h | h
  · exact h
  · rw [← h] at hq; unfold G at hq; rw [Fbar_zero M hM] at hq; linarith

/-- `ψ_k(q₀) = r q₀² f(q₀) > 0` at a positive root. -/
lemma psi_root_pos (M : Model) (hM : M.Std) (k q0 : ℝ) (hk : 0 < k) (hq0 : 0 < q0)
    (hq0e : M.r * G M.f q0 = k) : 0 < q0 * (M.r * Fbar M.f q0 - k) := by
  have hs := root_supp M hM k q0 hk hq0.le hq0e
  have hf := hM.f_pos q0 hs
  have hr := r_pos M hM
  unfold G at hq0e
  have : M.r * Fbar M.f q0 - k = M.r * q0 * M.f q0 := by linarith
  rw [this]; positivity

/-- Problem (A2.8) when the price constraint does not bind. -/
lemma A28_A (M : Model) (hM : M.Std) (qo qh : ℝ) (hqo0 : 0 < qo)
    (hqoe : M.r * G M.f qo = M.c / M.p)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (q qq : ℝ) (hq : 0 ≤ q) (hqq : 0 ≤ qq) :
    a28Obj M (q, qq) ≤ a28Obj M (qo, qh) ∧
      (a28Obj M (q, qq) = a28Obj M (qo, qh) → q = qo ∧ (M.p < 1 → qq = qh)) := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hcp : 0 < M.c / M.p := div_pos hM.c_pos hp
  obtain ⟨a1, a2⟩ := psi_max M hM (M.c / M.p) qo hcp hqo0 hqoe q hq
  obtain ⟨b1, b2⟩ := psi_s_max M hM qh hqh qq hqq
  rw [obj_eq M hp, obj_eq M hp]
  have e1 := mul_le_mul_of_nonneg_left a1 hp.le
  have e2 := mul_le_mul_of_nonneg_left b1 (by linarith : (0:ℝ) ≤ 1 - M.p)
  refine ⟨by linarith, fun heq => ?_⟩
  have hA : q * (M.r * Fbar M.f q - M.c / M.p) = qo * (M.r * Fbar M.f qo - M.c / M.p) := by
    by_contra hne
    have hlt := lt_of_le_of_ne a1 hne
    have := mul_lt_mul_of_pos_left hlt hp
    linarith
  refine ⟨a2 hA, fun hp' => b2 ?_⟩
  by_contra hne
  have hlt := lt_of_le_of_ne b1 hne
  have := mul_lt_mul_of_pos_left hlt (by linarith : (0:ℝ) < 1 - M.p)
  linarith

/-- Problem (A2.8) when the price constraint binds. -/
lemma A28_B (M : Model) (hM : M.Std) (qo qh qc : ℝ) (hqo0 : 0 < qo)
    (hqoe : M.r * G M.f qo = M.c / M.p)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hlt : qo < qc)
    (hqc : qh ≤ qc ∧ M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh))
    (x : ℝ × ℝ) (hx : x ∈ a28Feasible M) :
    a28Obj M x ≤ qc * (M.p * M.s - M.c) ∧
      (a28Obj M x = qc * (M.p * M.s - M.c) → x.1 = qc ∧ (M.p < 1 → x.2 = qh)) := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hcps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hcp : 0 < M.c / M.p := div_pos hM.c_pos hp
  obtain ⟨hx2, hx21, hxc⟩ := hx
  have hx1 : 0 ≤ x.1 := le_trans hx2 hx21
  have hbound : a28Obj M x ≤ x.1 * (M.p * M.s - M.c) := by
    unfold a28Obj; nlinarith
  have hqh0 : 0 ≤ qh := by
    by_cases hsr : M.s ≤ M.r
    · exact (hqh.1 hsr).1
    · rw [hqh.2 (lt_of_not_ge hsr)]
  have hobj_c : a28Obj M (qc, qh) = qc * (M.p * M.s - M.c) := by
    unfold a28Obj; simp only; linarith [hqc.2]
  obtain ⟨b1, b2⟩ := psi_s_max M hM qh hqh x.2 hx2
  rcases le_or_gt x.1 qc with hle | hgt
  · refine ⟨le_trans hbound (mul_le_mul_of_nonneg_right hle (by linarith)), fun heq => ?_⟩
    have hq1 : x.1 = qc := by
      by_contra hne
      have := lt_of_le_of_ne hle hne
      have := mul_lt_mul_of_pos_right this (by linarith : (0:ℝ) < M.p * M.s - M.c)
      linarith
    refine ⟨hq1, fun hp' => b2 ?_⟩
    have e : a28Obj M x = a28Obj M (qc, qh) := by rw [heq, hobj_c]
    have hx : x = (qc, x.2) := by rw [← hq1]
    rw [hx, obj_eq M hp, obj_eq M hp] at e
    have := mul_left_cancel₀ (by linarith : (1 - M.p) ≠ 0) (by linarith : (1 - M.p) *
      (x.2 * (M.r * Fbar M.f x.2 - M.s)) = (1 - M.p) * (qh * (M.r * Fbar M.f qh - M.s)))
    exact this
  · -- beyond `q̌` the objective is strictly smaller
    have hstr := psi_strict_anti M hM (M.c / M.p) qo hcp hqo0.le hqoe hlt.le hgt
    have hlt2 : a28Obj M x < a28Obj M (qc, qh) := by
      have hx : x = (x.1, x.2) := rfl
      rw [hx, obj_eq M hp, obj_eq M hp]
      have := mul_lt_mul_of_pos_left hstr hp
      have := mul_le_mul_of_nonneg_left b1 (by linarith : (0:ℝ) ≤ 1 - M.p)
      linarith
    rw [hobj_c] at hlt2
    exact ⟨hlt2.le, fun heq => absurd heq hlt2.ne⟩

/-! ### Continuation-level facts -/

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

lemma cp_lt_s (M : Model) (hM : M.Std) : M.c / M.p < M.s := hM.assm1_s

lemma Y_q (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b q : ℝ)
    (hadm : Admissible .flex w b) (hq : 0 ≤ q) (hcw : M.c / M.p < w) : σ.Y w b q = q := by
  obtain ⟨hY0, hY⟩ := h.2.1 w b q hadm hq
  by_contra hne
  have h1 := hY q hq
  rw [prodValue_eq M σ h w b q q hadm hq hq, prodValue_eq M σ h w b q _ hadm hq hY0] at h1
  by_cases hsw : M.s < w
  · exact absurd h1 (not_le.2 (pv_hi_lt M hM w b q _ hsw hq hne))
  · exact absurd h1 (not_le.2 ((pv_mid_le M hM w b q _ hsw hcw.le hq hadm.2.1 hadm.2.2 hY0).2
      hcw hne))

lemma OV_hi (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b q : ℝ)
    (hadm : Admissible .flex w b) (hq : 0 ≤ q) (hsw : M.s < w) :
    orderValue M σ w b q = buyerExPost M w q := by
  have hY := Y_q M hM σ h w b q hadm hq (lt_trans (cp_lt_s M hM) hsw)
  unfold orderValue Eα
  beta_reduce
  rw [hY, Z_true M σ h w b q q hadm hq hq, Z_false M σ h w b q q hadm hq hq, if_pos hsw, if_pos hsw]
  ring

lemma OV_mid (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b q : ℝ)
    (hadm : Admissible .flex w b) (hq : 0 ≤ q) (hsw : ¬ M.s < w) (hcw : M.c / M.p < w) :
    orderValue M σ w b q = Bv M w b q := by
  have hY := Y_q M hM σ h w b q hadm hq hcw
  have hbq : b * q ≤ q := by nlinarith [hadm.2.2]
  unfold orderValue Eα Bv
  beta_reduce
  rw [hY, Z_true M σ h w b q q hadm hq hq, Z_false M σ h w b q q hadm hq hq, if_neg hsw,
    if_neg hsw, min_self, max_eq_right hbq]

lemma Q_max_hi (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b : ℝ)
    (hadm : Admissible .flex w b) (hsw : M.s < w) :
    0 ≤ σ.Q w b ∧ ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w (σ.Q w b) := by
  obtain ⟨h0, h1⟩ := h.2.2 w b hadm
  refine ⟨h0, fun q' hq' => ?_⟩
  rw [← OV_hi M hM σ h w b q' hadm hq' hsw, ← OV_hi M hM σ h w b _ hadm h0 hsw]
  exact h1 q' hq'

lemma Q_max_mid (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b : ℝ)
    (hadm : Admissible .flex w b) (hsw : ¬ M.s < w) (hcw : M.c / M.p < w) :
    0 ≤ σ.Q w b ∧ ∀ q', 0 ≤ q' → Bv M w b q' ≤ Bv M w b (σ.Q w b) := by
  obtain ⟨h0, h1⟩ := h.2.2 w b hadm
  refine ⟨h0, fun q' hq' => ?_⟩
  rw [← OV_mid M hM σ h w b q' hadm hq' hsw hcw, ← OV_mid M hM σ h w b _ hadm h0 hsw hcw]
  exact h1 q' hq'

lemma CV_hi (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b : ℝ)
    (hadm : Admissible .flex w b) (hsw : M.s < w) :
    contractValue M σ w b = σ.Q w b * (w - (M.c + (1 - M.p) * M.s)) := by
  have hQ0 := (h.2.2 w b hadm).1
  unfold contractValue
  rw [Y_q M hM σ h w b _ hadm hQ0 (lt_trans (cp_lt_s M hM) hsw),
    prodValue_eq M σ h w b _ _ hadm hQ0 hQ0, pv_hi_q M w b _ hsw hQ0]

lemma CV_mid (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b : ℝ)
    (hadm : Admissible .flex w b) (hsw : ¬ M.s < w) (hcw : M.c / M.p < w) :
    contractValue M σ w b = a28Obj M (σ.Q w b, b * σ.Q w b) ∧
      (σ.Q w b, b * σ.Q w b) ∈ a28Feasible M := by
  obtain ⟨hQ0, hmax⟩ := Q_max_mid M hM σ h w b hadm hsw hcw
  have hprice := Bv_price M hM w b _ hQ0 hmax
  have hb0 := hadm.2.1
  have hb1 := hadm.2.2
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  set Q := σ.Q w b
  constructor
  · unfold contractValue
    rw [Y_q M hM σ h w b _ hadm hQ0 hcw, prodValue_eq M σ h w b _ _ hadm hQ0 hQ0,
      pv_mid_q M w b _ hsw hQ0 hb0 hb1]
    unfold a28Obj; simp only
    linarith
  · refine ⟨mul_nonneg hb0 hQ0, by nlinarith, ?_⟩
    simp only
    push_neg at hsw
    have hD : 0 ≤ M.p * Q + (1 - M.p) * (b * Q) := by
      have := mul_nonneg hb0 hQ0; nlinarith
    rw [← hprice]
    nlinarith

lemma CV_low (M : Model) (hM : M.Std) (σ : Profile) (h : ContOK M σ) (w b : ℝ)
    (hadm : Admissible .flex w b) (hcw : w ≤ M.c / M.p) : contractValue M σ w b ≤ 0 := by
  have hsw : ¬ M.s < w := by have := cp_lt_s M hM; intro h'; linarith
  have hQ0 := (h.2.2 w b hadm).1
  have hY0 := (h.2.1 w b _ hadm hQ0).1
  unfold contractValue
  rw [prodValue_eq M σ h w b _ _ hadm hQ0 hY0]
  exact pv_low M hM w b _ _ hsw hcw hQ0 hadm.2.1 hY0 hadm.1

/-- Strict decrease of the marginal value of the order, through either delivery. -/
lemma hv_strict' (M : Model) (hM : M.Std) (w b : ℝ) (hb : 0 ≤ b) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (h12 : q1 < q2)
    (hcond : q2 ∈ supp M.abar ∨ (M.p < 1 ∧ 0 < b ∧ b * q2 ∈ supp M.abar)) :
    hv M w b q2 < hv M w b q1 := by
  rcases hcond with hs | ⟨hp1', hb0, hs⟩
  · exact hv_strict M hM w b hb hq1 h12 hs
  · unfold hv
    have hp := hM.p_pos
    have hp1 := hM.p_le_one
    have hr := r_pos M hM
    have a1 := Fbar_anti M hM h12.le
    have a2 := Fbar_strict M hM (mul_nonneg hb hq1) (mul_lt_mul_of_pos_left h12 hb0) hs
    have e1 : M.p * (M.r * Fbar M.f q2 - w) ≤ M.p * (M.r * Fbar M.f q1 - w) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hp.le
    have e2 : (1 - M.p) * b * (M.r * Fbar M.f (b * q2) - w) <
        (1 - M.p) * b * (M.r * Fbar M.f (b * q1) - w) :=
      mul_lt_mul_of_pos_left (by nlinarith) (mul_pos (by linarith) hb0)
    linarith

/-- Uniqueness of the order from the first-order conditions (general form). -/
lemma Bv_unique' (M : Model) (hM : M.Std) (w b Q κ : ℝ) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hfoc : hv M w b Q ≤ 0 ∧ (0 < Q → 0 ≤ hv M w b Q)) (hκ : 0 < κ)
    (hcond : κ ∈ supp M.abar ∨ (M.p < 1 ∧ 0 < b ∧ b * κ ∈ supp M.abar))
    (hκ0 : hv M w b κ = 0) : Q = κ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hv_strict' M hM w b hb hQ hlt hcond
    linarith [hfoc.1]
  · -- find `m ∈ (κ, Q)` still satisfying the condition
    have hm : ∃ m, κ < m ∧ m < Q ∧
        (m ∈ supp M.abar ∨ (M.p < 1 ∧ 0 < b ∧ b * m ∈ supp M.abar)) := by
      rcases hcond with hs | ⟨hp1', hb0, hs⟩
      · obtain ⟨t, ht0, hκt, hta⟩ := ENNReal.lt_iff_exists_real_btwn.1 hs.2
        have hκt' : κ < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hκ.le).1 hκt
        refine ⟨(κ + min Q t) / 2, by have := lt_min hgt hκt'; linarith,
          by have := lt_min hgt hκt'; have := min_le_left Q t; linarith,
          Or.inl ⟨by have := lt_min hgt hκt'; linarith, ?_⟩⟩
        refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hta
        have := lt_min hgt hκt'; have := min_le_right Q t; linarith
      · obtain ⟨t, ht0, hκt, hta⟩ := ENNReal.lt_iff_exists_real_btwn.1 hs.2
        have hbκ0 : 0 ≤ b * κ := by positivity
        have hκt' : b * κ < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hbκ0).1 hκt
        set u := min Q (t / b)
        have hu : κ < u := lt_min hgt (by rw [lt_div_iff₀ hb0]; linarith)
        refine ⟨(κ + u) / 2, by linarith, by have := min_le_left Q (t / b); linarith,
          Or.inr ⟨hp1', hb0, ⟨by positivity, ?_⟩⟩⟩
        refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hta
        have h1 : (κ + u) / 2 < t / b := by have := min_le_right Q (t / b); linarith
        rw [lt_div_iff₀ hb0] at h1; linarith
    obtain ⟨m, hm1, hm2, hmc⟩ := hm
    have e1 := hv_strict' M hM w b hb hκ.le hm1 hmc
    have e2 := hv_anti M hM w b hb hm2.le
    have := hfoc.2 (by linarith)
    linarith

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

/-- Facts about the roots of (1)–(4) used throughout. -/
structure Roots (M : Model) (qt qo qh qc : ℝ) : Prop where
  qo_pos : 0 < qo
  qo_e : M.r * G M.f qo = M.c / M.p
  qo_s : qo ∈ supp M.abar
  qh0 : 0 ≤ qh
  qh_lt : qh < qo
  wo_le : M.r < M.s → wo M qo qh ≤ M.s
  wo_gt : M.c / M.p < wo M qo qh
  caseB : M.s < wo M qo qh →
    M.s < M.r ∧ 0 < qh ∧ qh ∈ supp M.abar ∧ M.r * G M.f qh = M.s ∧
    0 < qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s ∧ qt ∈ supp M.abar ∧
    qh ≤ qc ∧ qo < qc ∧
    M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
      M.s * (M.p * qc + (1 - M.p) * qh)

lemma roots (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hqc : M.s < wo M qo qh → qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh)) : Roots M qt qo qh qc := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hc0 := hM.c_pos
  have hcps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hcp : 0 < M.c / M.p := div_pos hc0 hp
  have hcpr : M.c / M.p < M.r := hM.assm1_r
  have hcps' : M.c / M.p < M.s := hM.assm1_s
  have hs0 : 0 < M.s := by linarith
  have hqoe : M.r * G M.f qo = M.c / M.p := by rw [eq_div_iff hp.ne']; linarith [hqo.2]
  have hqo_pos : 0 < qo := root_pos M hM _ qo hcpr hqo.1 hqoe
  have hqos := root_supp M hM _ qo hcp hqo.1 hqoe
  have hqh0 : 0 ≤ qh := by
    by_cases hsr : M.s ≤ M.r
    · exact (hqh.1 hsr).1
    · rw [hqh.2 (lt_of_not_ge hsr)]
  have hqh_lt : qh < qo := by
    by_cases hsr : M.s ≤ M.r
    · obtain ⟨h0, he⟩ := hqh.1 hsr
      by_contra hle; push_neg at hle
      have hGh : 0 < G M.f qh := by by_contra h'; push_neg at h'; nlinarith
      have := G_ge M hM hqos (root_supp M hM _ qh hs0 h0 he) hle hGh
      nlinarith
    · rw [hqh.2 (lt_of_not_ge hsr)]; exact hqo_pos
  have hD : 0 < M.p * qo + (1 - M.p) * qh := by nlinarith
  have hFo : M.c / M.p < M.r * Fbar M.f qo := by
    have := psi_root_pos M hM _ qo hcp hqo_pos hqoe
    nlinarith
  have hwo_r : M.r < M.s → wo M qo qh ≤ M.s := by
    intro hrs
    rw [hqh.2 hrs]
    unfold wo
    simp only [mul_zero, zero_mul, add_zero]
    rw [show M.r * (M.p * qo * Fbar M.f qo) / (M.p * qo) = M.r * Fbar M.f qo by
      field_simp]
    nlinarith [Fbar_le_one M hM qo]
  refine ⟨hqo_pos, hqoe, hqos, hqh0, hqh_lt, hwo_r, ?_, ?_⟩
  · -- `w° > c/p`
    unfold wo
    rw [lt_div_iff₀ hD]
    have h2 : (1 - M.p) * qh * (M.c / M.p) ≤ (1 - M.p) * qh * (M.r * Fbar M.f qh) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hqh0)
      by_cases hsr : M.s ≤ M.r
      · obtain ⟨_, he⟩ := hqh.1 hsr
        have : G M.f qh ≤ Fbar M.f qh := by
          unfold G; nlinarith [mul_nonneg hqh0 (f_nonneg M hM qh)]
        nlinarith
      · rw [hqh.2 (lt_of_not_ge hsr), Fbar_zero M hM]; linarith
    nlinarith [mul_lt_mul_of_pos_left hFo (mul_pos hp hqo_pos)]
  · intro hsw
    have hsr : M.s < M.r := by
      by_contra h'; push_neg at h'
      rcases h'.lt_or_eq with h'' | h''
      · exact absurd (hwo_r h'') (not_le.2 hsw)
      · -- `s = r` forces `q̂* = 0` and `w° = r F̄(q°) < r`
        obtain ⟨h0, he⟩ := hqh.1 (le_of_eq h''.symm)
        have hqhz : qh = 0 := by
          by_contra hne
          have hpos : 0 < qh := lt_of_le_of_ne h0 (Ne.symm hne)
          have := Fbar_lt_one M hM qh hpos
          unfold G at he
          nlinarith [mul_nonneg hpos.le (f_nonneg M hM qh)]
        rw [hqhz] at hsw
        unfold wo at hsw
        simp only [mul_zero, zero_mul, add_zero] at hsw
        rw [show M.r * (M.p * qo * Fbar M.f qo) / (M.p * qo) = M.r * Fbar M.f qo by
          field_simp] at hsw
        have := Fbar_lt_one M hM qo hqo_pos
        nlinarith
    obtain ⟨h0, he⟩ := hqh.1 hsr.le
    have hqh_pos : 0 < qh := root_pos M hM _ qh hsr h0 he
    have hk : M.c + (1 - M.p) * M.s < M.r := by nlinarith
    obtain ⟨ht0, hte⟩ := hqt hk.le
    have hk0 : 0 < M.c + (1 - M.p) * M.s := by nlinarith
    obtain ⟨hqc1, hqc2⟩ := hqc hsw
    exact ⟨hsr, hqh_pos, root_supp M hM _ qh hs0 h0 he, he, root_pos M hM _ qt hk ht0 hte, hte,
      root_supp M hM _ qt hk0 ht0 hte, hqc1,
      SupplyFlex.SupplierLed.qo_lt_qc M hM qo qh qc hqo hqh hsw (hqc hsw), hqc2⟩

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

lemma obj_diag (M : Model) (q : ℝ) :
    a28Obj M (q, q) = q * (M.r * Fbar M.f q - (M.c + (1 - M.p) * M.s)) := by
  unfold a28Obj; simp only; ring

/-- The supplier's continuation value of any offer is at most `V*`, with equality only at the
claimed outcomes. -/
lemma bound (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (R : Roots M qt qo qh qc)
    (V : ℝ) (hV : V = if wo M qo qh ≤ M.s then a28Obj M (qo, qh) else
        max (qc * (M.p * M.s - M.c)) (qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)))
    (σ : Profile) (h : ContOK M σ) (w b : ℝ) (hadm : Admissible .flex w b) :
    0 < V ∧ contractValue M σ w b ≤ V ∧ (contractValue M σ w b = V →
      (¬ M.s < w ∧ M.c / M.p < w ∧
        σ.Q w b = (if wo M qo qh ≤ M.s then qo else qc) ∧ (M.p < 1 → b * σ.Q w b = qh) ∧
        (¬ wo M qo qh ≤ M.s →
          qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) ≤ qc * (M.p * M.s - M.c))) ∨
      (M.s < w ∧ M.s < wo M qo qh ∧ σ.Q w b = qt ∧ w = M.r * Fbar M.f qt ∧
        qc * (M.p * M.s - M.c) ≤ qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c))) := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hc0 := hM.c_pos
  have hcps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hcp : 0 < M.c / M.p := div_pos hc0 hp
  have hcps' : M.c / M.p < M.s := hM.assm1_s
  set Q := σ.Q w b with hQdef
  have hQ0 : 0 ≤ Q := (h.2.2 w b hadm).1
  by_cases hA : wo M qo qh ≤ M.s
  · rw [if_pos hA] at hV
    -- `V = Obj(q°, q̂*) > 0`
    have hVpos : 0 < V := by
      rw [hV, obj_eq M hp]
      have h1 := psi_root_pos M hM _ qo hcp R.qo_pos R.qo_e
      have h2 := (psi_s_max M hM qh hqh 0 le_rfl).1
      simp only [zero_mul] at h2
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M.p) h2]
    refine ⟨hVpos, ?_⟩
    by_cases hcw : w ≤ M.c / M.p
    · have := CV_low M hM σ h w b hadm hcw
      exact ⟨by linarith, fun heq => by linarith⟩
    push_neg at hcw
    by_cases hsw : M.s < w
    · rw [CV_hi M hM σ h w b hadm hsw]
      obtain ⟨hQ0', hmax⟩ := Q_max_hi M hM σ h w b hadm hsw
      obtain ⟨c1, c2⟩ := BR_char M hM w hadm.1 Q hQ0 hmax
      by_cases hwr : M.r ≤ w
      · rw [← hQdef, c1 hwr, zero_mul]
        exact ⟨hVpos.le, fun heq => by linarith⟩
      · have hF := c2 (lt_of_not_ge hwr)
        have e : Q * (w - (M.c + (1 - M.p) * M.s)) = a28Obj M (Q, Q) := by
          rw [obj_diag, hF]
        rw [← hQdef, e]
        obtain ⟨a1, a2⟩ := A28_A M hM qo qh R.qo_pos R.qo_e hqh Q Q hQ0 hQ0
        rw [← hV] at a1 a2
        refine ⟨a1, fun heq => ?_⟩
        obtain ⟨e1, e2⟩ := a2 heq
        exfalso
        rcases hp1.lt_or_eq with hp' | hp'
        · have := e2 hp'; rw [e1] at this; linarith [R.qh_lt]
        · -- `p = 1`: then `w = r F̄(q°) = w° ≤ s`
          have hwo : wo M qo qh = M.r * Fbar M.f qo := by
            unfold wo; rw [hp']; simp only [sub_self, zero_mul, add_zero, one_mul]
            field_simp [R.qo_pos.ne']
          rw [e1] at hF
          linarith
    · rw [(CV_mid M hM σ h w b hadm hsw hcw).1]
      obtain ⟨a1, a2⟩ := A28_A M hM qo qh R.qo_pos R.qo_e hqh Q (b * Q) hQ0
        (mul_nonneg hadm.2.1 hQ0)
      rw [← hV] at a1 a2
      refine ⟨a1, fun heq => Or.inl ⟨hsw, hcw, ?_, ?_, fun h' => absurd hA h'⟩⟩
      · rw [if_pos hA]; exact (a2 heq).1
      · exact (a2 heq).2
  · rw [if_neg hA] at hV
    have hsw' : M.s < wo M qo qh := lt_of_not_ge hA
    obtain ⟨hsr, hqh_pos, hqh_s, hqh_e, hqt_pos, hqt_e, hqt_s, hqc1, hqoqc, hqc2⟩ := R.caseB hsw'
    have hk0 : 0 < M.c + (1 - M.p) * M.s := by nlinarith
    have hV2pos : 0 < qc * (M.p * M.s - M.c) :=
      mul_pos (lt_trans R.qo_pos hqoqc) (by linarith)
    have hVpos : 0 < V := by rw [hV]; exact lt_of_lt_of_le hV2pos (le_max_left _ _)
    have hV3 : qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) =
        qt * (M.r * Fbar M.f qt - (M.c + (1 - M.p) * M.s)) := by ring
    have m2 := le_max_left (qc * (M.p * M.s - M.c)) (qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c))
    have m3 := le_max_right (qc * (M.p * M.s - M.c)) (qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c))
    rw [← hV] at m2 m3
    refine ⟨hVpos, ?_⟩
    by_cases hcw : w ≤ M.c / M.p
    · have := CV_low M hM σ h w b hadm hcw
      exact ⟨by linarith, fun heq => by linarith⟩
    push_neg at hcw
    by_cases hsw : M.s < w
    · rw [CV_hi M hM σ h w b hadm hsw]
      obtain ⟨hQ0', hmax⟩ := Q_max_hi M hM σ h w b hadm hsw
      obtain ⟨c1, c2⟩ := BR_char M hM w hadm.1 Q hQ0 hmax
      by_cases hwr : M.r ≤ w
      · rw [← hQdef, c1 hwr, zero_mul]
        exact ⟨hVpos.le, fun heq => by linarith⟩
      · have hF := c2 (lt_of_not_ge hwr)
        have hval : Q * (w - (M.c + (1 - M.p) * M.s)) =
            Q * (M.r * Fbar M.f Q - (M.c + (1 - M.p) * M.s)) := by rw [hF]
        rw [← hQdef, hval]
        obtain ⟨a1, a2⟩ := psi_max M hM (M.c + (1 - M.p) * M.s) qt hk0 hqt_pos hqt_e Q hQ0
        refine ⟨by linarith, fun heq => ?_⟩
        have hQt : Q = qt := a2 (le_antisymm a1 (by linarith))
        refine Or.inr ⟨hsw, hsw', hQt, ?_, by linarith⟩
        rw [← hF, hQt]
    · obtain ⟨hcv, hfeas⟩ := CV_mid M hM σ h w b hadm hsw hcw
      rw [hcv]
      obtain ⟨a1, a2⟩ := A28_B M hM qo qh qc R.qo_pos R.qo_e hqh hqoqc ⟨hqc1, hqc2⟩ _ hfeas
      refine ⟨by linarith, fun heq => Or.inl ⟨hsw, hcw, ?_, ?_, fun _ => by linarith⟩⟩
      · rw [if_neg hA]
        exact (a2 (le_antisymm a1 (by linarith))).1
      · exact (a2 (le_antisymm a1 (by linarith))).2

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

lemma wStar_id (M : Model) (hM : M.Std) (qt qo qh qc : ℝ) (hβ : 0 ≤ betaStar M qt qo qh qc) :
    wStar M qt qo qh qc * (M.p + (1 - M.p) * betaStar M qt qo qh qc) =
      M.r * (M.p * Fbar M.f (kappaStar M qt qo qh qc) + (1 - M.p) * betaStar M qt qo qh qc *
        Fbar M.f (betaStar M qt qo qh qc * kappaStar M qt qo qh qc)) := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  unfold wStar
  rw [div_mul_cancel₀]
  have : 0 ≤ (1 - M.p) * betaStar M qt qo qh qc := mul_nonneg (by linarith) hβ
  linarith

lemma hv_star (M : Model) (hM : M.Std) (qt qo qh qc : ℝ) (hβ : 0 ≤ betaStar M qt qo qh qc) :
    hv M (wStar M qt qo qh qc) (betaStar M qt qo qh qc) (kappaStar M qt qo qh qc) = 0 := by
  have := wStar_id M hM qt qo qh qc hβ
  unfold hv
  linarith

lemma qc_supp (M : Model) (hM : M.Std) (qh qc : ℝ) (hp1 : M.p = 1) (hqc0 : 0 ≤ qc)
    (hqc2 : M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
      M.s * (M.p * qc + (1 - M.p) * qh)) (hqcpos : 0 < qc) : qc ∈ supp M.abar := by
  have hs0 : 0 < M.s := by
    have := hM.assm1_s; have : 0 < M.c / M.p := div_pos hM.c_pos hM.p_pos; linarith
  refine ⟨hqc0, lt_of_not_ge (fun h => ?_)⟩
  have := Fbar_out M hM qc h
  rw [hp1, this] at hqc2
  simp only [sub_self, zero_mul, add_zero, mul_zero, one_mul] at hqc2
  nlinarith

/-- At the equilibrium contract, any valid continuation yields exactly `V*`. -/
lemma cv_star (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (R : Roots M qt qo qh qc)
    (V : ℝ) (hV : V = if wo M qo qh ≤ M.s then a28Obj M (qo, qh) else
        max (qc * (M.p * M.s - M.c)) (qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)))
    (σ : Profile) (h : ContOK M σ) :
    Admissible .flex (wStar M qt qo qh qc) (betaStar M qt qo qh qc) ∧
      contractValue M σ (wStar M qt qo qh qc) (betaStar M qt qo qh qc) = V := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hc0 := hM.c_pos
  have hcps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hcp : 0 < M.c / M.p := div_pos hc0 hp
  have hcps' : M.c / M.p < M.s := hM.assm1_s
  by_cases hA : wo M qo qh ≤ M.s
  · rw [if_pos hA] at hV
    have hκ : kappaStar M qt qo qh qc = qo := by unfold kappaStar; rw [if_pos hA]
    have hβ : betaStar M qt qo qh qc * qo = qh ∧ 0 ≤ betaStar M qt qo qh qc ∧
        betaStar M qt qo qh qc ≤ 1 := by
      by_cases hrs : M.r < M.s
      · have : betaStar M qt qo qh qc = 0 := by unfold betaStar; rw [if_pos hrs]
        rw [this, hqh.2 hrs]; norm_num
      · have : betaStar M qt qo qh qc = qh / qo := by
          unfold betaStar; rw [if_neg hrs, if_neg (fun h => not_lt.2 hA h.1), hκ]
        rw [this]
        refine ⟨div_mul_cancel₀ _ R.qo_pos.ne', div_nonneg R.qh0 R.qo_pos.le, ?_⟩
        rw [div_le_one R.qo_pos]; exact R.qh_lt.le
    obtain ⟨hβq, hβ0, hβ1⟩ := hβ
    have hD : 0 < M.p * qo + (1 - M.p) * qh := by nlinarith [R.qo_pos, R.qh0]
    have hw : wStar M qt qo qh qc = wo M qo qh := by
      have e := wStar_id M hM qt qo qh qc hβ0
      rw [hκ, hβq] at e
      unfold wo
      rw [eq_div_iff hD.ne']
      linear_combination qo * e - (1 - M.p) * (wStar M qt qo qh qc - M.r * Fbar M.f qh) * hβq
    set w := wStar M qt qo qh qc with hwdef
    set β := betaStar M qt qo qh qc with hβdef
    have hw0 : 0 < w := by rw [hw]; linarith [R.wo_gt]
    have hadm : Admissible .flex w β := ⟨hw0, hβ0, hβ1⟩
    refine ⟨hadm, ?_⟩
    have hsw : ¬ M.s < w := by rw [hw]; exact not_lt.2 hA
    have hcw : M.c / M.p < w := by rw [hw]; exact R.wo_gt
    obtain ⟨hQ0, hmax⟩ := Q_max_mid M hM σ h w β hadm hsw hcw
    have hfoc := Bv_foc M hM w β _ hQ0 hmax
    have hhv := hv_star M hM qt qo qh qc hβ0
    rw [hκ] at hhv
    have hQ := Bv_unique' M hM w β _ qo hβ0 hQ0 hfoc R.qo_pos (Or.inl R.qo_s) hhv
    rw [(CV_mid M hM σ h w β hadm hsw hcw).1, hQ, hβq, hV]
  · rw [if_neg hA] at hV
    have hsw' : M.s < wo M qo qh := lt_of_not_ge hA
    obtain ⟨hsr, hqh_pos, hqh_s, hqh_e, hqt_pos, hqt_e, hqt_s, hqc1, hqoqc, hqc2⟩ :=
      R.caseB hsw'
    have hqc_pos : 0 < qc := lt_trans R.qo_pos hqoqc
    have hk0 : 0 < M.c + (1 - M.p) * M.s := by nlinarith
    by_cases h32 : qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) ≤ qc * (M.p * M.s - M.c)
    · have hκ : kappaStar M qt qo qh qc = qc := by unfold kappaStar; rw [if_neg hA, if_pos h32]
      have hβe : betaStar M qt qo qh qc = qh / qc := by
        unfold betaStar
        rw [if_neg (not_lt.2 hsr.le), if_neg (fun h => not_lt.2 h32 h.2), hκ]
      have hβq : betaStar M qt qo qh qc * qc = qh := by rw [hβe]; exact div_mul_cancel₀ _ hqc_pos.ne'
      have hβ0 : 0 < betaStar M qt qo qh qc := by rw [hβe]; exact div_pos hqh_pos hqc_pos
      have hβ1 : betaStar M qt qo qh qc ≤ 1 := by rw [hβe, div_le_one hqc_pos]; exact hqc1
      have hD : 0 < M.p * qc + (1 - M.p) * qh := by nlinarith
      have hw : wStar M qt qo qh qc = M.s := by
        have e := wStar_id M hM qt qo qh qc hβ0.le
        rw [hκ, hβq] at e
        have : wStar M qt qo qh qc * (M.p * qc + (1 - M.p) * qh) = M.s * (M.p * qc + (1 - M.p) * qh) := by
          linear_combination qc * e - (1 - M.p) * (wStar M qt qo qh qc - M.r * Fbar M.f qh) * hβq + hqc2
        exact mul_right_cancel₀ hD.ne' this
      set w := wStar M qt qo qh qc with hwdef
      set β := betaStar M qt qo qh qc with hβdef
      have hadm : Admissible .flex w β := ⟨by rw [hw]; linarith, hβ0.le, hβ1⟩
      refine ⟨hadm, ?_⟩
      have hsw : ¬ M.s < w := by rw [hw]; exact lt_irrefl _
      have hcw : M.c / M.p < w := by rw [hw]; exact hcps'
      obtain ⟨hQ0, hmax⟩ := Q_max_mid M hM σ h w β hadm hsw hcw
      have hfoc := Bv_foc M hM w β _ hQ0 hmax
      have hhv := hv_star M hM qt qo qh qc hβ0.le
      rw [hκ] at hhv
      have hcond : qc ∈ supp M.abar ∨ (M.p < 1 ∧ 0 < β ∧ β * qc ∈ supp M.abar) := by
        rcases hp1.lt_or_eq with hp' | hp'
        · exact Or.inr ⟨hp', hβ0, by rw [hβq]; exact hqh_s⟩
        · exact Or.inl (qc_supp M hM qh qc hp' hqc_pos.le hqc2 hqc_pos)
      have hQ := Bv_unique' M hM w β _ qc hβ0.le hQ0 hfoc hqc_pos hcond hhv
      rw [(CV_mid M hM σ h w β hadm hsw hcw).1, hQ, hβq, hV, max_eq_left h32]
      unfold a28Obj; simp only; linarith [hqc2]
    · push_neg at h32
      have hκ : kappaStar M qt qo qh qc = qt := by
        unfold kappaStar; rw [if_neg hA, if_neg (not_le.2 h32)]
      have hβe : betaStar M qt qo qh qc = 1 := by
        unfold betaStar; rw [if_neg (not_lt.2 hsr.le), if_pos ⟨hsw', h32⟩]
      have hw : wStar M qt qo qh qc = M.r * Fbar M.f qt := by
        unfold wStar; rw [hκ, hβe]; field_simp
      have hFt : M.r * Fbar M.f qt - (M.c + (1 - M.p) * M.s) = M.r * qt * M.f qt := by
        unfold G at hqt_e; linarith
      have hft := hM.f_pos qt hqt_s
      have hkcp : M.c / M.p ≤ M.c + (1 - M.p) * M.s := by
        rw [div_le_iff₀ hp]; nlinarith
      set w := wStar M qt qo qh qc with hwdef
      set β := betaStar M qt qo qh qc with hβdef
      have hcw : M.c / M.p < w := by
        rw [hw]; have : 0 < M.r * qt * M.f qt := by positivity
        linarith
      have hadm : Admissible .flex w β := ⟨by linarith, by rw [hβe]; norm_num, by rw [hβe]⟩
      refine ⟨hadm, ?_⟩
      have hV3 : V = qt * (M.r * Fbar M.f qt - (M.c + (1 - M.p) * M.s)) := by
        rw [hV, max_eq_right h32.le]; ring
      by_cases hsw : M.s < w
      · rw [CV_hi M hM σ h w β hadm hsw]
        obtain ⟨hQ0, hmax⟩ := Q_max_hi M hM σ h w β hadm hsw
        have hmt : ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w qt := by
          intro q' _
          have := bEP_support M hM w qt q'
          rw [hw, sub_self, mul_zero, add_zero] at this
          rw [hw]; exact this
        have hQ := buyer_unique M hM w hadm.1 _ qt hQ0 hqt_pos.le hmax hmt
        rw [hQ, hV3, hw]
      · have hhv := hv_star M hM qt qo qh qc (by show 0 ≤ β; rw [hβe]; norm_num)
        rw [hκ] at hhv
        obtain ⟨hQ0, hmax⟩ := Q_max_mid M hM σ h w β hadm hsw hcw
        have hfoc := Bv_foc M hM w β _ hQ0 hmax
        have hQ := Bv_unique' M hM w β _ qt (by rw [hβe]; norm_num) hQ0 hfoc hqt_pos
          (Or.inl hqt_s) hhv
        rw [(CV_mid M hM σ h w β hadm hsw hcw).1, hQ, hβe, one_mul, obj_diag, hV3]

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

lemma outcome_II (M : Model) (hM : M.Std) (qt qo qh qc : ℝ) (σ : Profile) (h : ContOK M σ)
    (hadm : Admissible .flex σ.w σ.b) (hsw : ¬ M.s < σ.w) (hcw : M.c / M.p < σ.w)
    (hQ : σ.Q σ.w σ.b = kappaStar M qt qo qh qc) (hκ : 0 < kappaStar M qt qo qh qc)
    (hβ0 : 0 ≤ betaStar M qt qo qh qc) (hβ1 : betaStar M qt qo qh qc ≤ 1)
    (hbq : M.p < 1 → σ.b * kappaStar M qt qo qh qc =
      betaStar M qt qo qh qc * kappaStar M qt qo qh qc) :
    σ.w = wStar M qt qo qh qc ∧
      σ.Q σ.w σ.b = kappaStar M qt qo qh qc ∧
      σ.Y σ.w σ.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
      ∀ α : Bool, (α = true ∨ M.p < 1) →
        σ.Z σ.w σ.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
          kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc) := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  set κ := kappaStar M qt qo qh qc with hκdef
  set β := betaStar M qt qo qh qc with hβdef
  obtain ⟨hQ0, hmax⟩ := Q_max_mid M hM σ h σ.w σ.b hadm hsw hcw
  have hprice := Bv_price M hM σ.w σ.b _ hQ0 hmax
  rw [hQ] at hprice
  have hid := wStar_id M hM qt qo qh qc hβ0
  rw [← hκdef, ← hβdef] at hid
  have hpos : 0 < M.p + (1 - M.p) * β := by nlinarith
  have hY := Y_q M hM σ h σ.w σ.b κ hadm hκ.le hcw
  refine ⟨?_, hQ, hY, ?_⟩
  · rcases hp1.lt_or_eq with hp' | hp'
    · have hb : σ.b = β := mul_right_cancel₀ hκ.ne' (hbq hp')
      rw [hb] at hprice
      have e : σ.w * (M.p + (1 - M.p) * β) = wStar M qt qo qh qc * (M.p + (1 - M.p) * β) := by
        rw [hid]
        have := mul_right_cancel₀ hκ.ne' (show σ.w * (M.p + (1 - M.p) * β) * κ =
          M.r * (M.p * Fbar M.f κ + (1 - M.p) * β * Fbar M.f (β * κ)) * κ by
            linear_combination hprice)
        exact this
      exact mul_right_cancel₀ hpos.ne' e
    · rw [hp'] at hprice hid
      simp only [sub_self, zero_mul, add_zero, one_mul, mul_one] at hprice hid
      have : σ.w = M.r * Fbar M.f κ := by
        have := mul_right_cancel₀ hκ.ne' (show σ.w * κ = M.r * Fbar M.f κ * κ by linarith)
        exact this
      rw [this, ← hid]
  · intro α hα
    have hbq' : σ.b * κ ≤ κ := by nlinarith [hadm.2.2, hadm.2.1]
    cases α with
    | true =>
      rw [Z_true M σ h σ.w σ.b κ κ hadm hκ.le hκ.le, if_neg hsw, min_self, max_eq_right hbq']
      simp only [if_true]
      rw [max_eq_left hβ1, mul_one]
    | false =>
      have hp' : M.p < 1 := hα.resolve_left (by decide)
      rw [Z_false M σ h σ.w σ.b κ κ hadm hκ.le hκ.le, if_neg hsw, hbq hp']
      simp only [Bool.false_eq_true, if_false]
      rw [max_eq_right hβ0, mul_comm]

lemma outcome_I (M : Model) (hM : M.Std) (qt : ℝ) (σ : Profile) (h : ContOK M σ)
    (hadm : Admissible .flex σ.w σ.b) (hsw : M.s < σ.w) (hQ : σ.Q σ.w σ.b = qt) (hqt : 0 < qt) :
    σ.Y σ.w σ.b qt = qt ∧ ∀ α : Bool, σ.Z σ.w σ.b qt qt α = qt := by
  have hY := Y_q M hM σ h σ.w σ.b qt hadm hqt.le (lt_trans (cp_lt_s M hM) hsw)
  refine ⟨hY, fun α => ?_⟩
  cases α with
  | true => rw [Z_true M σ h σ.w σ.b qt qt hadm hqt.le hqt.le, if_pos hsw]
  | false => rw [Z_false M σ h σ.w σ.b qt qt hadm hqt.le hqt.le, if_pos hsw]

/-- Every equilibrium has outcome `V*` and therefore one of the two outcome shapes. -/
lemma eq_outcome (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (R : Roots M qt qo qh qc) (σ : Profile) (hσ : IsSPE M .flex σ) :
    (¬ M.s < σ.w ∧ M.c / M.p < σ.w ∧
        σ.Q σ.w σ.b = (if wo M qo qh ≤ M.s then qo else qc) ∧
        (M.p < 1 → σ.b * σ.Q σ.w σ.b = qh) ∧
        (¬ wo M qo qh ≤ M.s →
          qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) ≤ qc * (M.p * M.s - M.c))) ∨
      (M.s < σ.w ∧ M.s < wo M qo qh ∧ σ.Q σ.w σ.b = qt ∧ σ.w = M.r * Fbar M.f qt ∧
        qc * (M.p * M.s - M.c) ≤ qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)) := by
  have h := contOK_of M σ hσ
  obtain ⟨V, hV⟩ : ∃ V, V = if wo M qo qh ≤ M.s then a28Obj M (qo, qh) else
      max (qc * (M.p * M.s - M.c)) (qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)) :=
    ⟨_, rfl⟩
  obtain ⟨hadm, hcv⟩ := cv_star M hM qt qo qh qc hqh R V hV σ h
  have htop := hσ.2.2.2.2 _ _ hadm
  obtain ⟨_, hle, heq⟩ := bound M hM qt qo qh qc hqh R V hV σ h σ.w σ.b hσ.2.2.2.1
  exact heq (le_antisymm hle (by rw [← hcv]; exact htop))

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

/-- The delivery rule of the constructed equilibrium. -/
noncomputable def Zf (M : Model) (w b q y : ℝ) (α : Bool) : ℝ :=
  if α then (if M.s < w then q else max (b * q) (min y q)) else (if M.s < w then q else b * q)

/-- The production rule of the constructed equilibrium. -/
noncomputable def Yf (M : Model) (w b q : ℝ) : ℝ := if M.c / M.p ≤ w then q else b * q

lemma isLeast_Zf (M : Model) (w b q y : ℝ) (α : Bool) (hw : 0 < w) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hq : 0 ≤ q) (hy : 0 ≤ y) :
    IsLeast {z | z ∈ Set.Icc (b * q) q ∧
        ∀ z' ∈ Set.Icc (b * q) q, supplierExPost M w y z' α ≤ supplierExPost M w y z α}
      (Zf M w b q y α) := by
  have hbq : b * q ≤ q := by nlinarith
  have hbq0 : 0 ≤ b * q := mul_nonneg hb0 hq
  cases α with
  | false =>
    have hπ : ∀ z', 0 ≤ z' → supplierExPost M w y z' false = (w - M.s) * z' - M.c * y := by
      intro z' hz'
      unfold supplierExPost
      simp only [Bool.false_eq_true, if_false, sub_zero, max_eq_left hz']
      ring
    unfold Zf
    simp only [Bool.false_eq_true, if_false]
    split_ifs with hsw
    · refine ⟨⟨⟨hbq, le_rfl⟩, fun z' hz' => ?_⟩, fun z hz => ?_⟩
      · rw [hπ z' (le_trans hbq0 hz'.1), hπ q hq]; nlinarith [hz'.2]
      · have h1 := hz.2 q ⟨hbq, le_rfl⟩
        rw [hπ q hq, hπ z (le_trans hbq0 hz.1.1)] at h1
        nlinarith
    · push_neg at hsw
      refine ⟨⟨⟨le_rfl, hbq⟩, fun z' hz' => ?_⟩, fun z hz => hz.1.1⟩
      rw [hπ z' (le_trans hbq0 hz'.1), hπ _ hbq0]; nlinarith [hz'.1]
  | true =>
    have hπ : ∀ z', supplierExPost M w y z' true = w * z' - M.c * y - M.s * max (z' - y) 0 := by
      intro z'; unfold supplierExPost; simp
    unfold Zf
    simp only [if_true]
    split_ifs with hsw
    · have hmono : ∀ z', z' ≤ q → w * z' - M.c * y - M.s * max (z' - y) 0 ≤
          w * q - M.c * y - M.s * max (q - y) 0 := by
        intro z' hz'
        have hm : max (q - y) 0 - max (z' - y) 0 ≤ q - z' := by
          simp only [max_def]; split_ifs <;> linarith
        have hm' : 0 ≤ max (q - y) 0 - max (z' - y) 0 := by
          simp only [max_def]; split_ifs <;> linarith
        rcases le_or_gt 0 M.s with h0 | h0 <;> nlinarith
      refine ⟨⟨⟨hbq, le_rfl⟩, fun z' hz' => ?_⟩, fun z hz => ?_⟩
      · rw [hπ, hπ]; exact hmono z' hz'.2
      · by_contra hlt
        push_neg at hlt
        have h1 := hz.2 q ⟨hbq, le_rfl⟩
        rw [hπ, hπ] at h1
        have hm : max (q - y) 0 - max (z - y) 0 ≤ q - z := by
          simp only [max_def]; split_ifs <;> linarith
        have hm' : 0 ≤ max (q - y) 0 - max (z - y) 0 := by
          simp only [max_def]; split_ifs <;> linarith
        rcases le_or_gt 0 M.s with h0 | h0 <;> nlinarith
    · push_neg at hsw
      set m := max (b * q) (min y q) with hmdef
      have hm1 : b * q ≤ m := le_max_left _ _
      have hm2 : m ≤ q := max_le hbq (min_le_right _ _)
      refine ⟨⟨⟨hm1, hm2⟩, fun z' hz' => ?_⟩, fun z hz => ?_⟩
      · rw [hπ, hπ]
        obtain ⟨hz1, hz2⟩ := hz'
        simp only [hmdef, max_def, min_def]
        split_ifs <;> nlinarith
      · by_contra hlt
        push_neg at hlt
        have h1 := hz.2 m ⟨hm1, hm2⟩
        rw [hπ, hπ] at h1
        have hzy : z < y := by
          have : z < min y q := by
            rcases le_total (b * q) (min y q) with hh | hh
            · rw [hmdef, max_eq_right hh] at hlt; exact hlt
            · rw [hmdef, max_eq_left hh] at hlt; linarith [hz.1.1]
          exact lt_of_lt_of_le this (min_le_left _ _)
        have hmy : m ≤ y := by
          rcases le_total (b * q) (min y q) with hh | hh
          · rw [hmdef, max_eq_right hh]; exact min_le_left _ _
          · rw [hmdef, max_eq_left hh] at hlt ⊢; linarith [hz.1.1]
        rw [max_eq_right (by linarith : z - y ≤ 0), max_eq_right (by linarith : m - y ≤ 0)] at h1
        nlinarith

/-- Below `c/p` the input `b q` is optimal. -/
lemma pv_low_opt (M : Model) (hM : M.Std) (w b q y : ℝ) (hsw : ¬ M.s < w) (hcw : w ≤ M.c / M.p)
    (hq : 0 ≤ q) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hy : 0 ≤ y) :
    pv M w b q y ≤ pv M w b q (b * q) := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hc := hM.c_pos
  have hps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hpw : M.p * w ≤ M.c := by rw [le_div_iff₀ hp] at hcw; linarith
  have hbq : b * q ≤ q := by nlinarith
  have hbq0 : 0 ≤ b * q := mul_nonneg hb0 hq
  rw [pv_mid M w b q y hsw hq hb0, pv_mid M w b q (b * q) hsw hq hb0, min_eq_left hbq,
    max_self, sub_self, max_eq_left le_rfl]
  push_neg at hsw
  rcases le_total y (b * q) with h1 | h1
  · rw [min_eq_left (le_trans h1 hbq), max_eq_left h1, max_eq_left (by linarith)]
    nlinarith
  · rcases le_total y q with h2 | h2
    · rw [min_eq_left h2, max_eq_right h1, sub_self, max_eq_left le_rfl]
      nlinarith
    · rw [min_eq_right h2, max_eq_right hbq, max_eq_right (by linarith)]
      nlinarith

/-- Existence of a best order in the region `w ≤ s`. -/
lemma Bv_exists (M : Model) (hM : M.Std) (w b : ℝ) (hw : 0 < w) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ Q, 0 ≤ Q ∧ ∀ q', 0 ≤ q' → Bv M w b q' ≤ Bv M w b Q := by
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hr := r_pos M hM
  by_cases h0 : hv M w b 0 ≤ 0
  · refine ⟨0, le_rfl, fun q' hq' => ?_⟩
    have := Bv_support M hM w b 0 q' hp1 hp.le
    nlinarith
  push_neg at h0
  -- a point where `h ≤ 0`
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    ((Fbar_tendsto M hM).eventually (gt_mem_nhds (div_pos hw hr)))
  set x1 := max x0 1
  have hx1 : M.r * Fbar M.f x1 < w := by
    have := hx0 x1 (le_max_left _ _); rw [lt_div_iff₀ hr] at this; linarith
  have hx1pos : 0 < x1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 ≤ R ∧ hv M w b R ≤ 0 := by
    rcases hb0.lt_or_eq with hbp | hbz
    · refine ⟨x1 / b, by positivity, ?_⟩
      have hbx : b * (x1 / b) = x1 := by field_simp
      have hle : x1 ≤ x1 / b := by rw [le_div_iff₀ hbp]; nlinarith
      have hF := Fbar_anti M hM hle
      unfold hv
      rw [hbx]
      have e1 : M.p * (M.r * Fbar M.f (x1 / b) - w) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp.le (by nlinarith)
      have e2 : (1 - M.p) * b * (M.r * Fbar M.f x1 - w) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hb0) (by linarith)
      linarith
    · refine ⟨x1, hx1pos.le, ?_⟩
      unfold hv
      rw [← hbz]
      have e1 : M.p * (M.r * Fbar M.f x1 - w) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith)
      simp only [mul_zero, zero_mul, add_zero]
      linarith
  obtain ⟨κ, hκ, hκ0⟩ := intermediate_value_Icc' hR0 (hv_cont M hM w b).continuousOn
    ⟨hR, h0.le⟩
  exact ⟨κ, hκ.1, Bv_suff M hM w b κ hκ0⟩

end Flex

namespace Flex
open T6Fbar T6Psi T6Aux T2

/-- Facts about the equilibrium contract of Theorem 3. -/
lemma star_facts (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (R : Roots M qt qo qh qc) :
    Admissible .flex (wStar M qt qo qh qc) (betaStar M qt qo qh qc) ∧
      M.c / M.p < wStar M qt qo qh qc ∧ 0 < kappaStar M qt qo qh qc ∧
      (M.s < wStar M qt qo qh qc → betaStar M qt qo qh qc = 1) ∧
      hv M (wStar M qt qo qh qc) (betaStar M qt qo qh qc) (kappaStar M qt qo qh qc) = 0 ∧
      (wo M qo qh ≤ M.s → kappaStar M qt qo qh qc = qo ∧
        betaStar M qt qo qh qc * qo = qh) ∧
      (¬ wo M qo qh ≤ M.s →
        qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) ≤ qc * (M.p * M.s - M.c) →
        kappaStar M qt qo qh qc = qc ∧ betaStar M qt qo qh qc * qc = qh) := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hc0 := hM.c_pos
  have hcps : M.c < M.p * M.s := by
    have := hM.assm1_s; rw [div_lt_iff₀ hp] at this; linarith
  have hcps' : M.c / M.p < M.s := hM.assm1_s
  -- the scenario facts for the binding case
  have hB2 : ¬ wo M qo qh ≤ M.s →
      qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) ≤ qc * (M.p * M.s - M.c) →
      kappaStar M qt qo qh qc = qc ∧ betaStar M qt qo qh qc * qc = qh := by
    intro hA h32
    obtain ⟨hsr, hqh_pos, _, _, _, _, _, _, hqoqc, _⟩ := R.caseB (lt_of_not_ge hA)
    have hqc_pos : 0 < qc := lt_trans R.qo_pos hqoqc
    have hκ : kappaStar M qt qo qh qc = qc := by unfold kappaStar; rw [if_neg hA, if_pos h32]
    refine ⟨hκ, ?_⟩
    have hβe : betaStar M qt qo qh qc = qh / qc := by
      unfold betaStar
      rw [if_neg (not_lt.2 hsr.le), if_neg (fun h => not_lt.2 h32 h.2), hκ]
    rw [hβe]; exact div_mul_cancel₀ _ hqc_pos.ne'
  have hA1 : wo M qo qh ≤ M.s → kappaStar M qt qo qh qc = qo ∧
      betaStar M qt qo qh qc * qo = qh := by
    intro hA
    have hκ : kappaStar M qt qo qh qc = qo := by unfold kappaStar; rw [if_pos hA]
    refine ⟨hκ, ?_⟩
    by_cases hrs : M.r < M.s
    · have : betaStar M qt qo qh qc = 0 := by unfold betaStar; rw [if_pos hrs]
      rw [this, hqh.2 hrs, zero_mul]
    · have : betaStar M qt qo qh qc = qh / qo := by
        unfold betaStar; rw [if_neg hrs, if_neg (fun h => not_lt.2 hA h.1), hκ]
      rw [this]; exact div_mul_cancel₀ _ R.qo_pos.ne'
  by_cases hA : wo M qo qh ≤ M.s
  · obtain ⟨hκ, hβq⟩ := hA1 hA
    have hβ0 : 0 ≤ betaStar M qt qo qh qc := by
      by_cases hrs : M.r < M.s
      · have : betaStar M qt qo qh qc = 0 := by unfold betaStar; rw [if_pos hrs]
        rw [this]
      · have : betaStar M qt qo qh qc = qh / qo := by
          unfold betaStar; rw [if_neg hrs, if_neg (fun h => not_lt.2 hA h.1), hκ]
        rw [this]; exact div_nonneg R.qh0 R.qo_pos.le
    have hβ1 : betaStar M qt qo qh qc ≤ 1 := by
      have : betaStar M qt qo qh qc * qo ≤ 1 * qo := by rw [hβq, one_mul]; exact R.qh_lt.le
      exact le_of_mul_le_mul_right this R.qo_pos
    have hD : 0 < M.p * qo + (1 - M.p) * qh := by nlinarith [R.qo_pos, R.qh0]
    have hw : wStar M qt qo qh qc = wo M qo qh := by
      have e := wStar_id M hM qt qo qh qc hβ0
      rw [hκ, hβq] at e
      unfold wo
      rw [eq_div_iff hD.ne']
      linear_combination qo * e - (1 - M.p) * (wStar M qt qo qh qc - M.r * Fbar M.f qh) * hβq
    refine ⟨⟨by rw [hw]; linarith [R.wo_gt, div_pos hc0 hp], hβ0, hβ1⟩, by rw [hw]; exact R.wo_gt,
      by rw [hκ]; exact R.qo_pos, fun h => absurd (hw ▸ h) (not_lt.2 hA),
      hv_star M hM qt qo qh qc hβ0, hA1, hB2⟩
  · have hsw' : M.s < wo M qo qh := lt_of_not_ge hA
    obtain ⟨hsr, hqh_pos, hqh_s, hqh_e, hqt_pos, hqt_e, hqt_s, hqc1, hqoqc, hqc2⟩ := R.caseB hsw'
    have hqc_pos : 0 < qc := lt_trans R.qo_pos hqoqc
    by_cases h32 : qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) ≤ qc * (M.p * M.s - M.c)
    · obtain ⟨hκ, hβq⟩ := hB2 hA h32
      have hβe : betaStar M qt qo qh qc = qh / qc := by
        unfold betaStar
        rw [if_neg (not_lt.2 hsr.le), if_neg (fun h => not_lt.2 h32 h.2), hκ]
      have hβ0 : 0 < betaStar M qt qo qh qc := by rw [hβe]; exact div_pos hqh_pos hqc_pos
      have hβ1 : betaStar M qt qo qh qc ≤ 1 := by rw [hβe, div_le_one hqc_pos]; exact hqc1
      have hD : 0 < M.p * qc + (1 - M.p) * qh := by nlinarith
      have hw : wStar M qt qo qh qc = M.s := by
        have e := wStar_id M hM qt qo qh qc hβ0.le
        rw [hκ, hβq] at e
        have : wStar M qt qo qh qc * (M.p * qc + (1 - M.p) * qh) =
            M.s * (M.p * qc + (1 - M.p) * qh) := by
          linear_combination qc * e - (1 - M.p) * (wStar M qt qo qh qc - M.r * Fbar M.f qh) * hβq + hqc2
        exact mul_right_cancel₀ hD.ne' this
      refine ⟨⟨by rw [hw]; linarith [div_pos hc0 hp], hβ0.le, hβ1⟩, by rw [hw]; exact hcps',
        by rw [hκ]; exact hqc_pos, fun h => absurd (hw ▸ h) (lt_irrefl _),
        hv_star M hM qt qo qh qc hβ0.le, fun h => absurd h hA, hB2⟩
    · push_neg at h32
      have hκ : kappaStar M qt qo qh qc = qt := by
        unfold kappaStar; rw [if_neg hA, if_neg (not_le.2 h32)]
      have hβe : betaStar M qt qo qh qc = 1 := by
        unfold betaStar; rw [if_neg (not_lt.2 hsr.le), if_pos ⟨hsw', h32⟩]
      have hw : wStar M qt qo qh qc = M.r * Fbar M.f qt := by
        unfold wStar; rw [hκ, hβe]; field_simp
      have hFt : M.r * Fbar M.f qt - (M.c + (1 - M.p) * M.s) = M.r * qt * M.f qt := by
        unfold G at hqt_e; linarith
      have hft := hM.f_pos qt hqt_s
      have hkcp : M.c / M.p ≤ M.c + (1 - M.p) * M.s := by
        rw [div_le_iff₀ hp]; nlinarith
      have hcw : M.c / M.p < wStar M qt qo qh qc := by
        rw [hw]; have : 0 < M.r * qt * M.f qt := by positivity
        linarith
      refine ⟨⟨by linarith [div_pos hc0 hp], by rw [hβe]; norm_num, by rw [hβe]⟩, hcw,
        by rw [hκ]; exact hqt_pos, fun _ => hβe, hv_star M hM qt qo qh qc (by rw [hβe]; norm_num),
        fun h => absurd h hA, fun _ h => absurd h (not_le.2 h32)⟩

end Flex

open T6Fbar T6Psi T6Aux T2 Flex in
theorem solution (M : Model) (hM : M.Std) (qt qo qh qc : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hqc : M.s < wo M qo qh → qh ≤ qc ∧
      M.r * (M.p * qc * Fbar M.f qc + (1 - M.p) * qh * Fbar M.f qh) =
        M.s * (M.p * qc + (1 - M.p) * qh)) :
    (∃ σ : Profile, IsSPE M .flex σ ∧ σ.w = wStar M qt qo qh qc ∧
        σ.b = betaStar M qt qo qh qc ∧
        σ.Q σ.w σ.b = kappaStar M qt qo qh qc ∧
        σ.Y σ.w σ.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
        ∀ α : Bool, σ.Z σ.w σ.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
          kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc)) ∧
    (¬ (M.s < wo M qo qh ∧
        qc * (M.p * M.s - M.c) = qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)) →
      ∀ σ : Profile, IsSPE M .flex σ →
        σ.w = wStar M qt qo qh qc ∧
        σ.Q σ.w σ.b = kappaStar M qt qo qh qc ∧
        σ.Y σ.w σ.b (kappaStar M qt qo qh qc) = kappaStar M qt qo qh qc ∧
        ∀ α : Bool, (α = true ∨ M.p < 1) →
          σ.Z σ.w σ.b (kappaStar M qt qo qh qc) (kappaStar M qt qo qh qc) α =
            kappaStar M qt qo qh qc * max (if α then 1 else 0) (betaStar M qt qo qh qc)) := by
  have R := roots M hM qt qo qh qc hqt hqo hqh hqc
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  have hcps' : M.c / M.p < M.s := hM.assm1_s
  obtain ⟨hadmS, hcwS, hκS, hsβ, hhvS, hA1, hB2⟩ := star_facts M hM qt qo qh qc hqh R
  set κ := kappaStar M qt qo qh qc with hκdef
  set β := betaStar M qt qo qh qc with hβdef
  set wS := wStar M qt qo qh qc with hwdef
  obtain ⟨V, hV⟩ : ∃ V, V = if wo M qo qh ≤ M.s then a28Obj M (qo, qh) else
      max (qc * (M.p * M.s - M.c)) (qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c)) :=
    ⟨_, rfl⟩
  constructor
  · -- existence
    have hQex : ∀ w b : ℝ, ∃ Q : ℝ, Admissible .flex w b → 0 ≤ Q ∧ ∀ q', 0 ≤ q' →
        Eα M.p (fun α => buyerExPost M w (Zf M w b q' (Yf M w b q') α)) ≤
          Eα M.p (fun α => buyerExPost M w (Zf M w b Q (Yf M w b Q) α)) := by
      intro w b
      by_cases hadm : Admissible .flex w b
      · obtain ⟨hw, hb0, hb1⟩ := hadm
        have hOV : ∀ q, 0 ≤ q → Eα M.p (fun α => buyerExPost M w (Zf M w b q (Yf M w b q) α)) =
            if M.s < w then buyerExPost M w q else if M.c / M.p ≤ w then Bv M w b q
            else buyerExPost M w (b * q) := by
          intro q hq
          have hbq : b * q ≤ q := by nlinarith
          unfold Eα Zf Yf Bv
          by_cases hsw : M.s < w
          · rw [if_pos (le_of_lt (lt_trans hcps' hsw)), if_pos hsw]
            simp only [if_true, Bool.false_eq_true, if_false, if_pos hsw]; ring
          · rw [if_neg hsw]
            by_cases hcw : M.c / M.p ≤ w
            · rw [if_pos hcw, if_pos hcw]
              simp only [if_true, Bool.false_eq_true, if_false, if_neg hsw, min_self,
                max_eq_right hbq]
            · rw [if_neg hcw, if_neg hcw]
              simp only [if_true, Bool.false_eq_true, if_false, if_neg hsw, min_eq_left hbq,
                max_self]
              ring
        by_cases hsw : M.s < w
        · obtain ⟨Q, hQ0, hQ⟩ := BR_exists M hM w hw
          refine ⟨Q, fun _ => ⟨hQ0, fun q' hq' => ?_⟩⟩
          rw [hOV q' hq', hOV Q hQ0, if_pos hsw, if_pos hsw]; exact hQ q' hq'
        · by_cases hcw : M.c / M.p ≤ w
          · obtain ⟨Q, hQ0, hQ⟩ := Bv_exists M hM w b hw hb0 hb1
            refine ⟨Q, fun _ => ⟨hQ0, fun q' hq' => ?_⟩⟩
            rw [hOV q' hq', hOV Q hQ0, if_neg hsw, if_neg hsw, if_pos hcw, if_pos hcw]
            exact hQ q' hq'
          · rcases hb0.lt_or_eq with hbp | hbz
            · obtain ⟨X, hX0, hX⟩ := BR_exists M hM w hw
              refine ⟨X / b, fun _ => ⟨by positivity, fun q' hq' => ?_⟩⟩
              rw [hOV q' hq', hOV _ (by positivity), if_neg hsw, if_neg hsw, if_neg hcw,
                if_neg hcw, mul_div_cancel₀ _ hbp.ne']
              exact hX _ (mul_nonneg hb0 hq')
            · refine ⟨0, fun _ => ⟨le_rfl, fun q' hq' => ?_⟩⟩
              rw [hOV q' hq', hOV 0 le_rfl, if_neg hsw, if_neg hsw, if_neg hcw, if_neg hcw, ← hbz,
                zero_mul, zero_mul]
      · exact ⟨0, fun h => absurd h hadm⟩
    choose Qc hQc using hQex
    let σ : Profile := ⟨wS, β, fun w b => if w = wS ∧ b = β then κ else Qc w b, Yf M, Zf M⟩
    have hPV : ∀ w b q y, prodValue M σ w b q y = pv M w b q y := by
      intro w b q y
      show Eα M.p (fun α => supplierExPost M w y (Zf M w b q y α) α) = pv M w b q y
      unfold Eα supplierExPost pv Zf
      simp only [if_true, Bool.false_eq_true, if_false, sub_zero]
    have hcont : ContOK M σ := by
      refine ⟨?_, ?_, ?_⟩
      · intro w b q y α hadm hq hy
        exact isLeast_Zf M w b q y α hadm.1 hadm.2.1 hadm.2.2 hq hy
      · intro w b q hadm hq
        have hb0 := hadm.2.1
        have hb1 := hadm.2.2
        show 0 ≤ Yf M w b q ∧ ∀ y', 0 ≤ y' → prodValue M σ w b q y' ≤
          prodValue M σ w b q (Yf M w b q)
        unfold Yf
        by_cases hcw : M.c / M.p ≤ w
        · rw [if_pos hcw]
          refine ⟨hq, fun y' hy' => ?_⟩
          rw [hPV, hPV]
          by_cases hsw : M.s < w
          · by_cases hyq : y' = q
            · rw [hyq]
            · exact (pv_hi_lt M hM w b q y' hsw hq hyq).le
          · exact (pv_mid_le M hM w b q y' hsw hcw hq hb0 hb1 hy').1
        · rw [if_neg hcw]
          push_neg at hcw
          have hsw : ¬ M.s < w := by intro h'; linarith
          refine ⟨mul_nonneg hb0 hq, fun y' hy' => ?_⟩
          rw [hPV, hPV]
          exact pv_low_opt M hM w b q y' hsw hcw.le hq hb0 hb1 hy'
      · intro w b hadm
        show 0 ≤ (if w = wS ∧ b = β then κ else Qc w b) ∧ ∀ q', 0 ≤ q' →
          Eα M.p (fun α => buyerExPost M w (Zf M w b q' (Yf M w b q') α)) ≤
            Eα M.p (fun α => buyerExPost M w (Zf M w b (if w = wS ∧ b = β then κ else Qc w b)
              (Yf M w b (if w = wS ∧ b = β then κ else Qc w b)) α))
        by_cases hst : w = wS ∧ b = β
        · rw [if_pos hst]
          obtain ⟨hw', hb'⟩ := hst
          subst hw' hb'
          refine ⟨hκS.le, fun q' hq' => ?_⟩
          have hYq : ∀ q, Yf M wS β q = q := fun q => by unfold Yf; rw [if_pos hcwS.le]
          have hb0 := hadmS.2.1
          have hb1 := hadmS.2.2
          unfold Eα
          rw [hYq, hYq]
          unfold Zf
          by_cases hsw : M.s < wS
          · simp only [if_true, Bool.false_eq_true, if_false, if_pos hsw]
            have hβ1 := hsβ hsw
            have h0 : M.r * Fbar M.f κ - wS = 0 := by
              have := hhvS; rw [hβ1] at this; unfold hv at this; simp only [one_mul] at this
              linarith
            have := bEP_support M hM wS κ q'
            rw [h0, mul_zero, add_zero] at this
            nlinarith
          · simp only [if_true, Bool.false_eq_true, if_false, if_neg hsw, min_self]
            rw [max_eq_right (by nlinarith), max_eq_right (by nlinarith)]
            exact Bv_suff M hM wS β κ hhvS q' hq'
        · rw [if_neg hst]
          exact hQc w b hadm
    have htop : ∀ w' b', Admissible .flex w' b' →
        contractValue M σ w' b' ≤ contractValue M σ σ.w σ.b := by
      intro w' b' hadm
      have h1 := (bound M hM qt qo qh qc hqh R V hV σ hcont w' b' hadm).2.1
      have h2 := (cv_star M hM qt qo qh qc hqh R V hV σ hcont).2
      show contractValue M σ w' b' ≤ contractValue M σ wS β
      rw [h2]; exact h1
    refine ⟨σ, ⟨hcont.1, hcont.2.1, hcont.2.2, hadmS, htop⟩, rfl, rfl, ?_, ?_, ?_⟩
    · show (if wS = wS ∧ β = β then κ else Qc wS β) = κ
      rw [if_pos ⟨rfl, rfl⟩]
    · show Yf M wS β κ = κ
      unfold Yf; rw [if_pos hcwS.le]
    · intro α
      show Zf M wS β κ κ α = κ * max (if α then 1 else 0) β
      have hb0 := hadmS.2.1
      have hb1 := hadmS.2.2
      unfold Zf
      cases α with
      | true =>
        simp only [if_true]
        rw [max_eq_left hb1, mul_one]
        split_ifs
        · rfl
        · rw [min_self, max_eq_right (by nlinarith)]
      | false =>
        simp only [Bool.false_eq_true, if_false]
        split_ifs with hsw
        · rw [hsβ hsw, max_eq_right zero_le_one, mul_one]
        · rw [max_eq_right hb0, mul_comm]
  · -- uniqueness away from the tie
    intro hnt σ hσ
    have h := contOK_of M σ hσ
    rcases eq_outcome M hM qt qo qh qc hqh R σ hσ with ⟨hsw, hcw, hQ, hbq, hB⟩ |
        ⟨hsw, hswo, hQ, hw, h23⟩
    · by_cases hA : wo M qo qh ≤ M.s
      · rw [if_pos hA] at hQ
        obtain ⟨hκ, hβq⟩ := hA1 hA
        have hκ' : kappaStar M qt qo qh qc = qo := hκ
        have hβq' : betaStar M qt qo qh qc * qo = qh := hβq
        exact outcome_II M hM qt qo qh qc σ h hσ.2.2.2.1 hsw hcw (by rw [hQ]; exact hκ'.symm)
          hκS hadmS.2.1 hadmS.2.2
          (fun hp' => by have e1 := hbq hp'; rw [hQ] at e1; rw [hκ', e1, hβq'])
      · rw [if_neg hA] at hQ
        obtain ⟨hκ, hβq⟩ := hB2 hA (hB hA)
        have hκ' : kappaStar M qt qo qh qc = qc := hκ
        have hβq' : betaStar M qt qo qh qc * qc = qh := hβq
        exact outcome_II M hM qt qo qh qc σ h hσ.2.2.2.1 hsw hcw (by rw [hQ]; exact hκ'.symm)
          hκS hadmS.2.1 hadmS.2.2
          (fun hp' => by have e1 := hbq hp'; rw [hQ] at e1; rw [hκ', e1, hβq'])
    · have hlt : qc * (M.p * M.s - M.c) < qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) :=
        lt_of_le_of_ne h23 (fun he => hnt ⟨hswo, he⟩)
      have hA : ¬ wo M qo qh ≤ M.s := not_le.2 hswo
      obtain ⟨_, _, _, _, hqt_pos, _, _, _, _, _⟩ := R.caseB hswo
      have hκ : κ = qt := by
        rw [hκdef]; unfold kappaStar; rw [if_neg hA, if_neg (not_le.2 hlt)]
      have hβ : β = 1 := by
        obtain ⟨hsr, _⟩ := R.caseB hswo
        rw [hβdef]; unfold betaStar; rw [if_neg (not_lt.2 hsr.le), if_pos ⟨hswo, hlt⟩]
      have hwS : wS = M.r * Fbar M.f qt := by
        rw [hwdef]; unfold wStar; rw [← hκdef, ← hβdef, hκ, hβ]; field_simp
      obtain ⟨hY, hZ⟩ := outcome_I M hM qt σ h hσ.2.2.2.1 hsw hQ hqt_pos
      refine ⟨by rw [hw, hwS], by rw [hQ, hκ], by rw [hκ]; exact hY, fun α _ => ?_⟩
      rw [hκ, hZ α, hβ]
      cases α <;> simp
