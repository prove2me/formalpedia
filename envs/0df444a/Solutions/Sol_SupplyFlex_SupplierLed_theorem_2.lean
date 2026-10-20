-- Prove2me | solution 1 for SupplyFlex.SupplierLed.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:56:27.312031+00:00
-- url     : https://prove2.me/submissions/f77182f3-7c0a-41af-8f98-b9534fb9f231

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

open T6Fbar T6Psi T6Aux T2 in
theorem solution (M : Model) (hM : M.Std) (qstar : ℝ)
    (hqstar : (M.c + (1 - M.p) * M.s ≤ M.r →
        0 ≤ qstar ∧ M.r * G M.f qstar = M.c + (1 - M.p) * M.s) ∧
      (M.r < M.c + (1 - M.p) * M.s → qstar = 0)) :
    (∃ σ : Profile, IsSPE M .priceOnly σ ∧ σ.w = M.r * Fbar M.f qstar ∧
        σ.Q σ.w σ.b = qstar ∧ σ.Y σ.w σ.b qstar = qstar) ∧
    ∀ σ : Profile, IsSPE M .priceOnly σ →
      σ.Q σ.w σ.b = qstar ∧ σ.Y σ.w σ.b qstar = qstar ∧
      (0 < qstar → σ.w = M.r * Fbar M.f qstar) ∧ (qstar = 0 → M.r ≤ σ.w) := by
  have hr := r_pos M hM
  have hp := hM.p_pos
  have hp1 := hM.p_le_one
  set K := M.c + (1 - M.p) * M.s with hK
  have hs0 : 0 < M.s := by
    have := hM.assm1_s; have : 0 < M.c / M.p := div_pos hM.c_pos hp; linarith
  have hK0 : 0 < K := by have := hM.c_pos; nlinarith
  set ψ := fun q => q * (M.r * Fbar M.f q - K) with hψ
  have hqs0 : 0 ≤ qstar := by
    by_cases h : K ≤ M.r
    · exact (hqstar.1 h).1
    · rw [hqstar.2 (lt_of_not_ge h)]
  have hqs_supp : qstar ∈ supp M.abar := by
    by_cases h : K ≤ M.r
    · exact root_supp M hM K qstar hK0 (hqstar.1 h).1 (hqstar.1 h).2
    · rw [hqstar.2 (lt_of_not_ge h)]
      exact ⟨le_rfl, by simpa using hM.abar_pos⟩
  set wst := M.r * Fbar M.f qstar with hwst
  have hwst0 : 0 < wst := mul_pos hr (Fbar_pos M hM qstar hqs_supp)
  -- qstar is the buyer's best response to wst
  have hBRst : ∀ q', 0 ≤ q' → buyerExPost M wst q' ≤ buyerExPost M wst qstar := fun q' _ => by
    have := bEP_support M hM wst qstar q'
    rw [← hwst, sub_self, mul_zero, add_zero] at this
    exact this
  -- `ψ` is maximised at `q*`
  have hpsi_le : ∀ q, 0 ≤ q → ψ q ≤ ψ qstar := by
    intro q hq
    by_cases h : K ≤ M.r
    · obtain ⟨h0, he⟩ := hqstar.1 h
      rcases le_total qstar q with hle | hle
      · exact psi_anti M hM K qstar h0 he hK0 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hle) hle
      · exact psi_mono M hM K qstar hK0 h0 he ⟨hq, hle⟩ ⟨h0, le_rfl⟩ hle
    · rw [hqstar.2 (lt_of_not_ge h)]
      simp only [hψ, zero_mul]
      have := Fbar_le_one M hM q
      have hrK := lt_of_not_ge h
      have : M.r * Fbar M.f q - K ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hq this
  have hpsi_nn : 0 ≤ ψ qstar := by
    have := hpsi_le 0 le_rfl; simp only [hψ, zero_mul] at this; exact this
  -- value of any best response
  have hPhi : ∀ w, 0 < w → ∀ q, 0 ≤ q →
      (∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w q) → q * (w - K) ≤ ψ qstar := by
    intro w hw q hq hmax
    obtain ⟨h1, h2⟩ := BR_char M hM w hw q hq hmax
    by_cases hwr : M.r ≤ w
    · rw [h1 hwr, zero_mul]; exact hpsi_nn
    · have := h2 (lt_of_not_ge hwr)
      have e : q * (w - K) = ψ q := by simp only [hψ]; rw [this]
      rw [e]; exact hpsi_le q hq
  constructor
  · -- existence
    have hBR : ∀ w : ℝ, ∃ q : ℝ, 0 < w →
        0 ≤ q ∧ ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w q := by
      intro w
      by_cases hw : 0 < w
      · obtain ⟨q, hq⟩ := BR_exists M hM w hw; exact ⟨q, fun _ => hq⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose Qf hQf using hBR
    let σ : Profile := ⟨wst, 1, fun w _ => if w = wst then qstar else Qf w,
      fun _ _ q => q, fun _ _ q _ _ => q⟩
    have hOV : ∀ w b q, orderValue M σ w b q = buyerExPost M w q := by
      intro w b q; unfold orderValue Eα; ring
    have hQmax : ∀ w, 0 < w → 0 ≤ σ.Q w 1 ∧
        ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w (σ.Q w 1) := by
      intro w hw
      have hσQ : σ.Q w 1 = if w = wst then qstar else Qf w := rfl
      rw [hσQ]
      by_cases h : w = wst
      · rw [if_pos h, h]; exact ⟨hqs0, hBRst⟩
      · rw [if_neg h]; exact hQf w hw
    have hspe : IsSPE M .priceOnly σ := by
      refine ⟨?_, ?_, ?_, ⟨hwst0, rfl⟩, ?_⟩
      · intro w b q y α hadm hq hy
        have hb : b = 1 := hadm.2
        subst hb
        refine ⟨⟨⟨by rw [one_mul], le_rfl⟩, fun z' hz' => ?_⟩, fun z hz => ?_⟩
        · have : z' = q := le_antisymm hz'.2 (by simpa using hz'.1)
          rw [this]
        · simpa using hz.1.1
      · intro w b q hadm hq
        have hb : b = 1 := hadm.2
        subst hb
        refine ⟨hq, fun y' hy' => ?_⟩
        show Eα M.p (fun α => supplierExPost M w y' q α) ≤
          Eα M.p (fun α => supplierExPost M w q q α)
        by_cases h : y' = q
        · rw [h]
        · exact (prod_lt M hM w q y' hq h).le
      · intro w b hadm
        have hb : b = 1 := hadm.2
        subst hb
        refine ⟨(hQmax w hadm.1).1, fun q' hq' => ?_⟩
        rw [hOV, hOV]
        exact (hQmax w hadm.1).2 q' hq'
      · intro w' b' hadm
        have hb : b' = 1 := hadm.2
        subst hb
        have hcv : ∀ w, 0 < w → contractValue M σ w 1 = σ.Q w 1 * (w - K) := by
          intro w hw
          show Eα M.p (fun α => supplierExPost M w (σ.Q w 1) (σ.Q w 1) α) = _
          rw [prod_eq M w _ _ (hQmax w hw).1, sub_self, max_eq_left le_rfl]; ring
        show contractValue M σ w' 1 ≤ contractValue M σ wst 1
        rw [hcv w' hadm.1, hcv wst hwst0]
        have hq1 : σ.Q wst 1 = qstar := by show (if wst = wst then qstar else Qf wst) = qstar; simp
        rw [hq1]
        have := hPhi w' hadm.1 (σ.Q w' 1) (hQmax w' hadm.1).1 (hQmax w' hadm.1).2
        simp only [hψ] at this
        exact this
    refine ⟨σ, hspe, rfl, ?_, rfl⟩
    show (if wst = wst then qstar else Qf wst) = qstar
    simp
  · -- uniqueness
    intro σ hσ
    obtain ⟨hw, hb⟩ := hσ.2.2.2.1
    have hb1 : σ.b = 1 := hb
    rw [hb1]
    have hQmax : ∀ w, 0 < w → 0 ≤ σ.Q w 1 ∧
        ∀ q', 0 ≤ q' → buyerExPost M w q' ≤ buyerExPost M w (σ.Q w 1) := by
      intro w hw'
      have hadm : Admissible .priceOnly w 1 := ⟨hw', rfl⟩
      obtain ⟨h0, h1⟩ := hσ.2.2.1 w 1 hadm
      refine ⟨h0, fun q' hq' => ?_⟩
      rw [← orderValue_b1 M _ σ hσ w q' hadm hq', ← orderValue_b1 M _ σ hσ w _ hadm h0]
      exact h1 q' hq'
    set q := σ.Q σ.w 1 with hq
    obtain ⟨hq0, hqmax⟩ := hQmax σ.w hw
    have hQst : σ.Q wst 1 = qstar :=
      buyer_unique M hM wst hwst0 _ _ (hQmax wst hwst0).1 hqs0 (hQmax wst hwst0).2 hBRst
    have htop := hσ.2.2.2.2 wst 1 ⟨hwst0, rfl⟩
    rw [hb1, CV_eq M hM σ hσ wst hwst0, CV_eq M hM σ hσ σ.w hw, hQst] at htop
    have hle := hPhi σ.w hw q hq0 hqmax
    have heq : q * (σ.w - K) = ψ qstar := by
      apply le_antisymm hle; simp only [hψ]; rw [← hwst]; exact htop
    obtain ⟨hc1, hc2⟩ := BR_char M hM σ.w hw q hq0 hqmax
    have hY := Y_eq M hM σ hσ σ.w qstar hw hqs0
    have key : (0 < qstar → σ.w < M.r ∧ q = qstar) ∧ (qstar = 0 → M.r ≤ σ.w ∧ q = 0) := by
      constructor
      · intro hpos
        have hKr : K ≤ M.r := by
          by_contra h; exact absurd (hqstar.2 (lt_of_not_ge h)) hpos.ne'
        obtain ⟨_, he⟩ := hqstar.1 hKr
        have hpsi_pos : 0 < ψ qstar := by
          simp only [hψ]
          have hf := hM.f_pos qstar hqs_supp
          unfold G at he
          have : M.r * Fbar M.f qstar - K = M.r * qstar * M.f qstar := by linarith
          rw [this]; positivity
        have hwr : σ.w < M.r := by
          by_contra h
          have := hc1 (le_of_not_gt h)
          rw [this, zero_mul] at heq
          linarith
        refine ⟨hwr, ?_⟩
        have hFq := hc2 hwr
        have : ψ q = ψ qstar := by
          rw [← heq]; simp only [hψ]; rw [show M.r * Fbar M.f q = σ.w from hFq]
        exact psi_unique M hM K qstar hK0 hpos he q hq0 this
      · intro hz
        have hpsi0 : ψ qstar = 0 := by simp only [hψ]; rw [hz, zero_mul]
        by_contra hcon
        have hwr : σ.w < M.r := by
          by_contra h; push_neg at h
          exact hcon ⟨h, hc1 h⟩
        have hFq := hc2 hwr
        have hqpos : 0 < q := by
          rcases hq0.lt_or_eq with h | h
          · exact h
          · have h' : q = 0 := by rw [hq]; exact h.symm
            rw [h', Fbar_zero M hM, mul_one] at hFq; linarith
        have hneg : ψ q < 0 := by
          simp only [hψ]
          by_cases hKr : K ≤ M.r
          · have he := (hqstar.1 hKr).2
            rw [hz] at he; unfold G at he; rw [Fbar_zero M hM] at he
            have := Fbar_lt_one M hM q hqpos
            have : M.r * Fbar M.f q - K < 0 := by nlinarith
            exact mul_neg_of_pos_of_neg hqpos this
          · have := Fbar_le_one M hM q
            have : M.r * Fbar M.f q - K < 0 := by nlinarith
            exact mul_neg_of_pos_of_neg hqpos this
        have : ψ q = q * (σ.w - K) := by
          simp only [hψ]; rw [show M.r * Fbar M.f q = σ.w from hFq]
        rw [this, heq, hpsi0] at hneg
        exact lt_irrefl _ hneg
    refine ⟨?_, hY, ?_, ?_⟩
    · rcases hqs0.lt_or_eq with h | h
      · exact (key.1 h).2
      · rw [(key.2 h.symm).2, ← h]
    · intro hpos
      have ⟨hwr, hqq⟩ := key.1 hpos
      have := hc2 hwr
      rw [hqq] at this
      exact this.symm
    · intro hz; exact (key.2 hz).1
