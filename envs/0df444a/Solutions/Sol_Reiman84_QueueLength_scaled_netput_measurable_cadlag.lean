-- Prove2me | solution 1 for Reiman84.QueueLength.scaled_netput_measurable_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T13:25:02.427264+00:00
-- url     : https://prove2.me/submissions/e227e521-66a5-4c6f-9abb-ebd0e062d069

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

set_option autoImplicit false

/-! Child MeasNetputT of Reiman (1984) Proposition 5 (755ffe80): the scaled netput and the
time-changed scaled netput are a.e.-measurable random paths and a.s. cadlag on `[0,1]`.
Key idea: on the event where all renewal sums diverge, the Picard iterates of the busy-time
equation agree with ANY solution on `[0, T]` after finitely many steps (a sup argument using
right- and left-local constancy of the arrival and service counting processes). The iterates
are jointly measurable, so their liminf is a measurable version of the busy time. -/

namespace MeasP

open Filter Topology MeasureTheory Set

variable {K : ℕ}

noncomputable def ind (x : ℝ) : ℝ := if 0 < x then 1 else 0

lemma ind_nonneg (x : ℝ) : 0 ≤ ind x := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (x : ℝ) : ind x ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma measurable_ind : Measurable ind := by
  unfold ind
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

lemma ii_ind {f : ℝ → ℝ} (hf : Measurable f) (a b : ℝ) :
    IntervalIntegrable (fun s => ind (f s)) volume a b := by
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun
    ((measurable_ind.comp hf).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun s => by
    simp only [Real.norm_eq_abs, abs_of_nonneg (ind_nonneg _), abs_one]
    exact ind_le_one _

/-- the busy-time primitive `t ↦ ∫₀ᵗ 1{f(s) > 0} ds`, coordinatewise. -/
noncomputable def prim (f : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t k => ∫ s in (0:ℝ)..t, ind (f s k)

/-- nondecreasing with slope at most one on `[0, ∞)`. -/
def Grow (b : ℝ → Fin K → ℝ) : Prop :=
  ∀ k t s, 0 ≤ t → t ≤ s → b t k ≤ b s k ∧ b s k ≤ b t k + (s - t)

lemma prim_zero (f : ℝ → Fin K → ℝ) : prim f 0 = 0 := by
  funext k; simp [prim]

lemma prim_split {f : ℝ → Fin K → ℝ} (hf : ∀ k, Measurable fun s => f s k) (k : Fin K)
    (t s : ℝ) : prim f s k = prim f t k + ∫ r in t..s, ind (f r k) := by
  simp only [prim]
  exact (intervalIntegral.integral_add_adjacent_intervals (ii_ind (hf k) 0 t)
    (ii_ind (hf k) t s)).symm

lemma prim_grow {f : ℝ → Fin K → ℝ} (hf : ∀ k, Measurable fun s => f s k) : Grow (prim f) := by
  intro k t s _ hts
  have hsplit := prim_split hf k t s
  have h0 : 0 ≤ ∫ r in t..s, ind (f r k) :=
    intervalIntegral.integral_nonneg hts (fun r _ => ind_nonneg _)
  have h1 : ∫ r in t..s, ind (f r k) ≤ s - t := by
    have := intervalIntegral.integral_mono_on hts (ii_ind (hf k) t s)
      (intervalIntegrable_const (c := (1:ℝ))) (fun r _ => ind_le_one (f r k))
    simpa using this
  constructor <;> linarith

lemma prim_cont {f : ℝ → Fin K → ℝ} (hf : ∀ k, Measurable fun s => f s k) :
    Continuous (prim f) :=
  continuous_pi fun k => intervalIntegral.continuous_primitive (fun a b => ii_ind (hf k) a b) 0

lemma prim_congr {f g : ℝ → Fin K → ℝ} {t : ℝ} (ht : 0 ≤ t) (k : Fin K)
    (h : ∀ s, 0 < s → s < t → f s k = g s k) : prim f t k = prim g t k := by
  simp only [prim]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) t)]
    with s hs hst
  rw [uIoc_of_le ht] at hst
  have hne : s ≠ t := fun h' => hs (by simp [h'])
  rw [h s hst.1 (lt_of_le_of_ne hst.2 hne)]

section Det

variable (a : ℝ → Fin K → ℝ) (sh : Fin K → ℝ → Fin K → ℝ)

/-- the queue length produced by a busy-time path `b`, equation (3). -/
noncomputable def Fq (b : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ := fun t => a t + ∑ k, sh k (b t k)

/-- Picard iterates of the busy-time equation. -/
noncomputable def pic : ℕ → ℝ → Fin K → ℝ
  | 0 => fun _ _ => 0
  | m + 1 => prim (Fq a sh (pic m))

/-- step-function hypotheses on the arrival vector `a` and the service-routing vectors `sh`. -/
structure Good : Prop where
  ma : Measurable a
  ms : ∀ k, Measurable (sh k)
  ra : ∀ t, 0 ≤ t → ∀ᶠ s in 𝓝[≥] t, a s = a t
  rs : ∀ k x, 0 ≤ x → ∀ᶠ y in 𝓝[≥] x, sh k y = sh k x
  la : ∀ t, 0 < t → ∃ c, ∀ᶠ s in 𝓝[<] t, a s = c
  ls : ∀ k x, 0 < x → ∃ c, ∀ᶠ y in 𝓝[<] x, sh k y = c

/-- a solution of (2)–(3) on `[0, ∞)`. -/
structure Sol (B Q : ℝ → Fin K → ℝ) : Prop where
  qm : ∀ k, Measurable fun s => Q s k
  bq : ∀ k t, 0 ≤ t → B t k = ∫ s in (0:ℝ)..t, ind (Q s k)
  qf : ∀ t, 0 ≤ t → Q t = Fq a sh B t

variable {a sh}

lemma Fq_meas (hma : Measurable a) (hms : ∀ k, Measurable (sh k)) {b : ℝ → Fin K → ℝ}
    (hb : ∀ k, Measurable fun s => b s k)
    (k : Fin K) : Measurable fun s => Fq a sh b s k := by
  have h : Measurable (Fq a sh b) :=
    hma.add (Finset.measurable_sum _ fun j _ => (hms j).comp (hb j))
  exact (measurable_pi_apply k).comp h

lemma pic_prop (hma : Measurable a) (hms : ∀ k, Measurable (sh k)) (m : ℕ) :
    (∀ k, Measurable fun s => pic a sh m s k) ∧ Grow (pic a sh m) ∧ pic a sh m 0 = 0 ∧
      Continuous (pic a sh m) := by
  induction m with
  | zero =>
    refine ⟨fun k => measurable_const, fun k t s _ hts => ?_, rfl, continuous_const⟩
    simp only [pic]; constructor <;> linarith
  | succ m ih =>
    have hF := Fq_meas hma hms ih.1
    refine ⟨fun k => ?_, prim_grow hF, prim_zero _, prim_cont hF⟩
    exact (measurable_pi_apply k).comp (prim_cont hF).measurable

lemma sol_prim {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {t : ℝ} (ht : 0 ≤ t) (k : Fin K) :
    B t k = prim (Fq a sh B) t k := by
  rw [hS.bq k t ht]
  exact prim_congr (f := Q) ht k fun s hs _ => by rw [hS.qf s hs.le]

lemma sol_zero {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) : B 0 = 0 := by
  funext k; rw [hS.bq k 0 le_rfl]; simp

lemma sol_grow {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) : Grow B := by
  intro k t s ht hts
  have := prim_grow hS.qm k t s ht hts
  simp only [prim] at this
  rw [hS.bq k t ht, hS.bq k s (ht.trans hts)]
  exact this

lemma sol_nonneg {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {t : ℝ} (ht : 0 ≤ t) (k : Fin K) :
    0 ≤ B t k := by
  have := (sol_grow hS k 0 t le_rfl ht).1
  rwa [sol_zero hS] at this

/-- one Picard step extends agreement with a solution to the right. -/
lemma step (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {b : ℝ → Fin K → ℝ}
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hbB : ∀ s, 0 ≤ s → s ≤ t₀ → b s = B s) (hb : Grow b) :
    ∃ h > 0, ∀ t, 0 ≤ t → t ≤ t₀ + h → prim (Fq a sh b) t = B t := by
  have hB := sol_grow hS
  have hev : ∀ᶠ s in 𝓝[≥] t₀, a s = a t₀ ∧
      ∀ k y, B t₀ k ≤ y → y ≤ B t₀ k + (s - t₀) → sh k y = sh k (B t₀ k) := by
    refine (hG.ra t₀ ht₀).and (eventually_all.2 fun k => ?_)
    obtain ⟨u, hu, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.1 (hG.rs k (B t₀ k) (sol_nonneg hS ht₀ k))
    have hu' : B t₀ k < u := hu
    have : ∀ᶠ s in 𝓝[≥] t₀, s < t₀ + (u - B t₀ k) :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by linarith))
    filter_upwards [this] with s hs y hy1 hy2
    exact hsub ⟨hy1, by linarith⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
  have hu' : t₀ < u := hu
  refine ⟨(u - t₀) / 2, by linarith, fun t ht htu => ?_⟩
  funext k
  rw [sol_prim hS ht k]
  refine prim_congr ht k fun s hs hst => ?_
  by_cases hs0 : s ≤ t₀
  · simp only [Fq, hbB s hs.le hs0]
  · push_neg at hs0
    obtain ⟨_, hsh⟩ := hsub (show s ∈ Ico t₀ u from ⟨hs0.le, by linarith⟩)
    have hbt := hbB t₀ ht₀ le_rfl
    have hfq : Fq a sh b s = Fq a sh B s := by
      simp only [Fq]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 := hb j t₀ s ht₀ hs0.le
      have h2 := hB j t₀ s ht₀ hs0.le
      rw [hbt] at h1
      rw [hsh j (b s j) h1.1 h1.2, hsh j (B s j) h2.1 h2.2]
    rw [hfq]

/-- left-local constancy of `sh k ∘ B_k` at `T > 0`. -/
lemma left_sh (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {T : ℝ} (hT : 0 < T)
    (k : Fin K) : ∃ c, ∀ᶠ s in 𝓝[<] T, sh k (B s k) = c := by
  have hB := sol_grow hS
  have hpos : ∀ᶠ s in 𝓝[<] T, 0 ≤ s :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_ge_nhds hT)
  have hlt : ∀ᶠ s in 𝓝[<] T, s < T := self_mem_nhdsWithin
  rcases (sol_nonneg hS hT.le k).eq_or_lt with h0 | hx
  · refine ⟨sh k 0, ?_⟩
    filter_upwards [hpos, hlt] with s hs hsT
    have h1 := (hB k s T hs hsT.le).1
    have h2 := sol_nonneg hS hs k
    rw [show B s k = 0 by linarith]
  · by_cases hex : ∃ s₀, 0 ≤ s₀ ∧ s₀ < T ∧ B s₀ k = B T k
    · obtain ⟨s₀, hs₀, hs₀T, hBs₀⟩ := hex
      refine ⟨sh k (B T k), ?_⟩
      have : ∀ᶠ s in 𝓝[<] T, s₀ < s :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hs₀T)
      filter_upwards [this, hlt] with s hs hsT
      have h1 := (hB k s₀ s hs₀ hs.le).1
      have h2 := (hB k s T (hs₀.trans hs.le) hsT.le).1
      rw [show B s k = B T k by linarith]
    · push_neg at hex
      obtain ⟨c, hc⟩ := hG.ls k (B T k) hx
      refine ⟨c, ?_⟩
      have hten : Tendsto (fun s => B s k) (𝓝[<] T) (𝓝[<] (B T k)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have hlow : Tendsto (fun s => B T k - (T - s)) (𝓝[<] T) (𝓝 (B T k)) := by
            have : Tendsto (fun s => B T k - (T - s)) (𝓝 T) (𝓝 (B T k - (T - T))) :=
              tendsto_const_nhds.sub (tendsto_const_nhds.sub tendsto_id)
            simpa using this.mono_left nhdsWithin_le_nhds
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
          · filter_upwards [hpos, hlt] with s hs hsT
            have := (hB k s T hs hsT.le).2; linarith
          · filter_upwards [hpos, hlt] with s hs hsT
            exact (hB k s T hs hsT.le).1
        · filter_upwards [hpos, hlt] with s hs hsT
          exact lt_of_le_of_ne (hB k s T hs hsT.le).1 (hex s hs hsT)
      exact hten.eventually hc

/-- left-local constancy of the queue length of a solution. -/
lemma left_Fq (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {T : ℝ} (hT : 0 < T) :
    ∃ c, ∀ᶠ s in 𝓝[<] T, Fq a sh B s = c := by
  choose cs hcs using left_sh hG hS hT
  obtain ⟨ca, hca⟩ := hG.la T hT
  refine ⟨ca + ∑ k, cs k, ?_⟩
  filter_upwards [hca, eventually_all.2 hcs] with s h1 h2
  simp only [Fq, h1, h2]

/-- slope classification of a solution on a left neighbourhood of `T > 0`. -/
lemma slope (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {T : ℝ} (hT : 0 < T) :
    ∃ c : Fin K → ℝ, ∃ ε > 0, ε ≤ T ∧
      ∀ k s, T - ε ≤ s → s ≤ T → B s k = B T k - (T - s) * ind (c k) := by
  obtain ⟨c, hc⟩ := left_Fq hG hS hT
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hc
  have hl' : l < T := hl
  refine ⟨c, min ((T - l) / 2) T, lt_min (by linarith) hT, min_le_right _ _,
    fun k s hs hsT => ?_⟩
  have hs0 : 0 ≤ s := by linarith [min_le_right ((T - l) / 2) T]
  have hls : l < s := by linarith [min_le_left ((T - l) / 2) T]
  have hsplit := prim_split hS.qm k s T
  simp only [prim] at hsplit
  rw [← hS.bq k T hT.le, ← hS.bq k s hs0] at hsplit
  have hint : ∫ r in s..T, ind (Q r k) = (T - s) * ind (c k) := by
    have : ∫ r in s..T, ind (Q r k) = ∫ r in s..T, ind (c k) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) T)]
        with r hr hrs
      rw [uIoc_of_le hsT] at hrs
      have hne : r ≠ T := fun h' => hr (by simp [h'])
      have hrT : r < T := lt_of_le_of_ne hrs.2 hne
      have hrc : Fq a sh B r = c := hsub ⟨hls.trans hrs.1, hrT⟩
      rw [hS.qf r (hs0.trans hrs.1.le), hrc]
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
  linarith

/-- near `T` from the left, any slope-≤1 path starting at `B(t₀)` sees the same service vectors. -/
lemma left_ext (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {T : ℝ} (hT : 0 < T)
    (k : Fin K) :
    ∀ᶠ t₀ in 𝓝[<] T, ∀ s, t₀ ≤ s → s < T → ∀ y, B t₀ k ≤ y → y ≤ B t₀ k + (s - t₀) →
      sh k y = sh k (B s k) := by
  obtain ⟨c, ε, hε, hεT, hsl⟩ := slope hG hS hT
  have hnear : ∀ᶠ t₀ in 𝓝[<] T, T - ε < t₀ :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by linarith))
  have hk := hsl k
  unfold ind at hk
  by_cases hck : 0 < c k
  · simp only [hck, if_true, mul_one] at hk
    have hx : 0 < B T k := by
      have := hk (T - ε) le_rfl (by linarith)
      have h0 := sol_nonneg hS (show 0 ≤ T - ε by linarith) k
      linarith
    obtain ⟨c', hc'⟩ := hG.ls k (B T k) hx
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hc'
    have hl' : l < B T k := hl
    have hnear2 : ∀ᶠ t₀ in 𝓝[<] T, T - (B T k - l) < t₀ :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by linarith))
    filter_upwards [hnear, hnear2] with t₀ h1 h2 s hs hsT y hy1 hy2
    have e0 := hk t₀ h1.le (hs.trans hsT.le)
    have e1 := hk s (by linarith) hsT.le
    have hy : sh k y = c' := hsub ⟨by linarith, by linarith⟩
    have hBs : sh k (B s k) = c' := hsub ⟨by linarith, by linarith⟩
    rw [hy, hBs]
  · simp only [hck, if_false, mul_zero, sub_zero] at hk
    obtain ⟨u, hu, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.1 (hG.rs k (B T k) (sol_nonneg hS hT.le k))
    have hu' : B T k < u := hu
    have hnear2 : ∀ᶠ t₀ in 𝓝[<] T, T - (u - B T k) < t₀ :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by linarith))
    filter_upwards [hnear, hnear2] with t₀ h1 h2 s hs hsT y hy1 hy2
    have e0 := hk t₀ h1.le (hs.trans hsT.le)
    have e1 := hk s (by linarith) hsT.le
    have hy : sh k y = sh k (B T k) := hsub ⟨by linarith, by linarith⟩
    rw [hy, e1]

/-- MAIN deterministic fact: the Picard iterates agree with any solution on `[0, T]` after
finitely many steps. -/
theorem pic_agree (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) :
    ∀ T, 0 ≤ T → ∃ m, ∀ s, 0 ≤ s → s ≤ T → pic a sh m s = B s := by
  have ext : ∀ m T, 0 ≤ T → (∀ s, 0 ≤ s → s ≤ T → pic a sh m s = B s) →
      ∃ h > 0, ∀ s, 0 ≤ s → s ≤ T + h → pic a sh (m+1) s = B s := by
    intro m T hT hm
    obtain ⟨h, hh, hh'⟩ := step hG hS hT hm (pic_prop hG.ma hG.ms m).2.1
    exact ⟨h, hh, fun s hs hsT => hh' s hs hsT⟩
  have hzero : ∀ m, ∀ s, 0 ≤ s → s ≤ 0 → pic a sh m s = B s := fun m s hs hs0 => by
    have : s = 0 := le_antisymm hs0 hs
    subst this; rw [sol_zero hS, (pic_prop hG.ma hG.ms m).2.2.1]
  by_contra hcon
  push_neg at hcon
  obtain ⟨T₁, hT₁, hT₁m⟩ := hcon
  set S : Set ℝ := {t | 0 ≤ t ∧ ∃ m, ∀ s, 0 ≤ s → s ≤ t → pic a sh m s = B s} with hSdef
  have h0S : (0:ℝ) ∈ S := ⟨le_rfl, 0, hzero 0⟩
  have hbdd : BddAbove S := ⟨T₁, fun t ⟨_, m, hm⟩ => by
    by_contra hlt; push_neg at hlt
    obtain ⟨s, hs, hsT, hne⟩ := hT₁m m
    exact hne (hm s hs (hsT.trans hlt.le))⟩
  have hne : S.Nonempty := ⟨0, h0S⟩
  have hT0 : 0 ≤ sSup S := le_csSup hbdd h0S
  have hTm : ∃ m, ∀ s, 0 ≤ s → s ≤ sSup S → pic a sh m s = B s := by
    rcases hT0.eq_or_lt with hT | hT
    · exact ⟨0, fun s hs hsT => hzero 0 s hs (hsT.trans hT.symm.le)⟩
    · have hev := eventually_all.2 (left_ext hG hS hT)
      obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
      have hl' : l < sSup S := hl
      obtain ⟨t₀, ⟨ht₀0, m, hm⟩, hlt₀⟩ :=
        exists_lt_of_lt_csSup hne (show max l 0 < sSup S from max_lt hl' hT)
      have ht₀T : t₀ ≤ sSup S := le_csSup hbdd ⟨ht₀0, m, hm⟩
      rcases ht₀T.eq_or_lt with heq | hlt
      · exact ⟨m, heq ▸ hm⟩
      · have hgood := hsub ⟨(le_max_left l 0).trans_lt hlt₀, hlt⟩
        simp only [Set.mem_ofPred_eq] at hgood
        obtain ⟨_, hgrow, _, _⟩ := pic_prop hG.ma hG.ms m
        refine ⟨m + 1, fun t ht htT => ?_⟩
        show prim (Fq a sh (pic a sh m)) t = B t
        funext k
        rw [sol_prim hS ht k]
        refine prim_congr ht k fun s hs hst => ?_
        by_cases hs0 : s ≤ t₀
        · simp only [Fq, hm s hs.le hs0]
        · push_neg at hs0
          have hbt := hm t₀ ht₀0 le_rfl
          have hfq : Fq a sh (pic a sh m) s = Fq a sh B s := by
            simp only [Fq]
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            have h1 := hgrow j t₀ s ht₀0 hs0.le
            rw [hbt] at h1
            exact hgood j s hs0.le (lt_of_lt_of_le hst htT) (pic a sh m s j) h1.1 h1.2
          rw [hfq]
  obtain ⟨m, hm⟩ := hTm
  obtain ⟨h, hh, hh'⟩ := ext m (sSup S) hT0 hm
  have hmem : sSup S + h ∈ S := ⟨by linarith, m + 1, hh'⟩
  have := le_csSup hbdd hmem
  linarith

lemma pic_eventually (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {T : ℝ}
    (hT : 0 ≤ T) : ∀ᶠ m in atTop, ∀ s, 0 ≤ s → s ≤ T → pic a sh m s = B s := by
  obtain ⟨m, hm⟩ := pic_agree hG hS T hT
  refine eventually_atTop.2 ⟨m, fun m' hm' => ?_⟩
  induction m', hm' using Nat.le_induction with
  | base => exact hm
  | succ m' _ ih =>
    obtain ⟨h, hh, hh'⟩ := step hG hS hT ih (pic_prop hG.ma hG.ms m').2.1
    exact fun s hs hsT => hh' s hs (by linarith)

/-- every solution equals the liminf of the Picard iterates on `[0, ∞)`. -/
lemma sol_eq_liminf (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) {t : ℝ}
    (ht : 0 ≤ t) (k : Fin K) : B t k = liminf (fun m => pic a sh m t k) atTop := by
  have hev : ∀ᶠ m in atTop, pic a sh m t k = B t k := by
    filter_upwards [pic_eventually hG hS ht] with m hm
    rw [hm t ht le_rfl]
  rw [liminf_congr hev, liminf_const]

/-- right/left local constancy on `[0, ∞)`. -/
def RL (y : ℝ → Fin K → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ∀ᶠ s in 𝓝[≥] t, y s = y t) ∧ (∀ t, 0 < t → ∃ c, ∀ᶠ s in 𝓝[<] t, y s = c)

lemma RL_add {y₁ y₂ : ℝ → Fin K → ℝ} (h₁ : RL y₁) (h₂ : RL y₂) : RL (fun t => y₁ t + y₂ t) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · filter_upwards [h₁.1 t ht, h₂.1 t ht] with s hs1 hs2
    rw [hs1, hs2]
  · obtain ⟨c₁, hc₁⟩ := h₁.2 t ht
    obtain ⟨c₂, hc₂⟩ := h₂.2 t ht
    exact ⟨c₁ + c₂, by filter_upwards [hc₁, hc₂] with s hs1 hs2; rw [hs1, hs2]⟩

lemma RL_sum {y : Fin K → ℝ → Fin K → ℝ} (h : ∀ i, RL (y i)) : RL (fun t => ∑ i, y i t) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · filter_upwards [eventually_all.2 fun i => (h i).1 t ht] with s hs
    simp only [hs]
  · choose c hc using fun i => (h i).2 t ht
    exact ⟨∑ i, c i, by filter_upwards [eventually_all.2 hc] with s hs; simp only [hs]⟩

lemma RL_a (hG : Good a sh) : RL a := ⟨hG.ra, hG.la⟩

lemma RL_sh (hG : Good a sh) (k : Fin K) : RL (sh k) :=
  ⟨fun t ht => hG.rs k t ht, fun t ht => hG.ls k t ht⟩

lemma RL_sol (hG : Good a sh) {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) : RL (Fq a sh B) := by
  refine ⟨fun t ht => ?_, fun t ht => left_Fq hG hS ht⟩
  have hk : ∀ k, ∀ᶠ s in 𝓝[≥] t, sh k (B s k) = sh k (B t k) := by
    intro k
    obtain ⟨u, hu, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.1 (hG.rs k (B t k) (sol_nonneg hS ht k))
    have hu' : B t k < u := hu
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (show t < t + (u - B t k) by linarith))] with s hs1 hs2
    have := sol_grow hS k t s ht hs1
    exact hsub ⟨this.1, by linarith⟩
  filter_upwards [hG.ra t ht, eventually_all.2 hk] with s h1 h2
  simp only [Fq, h1, h2]

lemma sol_contOn {B Q : ℝ → Fin K → ℝ} (hS : Sol a sh B Q) : ContinuousOn B (Ici 0) :=
  (prim_cont hS.qm).continuousOn.congr fun t ht => funext fun k => hS.bq k t ht

end Det

/-! ### cadlag criterion -/

open Reiman84.QueueLength in
lemma cadlag_of {x y z : ℝ → Fin K → ℝ} (hy : RL y) (hz : ContinuousOn z (Ici 0))
    (hx : ∀ t, x t = y t + z t) (n : ℕ) : IsCadlag01 (diffScale n x) := by
  have hxe : x = fun t => y t + z t := funext hx
  subst hxe
  rcases n.eq_zero_or_pos with rfl | hn
  · have h0 : diffScale 0 (fun t => y t + z t) = fun _ => 0 := by
      funext t; simp [diffScale]
    rw [h0]
    exact ⟨fun t _ => continuousWithinAt_const, fun t _ => ⟨0, tendsto_const_nhds⟩⟩
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hcm : Continuous fun s : ℝ => (n:ℝ) * s := continuous_const.mul continuous_id
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have ht0 : 0 ≤ (n:ℝ) * t := mul_nonneg hn'.le ht.1
    have hmap : Tendsto (fun s : ℝ => (n:ℝ) * s) (𝓝[≥] t) (𝓝[≥] ((n:ℝ) * t)) :=
      hcm.continuousWithinAt.tendsto_nhdsWithin fun s hs =>
        mul_le_mul_of_nonneg_left (show t ≤ s from hs) hn'.le
    have hy' : ∀ᶠ s in 𝓝[≥] t, y ((n:ℝ) * s) = y ((n:ℝ) * t) := hmap.eventually (hy.1 _ ht0)
    have hyc : ContinuousWithinAt (fun s => y ((n:ℝ) * s)) (Ici t) t :=
      continuousWithinAt_const.congr_of_eventuallyEq hy' rfl
    have hzc : ContinuousWithinAt (fun s => z ((n:ℝ) * s)) (Ici t) t :=
      (hz _ ht0).comp hcm.continuousWithinAt fun s hs =>
        (show (0:ℝ) ≤ n * s from mul_nonneg hn'.le (ht.1.trans hs))
    exact ((hyc.add hzc).const_smul ((Real.sqrt n)⁻¹)).mono Icc_subset_Ici_self
  · have ht0 : 0 < (n:ℝ) * t := mul_pos hn' ht.1
    obtain ⟨cy, hcy⟩ := hy.2 _ ht0
    refine ⟨(Real.sqrt n)⁻¹ • (cy + z ((n:ℝ) * t)), ?_⟩
    have hmap : Tendsto (fun s : ℝ => (n:ℝ) * s) (𝓝[Ico 0 t] t) (𝓝[<] ((n:ℝ) * t)) :=
      hcm.continuousWithinAt.tendsto_nhdsWithin fun s hs =>
        (show (n:ℝ) * s < n * t from mul_lt_mul_of_pos_left hs.2 hn')
    have hy2 : ∀ᶠ s in 𝓝[Ico 0 t] t, y ((n:ℝ) * s) = cy := hmap.eventually hcy
    have hz2 : Tendsto (fun s => z ((n:ℝ) * s)) (𝓝[Ico 0 t] t) (𝓝 (z ((n:ℝ) * t))) :=
      ((hz _ ht0.le).comp hcm.continuousWithinAt fun s hs =>
        (show (0:ℝ) ≤ n * s from mul_nonneg hn'.le hs.1)).tendsto
    have hy3 : Tendsto (fun s => y ((n:ℝ) * s)) (𝓝[Ico 0 t] t) (𝓝 cy) :=
      tendsto_const_nhds.congr' (hy2.mono fun s hs => hs.symm)
    exact (hy3.add hz2).const_smul _

/-! ### counting functions -/

/-- `max {l | F l ≤ b}` (junk `0` when unbounded), as in `Network.A`, `Network.S`. -/
noncomputable def cnt (F : ℕ → ℝ) (b : ℝ) : ℕ := sSup {l | F l ≤ b}

lemma nat_sSup_eq_iff (S : Set ℕ) (j : ℕ) :
    sSup S = j ↔ ((∀ a ∈ S, a ≤ j) ∧ (j = 0 ∨ j ∈ S)) ∨ (j = 0 ∧ ∀ n : ℕ, ∃ a ∈ S, n < a) := by
  by_cases hb : BddAbove S
  · have hnot : ¬ ∀ n : ℕ, ∃ a ∈ S, n < a := by
      intro h
      obtain ⟨M, hM⟩ := hb
      obtain ⟨a, ha, hMa⟩ := h M
      exact absurd (hM ha) (not_le.2 hMa)
    simp only [hnot, and_false, or_false]
    rcases S.eq_empty_or_nonempty with he | hne
    · subst he; simp [eq_comm]
    · constructor
      · rintro rfl; exact ⟨fun a ha => le_csSup hb ha, Or.inr (Nat.sSup_mem hne hb)⟩
      · rintro ⟨hub, h0 | hj⟩
        · subst h0; exact Nat.le_zero.1 (csSup_le hne hub)
        · exact le_antisymm (csSup_le hne hub) (le_csSup hb hj)
  · rw [Nat.sSup_of_not_bddAbove hb]
    have hall : ∀ n : ℕ, ∃ a ∈ S, n < a := by
      intro n; by_contra h; push_neg at h; exact hb ⟨n, fun a ha => h a ha⟩
    have hnub : ¬ ∀ a ∈ S, a ≤ j := fun h => hb ⟨j, h⟩
    simp only [hnub, false_and, false_or, hall, implies_true, and_true]
    exact eq_comm

lemma meas_cnt {Ω' : Type*} [MeasurableSpace Ω'] (F : ℕ → Ω' → ℝ) (hF : ∀ l, Measurable (F l)) :
    Measurable (fun p : ℝ × Ω' => cnt (fun l => F l p.2) p.1) := by
  have hle : ∀ a, Measurable fun p : ℝ × Ω' => F a p.2 ≤ p.1 := fun a =>
    measurableSet_setOfPred.1 (measurableSet_le ((hF a).comp measurable_snd) measurable_fst)
  refine measurable_to_countable' fun j => ?_
  have hset : (fun p : ℝ × Ω' => cnt (fun l => F l p.2) p.1) ⁻¹' {j} =
      {p | ((∀ a, F a p.2 ≤ p.1 → a ≤ j) ∧ (j = 0 ∨ F j p.2 ≤ p.1)) ∨
        (j = 0 ∧ ∀ n : ℕ, ∃ a, F a p.2 ≤ p.1 ∧ n < a)} := by
    ext p; exact nat_sSup_eq_iff _ j
  rw [hset]
  exact measurableSet_setOfPred.2
    (((Measurable.forall fun a => (hle a).imp measurable_const).and
      (measurable_const.or (hle j))).or
      (measurable_const.and (Measurable.forall fun n =>
        Measurable.exists fun a => (hle a).and measurable_const)))

lemma cnt_spec {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b : ℝ} (hb : 0 ≤ b) :
    F (cnt F b) ≤ b ∧ b < F (cnt F b + 1) := by
  obtain ⟨L, hL⟩ := (hFt.eventually (eventually_gt_atTop b)).exists
  have hbdd : BddAbove {l | F l ≤ b} := ⟨L, fun l (hl : F l ≤ b) => by
    by_contra h; push_neg at h; linarith [hFm h]⟩
  have hne : ({l | F l ≤ b} : Set ℕ).Nonempty := ⟨0, by show F 0 ≤ b; rw [hF0]; exact hb⟩
  refine ⟨Nat.sSup_mem hne hbdd, ?_⟩
  by_contra h; push_neg at h
  have := le_csSup hbdd (show F (sSup {l | F l ≤ b} + 1) ≤ b from h)
  unfold cnt at *
  omega

lemma cnt_eq {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F) (hFt : Tendsto F atTop atTop)
    {i : ℕ} {s : ℝ} (h1 : F i ≤ s) (h2 : s < F (i + 1)) : cnt F s = i := by
  have hs : 0 ≤ s := by
    have := hFm.monotone (Nat.zero_le i); rw [hF0] at this; linarith
  obtain ⟨c1, c2⟩ := cnt_spec hF0 hFm hFt hs
  rcases lt_trichotomy (cnt F s) i with h | h | h
  · have := hFm.monotone (show cnt F s + 1 ≤ i by omega); linarith
  · exact h
  · have := hFm.monotone (show i + 1 ≤ cnt F s by omega); linarith

lemma cnt_right {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F) (hFt : Tendsto F atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) : ∀ᶠ s in 𝓝[≥] t, cnt F s = cnt F t := by
  obtain ⟨c1, c2⟩ := cnt_spec hF0 hFm hFt ht
  have : ∀ᶠ s in 𝓝[≥] t, s < F (cnt F t + 1) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds c2)
  filter_upwards [this, self_mem_nhdsWithin] with s hs hts
  exact cnt_eq hF0 hFm hFt (c1.trans hts) hs

lemma cnt_left {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F) (hFt : Tendsto F atTop atTop)
    {t : ℝ} (ht : 0 < t) : ∃ c, ∀ᶠ s in 𝓝[<] t, cnt F s = c := by
  obtain ⟨c1, c2⟩ := cnt_spec hF0 hFm hFt ht.le
  rcases c1.lt_or_eq with hlt | heq
  · refine ⟨cnt F t, ?_⟩
    have : ∀ᶠ s in 𝓝[<] t, F (cnt F t) < s :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hlt)
    filter_upwards [this, self_mem_nhdsWithin] with s hs hst
    exact cnt_eq hF0 hFm hFt hs.le (lt_trans hst c2)
  · have hne : cnt F t ≠ 0 := by intro h; rw [h, hF0] at heq; linarith
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine ⟨i, ?_⟩
    have hFi : F i < t := by rw [← heq, hi]; exact hFm (Nat.lt_succ_self i)
    have : ∀ᶠ s in 𝓝[<] t, F i < s :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hFi)
    filter_upwards [this, self_mem_nhdsWithin] with s hs hst
    refine cnt_eq hF0 hFm hFt hs.le ?_
    rw [show i + 1 = cnt F t by omega, heq]; exact hst

/-! ### the network -/

section Net

open Reiman84.QueueLength ProbabilityTheory

variable {J : Finset (Fin K)} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (N : Network K J P)

lemma U_meas {k : Fin K} (hk : k ∈ J) (l : ℕ) : Measurable (N.U k l) := by
  show Measurable fun ω => ∑ i ∈ Finset.range l, N.u k i ω
  exact Finset.measurable_sum _ fun i _ => N.meas_u k hk i

lemma V_meas (k : Fin K) (l : ℕ) : Measurable (N.V k l) := by
  show Measurable fun ω => ∑ i ∈ Finset.range l, N.v k i ω
  exact Finset.measurable_sum _ fun i _ => N.meas_v k i

lemma U_props {k : Fin K} (hk : k ∈ J) (ω : Ω) :
    N.U k 0 ω = 0 ∧ StrictMono (fun l => N.U k l ω) := by
  refine ⟨by simp [Network.U], strictMono_nat_of_lt_succ fun l => ?_⟩
  simp only [Network.U, Finset.sum_range_succ]
  linarith [N.pos_u k hk l ω]

lemma V_props (k : Fin K) (ω : Ω) : N.V k 0 ω = 0 ∧ StrictMono (fun l => N.V k l ω) := by
  refine ⟨by simp [Network.V], strictMono_nat_of_lt_succ fun l => ?_⟩
  simp only [Network.V, Finset.sum_range_succ]
  linarith [N.pos_v k l ω]

lemma A_eq {k : Fin K} (hk : k ∈ J) (t : ℝ) (ω : Ω) :
    N.A k t ω = cnt (fun l => N.U k l ω) t := by
  simp only [Network.A, if_pos hk, cnt]

lemma Avec_jm : Measurable (fun p : ℝ × Ω => N.Avec p.1 p.2) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k ∈ J
  · simp only [Network.Avec, A_eq N hk]
    exact measurable_from_nat.comp (meas_cnt (fun l ω => N.U k l ω) (U_meas N hk))
  · simp only [Network.Avec, Network.A, if_neg hk, Nat.cast_zero]
    exact measurable_const

/-- `Ŝ_k` as a function of the number of completed services. -/
noncomputable def shG (k : Fin K) (q : Ω × ℕ) : Fin K → ℝ :=
  (∑ i ∈ Finset.range q.2, routeVec (N.φ k i q.1)) - (q.2 : ℝ) • Pi.single k 1

lemma shG_meas (k : Fin K) : Measurable (shG N k) := by
  refine measurable_from_prod_countable_left fun j => ?_
  simp only [shG]
  exact (Finset.measurable_sum _ fun i _ =>
    (Measurable.of_discrete (f := (routeVec : Fin (K + 1) → Fin K → ℝ))).comp
      (N.meas_φ k i)).sub measurable_const

lemma Shat_eq (k : Fin K) (y : ℝ) (ω : Ω) :
    N.Shat k y ω = shG N k (ω, cnt (fun l => N.V k l ω) y) := rfl

lemma Shat_jm (k : Fin K) : Measurable (fun p : ℝ × Ω => N.Shat k p.1 p.2) := by
  simp only [Shat_eq]
  exact (shG_meas N k).comp
    (measurable_snd.prodMk (meas_cnt (fun l ω => N.V k l ω) (V_meas N k)))

/-- the arrival path and the service vectors at the sample point `ω`. -/
noncomputable def aω (ω : Ω) : ℝ → Fin K → ℝ := fun t => N.Avec t ω
noncomputable def shω (ω : Ω) : Fin K → ℝ → Fin K → ℝ := fun k y => N.Shat k y ω

lemma aω_meas (ω : Ω) : Measurable (aω N ω) := by
  have h : Measurable ((fun p : ℝ × Ω => N.Avec p.1 p.2) ∘ fun t : ℝ => (t, ω)) :=
    (Avec_jm N).comp measurable_prodMk_right
  exact h

lemma shω_meas (ω : Ω) (k : Fin K) : Measurable (shω N ω k) := by
  have h : Measurable ((fun p : ℝ × Ω => N.Shat k p.1 p.2) ∘ fun t : ℝ => (t, ω)) :=
    (Shat_jm N k).comp measurable_prodMk_right
  exact h

lemma Avec_sec (t : ℝ) : Measurable fun ω => N.Avec t ω := by
  have h : Measurable ((fun p : ℝ × Ω => N.Avec p.1 p.2) ∘ fun ω : Ω => (t, ω)) :=
    (Avec_jm N).comp measurable_prodMk_left
  exact h

lemma Shat_sec (k : Fin K) (t : ℝ) : Measurable fun ω => N.Shat k t ω := by
  have h : Measurable ((fun p : ℝ × Ω => N.Shat k p.1 p.2) ∘ fun ω : Ω => (t, ω)) :=
    (Shat_jm N k).comp measurable_prodMk_left
  exact h

/-- all renewal sums diverge. -/
def GoodPt (ω : Ω) : Prop :=
  (∀ k ∈ J, Tendsto (fun l => N.U k l ω) atTop atTop) ∧
    ∀ k, Tendsto (fun l => N.V k l ω) atTop atTop

lemma integral_pos_of_pos' {μP : Measure Ω} [IsProbabilityMeasure μP] {f : Ω → ℝ}
    (hf : ∀ ω, 0 < f ω) (hint : Integrable f μP) : 0 < ∫ ω, f ω ∂μP := by
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hf ω).le) hint]
  have : Function.support f = Set.univ := Set.eq_univ_of_forall fun ω => (hf ω).ne'
  rw [this, measure_univ]; exact one_pos

lemma ae_V' (k : Fin K) : ∀ᵐ ω ∂P, Tendsto (fun l => N.V k l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.v k 0) P := (N.memLp_v k).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.v k i) (N.v k i') P) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inr (Sum.inl (k, i))) (j := Sum.inr (Sum.inl (k, i')))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.v k 0 ω ∂P := integral_pos_of_pos' (N.pos_v k 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.v k i) hint hind
    (N.ident_v k)] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop, (∫ ω, N.v k 0 ω ∂P) / 2 <
      (∑ i ∈ Finset.range n, N.v k i ω) / n := hω.eventually (lt_mem_nhds (by linarith))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < (∫ ω, N.v k 0 ω ∂P) / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have : (0:ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ this] at hn
  simp only [Network.V]
  linarith

lemma ae_U' {k : Fin K} (hk : k ∈ J) : ∀ᵐ ω ∂P, Tendsto (fun l => N.U k l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.u k 0) P := (N.memLp_u k hk).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.u k i) (N.u k i') P) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inl (⟨k, hk⟩, i)) (j := Sum.inl (⟨k, hk⟩, i'))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.u k 0 ω ∂P := integral_pos_of_pos' (N.pos_u k hk 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.u k i) hint hind
    (N.ident_u k hk)] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop, (∫ ω, N.u k 0 ω ∂P) / 2 <
      (∑ i ∈ Finset.range n, N.u k i ω) / n := hω.eventually (lt_mem_nhds (by linarith))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < (∫ ω, N.u k 0 ω ∂P) / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have : (0:ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ this] at hn
  simp only [Network.U]
  linarith

lemma ae_goodPt : ∀ᵐ ω ∂P, GoodPt N ω := by
  have h1 : ∀ᵐ ω ∂P, ∀ k, k ∈ J → Tendsto (fun l => N.U k l ω) atTop atTop := by
    rw [ae_all_iff]; intro k
    by_cases hk : k ∈ J
    · filter_upwards [ae_U' N hk] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hk
  have h2 : ∀ᵐ ω ∂P, ∀ k, Tendsto (fun l => N.V k l ω) atTop atTop :=
    ae_all_iff.2 fun k => ae_V' N k
  filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩

lemma good_of {ω : Ω} (hω : GoodPt N ω) : Good (aω N ω) (shω N ω) := by
  have hA : ∀ k, (∀ t, 0 ≤ t → ∀ᶠ s in 𝓝[≥] t, N.Avec s ω k = N.Avec t ω k) ∧
      (∀ t, 0 < t → ∃ c, ∀ᶠ s in 𝓝[<] t, N.Avec s ω k = c) := by
    intro k
    by_cases hk : k ∈ J
    · obtain ⟨h0, hm⟩ := U_props N hk ω
      have ht := hω.1 k hk
      refine ⟨fun t ht0 => ?_, fun t ht0 => ?_⟩
      · filter_upwards [cnt_right h0 hm ht ht0] with s hs
        simp only [Network.Avec, A_eq N hk, hs]
      · obtain ⟨c, hc⟩ := cnt_left h0 hm ht ht0
        exact ⟨(c : ℝ), by filter_upwards [hc] with s hs; simp only [Network.Avec, A_eq N hk, hs]⟩
    · have h0 : ∀ s, N.Avec s ω k = 0 := fun s => by simp [Network.Avec, Network.A, hk]
      exact ⟨fun t _ => Eventually.of_forall fun s => by rw [h0, h0],
        fun t _ => ⟨0, Eventually.of_forall fun s => h0 s⟩⟩
  refine ⟨aω_meas N ω, shω_meas N ω, fun t ht => ?_, fun k x hx => ?_, fun t ht => ?_,
    fun k x hx => ?_⟩
  · filter_upwards [eventually_all.2 fun k => (hA k).1 t ht] with s hs
    exact funext hs
  · obtain ⟨h0, hm⟩ := V_props N k ω
    filter_upwards [cnt_right h0 hm (hω.2 k) hx] with y hy
    simp only [shω, Shat_eq, hy]
  · choose c hc using fun k => (hA k).2 t ht
    exact ⟨c, by filter_upwards [eventually_all.2 hc] with s hs; exact funext hs⟩
  · obtain ⟨h0, hm⟩ := V_props N k ω
    obtain ⟨c, hc⟩ := cnt_left h0 hm (hω.2 k) hx
    exact ⟨shG N k (ω, c), by filter_upwards [hc] with y hy; simp only [shω, Shat_eq, hy]⟩

lemma sol_of {ω : Ω} {Qω Bω : ℝ → Fin K → ℝ} (h : N.IsQueueSolution ω Qω Bω) :
    Sol (aω N ω) (shω N ω) Bω Qω :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

lemma pic_jm (m : ℕ) : Measurable (fun p : ℝ × Ω => pic (aω N p.2) (shω N p.2) m p.1) := by
  induction m with
  | zero => simp only [pic]; exact measurable_const
  | succ m ih =>
    have hF : Measurable fun p : ℝ × Ω =>
        Fq (aω N p.2) (shω N p.2) (pic (aω N p.2) (shω N p.2) m) p.1 :=
      (Avec_jm N).add (Finset.measurable_sum _ fun j _ =>
        (Shat_jm N j).comp (((measurable_pi_apply j).comp ih).prodMk measurable_snd))
    refine measurable_uncurry_of_continuous_of_measurable
      (u := fun t ω => pic (aω N ω) (shω N ω) (m + 1) t)
      (fun ω => (pic_prop (aω_meas N ω) (shω_meas N ω) (m + 1)).2.2.2) fun t => ?_
    refine measurable_pi_lambda _ fun k => ?_
    have hk : Measurable fun p : ℝ × Ω =>
        ind (Fq (aω N p.2) (shω N p.2) (pic (aω N p.2) (shω N p.2) m) p.1 k) :=
      measurable_ind.comp ((measurable_pi_apply k).comp hF)
    simp only [pic, prim, intervalIntegral]
    exact (hk.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc 0 t))).measurable.sub
      (hk.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc t 0))).measurable

/-- the measurable version of the busy time. -/
noncomputable def Bo (ω : Ω) : ℝ → Fin K → ℝ :=
  fun t k => liminf (fun m => pic (aω N ω) (shω N ω) m t k) atTop

lemma Bo_meas (t : ℝ) (k : Fin K) : Measurable fun ω => Bo N ω t k := by
  have h : ∀ m, Measurable fun ω => pic (aω N ω) (shω N ω) m t k := fun m => by
    have h1 : Measurable ((fun p : ℝ × Ω => pic (aω N p.2) (shω N p.2) m p.1) ∘
        fun ω : Ω => (t, ω)) := (pic_jm N m).comp measurable_prodMk_left
    have h2 := (measurable_pi_apply k).comp h1
    exact h2
  exact Measurable.liminf h

lemma B_eq_Bo {ω : Ω} (hg : GoodPt N ω) {Qω Bω : ℝ → Fin K → ℝ}
    (hs : N.IsQueueSolution ω Qω Bω) {t : ℝ} (ht : 0 ≤ t) : Bω t = Bo N ω t :=
  funext fun k => sol_eq_liminf (good_of N hg) (sol_of N hs) ht k

lemma X_meas (t : ℝ) : Measurable fun ω => N.X t ω := by
  simp only [Network.X]
  exact (Avec_sec N t).add (Finset.measurable_sum _ fun k _ => Shat_sec N k t)

lemma XtBo_meas (t : ℝ) : Measurable fun ω => N.Xtilde (Bo N ω) t ω := by
  have hS : ∀ k, Measurable fun ω => N.Shat k (Bo N ω t k) ω := fun k => by
    have h : Measurable ((fun p : ℝ × Ω => N.Shat k p.1 p.2) ∘ fun ω => (Bo N ω t k, ω)) :=
      (Shat_jm N k).comp ((Bo_meas N t k).prodMk measurable_id)
    exact h
  have hL : ∀ k, Measurable fun ω => (N.mu k * Bo N ω t k) • ((N.routing - 1) k) := fun k =>
    ((Bo_meas N t k).const_mul (N.mu k)).smul_const _
  simp only [Network.Xtilde, Network.Atilde, Network.Stilde]
  exact (((Avec_sec N t).sub measurable_const).add
    (Finset.measurable_sum _ fun k _ => (hS k).sub (hL k))).add measurable_const

lemma path_meas {f : Ω → ℝ → Fin K → ℝ} (hf : ∀ t, Measurable fun ω => f ω t) (n : ℕ) :
    Measurable fun ω => onUnit (diffScale n (f ω)) :=
  measurable_pi_lambda _ fun t => by
    simp only [onUnit, diffScale]
    exact (hf _).const_smul ((Real.sqrt n)⁻¹ : ℝ)

/-- MeasNetputT for one network: `ζⁿ` and `ζ̃ⁿ` are a.e.-measurable random paths, a.s. cadlag. -/
theorem meas_netput (Q B : Ω → ℝ → Fin K → ℝ)
    (hQ : ∀ᵐ ω ∂P, N.IsQueueSolution ω (Q ω) (B ω)) (n : ℕ) :
    (AEMeasurable (fun ω => onUnit (diffScale n (fun t => N.X t ω))) P ∧
      ∀ᵐ ω ∂P, IsCadlag01 (diffScale n (fun t => N.X t ω))) ∧
    (AEMeasurable (fun ω => onUnit (diffScale n (fun t => N.Xtilde (B ω) t ω))) P ∧
      ∀ᵐ ω ∂P, IsCadlag01 (diffScale n (fun t => N.Xtilde (B ω) t ω))) := by
  refine ⟨⟨(path_meas (f := fun ω t => N.X t ω) (X_meas N) n).aemeasurable, ?_⟩, ⟨?_, ?_⟩⟩
  · filter_upwards [ae_goodPt N] with ω hω
    have hG := good_of N hω
    refine cadlag_of (y := fun t => N.X t ω) (z := fun _ => 0) ?_ continuousOn_const
      (fun t => (add_zero _).symm) n
    exact RL_add (RL_a hG) (RL_sum fun k => RL_sh hG k)
  · refine ⟨fun ω => onUnit (diffScale n (fun t => N.Xtilde (Bo N ω) t ω)),
      path_meas (f := fun ω t => N.Xtilde (Bo N ω) t ω) (XtBo_meas N) n, ?_⟩
    filter_upwards [ae_goodPt N, hQ] with ω hω hs
    funext t
    have ht : 0 ≤ (n:ℝ) * clamp01 t :=
      mul_nonneg (Nat.cast_nonneg n) (le_min (le_max_right t 0) zero_le_one)
    simp only [onUnit, diffScale, Network.Xtilde, B_eq_Bo N hω hs ht]
  · filter_upwards [ae_goodPt N, hQ] with ω hω hs
    have hG := good_of N hω
    have hS := sol_of N hs
    refine cadlag_of (y := Fq (aω N ω) (shω N ω) (B ω))
      (z := fun t => N.Xtilde (B ω) t ω - Fq (aω N ω) (shω N ω) (B ω) t) (RL_sol hG hS) ?_
      (fun t => by abel) n
    have hBc := sol_contOn hS
    have hBk : ∀ k, ContinuousOn (fun t => B ω t k) (Ici 0) := fun k =>
      (continuous_apply k).comp_continuousOn hBc
    refine ContinuousOn.congr (f := fun t => -(t • N.lam) -
      ∑ k, (N.mu k * B ω t k) • (N.routing - 1) k + t • (N.lam + N.eta)) ?_ ?_
    · exact ((continuousOn_id.smul continuousOn_const).neg.sub (continuousOn_finsetSum _
        fun k _ => (continuousOn_const.mul (hBk k)).smul continuousOn_const)).add
        (continuousOn_id.smul continuousOn_const)
    · intro t _
      simp only [Network.Xtilde, Network.Atilde, Network.Stilde, Fq, aω, shω,
        Finset.sum_sub_distrib]
      abel

end Net

end MeasP


open MeasureTheory Reiman84.QueueLength in
theorem solution {K : ℕ} {J : Finset (Fin K)} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω}
    (N : Network K J P) (Q B : Ω → ℝ → Fin K → ℝ)
    (hQ : ∀ᵐ ω ∂P, N.IsQueueSolution ω (Q ω) (B ω)) (n : ℕ) :
    (AEMeasurable (fun ω => onUnit (diffScale n (fun t => N.X t ω))) P ∧
      ∀ᵐ ω ∂P, IsCadlag01 (diffScale n (fun t => N.X t ω))) ∧
    (AEMeasurable (fun ω => onUnit (diffScale n (fun t => N.Xtilde (B ω) t ω))) P ∧
      ∀ᵐ ω ∂P, IsCadlag01 (diffScale n (fun t => N.Xtilde (B ω) t ω))) := by
  exact MeasP.meas_netput N Q B hQ n
