-- Prove2me | solution 1 for OWMR.sl_adapted_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T04:27:16.068492+00:00
-- url     : https://prove2.me/submissions/e7dc4908-3c4e-40d8-94a0-893bc712d66f

import Definitions.Def_owmr_network_model
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
The finite-horizon bound (6) of Lemma 1 for a single-location position process embedded in a
larger probability space (network history and auxiliary randomness), given a bounded
subsolution `(J, v)` of the one-period cost inequality.

The position process is `pos t = y0 + ∑_{s ≤ t} q_s - ∑_{s < t} g(d_s)`, with nonnegative,
nonanticipative orders `q_s` and demands `g(d_s)`, where `d_s` is the `s`-th coordinate of an
i.i.d. sequence of law `μ`, independent of the auxiliary randomness. With `V = v + K ∈ [0, K]`,
`K 1{q_t > 0} + f(pos_t) + 𝔼 V(pos_t - D) ≥ J + V(pre_t)` pointwise, the coordinate `d_t` is
independent of `pos_t`, so `𝔼 V(pos_t - D) = 𝔼 V(pre_{t+1})`, and telescoping gives
`T J ≤ 𝔼 ∑_{t<T} [K 1{q_t > 0} + f(pos_t)] + K`.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

section

variable {α U : Type} [MeasurableSpace α] [Zero α] [MeasurableSpace U]

omit [MeasurableSpace U] in
private lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const

omit [MeasurableSpace α] [MeasurableSpace U] in
private lemma padHist_insertNth_lt {M : ℕ} (i : Fin (M + 1)) (a b : α) (z : Fin M → α) (s : ℕ)
    (hs : s < i.val) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) s = padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z) s := by
  have hsM : s < M + 1 := lt_trans hs i.2
  have hsM' : s < M := lt_of_lt_of_le hs (Nat.lt_succ_iff.1 i.2)
  simp only [padHist, dif_pos hsM]
  have he : (⟨s, hsM⟩ : Fin (M + 1)) = i.succAbove ⟨s, hsM'⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · simp [Fin.lt_def, hs]
  rw [he, Fin.insertNth_apply_succAbove (α := fun _ => α), Fin.insertNth_apply_succAbove (α := fun _ => α)]

omit [MeasurableSpace α] [MeasurableSpace U] in
private lemma padHist_insertNth_self {M : ℕ} (i : Fin (M + 1)) (a : α) (z : Fin M → α) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) i.val = a := by
  simp only [padHist, dif_pos i.2]
  exact Fin.insertNth_apply_same (α := fun _ => α) i a z

/-- Resampling one coordinate: if `Φ (u, d)` depends on `d` only through the coordinates before
`t`, then the `t`-th demand is independent of it. -/
private lemma lintegral_coord (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure U) [SFinite ν]
    (N t : ℕ) (ht : t < N) (Φ : U × (ℕ → α) → α → ℝ≥0∞)
    (hΦ : Measurable fun p : (U × (ℕ → α)) × α => Φ p.1 p.2)
    (hdep : ∀ (u : U) (d d' : ℕ → α) (a : α), (∀ s < t, d s = d' s) → Φ (u, d) a = Φ (u, d') a) :
    ∫⁻ ω, Φ (ω.1, padHist N ω.2) (padHist N ω.2 t) ∂(ν.prod (Measure.pi fun _ : Fin N => μ))
      = ∫⁻ ω, ∫⁻ a, Φ (ω.1, padHist N ω.2) a ∂μ ∂(ν.prod (Measure.pi fun _ : Fin N => μ)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hD : Measurable fun z : Fin (M + 1) → α => padHist (M + 1) z := measurable_padHist' _
  have hm1 : Measurable fun ω : U × (Fin (M + 1) → α) =>
      Φ (ω.1, padHist (M + 1) ω.2) (padHist (M + 1) ω.2 t) := by
    have h2 : Measurable fun ω : U × (Fin (M + 1) → α) => padHist (M + 1) ω.2 t :=
      (measurable_pi_apply t).comp (hD.comp measurable_snd)
    exact hΦ.comp ((measurable_fst.prodMk (hD.comp measurable_snd)).prodMk h2)
  have hm2 : Measurable fun ω : U × (Fin (M + 1) → α) =>
      ∫⁻ a, Φ (ω.1, padHist (M + 1) ω.2) a ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : (U × (Fin (M + 1) → α)) × α =>
      Φ (p.1.1, padHist (M + 1) p.1.2) p.2)
      (hΦ.comp (((measurable_fst.comp measurable_fst).prodMk
        (hD.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd))
  rw [lintegral_prod _ hm1.aemeasurable, lintegral_prod _ hm2.aemeasurable]
  refine lintegral_congr fun u => ?_
  set i : Fin (M + 1) := ⟨t, ht⟩ with hi
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => α) i with he
  have hsymm : ∀ p : α × (Fin M → α), e.symm p = Fin.insertNth (α := fun _ => α) i p.1 p.2 := fun p => rfl
  -- transport both sides through `e`
  have key : ∀ F : (Fin (M + 1) → α) → ℝ≥0∞,
      ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (M + 1) => μ)
        = ∫⁻ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin M => μ)) := by
    intro F
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp only [MeasurableEquiv.symm_apply_apply]
  -- independence of the earlier coordinates from the inserted value
  have hind : ∀ (a b : α) (z : Fin M → α) (c : α),
      Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c
        = Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z)) c := by
    intro a b z c
    exact hdep u _ _ c fun s hs => padHist_insertNth_lt i a b z s (by simpa [hi] using hs)
  have hins : Measurable fun p : α × (Fin M → α) => Fin.insertNth (α := fun _ => α) i p.1 p.2 := e.symm.measurable
  have hG : Measurable fun p : α × (Fin M → α) =>
      Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2)) p.1 :=
    hΦ.comp ((measurable_const.prodMk (hD.comp hins)).prodMk measurable_fst)
  rw [key, key]
  simp only [hsymm]
  have hl : ∀ p : α × (Fin M → α), padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2) t = p.1 :=
    fun p => padHist_insertNth_self i p.1 p.2
  simp only [hl]
  rw [lintegral_prod_symm _ hG.aemeasurable]
  have hc : ∀ (a : α) (z : Fin M → α),
      ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c ∂μ
        = ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ := fun a z =>
    lintegral_congr fun c => hind a c z c
  simp only [hc]
  have hH : Measurable fun z : Fin M → α =>
      ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin M → α) × α =>
      Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.2 p.1)) p.2)
      (hΦ.comp ((measurable_const.prodMk (hD.comp (hins.comp
        (measurable_snd.prodMk measurable_fst)))).prodMk measurable_snd))
  have hprod := lintegral_prod (μ := μ) (ν := Measure.pi fun _ : Fin M => μ)
    (fun p : α × (Fin M → α) =>
      ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c p.2)) c ∂μ)
    (hH.comp measurable_snd).aemeasurable
  rw [hprod]
  simp only [lintegral_const, measure_univ, mul_one]

end

/-- The position after the orders of period `t`. -/
private noncomputable def posF {α U : Type} (q : ℕ → U → (ℕ → α) → ℝ) (g : α → ℝ≥0) (y0 : ℝ)
    (t : ℕ) (ω : U × (ℕ → α)) : ℝ :=
  y0 + ∑ s ∈ Finset.range (t + 1), q s ω.1 ω.2 - ∑ s ∈ Finset.range t, (g (ω.2 s) : ℝ)

/-- The position before the orders of period `t`. -/
private noncomputable def preF {α U : Type} (q : ℕ → U → (ℕ → α) → ℝ) (g : α → ℝ≥0) (y0 : ℝ)
    (t : ℕ) (ω : U × (ℕ → α)) : ℝ :=
  y0 + ∑ s ∈ Finset.range t, q s ω.1 ω.2 - ∑ s ∈ Finset.range t, (g (ω.2 s) : ℝ)

theorem solution {α U : Type} [MeasurableSpace α] [Zero α] [MeasurableSpace U]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure U) [IsProbabilityMeasure ν]
    (g : α → ℝ≥0) (hg : Measurable g) (q : ℕ → U → (ℕ → α) → ℝ)
    (hna : ∀ (t : ℕ) (u : U) (d d' : ℕ → α), (∀ s < t, d s = d' s) → q t u d = q t u d')
    (hqm : ∀ t, Measurable fun ω : U × (ℕ → α) => q t ω.1 ω.2)
    (hq0 : ∀ t u d, 0 ≤ q t u d) (y0 : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (K J : ℝ) (v : ℝ → ℝ) (hv : Measurable v)
    (hvb : ∀ y, -K ≤ v y ∧ v y ≤ 0)
    (hsub : ∀ y, J ≤ f y + ∫ a, v (y - (g a : ℝ)) ∂μ - v y) (T N : ℕ) (hTN : T ≤ N) :
    ENNReal.ofReal (T * J)
      ≤ ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (K * (if 0 < q t ω.1 (padHist N ω.2) then 1 else 0)
            + f (y0 + ∑ s ∈ Finset.range (t + 1), q s ω.1 (padHist N ω.2)
              - ∑ s ∈ Finset.range t, (g (padHist N ω.2 s) : ℝ)))
          ∂(ν.prod (Measure.pi fun _ : Fin N => μ)) + ENNReal.ofReal K := by
  have hK : 0 ≤ K := by linarith [(hvb 0).1, (hvb 0).2]
  rcases le_or_gt J 0 with hJ | hJ
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg T) hJ)]
    exact zero_le
  set P := ν.prod (Measure.pi fun _ : Fin N => μ) with hP
  set V : ℝ → ℝ := fun y => v y + K with hV
  have hV0 : ∀ y, 0 ≤ V y := fun y => by simp only [hV]; linarith [(hvb y).1]
  have hVK : ∀ y, V y ≤ K := fun y => by simp only [hV]; linarith [(hvb y).2]
  have hVm : Measurable V := hv.add measurable_const
  have hgm : ∀ s, Measurable fun ω : U × (ℕ → α) => (g (ω.2 s) : ℝ) := by
    intro s
    have h1 : Measurable fun ω : U × (ℕ → α) => ω.2 s :=
      (measurable_pi_apply s).comp measurable_snd
    exact (hg.comp h1).coe_nnreal_real
  have hposm : ∀ t, Measurable (posF q g y0 t) := fun t =>
    (measurable_const.add (Finset.measurable_sum _ fun s _ => hqm s)).sub
      (Finset.measurable_sum _ fun s _ => hgm s)
  have hprem : ∀ t, Measurable (preF q g y0 t) := fun t =>
    (measurable_const.add (Finset.measurable_sum _ fun s _ => hqm s)).sub
      (Finset.measurable_sum _ fun s _ => hgm s)
  have hpos_pre : ∀ t ω, posF q g y0 t ω = preF q g y0 t ω + q t ω.1 ω.2 := by
    intro t ω
    simp only [posF, preF, Finset.sum_range_succ]
    ring
  have hpre_succ : ∀ t ω, preF q g y0 (t + 1) ω = posF q g y0 t ω - (g (ω.2 t) : ℝ) := by
    intro t ω
    simp only [posF, preF, Finset.sum_range_succ]
    ring
  -- the history map
  set D : U × (Fin N → α) → U × (ℕ → α) := fun ω => (ω.1, padHist N ω.2) with hDdef
  have hDm : Measurable D := measurable_fst.prodMk ((measurable_padHist' N).comp measurable_snd)
  -- per-period cost and the expected relative values
  set c : ℕ → U × (ℕ → α) → ℝ≥0∞ := fun t ω =>
    ENNReal.ofReal (K * (if 0 < q t ω.1 ω.2 then 1 else 0) + f (posF q g y0 t ω)) with hc
  have hcm : ∀ t, Measurable (c t) := by
    intro t
    refine ENNReal.measurable_ofReal.comp ((measurable_const.mul ?_).add (hf.comp (hposm t)))
    exact Measurable.ite (measurableSet_lt measurable_const (hqm t)) measurable_const
      measurable_const
  set a : ℕ → ℝ≥0∞ := fun t => ∫⁻ ω, ENNReal.ofReal (V (preF q g y0 t (D ω))) ∂P with ha
  have haK : ∀ t, a t ≤ ENNReal.ofReal K := by
    intro t
    calc a t ≤ ∫⁻ _ω, ENNReal.ofReal K ∂P :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hVK _)
      _ = ENNReal.ofReal K := by rw [lintegral_const, measure_univ, mul_one]
  -- integrability of the one-period expectation
  have hint : ∀ y : ℝ, Integrable (fun b : α => V (y - (g b : ℝ))) μ := by
    intro y
    refine Integrable.of_bound (hVm.comp (measurable_const.sub
      hg.coe_nnreal_real)).aestronglyMeasurable K (ae_of_all _ fun b => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 _)]
    exact hVK _
  have hintv : ∀ y : ℝ, Integrable (fun b : α => v (y - (g b : ℝ))) μ := by
    intro y
    refine Integrable.of_bound (hv.comp (measurable_const.sub
      hg.coe_nnreal_real)).aestronglyMeasurable K (ae_of_all _ fun b => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(hvb _).1, by linarith [(hvb (y - (g b : ℝ))).2]⟩
  -- the pointwise one-period inequality
  have hpt : ∀ t ω, ENNReal.ofReal J + ENNReal.ofReal (V (preF q g y0 t ω))
      ≤ c t ω + ∫⁻ b, ENNReal.ofReal (V (posF q g y0 t ω - (g b : ℝ))) ∂μ := by
    intro t ω
    have hE : ∫ b, V (posF q g y0 t ω - (g b : ℝ)) ∂μ
        = ∫ b, v (posF q g y0 t ω - (g b : ℝ)) ∂μ + K := by
      simp only [hV]
      rw [integral_add (hintv _) (integrable_const K), integral_const, probReal_univ, one_smul]
    have hset : K * (if 0 < q t ω.1 ω.2 then 1 else 0)
        ≥ v (preF q g y0 t ω) - v (posF q g y0 t ω) := by
      split_ifs with hq
      · linarith [(hvb (preF q g y0 t ω)).2, (hvb (posF q g y0 t ω)).1]
      · have hq' : q t ω.1 ω.2 = 0 := le_antisymm (not_lt.1 hq) (hq0 _ _ _)
        rw [hpos_pre, hq', add_zero]
        simp
    have hs := hsub (posF q g y0 t ω)
    have hreal : J + V (preF q g y0 t ω)
        ≤ (K * (if 0 < q t ω.1 ω.2 then 1 else 0) + f (posF q g y0 t ω))
          + ∫ b, V (posF q g y0 t ω - (g b : ℝ)) ∂μ := by
      rw [hE]
      simp only [hV] at *
      linarith
    have hc0 : 0 ≤ K * (if 0 < q t ω.1 ω.2 then 1 else 0) + f (posF q g y0 t ω) := by
      have : 0 ≤ K * (if 0 < q t ω.1 ω.2 then (1 : ℝ) else 0) := by positivity
      linarith [hf0 (posF q g y0 t ω)]
    have hI0 : 0 ≤ ∫ b, V (posF q g y0 t ω - (g b : ℝ)) ∂μ :=
      integral_nonneg fun b => hV0 _
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _) (ae_of_all _ fun b => hV0 _),
      ← ENNReal.ofReal_add hJ.le (hV0 _), hc]
    simp only
    rw [← ENNReal.ofReal_add hc0 hI0]
    exact ENNReal.ofReal_le_ofReal hreal
  -- independence of the period-`t` demand: `𝔼 V(pos_t - D_t) = 𝔼 V(pre_{t+1})`
  have hkey : ∀ t, t < N → ∫⁻ ω, ∫⁻ b, ENNReal.ofReal (V (posF q g y0 t (D ω) - (g b : ℝ))) ∂μ ∂P
      = a (t + 1) := by
    intro t ht
    have hΦ : Measurable fun p : (U × (ℕ → α)) × α =>
        ENNReal.ofReal (V (posF q g y0 t p.1 - (g p.2 : ℝ))) :=
      ENNReal.measurable_ofReal.comp (hVm.comp (((hposm t).comp measurable_fst).sub
        (hg.comp measurable_snd).coe_nnreal_real))
    have hdep : ∀ (u : U) (d d' : ℕ → α) (b : α), (∀ s < t, d s = d' s) →
        ENNReal.ofReal (V (posF q g y0 t (u, d) - (g b : ℝ)))
          = ENNReal.ofReal (V (posF q g y0 t (u, d') - (g b : ℝ))) := by
      intro u d d' b h
      have : posF q g y0 t (u, d) = posF q g y0 t (u, d') := by
        simp only [posF]
        have h1 : ∑ s ∈ Finset.range (t + 1), q s u d = ∑ s ∈ Finset.range (t + 1), q s u d' :=
          Finset.sum_congr rfl fun s hs => hna s u d d' fun r hr =>
            h r (by have := Finset.mem_range.1 hs; omega)
        have h2 : ∑ s ∈ Finset.range t, (g (d s) : ℝ) = ∑ s ∈ Finset.range t, (g (d' s) : ℝ) :=
          Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.1 hs)]
        rw [h1, h2]
      rw [this]
    have := lintegral_coord μ ν N t ht
      (fun ω b => ENNReal.ofReal (V (posF q g y0 t ω - (g b : ℝ)))) hΦ hdep
    simp only [ha]
    rw [← this]
    refine lintegral_congr fun ω => ?_
    simp only [hDdef, hpre_succ]
  -- telescoping by induction on the horizon
  have hind : ∀ T' : ℕ, T' ≤ N →
      ENNReal.ofReal (T' * J) + a 0 ≤ ∫⁻ ω, ∑ t ∈ Finset.range T', c t (D ω) ∂P + a T' := by
    intro T'
    induction T' with
    | zero => intro _; simp
    | succ T' ih =>
      intro hT'
      have ih' := ih (by omega)
      have hsplit : ∫⁻ ω, ∑ t ∈ Finset.range (T' + 1), c t (D ω) ∂P
          = ∫⁻ ω, ∑ t ∈ Finset.range T', c t (D ω) ∂P + ∫⁻ ω, c T' (D ω) ∂P := by
        simp only [Finset.sum_range_succ]
        exact lintegral_add_right _ ((hcm T').comp hDm)
      have hstep : ENNReal.ofReal J + a T' ≤ ∫⁻ ω, c T' (D ω) ∂P + a (T' + 1) := by
        rw [← hkey T' (by omega)]
        have hm2 : Measurable fun ω : U × (Fin N → α) =>
            ∫⁻ b, ENNReal.ofReal (V (posF q g y0 T' (D ω) - (g b : ℝ))) ∂μ :=
          Measurable.lintegral_prod_right' (f := fun p : (U × (Fin N → α)) × α =>
            ENNReal.ofReal (V (posF q g y0 T' (D p.1) - (g p.2 : ℝ))))
            (ENNReal.measurable_ofReal.comp (hVm.comp ((((hposm T').comp hDm).comp
              measurable_fst).sub (hg.comp measurable_snd).coe_nnreal_real)))
        rw [← lintegral_add_left (f := fun ω => c T' (D ω)) ((hcm T').comp hDm)]
        calc ENNReal.ofReal J + a T'
            = ∫⁻ ω, (ENNReal.ofReal J + ENNReal.ofReal (V (preF q g y0 T' (D ω)))) ∂P := by
              rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ _ := lintegral_mono fun ω => hpt T' (D ω)
      have hcast : ENNReal.ofReal (((T' + 1 : ℕ) : ℝ) * J)
          = ENNReal.ofReal (T' * J) + ENNReal.ofReal J := by
        rw [← ENNReal.ofReal_add (by positivity) hJ.le]
        congr 1
        push_cast
        ring
      rw [hsplit, hcast]
      calc ENNReal.ofReal (T' * J) + ENNReal.ofReal J + a 0
          = (ENNReal.ofReal (T' * J) + a 0) + ENNReal.ofReal J := by ring
        _ ≤ (∫⁻ ω, ∑ t ∈ Finset.range T', c t (D ω) ∂P + a T') + ENNReal.ofReal J := by gcongr
        _ = ∫⁻ ω, ∑ t ∈ Finset.range T', c t (D ω) ∂P + (ENNReal.ofReal J + a T') := by ring
        _ ≤ ∫⁻ ω, ∑ t ∈ Finset.range T', c t (D ω) ∂P
            + (∫⁻ ω, c T' (D ω) ∂P + a (T' + 1)) := by gcongr
        _ = _ := by ring
  calc ENNReal.ofReal (T * J) ≤ ENNReal.ofReal (T * J) + a 0 := le_self_add
    _ ≤ ∫⁻ ω, ∑ t ∈ Finset.range T, c t (D ω) ∂P + a T := hind T hTN
    _ ≤ ∫⁻ ω, ∑ t ∈ Finset.range T, c t (D ω) ∂P + ENNReal.ofReal K := by gcongr; exact haK T
    _ = _ := rfl
