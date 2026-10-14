-- Prove2me | solution 1 for StochApproxDyn.WeakAPT.conditional_drift_eq51
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:12:28.808159+00:00
-- url     : https://prove2.me/submissions/f4fa0a8e-fbbb-42a9-b9d1-9263566f14e1

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral



namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- essential supremum of a family, realized by a countable subfamily -/
lemma e51_exists_seq_ae_sup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    [Nonempty ι] (Y : ι → Ω → ℝ≥0∞) (hY : ∀ i, Measurable (Y i)) (hb : ∀ i ω, Y i ω ≤ 1) :
    ∃ σ : ℕ → ι, ∀ i, Y i ≤ᵐ[P] fun ω => ⨆ n, Y (σ n) ω := by
  classical
  let F : (ℕ → ι) → ℝ≥0∞ := fun σ => ∫⁻ ω, ⨆ n, Y (σ n) ω ∂P
  have hS : (Set.range F).Nonempty := Set.range_nonempty F
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hS (OrderTop.bddAbove _)
  choose τ hτ using huS
  let σ : ℕ → ι := fun n => τ (Nat.unpair n).1 (Nat.unpair n).2
  have hV : ∀ k ω, (⨆ n, Y (τ k n) ω) ≤ ⨆ n, Y (σ n) ω := fun k ω =>
    iSup_le fun n => le_iSup_of_le (Nat.pair k n) (by simp [σ, Nat.unpair_pair])
  have hFσ : sSup (Set.range F) ≤ F σ :=
    le_of_tendsto' hu (fun k => (hτ k) ▸ lintegral_mono (hV k))
  refine ⟨σ, fun i => ?_⟩
  let σ' : ℕ → ι := fun n => Nat.casesOn n i σ
  have hle : (fun ω => ⨆ n, Y (σ n) ω) ≤ᵐ[P] fun ω => ⨆ n, Y (σ' n) ω :=
    ae_of_all _ (fun ω => iSup_le fun n => le_iSup_of_le (n+1) le_rfl)
  have hF' : F σ' ≤ F σ := (le_sSup (Set.mem_range_self σ')).trans hFσ
  have hfin : ∫⁻ ω, ⨆ n, Y (σ n) ω ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂P) ?_ (lintegral_mono fun ω => iSup_le fun n => hb _ _)
    simp
  have heq := ae_eq_of_ae_le_of_lintegral_le hle hfin
    (Measurable.iSup fun n => hY (σ' n)).aemeasurable hF'
  filter_upwards [heq] with ω hω
  rw [hω]; exact le_iSup_of_le 0 le_rfl

/-- joint measurability of a progressively measurable process -/
lemma e51_joint_meas {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (hX : IsProgressivelyMeasurable ℱ X) :
    Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2) := by
  let g : ℕ → ℝ≥0 × Ω → M := fun n p =>
    X (Set.projIcc (0:ℝ≥0) ((n:ℝ≥0) + 1) (by positivity) p.1) p.2
  have hg : ∀ n, Measurable (g n) := by
    intro n
    have h1 := hX ((n:ℝ≥0) + 1) (by positivity)
    have h2 : Measurable[_, (inferInstance : MeasurableSpace (Set.Icc (0 : ℝ≥0) ((n:ℝ≥0) + 1))).prod
        (ℱ ((n:ℝ≥0) + 1))] (fun p : ℝ≥0 × Ω =>
          ((Set.projIcc (0:ℝ≥0) ((n:ℝ≥0) + 1) (by positivity) p.1), p.2)) := by
      apply Measurable.prodMk
      · exact (continuous_projIcc).measurable.comp measurable_fst
      · exact (measurable_id.mono (ℱ.le _) le_rfl).comp measurable_snd
    exact h1.comp h2
  refine measurable_of_tendsto_metrizable hg ?_
  rw [tendsto_pi_nhds]
  intro p
  apply tendsto_nhds_of_eventually_eq
  obtain ⟨N, hN⟩ := exists_nat_ge p.1
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [g]
  rw [Set.projIcc_of_mem]
  exact ⟨zero_le, hN.trans (by exact_mod_cast (show (N:ℝ≥0) ≤ n + 1 by exact_mod_cast (by omega)))⟩

lemma e51_ii {h : ℝ → ℝ} (hm : Measurable h) (C : ℝ) (hb : ∀ s, |h s| ≤ C) (a b : ℝ) :
    IntervalIntegrable h volume a b :=
  ⟨Measure.integrableOn_of_bounded (s := Set.Ioc a b) (by simp) hm.aestronglyMeasurable
    (ae_of_all _ (fun s => by rw [Real.norm_eq_abs]; exact hb s)),
   Measure.integrableOn_of_bounded (s := Set.Ioc b a) (by simp) hm.aestronglyMeasurable
    (ae_of_all _ (fun s => by rw [Real.norm_eq_abs]; exact hb s))⟩

lemma e51_int_meas {Ω : Type*} [MeasurableSpace Ω] (H : ℝ × Ω → ℝ) (hH : Measurable H)
    (a b : ℝ) (hab : a ≤ b) :
    Measurable (fun ω => ∫ s in a..b, H (s, ω)) := by
  have h1 : StronglyMeasurable (fun q : Ω × ℝ => H (q.2, q.1)) :=
    (hH.comp measurable_swap).stronglyMeasurable
  have h2 := h1.integral_prod_right' (ν := volume.restrict (Set.Ioc a b))
  have e : (fun ω => ∫ s in a..b, H (s, ω)) =
      fun ω => ∫ s, H (s, ω) ∂(volume.restrict (Set.Ioc a b)) := by
    funext ω; rw [intervalIntegral.integral_of_le hab]
  rw [e]; exact h2.measurable

lemma e51_step {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hf : Continuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hfε : ∀ a b, dist a b < δ → |f a - f b| ≤ ε)
    (v : Ω → ℝ) (hv : Measurable v) (hv1 : ∀ ω, |v ω| ≤ 1) (S : ℝ≥0)
    (hvS : ∀ s : ℝ≥0, S ≤ s →
      P[(deviationEvent Φ X s δ T).indicator (fun _ => (1:ℝ)) | ℱ s] ≤ᵐ[P] v)
    (a : ℝ≥0) (ha : S ≤ a) :
    ∀ᵐ ω ∂P, |(P[fun ω => ∫ s in (a:ℝ)..(a:ℝ) + T,
        (f (X (s + T).toNNReal ω) - f (Φ T (X s.toNNReal ω))) | ℱ a]) ω|
      ≤ ε * T + T * (P[v | ℱ a]) ω := by
  have hm := ℱ.le a
  have hjm := e51_joint_meas ℱ X hX.progMeasurable
  have hX1 : Measurable (fun p : ℝ × Ω => X (p.1 + T).toNNReal p.2) :=
    hjm.comp ((measurable_real_toNNReal.comp (measurable_fst.add_const _)).prodMk measurable_snd)
  have hX0 : Measurable (fun p : ℝ × Ω => X p.1.toNNReal p.2) :=
    hjm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hΦm : Measurable (fun x => Φ T x) := (Φ.continuous continuous_const continuous_id).measurable
  set g : ℝ × Ω → ℝ := fun p => f (X (p.1 + T).toNNReal p.2) - f (Φ T (X p.1.toNNReal p.2))
    with hgdef
  have hgm : Measurable g := (hf.measurable.comp hX1).sub (hf.measurable.comp (hΦm.comp hX0))
  set C : Set (ℝ × Ω) := {p | ENNReal.ofReal δ ≤
    edist (X (p.1 + T).toNNReal p.2) (Φ T (X p.1.toNNReal p.2))} with hCdef
  have hCm : MeasurableSet C := measurableSet_le measurable_const (hX1.edist (hΦm.comp hX0))
  set k : ℝ × Ω → ℝ := C.indicator (fun _ => 1) with hkdef
  have hkm : Measurable k := measurable_const.indicator hCm
  have hk01 : ∀ p, 0 ≤ k p ∧ k p ≤ 1 := fun p => by
    simp only [hkdef, Set.indicator]; split_ifs <;> norm_num
  have hkb : ∀ p, |k p| ≤ 1 := fun p => by
    rw [abs_le]; constructor <;> linarith [hk01 p]
  have hgb : ∀ p, |g p| ≤ 1 := fun p => by
    have h1 := hf01 (X (p.1 + T).toNNReal p.2); have h2 := hf01 (Φ T (X p.1.toNNReal p.2))
    simp only [hgdef]; rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hgk : ∀ p, |g p| ≤ ε + k p := by
    intro p
    by_cases hp : p ∈ C
    · have : k p = 1 := by simp [hkdef, hp]
      rw [this]
      linarith [hgb p]
    · have : k p = 0 := by simp [hkdef, hp]
      rw [this, add_zero]
      apply hfε
      simp only [hCdef, Set.mem_setOf_eq, not_le] at hp
      exact (edist_lt_ofReal).1 hp
  set D : Ω → ℝ := fun ω => ∫ s in (a:ℝ)..(a:ℝ) + T, g (s, ω) with hDdef
  set Z : Ω → ℝ := fun ω => ∫ s in (a:ℝ)..(a:ℝ) + T, k (s, ω) with hZdef
  have hab : (a:ℝ) ≤ a + T := le_add_of_nonneg_right T.2
  have hDm : Measurable D := e51_int_meas g hgm _ _ hab
  have hZm : Measurable Z := e51_int_meas k hkm _ _ hab
  have hTab : |((a:ℝ) + T) - a| = T := by rw [add_sub_cancel_left, NNReal.abs_eq]
  have hDb : ∀ ω, ‖D ω‖ ≤ T := fun ω => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a:ℝ)) (b := (a:ℝ) + T)
      (f := fun s => g (s, ω)) (C := 1) (fun s _ => by rw [Real.norm_eq_abs]; exact hgb _)
    rw [hTab, one_mul] at this; exact this
  have hZb : ∀ ω, ‖Z ω‖ ≤ T := fun ω => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a:ℝ)) (b := (a:ℝ) + T)
      (f := fun s => k (s, ω)) (C := 1) (fun s _ => by rw [Real.norm_eq_abs]; exact hkb _)
    rw [hTab, one_mul] at this; exact this
  have hDi : Integrable D P := Integrable.of_bound hDm.aestronglyMeasurable T (ae_of_all _ hDb)
  have hZi : Integrable Z P := Integrable.of_bound hZm.aestronglyMeasurable T (ae_of_all _ hZb)
  have hvi : Integrable v P := Integrable.of_bound hv.aestronglyMeasurable 1
    (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hv1 ω))
  have hkii : ∀ ω, IntervalIntegrable (fun s => k (s, ω)) volume (a:ℝ) (a + T) := fun ω =>
    e51_ii (hkm.comp (measurable_id.prodMk measurable_const)) 1 (fun s => hkb _) _ _
  have hDZ : ∀ ω, |D ω| ≤ ε * T + Z ω := by
    intro ω
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun s => g (s, ω)) (g := fun s => ε + k (s, ω)) hab
      (ae_of_all _ (fun s _ => by rw [Real.norm_eq_abs]; exact hgk (s, ω)))
      ((intervalIntegrable_const).add (hkii ω))
    rw [Real.norm_eq_abs, intervalIntegral.integral_add intervalIntegrable_const (hkii ω),
      intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] at h1
    simp only [hDdef, hZdef]
    linarith
  -- key set-integral inequality
  have key : ∀ B, MeasurableSet[ℱ a] B → ∫ ω in B, Z ω ∂P ≤ T * ∫ ω in B, v ω ∂P := by
    intro B hB
    have hBm : MeasurableSet B := hm _ hB
    have hint : Integrable (Function.uncurry fun ω s => k (s, ω))
        ((P.restrict B).prod (volume.restrict (Set.Ioc (a:ℝ) (a + T)))) :=
      Integrable.of_bound (hkm.comp measurable_swap).aestronglyMeasurable 1
        (ae_of_all _ (fun q => by rw [Real.norm_eq_abs]; exact hkb _))
    have e1 : ∫ ω in B, Z ω ∂P =
        ∫ s in Set.Ioc (a:ℝ) (a + T), ∫ ω in B, k (s, ω) ∂P := by
      simp only [hZdef]
      simp_rw [intervalIntegral.integral_of_le hab]
      exact integral_integral_swap hint
    rw [e1]
    have hbd : ∀ s ∈ Set.Ioc (a:ℝ) (a + T), ∫ ω in B, k (s, ω) ∂P ≤ ∫ ω in B, v ω ∂P := by
      intro s hs
      have hs0 : 0 ≤ s := (a.2).trans hs.1.le
      have has' : a ≤ s.toNNReal := (Real.le_toNNReal_iff_coe_le hs0).2 hs.1.le
      have hBs : MeasurableSet[ℱ s.toNNReal] B := ℱ.mono has' _ hB
      have hA := hX.measurableSet_deviation s.toNNReal δ T hδ hT
      have hind : Integrable ((deviationEvent Φ X s.toNNReal δ T).indicator
          (fun _ => (1:ℝ))) P := (integrable_const 1).indicator hA
      have hks : Integrable (fun ω => k (s, ω)) P :=
        Integrable.of_bound (hkm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
          (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hkb _))
      calc ∫ ω in B, k (s, ω) ∂P
          ≤ ∫ ω in B, (deviationEvent Φ X s.toNNReal δ T).indicator (fun _ => (1:ℝ)) ω ∂P := by
            apply setIntegral_mono hks.integrableOn hind.integrableOn
            intro ω
            by_cases hp : (s, ω) ∈ C
            · have hmem : ω ∈ deviationEvent Φ X s.toNNReal δ T := by
                simp only [deviationEvent, Set.mem_setOf_eq]
                refine le_trans ?_ (le_iSup₂_of_le T ⟨zero_le, le_rfl⟩ le_rfl)
                have e : (s + T).toNNReal = s.toNNReal + T := by
                  rw [Real.toNNReal_add hs0 T.coe_nonneg, Real.toNNReal_coe]
                simpa [hCdef, e] using hp
              simp [hkdef, hp, hmem]
            · simp only [hkdef, Set.indicator_of_notMem hp]
              exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
        _ = ∫ ω in B, (P[(deviationEvent Φ X s.toNNReal δ T).indicator (fun _ => (1:ℝ)) |
              ℱ s.toNNReal]) ω ∂P := (setIntegral_condExp (ℱ.le _) hind hBs).symm
        _ ≤ ∫ ω in B, v ω ∂P := setIntegral_mono_ae integrable_condExp.integrableOn
              hvi.integrableOn (hvS _ (ha.trans has'))
    have hsm : StronglyMeasurable (fun s : ℝ => ∫ ω in B, k (s, ω) ∂P) :=
      hkm.stronglyMeasurable.integral_prod_right' (ν := P.restrict B)
    have hsi : IntegrableOn (fun s : ℝ => ∫ ω in B, k (s, ω) ∂P) (Set.Ioc (a:ℝ) (a + T)) volume :=
      Measure.integrableOn_of_bounded (M := 1) (by simp) hsm.aestronglyMeasurable
        (ae_of_all _ (fun s => by
          rw [Real.norm_eq_abs]
          refine (abs_integral_le_integral_abs).trans ?_
          calc ∫ ω in B, |k (s, ω)| ∂P ≤ ∫ ω in B, (1:ℝ) ∂P :=
                setIntegral_mono (Integrable.of_bound
                  ((hkm.comp (measurable_const.prodMk measurable_id)).abs).aestronglyMeasurable 1
                  (ae_of_all _ (fun ω => by simp [hkb]))).integrableOn
                  (integrableOn_const (by simp)) (fun ω => hkb _)
            _ ≤ 1 := by
                rw [setIntegral_const, smul_eq_mul, mul_one]
                exact measureReal_le_one))
    calc ∫ s in Set.Ioc (a:ℝ) (a + T), ∫ ω in B, k (s, ω) ∂P
        ≤ ∫ s in Set.Ioc (a:ℝ) (a + T), ∫ ω in B, v ω ∂P :=
          setIntegral_mono_on hsi (integrableOn_const (by simp)) measurableSet_Ioc hbd
      _ = T * ∫ ω in B, v ω ∂P := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hab, add_sub_cancel_left]
  have hZcond : P[Z | ℱ a] ≤ᵐ[P] fun ω => (T:ℝ) * (P[v | ℱ a]) ω := by
    have hint1 : Integrable (P[Z | ℱ a]) (P.trim hm) :=
      integrable_condExp.trim hm stronglyMeasurable_condExp
    have hsm2 : StronglyMeasurable[ℱ a] (fun ω => (T:ℝ) * (P[v | ℱ a]) ω) :=
      stronglyMeasurable_condExp.const_mul _
    have hint2 : Integrable (fun ω => (T:ℝ) * (P[v | ℱ a]) ω) (P.trim hm) :=
      (integrable_condExp.const_mul (T:ℝ)).trim hm hsm2
    refine ae_of_ae_trim hm (ae_le_of_forall_setIntegral_le hint1 hint2 (fun B hB _ => ?_))
    rw [← setIntegral_trim hm stronglyMeasurable_condExp hB, ← setIntegral_trim hm hsm2 hB,
      setIntegral_condExp hm hZi hB, integral_const_mul, setIntegral_condExp hm hvi hB]
    exact key B hB
  have hc : P[fun _ => ε * (T:ℝ) | ℱ a] = fun _ => ε * (T:ℝ) := condExp_const hm _
  have hup : P[D | ℱ a] ≤ᵐ[P] P[(fun _ => ε * (T:ℝ)) + Z | ℱ a] :=
    condExp_mono hDi ((integrable_const _).add hZi)
      (ae_of_all _ (fun ω => (le_abs_self _).trans (hDZ ω)))
  have hdn : P[-D | ℱ a] ≤ᵐ[P] P[(fun _ => ε * (T:ℝ)) + Z | ℱ a] :=
    condExp_mono hDi.neg ((integrable_const _).add hZi)
      (ae_of_all _ (fun ω => (neg_le_abs _).trans (hDZ ω)))
  have hadd := condExp_add (m := ℱ a) (μ := P) (integrable_const (ε * (T:ℝ))) hZi
  have hneg := condExp_neg (m := ℱ a) (μ := P) D
  filter_upwards [hup, hdn, hadd, hneg, hZcond] with ω h1 h2 h3 h4 h5
  rw [h3, hc] at h1 h2
  rw [h4] at h2
  simp only [Pi.add_apply, Pi.neg_apply] at h1 h2
  show |(P[D | ℱ a]) ω| ≤ _
  rw [abs_le]; constructor <;> linarith

theorem e51_core {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hfu : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun i : ℕ => (P[blockIntegral X f T (i + 1) - blockIntegral X (f ∘ Φ T) T i |
        ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω)
      atTop (𝓝 0) := by
  have hf : Continuous f := hfu.continuous
  have hTr : (0:ℝ) < T := hT
  have hδex : ∀ k : ℕ, ∃ δ > 0, ∀ a b, dist a b < δ → |f a - f b| ≤ 1 / ((k:ℝ) + 1) := by
    intro k
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 hfu (1 / ((k:ℝ) + 1)) (by positivity)
    exact ⟨δ, hδ, fun a b hab => by have := h hab; rw [Real.dist_eq] at this; exact this.le⟩
  choose δ hδpos hδ using hδex
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun k s =>
    P[(deviationEvent Φ X s (δ k) T).indicator (fun _ => (1:ℝ)) | ℱ s] with hYdef
  set Y' : ℕ → ℝ≥0 → Ω → ℝ≥0∞ := fun k s ω => ENNReal.ofReal (min (Y k s ω) 1) with hY'def
  have hY'm : ∀ k s, Measurable (Y' k s) := fun k s =>
    ENNReal.measurable_ofReal.comp
      ((stronglyMeasurable_condExp.mono (ℱ.le s)).measurable.min measurable_const)
  have hY'1 : ∀ k s ω, Y' k s ω ≤ 1 := fun k s ω => ENNReal.ofReal_le_one.2 (min_le_right _ _)
  have hex : ∀ k m : ℕ, ∃ σ : ℕ → {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s},
      ∀ i : {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s}, Y' k i.1 ≤ᵐ[P] fun ω => ⨆ n, Y' k (σ n).1 ω := by
    intro k m
    have : Nonempty {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s} := ⟨⟨(m:ℝ≥0) * T, le_rfl⟩⟩
    exact e51_exists_seq_ae_sup (ι := {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s}) P
      (fun i : {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s} => Y' k i.1)
      (fun i => hY'm k i.1) (fun i ω => hY'1 k i.1 ω)
  choose σ hσ using hex
  set v : ℕ → ℕ → Ω → ℝ := fun k m ω => (⨆ n, Y' k (σ k m n).1 ω).toReal with hvdef
  have hVle1 : ∀ k m ω, (⨆ n, Y' k (σ k m n).1 ω) ≤ 1 := fun k m ω =>
    iSup_le fun n => hY'1 _ _ _
  have hvm : ∀ k m, Measurable (v k m) := fun k m =>
    (Measurable.iSup fun n => hY'm k _).ennreal_toReal
  have hv01 : ∀ k m ω, 0 ≤ v k m ω ∧ v k m ω ≤ 1 := fun k m ω =>
    ⟨ENNReal.toReal_nonneg, by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (hVle1 k m ω); simpa using this⟩
  have hv1 : ∀ k m ω, |v k m ω| ≤ 1 := fun k m ω => by
    rw [abs_le]; constructor <;> linarith [hv01 k m ω]
  have hvS : ∀ (k m : ℕ) (s : ℝ≥0), (m:ℝ≥0) * T ≤ s → Y k s ≤ᵐ[P] v k m := by
    intro k m s hs
    have hb : ∀ᵐ ω ∂P, |(deviationEvent Φ X s (δ k) T).indicator (fun _ => (1:ℝ)) ω|
        ≤ ((1:ℝ≥0):ℝ) :=
      ae_of_all _ (fun ω => by
        simp only [Set.indicator]; split_ifs <;> norm_num)
    filter_upwards [hσ k m ⟨s, hs⟩, ae_bdd_condExp_of_ae_bdd (m := ℱ s) hb] with ω h1 h2
    have h2' : Y k s ω ≤ 1 := by have := (abs_le.1 h2).2; simpa using this
    have e : min (Y k s ω) 1 = Y k s ω := min_eq_left h2'
    calc Y k s ω ≤ (Y' k s ω).toReal := by
          simp only [hY'def, e]; rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
      _ ≤ v k m ω := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (hVle1 k m ω)) h1
  let G : Filtration ℕ m0 := ⟨fun n => ℱ ((n:ℝ≥0) * T),
    fun a b hab => ℱ.mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) zero_le), fun n => ℱ.le _⟩
  have hstep : ∀ k m j : ℕ, m ≤ j → ∀ᵐ ω ∂P,
      |(P[blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) |
        ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω|
        ≤ 1 / ((k:ℝ) + 1) * T + T * (P[v k m | G j]) ω := by
    intro k m j hj
    have heq : blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) =
        fun ω => ∫ s in (((j:ℝ≥0) * T : ℝ≥0):ℝ)..(((j:ℝ≥0) * T : ℝ≥0):ℝ) + T,
          (f (X (s + T).toNNReal ω) - f (Φ T (X s.toNNReal ω))) := by
      funext ω
      have hpath : Measurable (fun s : ℝ => X s.toNNReal ω) :=
        (hX.progMeasurable.measurable_path ω).comp measurable_real_toNNReal
      have hΦm : Measurable (fun x => Φ T x) :=
        (Φ.continuous continuous_const continuous_id).measurable
      have hi1 : ∀ c d, IntervalIntegrable (fun s : ℝ => f (X (s + T).toNNReal ω)) volume c d :=
        fun c d => e51_ii (hf.measurable.comp (hpath.comp (measurable_add_const _))) 1
          (fun s => by
            have := hf01 (X (s + T).toNNReal ω)
            simp only [Function.comp_apply]
            rw [abs_le]; constructor <;> linarith [this.1, this.2]) c d
      have hi2 : ∀ c d, IntervalIntegrable (fun s : ℝ => f (Φ T (X s.toNNReal ω))) volume c d :=
        fun c d => e51_ii (hf.measurable.comp (hΦm.comp hpath)) 1
          (fun s => by
            have := hf01 (Φ T (X s.toNNReal ω))
            simp only [Function.comp_apply]
            rw [abs_le]; constructor <;> linarith [this.1, this.2]) c d
      rw [intervalIntegral.integral_sub (hi1 _ _) (hi2 _ _),
        intervalIntegral.integral_comp_add_right (fun s => f (X s.toNNReal ω)) (T:ℝ)]
      have h0 : ((j:ℕ):ℝ) * T = (((j:ℝ≥0) * T : ℝ≥0):ℝ) := by push_cast; ring
      have h1 : ((j + 1 : ℕ) : ℝ) * T = (((j:ℝ≥0) * T : ℝ≥0):ℝ) + T := by push_cast; ring
      have h2 : ((j + 1 + 1 : ℕ) : ℝ) * T = (((j:ℝ≥0) * T : ℝ≥0):ℝ) + T + T := by push_cast; ring
      simp only [Pi.sub_apply, blockIntegral, Function.comp_apply, Nat.add_sub_cancel]
      rw [h0, h1, h2]
    have h := e51_step P ℱ Φ X hX f hf hf01 T hT (δ k) (1 / ((k:ℝ) + 1)) (hδpos k)
      (by positivity) (hδ k) (v k m) (hvm k m) (hv1 k m) ((m:ℝ≥0) * T) (hvS k m) ((j:ℝ≥0) * T)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) zero_le)
    rw [heq, show (j + 1 - 1 : ℕ) = j by omega]
    exact h
  have hlevy : ∀ k m, ∀ᵐ ω ∂P, Tendsto (fun n => (P[v k m | G n]) ω) atTop
      (𝓝 ((P[v k m | ⨆ n, G n]) ω)) := fun k m => tendsto_ae_condExp _
  have hinf : ∀ k, ∀ᵐ ω ∂P, ∀ ε > 0, ∃ m, (P[v k m | ⨆ n, G n]) ω < ε := by
    intro k
    set L : ℕ → Ω → ℝ := fun m => P[v k m | ⨆ n, G n] with hLdef
    have hGle : (⨆ n, G n) ≤ m0 := iSup_le fun n => G.le n
    have hLm : ∀ m, Measurable (L m) := fun m =>
      (stronglyMeasurable_condExp.mono hGle).measurable
    have hL01 : ∀ m, ∀ᵐ ω ∂P, 0 ≤ L m ω ∧ L m ω ≤ 1 := by
      intro m
      filter_upwards [condExp_nonneg (m := ⨆ n, G n) (μ := P) (f := v k m)
        (ae_of_all _ (fun ω => (hv01 k m ω).1)),
        ae_bdd_condExp_of_ae_bdd (m := ⨆ n, G n) (μ := P) (R := 1)
          (ae_of_all _ (fun ω => by simpa using hv1 k m ω))] with ω h1 h2
      exact ⟨h1, by have := (abs_le.1 h2).2; simpa using this⟩
    have hL01' := ae_all_iff.2 hL01
    set ℓ : Ω → ℝ := fun ω => ⨅ m, L m ω with hℓdef
    have hℓm : Measurable ℓ := Measurable.iInf hLm
    have hℓ01 : ∀ᵐ ω ∂P, 0 ≤ ℓ ω ∧ ℓ ω ≤ 1 ∧ ∀ m, ℓ ω ≤ L m ω := by
      filter_upwards [hL01'] with ω h
      have hbdd : BddBelow (Set.range fun m => L m ω) := ⟨0, by rintro _ ⟨m, rfl⟩; exact (h m).1⟩
      exact ⟨le_ciInf fun m => (h m).1, (ciInf_le hbdd 0).trans (h 0).2,
        fun m => ciInf_le hbdd m⟩
    have hℓi : Integrable ℓ P := Integrable.of_bound hℓm.aestronglyMeasurable 1 (by
      filter_upwards [hℓ01] with ω h
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2.1])
    have hgood := hX.tendsto_condProb (δ k) T (hδpos k) hT
    have hvto : ∀ᵐ ω ∂P, Tendsto (fun m => v k m ω) atTop (𝓝 0) := by
      filter_upwards [hgood] with ω hω
      rw [Metric.tendsto_atTop] at hω ⊢
      intro ε hε
      obtain ⟨t0, ht0⟩ := hω (ε / 2) (by positivity)
      obtain ⟨m1, hm1⟩ := exists_nat_ge (t0 / T)
      refine ⟨m1, fun m hm => ?_⟩
      have hle : ∀ s : ℝ≥0, (m:ℝ≥0) * T ≤ s → Y' k s ω ≤ ENNReal.ofReal (ε / 2) := by
        intro s hs
        have hts : t0 ≤ s := by
          have e1 : t0 ≤ (m1:ℝ≥0) * T := (div_le_iff₀ hT).1 hm1
          have e2 : (m1:ℝ≥0) * T ≤ (m:ℝ≥0) * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) zero_le
          exact e1.trans (e2.trans hs)
        have := ht0 s hts
        rw [Real.dist_eq, sub_zero] at this
        exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans ((le_abs_self _).trans this.le))
      have hV : (⨆ n, Y' k (σ k m n).1 ω) ≤ ENNReal.ofReal (ε / 2) :=
        iSup_le fun n => hle _ (σ k m n).2
      have hvle : v k m ω ≤ ε / 2 := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hV
        rwa [ENNReal.toReal_ofReal (by positivity)] at this
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hv01 k m ω).1]; linarith
    have hint_to : Tendsto (fun m => ∫ ω, v k m ω ∂P) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
        (fun m => (hvm k m).aestronglyMeasurable) (integrable_const 1)
        (fun m => ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hv1 k m ω)) hvto
      simpa using this
    have hℓint : ∫ ω, ℓ ω ∂P ≤ 0 := by
      refine ge_of_tendsto' hint_to (fun m => ?_)
      calc ∫ ω, ℓ ω ∂P ≤ ∫ ω, L m ω ∂P := integral_mono_ae hℓi integrable_condExp
            (by filter_upwards [hℓ01] with ω h; exact h.2.2 m)
        _ = ∫ ω, v k m ω ∂P := integral_condExp hGle
    have hnn : 0 ≤ᵐ[P] ℓ := by filter_upwards [hℓ01] with ω h; exact h.1
    have hℓ0 : ℓ =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hℓi).1
        (le_antisymm hℓint (integral_nonneg_of_ae hnn))
    filter_upwards [hℓ0, hL01'] with ω h0 h
    intro ε hε
    have : ℓ ω < ε := by rw [h0]; exact hε
    exact exists_lt_of_ciInf_lt this
  have hS : ∀ᵐ ω ∂P, ∀ k m j : ℕ, m ≤ j →
      |(P[blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) |
        ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω|
        ≤ 1 / ((k:ℝ) + 1) * T + T * (P[v k m | G j]) ω := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun m => ae_all_iff.2 fun j => ?_
    by_cases h : m ≤ j
    · filter_upwards [hstep k m j h] with ω hω _; exact hω
    · exact ae_of_all _ (fun ω h' => absurd h' h)
  filter_upwards [hS, ae_all_iff.2 fun k => ae_all_iff.2 fun m => hlevy k m,
    ae_all_iff.2 hinf] with ω hS hL hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / (3 * T) by positivity)
  obtain ⟨m, hm⟩ := hI k (ε / (3 * T)) (by positivity)
  have hev := (hL k m).eventually (gt_mem_nhds (show (P[v k m | ⨆ n, G n]) ω < 2 * (ε / (3 * T))
    by linarith [show 0 < ε / (3 * T) by positivity]))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max (m + 1) (N + 1), fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 := hS k m j (by omega)
  have h2 := hN j (by omega)
  rw [Real.dist_eq, sub_zero]
  have a1 : 1 / ((k:ℝ) + 1) * T < ε / 3 := by
    calc 1 / ((k:ℝ) + 1) * T < ε / (3 * T) * T := mul_lt_mul_of_pos_right hk hTr
      _ = ε / 3 := by field_simp
  have a2 : (T:ℝ) * (P[v k m | G j]) ω < 2 * ε / 3 := by
    calc (T:ℝ) * (P[v k m | G j]) ω < T * (2 * (ε / (3 * T))) := mul_lt_mul_of_pos_left h2 hTr
      _ = 2 * ε / 3 := by field_simp
  linarith

end StochApproxDyn.WeakAPT

open StochApproxDyn.WeakAPT
open MeasureTheory Filter Topology
open scoped NNReal

theorem solution
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hf : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun i : ℕ => (P[blockIntegral X f T (i + 1) - blockIntegral X (f ∘ Φ T) T i |
        ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω)
      atTop (𝓝 0) := by
  exact e51_core P ℱ Φ X hX f hf hf01 T hT
