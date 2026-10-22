-- Prove2me | solution 1 for SeqSocialLearning.Adequate.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T10:05:49.75618+00:00
-- url     : https://prove2.me/submissions/726e37df-a6ca-4b26-9a6e-3b768bde69e0

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals
import Theorems.Thm_SeqSocialLearning_Adequate_lemma_3

open MeasureTheory ProbabilityTheory Filter Topology

namespace SSLLem8Aux
open SeqSocialLearning.Adequate

variable {Ω A S : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace S]

lemma law0 (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) :
    (playMeasure μ F p).map (fun x => x 0) = initMeasure μ F p := by
  set e := MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => (fun _ : ℕ => Ω × S × A) i)
  have h1 : (fun x : ℕ → Ω × S × A => x 0) = e ∘ Preorder.frestrictLe 0 := by
    funext x
    rfl
  rw [h1, ← Measure.map_map e.measurable (Preorder.measurable_frestrictLe 0)]
  unfold playMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_map e.measurable e.symm.measurable]
  simp

lemma measurable_state : Measurable (state (Ω := Ω) (S := S) (A := A)) := by
  unfold state; fun_prop

lemma stateLaw (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) : (playMeasure μ F p).map state = μ := by
  have : (state : (ℕ → Ω × S × A) → Ω) = Prod.fst ∘ (fun x => x 0) := rfl
  rw [this, ← Measure.map_map measurable_fst (measurable_pi_apply 0), law0]
  unfold initMeasure
  exact Measure.fst_compProd _ _

end SSLLem8Aux

open SeqSocialLearning.Adequate SSLLem8Aux

theorem solution {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F)
    (u : A → Ω → ℝ) (hu : InU u) (M : ℝ) (hM : ∀ a ω, |u a ω| ≤ M)
    (p : Profile A S) (hp : IsPBE μ F u p) (r' : ℝ) (hr' : 0 < r')
    (h12 : ENNReal.ofReal r' < playMeasure μ F p
      {x | ∃ᶠ t in atTop, r' < maxPayoff u (state x) - u (action x t) (state x)}) :
    ∃ B : Set Ω, MeasurableSet B ∧ 0 < μ B ∧
      ∃ r : ℝ, 0 < r ∧
        ENNReal.ofReal r < (playMeasure μ F p)[|state ⁻¹' B]
          {x | ∃ᶠ t in atTop, r < ⨅ ω' : B, (maxPayoff u ω' - u (action x t) ω')} ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ ν : Measure Ω, IsProbabilityMeasure ν → 1 - δ ≤ ν.real B →
            ∀ aStar : A, (∀ b : A, ∫ ω, u b ω ∂ν ≤ ∫ ω, u aStar ω ∂ν) →
              ∀ ω ∈ B, |maxPayoff u ω - u aStar ω| ≤
                (r * (1 - 2 * δ) - 4 * δ * M) / (2 * (1 - δ)) := by
  classical
  have hu' := hu
  obtain ⟨hmeas, -, hcont⟩ := hu'
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary A) (Classical.arbitrary Ω))
  -- basic facts about `maxPayoff`
  have hbdd : ∀ ω, BddAbove (Set.range fun a => u a ω) := fun ω =>
    ⟨M, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (hM a ω)⟩
  have hle_max : ∀ a ω, u a ω ≤ maxPayoff u ω := fun a ω => le_ciSup (hbdd ω) a
  have hatt : ∀ ω, ∃ b, maxPayoff u ω = u b ω := by
    intro ω
    obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (hcont ω).continuousOn
    refine ⟨b, le_antisymm (ciSup_le fun a => hb (Set.mem_univ a)) (hle_max b ω)⟩
  -- constants
  set γ : ℝ := r' / 32 with hγ
  set r : ℝ := r' / 4 with hr
  set δ : ℝ := min (1 / 4) (r' / (64 * M + 4 * r' + 1)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδ2 : δ * (64 * M + 4 * r') ≤ r' := by
    have h1 : δ ≤ r' / (64 * M + 4 * r' + 1) := min_le_right _ _
    have h2 : 0 < 64 * M + 4 * r' + 1 := by positivity
    calc δ * (64 * M + 4 * r') ≤ r' / (64 * M + 4 * r' + 1) * (64 * M + 4 * r') := by
          gcongr
      _ ≤ r' / (64 * M + 4 * r' + 1) * (64 * M + 4 * r' + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = r' := by field_simp
  -- Lemma 3: a large compact set on which `u` is uniformly continuous
  obtain ⟨E, hEc, hEμ, η, β, hη, hβ, hEu⟩ :=
    lemma_3 μ u hu (r' / 2) γ (by positivity) (by positivity)
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  -- cut `E` into countably many small measurable pieces
  set d := TopologicalSpace.denseSeq Ω
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq Ω
  set f : ℕ → Set Ω := fun n => E ∩ Metric.ball (d n) (β / 2) with hf
  set Bs := disjointed f with hBs
  have hBsm : ∀ n, MeasurableSet (Bs n) :=
    MeasurableSet.disjointed fun n => hEm.inter Metric.isOpen_ball.measurableSet
  have hBsf : ∀ n, Bs n ⊆ f n := fun n => disjointed_le f n
  have hunion : (⋃ n, Bs n) = E := by
    rw [hBs, iUnion_disjointed]
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun n => Set.inter_subset_left
    · intro ω hω
      obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hd ω (β / 2) (by positivity)
      exact Set.mem_iUnion.2 ⟨n, hω, by rw [Metric.mem_ball]; exact hn⟩
  have hdisj : Pairwise (Function.onFun Disjoint Bs) := disjoint_disjointed f
  -- the play measure and the bad event
  set P := playMeasure μ F p with hP
  set Λ := {x : ℕ → Ω × S × A |
    ∃ᶠ t in atTop, r' < maxPayoff u (state x) - u (action x t) (state x)} with hΛ
  have hPstate : ∀ {B : Set Ω}, MeasurableSet B → P (state ⁻¹' B) = μ B := by
    intro B hB
    rw [← Measure.map_apply measurable_state hB, stateLaw]
  -- Claim 1
  have hEc' : μ Eᶜ ≤ ENNReal.ofReal (r' / 2) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    apply ENNReal.ofReal_le_ofReal
    have := probReal_compl_eq_one_sub (μ := μ) hEm
    rw [measureReal_def] at this
    rw [this]; linarith
  have hclaim1 : ENNReal.ofReal (r' / 2) < P (Λ ∩ state ⁻¹' E) := by
    by_contra hcon
    push Not at hcon
    have h1 : P Λ ≤ P (Λ ∩ state ⁻¹' E) + P (state ⁻¹' E)ᶜ :=
      (measure_le_inter_add_sdiff P Λ (state ⁻¹' E)).trans
        (add_le_add le_rfl (measure_mono fun x hx => hx.2))
    rw [← Set.preimage_compl, hPstate hEm.compl] at h1
    have : ENNReal.ofReal r' < ENNReal.ofReal (r' / 2) + ENNReal.ofReal (r' / 2) :=
      h12.trans_le (h1.trans (add_le_add hcon hEc'))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at this
    have h3 : r' / 2 + r' / 2 = r' := by ring
    rw [h3] at this
    exact lt_irrefl _ this
  -- Claim 2: pigeonhole
  obtain ⟨n, hn⟩ : ∃ n, ENNReal.ofReal (r' / 2) * μ (Bs n) < P (Λ ∩ state ⁻¹' Bs n) := by
    by_contra hcon
    push Not at hcon
    have h1 : P (Λ ∩ state ⁻¹' E) ≤ ENNReal.ofReal (r' / 2) := by
      calc P (Λ ∩ state ⁻¹' E) = P (⋃ n, Λ ∩ state ⁻¹' Bs n) := by
            rw [← Set.inter_iUnion, ← Set.preimage_iUnion, hunion]
        _ ≤ ∑' n, P (Λ ∩ state ⁻¹' Bs n) := measure_iUnion_le _
        _ ≤ ∑' n, ENNReal.ofReal (r' / 2) * μ (Bs n) := ENNReal.tsum_le_tsum hcon
        _ = ENNReal.ofReal (r' / 2) * μ E := by
            rw [ENNReal.tsum_mul_left, ← measure_iUnion hdisj hBsm, hunion]
        _ ≤ ENNReal.ofReal (r' / 2) * 1 := by gcongr; exact prob_le_one
        _ = ENNReal.ofReal (r' / 2) := mul_one _
    exact absurd hclaim1 (not_lt.2 h1)
  set B := Bs n with hB
  have hBm : MeasurableSet B := hBsm n
  have hBpos : 0 < μ B := by
    rw [pos_iff_ne_zero]
    intro h0
    have : P (Λ ∩ state ⁻¹' B) = 0 :=
      measure_mono_null Set.inter_subset_right (by rw [hPstate hBm]; exact h0)
    rw [this] at hn
    exact absurd hn (not_lt.2 zero_le)
  have hBE : B ⊆ E := fun ω hω => (hBsf n hω).1
  have hosc : ∀ ω ∈ B, ∀ ω' ∈ B, ∀ a, |u a ω - u a ω'| ≤ γ := by
    intro ω hω ω' hω' a
    refine hEu ω (hBE hω) ω' (hBE hω') a a ?_ (by simp [hη.le])
    have h1 := (hBsf n hω).2
    have h2 := (hBsf n hω').2
    rw [Metric.mem_ball] at h1 h2
    calc dist ω ω' ≤ dist ω (d n) + dist (d n) ω' := dist_triangle _ _ _
      _ ≤ β := by rw [dist_comm (d n)]; linarith
  have hOosc : ∀ ω ∈ B, ∀ ω' ∈ B, maxPayoff u ω ≤ maxPayoff u ω' + γ := by
    intro ω hω ω' hω'
    obtain ⟨b, hb⟩ := hatt ω
    have := hosc ω hω ω' hω' b
    rw [abs_le] at this
    rw [hb]
    linarith [hle_max b ω']
  refine ⟨B, hBm, hBpos, r, by positivity, ?_, δ, hδ0, ?_⟩
  · -- part 2
    have hsub : Λ ∩ state ⁻¹' B ⊆
        {x | ∃ᶠ t in atTop, r < ⨅ ω' : B, (maxPayoff u ω' - u (action x t) ω')} := by
      rintro x ⟨hx, hxB⟩
      have : Nonempty B := ⟨⟨state x, hxB⟩⟩
      refine Frequently.mono (show ∃ᶠ t in atTop,
        r' < maxPayoff u (state x) - u (action x t) (state x) from hx) fun t ht => ?_
      have hlow : maxPayoff u (state x) - u (action x t) (state x) - 2 * γ ≤
          ⨅ ω' : B, (maxPayoff u ω' - u (action x t) ω') := by
        refine le_ciInf fun ω' => ?_
        have h1 := hOosc (state x) hxB ω' ω'.2
        have h2 := hosc (state x) hxB ω' ω'.2 (action x t)
        rw [abs_le] at h2
        linarith
      have : r < maxPayoff u (state x) - u (action x t) (state x) - 2 * γ := by
        simp only [hr, hγ]; linarith
      exact this.trans_le hlow
    have hsB : MeasurableSet (state ⁻¹' B : Set (ℕ → Ω × S × A)) := measurable_state hBm
    rw [cond_apply hsB, hPstate hBm]
    have hμB0 : μ B ≠ 0 := hBpos.ne'
    have hμBtop : μ B ≠ ⊤ := measure_ne_top _ _
    calc ENNReal.ofReal r < ENNReal.ofReal (r' / 2) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by simp only [hr]; linarith)
      _ = (μ B)⁻¹ * (ENNReal.ofReal (r' / 2) * μ B) := by
          rw [mul_comm (ENNReal.ofReal _), ← mul_assoc, ENNReal.inv_mul_cancel hμB0 hμBtop,
            one_mul]
      _ < (μ B)⁻¹ * P (Λ ∩ state ⁻¹' B) :=
          ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 hμBtop) (ENNReal.inv_ne_top.2 hμB0) hn
      _ ≤ (μ B)⁻¹ * P (state ⁻¹' B ∩
          {x | ∃ᶠ t in atTop, r < ⨅ ω' : B, (maxPayoff u ω' - u (action x t) ω')}) := by
          refine mul_le_mul_right ?_ _
          refine measure_mono fun x hx => ?_
          exact ⟨hx.2, hsub hx⟩
  · -- part 3
    intro ν hν hνB aStar hbest ω hω
    obtain ⟨b, hb⟩ := hatt ω
    have hmeasa : ∀ a, Measurable fun x => u a x := fun a =>
      hmeas.comp (measurable_const.prodMk measurable_id)
    have hint : ∀ a, Integrable (fun x => u a x) ν := fun a =>
      Integrable.of_bound (hmeasa a).aestronglyMeasurable M
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM a x)
    set q := ν.real B with hq
    have hq1 : q ≤ 1 := measureReal_le_one
    have hqc : ν.real Bᶜ = 1 - q := probReal_compl_eq_one_sub hBm
    -- integral bounds
    have hA1 : ∫ x in B, u aStar x ∂ν ≤ q * (u aStar ω + γ) := by
      calc ∫ x in B, u aStar x ∂ν ≤ ∫ _x in B, (u aStar ω + γ) ∂ν := by
            refine setIntegral_mono_on (hint aStar).integrableOn (integrableOn_const) hBm
              fun x hx => ?_
            have := hosc ω hω x hx aStar
            rw [abs_le] at this; linarith
        _ = q * (u aStar ω + γ) := by rw [setIntegral_const, smul_eq_mul]
    have hB1 : q * (u b ω - γ) ≤ ∫ x in B, u b x ∂ν := by
      calc q * (u b ω - γ) = ∫ _x in B, (u b ω - γ) ∂ν := by
            rw [setIntegral_const, smul_eq_mul]
        _ ≤ ∫ x in B, u b x ∂ν := by
            refine setIntegral_mono_on (integrableOn_const) (hint b).integrableOn hBm
              fun x hx => ?_
            have := hosc ω hω x hx b
            rw [abs_le] at this; linarith
    have hA2 : ∫ x in Bᶜ, u aStar x ∂ν ≤ M * (1 - q) := by
      calc ∫ x in Bᶜ, u aStar x ∂ν ≤ ∫ _x in Bᶜ, M ∂ν :=
            setIntegral_mono (hint aStar).integrableOn integrableOn_const
              fun x => (le_abs_self _).trans (hM _ _)
        _ = M * (1 - q) := by rw [setIntegral_const, smul_eq_mul, hqc, mul_comm]
    have hB2 : -(M * (1 - q)) ≤ ∫ x in Bᶜ, u b x ∂ν := by
      calc -(M * (1 - q)) = ∫ _x in Bᶜ, -M ∂ν := by
            rw [setIntegral_const, smul_eq_mul, hqc]; ring
        _ ≤ ∫ x in Bᶜ, u b x ∂ν :=
            setIntegral_mono integrableOn_const (hint b).integrableOn
              fun x => by have := hM b x; rw [abs_le] at this; linarith
    have hsplitA := integral_add_compl hBm (hint aStar)
    have hsplitB := integral_add_compl hBm (hint b)
    have hbst := hbest b
    have hmain : q * (maxPayoff u ω - u aStar ω) ≤ 2 * q * γ + 2 * M * (1 - q) := by
      rw [hb]; nlinarith
    have hnonneg : 0 ≤ maxPayoff u ω - u aStar ω := sub_nonneg.2 (hle_max aStar ω)
    rw [abs_of_nonneg hnonneg, le_div_iff₀ (by linarith)]
    have hγ0 : 0 < γ := by positivity
    have h1 : (maxPayoff u ω - u aStar ω) * (1 - δ) ≤ 2 * γ + 2 * M * δ := by
      have e1 : (maxPayoff u ω - u aStar ω) * (1 - δ) ≤ q * (maxPayoff u ω - u aStar ω) := by
        nlinarith
      have e2 : 2 * q * γ ≤ 2 * γ := by nlinarith
      have e3 : 2 * M * (1 - q) ≤ 2 * M * δ := by nlinarith
      linarith
    have h2 : 4 * γ + 8 * M * δ ≤ r * (1 - 2 * δ) := by
      simp only [hr, hγ]; nlinarith
    nlinarith
