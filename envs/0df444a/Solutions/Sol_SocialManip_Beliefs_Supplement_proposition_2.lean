-- Prove2me | solution 1 for SocialManip.Beliefs.Supplement.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:05.182936+00:00
-- url     : https://prove2.me/submissions/5cf0d017-7c40-44b3-860b-76067ee5fe8e

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open MeasureTheory ProbabilityTheory Filter Topology Matrix

open SocialManip
open SocialManip.Beliefs
open SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

theorem solution {n : ℕ} (M : Model n) (hS : M.Standing) (hG : M.GameDomain)
    (adj : Fin n → Fin n → Prop) (hA : M.Assumption1 adj)
    (y yhat : State) (hyhat : yhat ≠ y) (x : Fin n → Bool) :
    (∀ i, centrality M.B M.θ M.α (influence M.B x) i ≠ ⊤) ∧
      (fun i => (centrality M.B M.θ M.α (influence M.B x) i).toReal) =
        (1 - W M.B M.α)⁻¹ *ᵥ (fun i => influence M.B x i * thetaVec M.B M.θ i) ∧
      ∀ᵐ ω ∂(sampleMeasure M y),
        Tendsto (fun T : ℝ => fun i =>
          if yhat = State.R then beliefR M y yhat x ω T i
          else 1 - beliefR M y yhat x ω T i) atTop
          (𝓝 fun i => (centrality M.B M.θ M.α (influence M.B x) i).toReal) := by
            classical
            obtain ⟨hp, hθ, hα, hsum⟩ := hS
            obtain ⟨hq0, hq1, hlam, hlamS, -, -, -⟩ := hG
            obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := hA
            have hpers0 : ∀ᵐ ω ∂(sampleMeasure M y), ∀ i, i ∉ M.B →
                Tendsto (fun T : ℝ => M.θ i * (if yhat = State.R then personalR M yhat x ω i T
                  else 1 - personalR M yhat x ω i T)) atTop
                  (𝓝 (influence M.B x i * thetaVec M.B M.θ i)) := by
              set f : ℝ → ℝ := fun z => if yhat = State.R then z else 1 - z with hf
              set c : Fin n → ℝ := fun i => influence M.B x i * thetaVec M.B M.θ i with hc
              show ∀ᵐ ω ∂(sampleMeasure M y), ∀ i, i ∉ M.B →
                Tendsto (fun T : ℝ => M.θ i * f (personalR M yhat x ω i T)) atTop (𝓝 (c i))
              have hgen : ∀ (ι X : Type) [MeasurableSpace X] (P : ι → Measure X)
                  [∀ i, IsProbabilityMeasure (P i)] (g : ℕ → ι) (_ : Function.Injective g)
                  (_ : ∀ k, P (g k) = P (g 0)) (φ : X → ℝ) (_ : Measurable φ)
                  (_ : Integrable φ (P (g 0))),
                  ∀ᵐ ω ∂(Measure.infinitePi P), Tendsto (fun m : ℕ =>
                    (∑ k ∈ Finset.range m, φ (ω (g k))) / m) atTop (𝓝 (∫ z, φ z ∂(P (g 0)))) := by
                intro ι X _ P _ g hg hP φ hφ hint
                have hind := iIndepFun_infinitePi (P := P) (X := fun _ => φ) (fun _ => hφ)
                have hmap : ∀ k, (Measure.infinitePi P).map (fun ω => φ (ω (g k))) = (P (g 0)).map φ := by
                  intro k
                  rw [← hP k, ← Measure.infinitePi_map_eval P (g k), Measure.map_map hφ (by fun_prop)]
                  rfl
                have hint0 : Integrable (fun ω : (i : ι) → X => φ (ω (g 0))) (Measure.infinitePi P) := by
                  have := (integrable_map_measure (f := fun ω : (i : ι) → X => ω (g 0)) (g := φ)
                    (by rw [Measure.infinitePi_map_eval P (g 0)]; exact hφ.aestronglyMeasurable)
                    (measurable_pi_apply (g 0)).aemeasurable).1
                  rw [Measure.infinitePi_map_eval P (g 0)] at this
                  exact this hint
                have h := strong_law_ae_real (μ := Measure.infinitePi P)
                  (fun k ω => φ (ω (g k))) hint0
                  (fun a b hab => hind.indepFun (hg.ne hab))
                  (fun k => ⟨(hφ.comp (measurable_pi_apply (g k))).aemeasurable,
                    (hφ.comp (measurable_pi_apply (g 0))).aemeasurable, by rw [hmap k, hmap 0]⟩)
                have hmean : ∫ ω, φ (ω (g 0)) ∂(Measure.infinitePi P) = ∫ z, φ z ∂(P (g 0)) := by
                  have := integral_map (μ := Measure.infinitePi P) (φ := fun ω : (i : ι) → X => ω (g 0)) (f := φ)
                    (measurable_pi_apply (g 0)).aemeasurable
                    (by rw [Measure.infinitePi_map_eval P (g 0)]; exact hφ.aestronglyMeasurable)
                  rw [Measure.infinitePi_map_eval P (g 0)] at this
                  exact this.symm
                rw [hmean] at h
                exact h
              have hexp_nn : ∀ᵐ x ∂(expMeasure 1), 0 ≤ x := by
                rw [ae_iff]
                simp only [not_le]
                show gammaMeasure 1 1 (Set.Iio 0) = 0
                rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
                exact lintegral_gammaPDF_of_nonpos le_rfl
              have hexp_int : Integrable (fun x : ℝ => x) (expMeasure 1) := by
                show Integrable (fun x : ℝ => x) (volume.withDensity (gammaPDF 1 1))
                rw [MeasureTheory.integrable_withDensity_iff_integrable_smul' (f := gammaPDF 1 1) (measurable_gammaPDFReal 1 1).ennreal_ofReal
                  (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
                have h2 := Real.GammaIntegral_convergent (s := 2) (by norm_num)
                have h3 : (fun x : ℝ => (gammaPDF 1 1 x).toReal • x) =
                    Set.indicator (Set.Ioi 0) (fun x : ℝ => Real.exp (-x) * x ^ ((2:ℝ) - 1)) := by
                  funext x
                  simp only [gammaPDF, gammaPDFReal, smul_eq_mul, Set.indicator_apply, Set.mem_Ioi]
                  rcases lt_trichotomy x 0 with h | h | h
                  · simp [not_le.2 h, not_lt.2 h.le]
                  · simp [h]
                  · rw [if_pos h.le, if_pos h, ENNReal.toReal_ofReal (by positivity)]
                    norm_num
                rw [h3]
                exact h2.integrable_indicator measurableSet_Ioi
              have hexp_pos : 0 < ∫ x, x ∂(expMeasure 1) := by
                rw [integral_pos_iff_support_of_nonneg_ae hexp_nn hexp_int]
                have hsupp : Function.support (fun x : ℝ => x) = {0}ᶜ := by
                  ext x; simp
                rw [hsupp]
                have h0 : expMeasure 1 {0} = 0 := by
                  show gammaMeasure 1 1 {0} = 0
                  rw [gammaMeasure]
                  exact withDensity_absolutelyContinuous _ _ (by simp)
                have := isProbabilityMeasure_expMeasure (r := 1) one_pos
                rw [prob_compl_eq_one_sub (measurableSet_singleton 0), h0]
                simp
              have hrenew : ∀ (e : ℕ → ℝ) (μ r ρ : ℝ) (φ : ℕ → Prop) [DecidablePred φ], 0 < μ → 0 < r →
                  Tendsto (fun m : ℕ => (∑ l ∈ Finset.range m, e l) / m) atTop (𝓝 μ) →
                  Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, if φ k then (1:ℝ) else 0) / K) atTop (𝓝 ρ) →
                  Tendsto (fun t : ℝ => ({k : ℕ | (∑ l ∈ Finset.range (k + 1), e l) / r ≤ t ∧ φ k}.ncard : ℝ)
                    / t) atTop (𝓝 (r * ρ / μ)) := by
                intro e μ r ρ φ _ hμ hr hS hC
                set C : ℕ → ℝ := fun K => ∑ k ∈ Finset.range K, if φ k then (1:ℝ) else 0 with hCdef
                have hCcard : ∀ K, C K = (((Finset.range K).filter φ).card : ℝ) := by
                  intro K; simp [hCdef, Finset.sum_boole]
                have hρ : 0 ≤ ρ := ge_of_tendsto' hC fun K => div_nonneg
                  (Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num) (Nat.cast_nonneg _)
                have hCcomp : ∀ (g : ℝ → ℕ) (c : ℝ), Tendsto g atTop atTop →
                    Tendsto (fun t => (g t : ℝ) / t) atTop (𝓝 c) →
                    Tendsto (fun t => C (g t) / t) atTop (𝓝 (ρ * c)) := by
                  intro g c hg hgc
                  refine ((hC.comp hg).mul hgc).congr fun t => ?_
                  simp only [Function.comp]
                  rcases Nat.eq_zero_or_pos (g t) with h | h
                  · simp [h, hCdef]
                  · have : (g t : ℝ) ≠ 0 := by positivity
                    field_simp
                    rfl
                set Sx : ℝ → Set ℕ := fun t => {k : ℕ | (∑ l ∈ Finset.range (k + 1), e l) / r ≤ t ∧ φ k}
                  with hSx
                have hup : ∀ ε, 0 < ε → ε < μ → ∃ M' : ℕ, ∀ t, Sx t ⊆
                    ↑((Finset.range (M' + ⌊(r / (μ - ε)) * t⌋₊ + 1)).filter φ) := by
                  intro ε hε hεμ
                  obtain ⟨M', hM'⟩ := eventually_atTop.1 (hS.eventually (lt_mem_nhds (show μ - ε < μ by linarith)))
                  refine ⟨M', fun t k hk => ?_⟩
                  obtain ⟨hk1, hk2⟩ := hk
                  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
                  refine ⟨?_, hk2⟩
                  by_cases hkM : M' ≤ k + 1
                  · have h1 := hM' (k+1) hkM
                    have hpos : (0:ℝ) < (k+1 : ℕ) := by positivity
                    rw [lt_div_iff₀ hpos] at h1
                    rw [div_le_iff₀ hr] at hk1
                    have h2 : ((k + 1 : ℕ) : ℝ) ≤ (r / (μ - ε)) * t := by
                      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; push_cast at h1 ⊢; linarith only [h1, hk1]
                    have h3 := Nat.le_floor h2
                    omega
                  · omega
                have hfin : ∀ t, (Sx t).Finite := by
                  obtain ⟨M', hM'⟩ := hup (μ/2) (by linarith) (by linarith)
                  exact fun t => (Finset.finite_toSet _).subset (hM' t)
                rw [tendsto_order]
                constructor
                · intro a ha
                  have hcont : Tendsto (fun ε => r * ρ / (μ + ε)) (𝓝[>] 0) (𝓝 (r * ρ / μ)) := by
                    apply tendsto_nhdsWithin_of_tendsto_nhds
                    have : ContinuousAt (fun ε => r * ρ / (μ + ε)) 0 :=
                      continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simp; linarith)
                    simpa using this.tendsto
                  obtain ⟨ε, hε1, hε2⟩ := ((hcont.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
                  change 0 < ε at hε2
                  obtain ⟨M, hM⟩ := eventually_atTop.1 (hS.eventually (gt_mem_nhds (show μ < μ + ε by linarith)))
                  set g : ℝ → ℕ := fun t => ⌊(r / (μ + ε)) * t⌋₊ with hg
                  have hgt : Tendsto (fun t => (g t : ℝ) / t) atTop (𝓝 (r / (μ + ε))) :=
                    tendsto_nat_floor_mul_div_atTop (by positivity)
                  have hgtop : Tendsto g atTop atTop :=
                    tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
                  have hlow := (hCcomp g _ hgtop hgt).sub ((tendsto_const_nhds (x := (M:ℝ))).div_atTop tendsto_id)
                  have hlim : a < ρ * (r / (μ + ε)) - 0 := by
                    have h' : a < r * ρ / (μ + ε) := hε1
                    rw [sub_zero]; linarith [show ρ * (r/(μ+ε)) = r*ρ/(μ+ε) by ring]
                  filter_upwards [hlow.eventually (lt_mem_nhds hlim), eventually_gt_atTop (0:ℝ)] with t ht htpos
                  refine lt_of_lt_of_le ht ?_
                  simp only [id, ← sub_div]
                  apply div_le_div_of_nonneg_right _ htpos.le
                  have hsub : ↑((Finset.range (g t)).filter φ \ Finset.range M) ⊆ Sx t := by
                    intro k hk
                    simp only [Finset.coe_sdiff, Finset.coe_filter, Finset.mem_range, Set.mem_diff,
                      Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio, not_lt] at hk
                    obtain ⟨⟨hk1, hk2⟩, hk3⟩ := hk
                    refine ⟨?_, hk2⟩
                    have h1 := hM (k+1) (by omega)
                    have hpos : (0:ℝ) < (k+1 : ℕ) := by positivity
                    rw [div_lt_iff₀ hpos] at h1
                    rw [div_le_iff₀ hr]
                    have h2 : ((k + 1 : ℕ) : ℝ) ≤ (r / (μ + ε)) * t := by
                      have := Nat.floor_le (show 0 ≤ (r / (μ + ε)) * t by positivity)
                      have h4 : k + 1 ≤ g t := hk1
                      exact le_trans (by exact_mod_cast h4) this
                    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at h2
                    push_cast at h1 h2; linarith only [h1, h2]
                  have h5 := Set.ncard_le_ncard hsub (hfin t)
                  rw [Set.ncard_coe_finset] at h5
                  have h6 := Finset.le_card_sdiff (Finset.range M) ((Finset.range (g t)).filter φ)
                  rw [Finset.card_range] at h6
                  rw [hCcard]
                  have : (((Finset.range (g t)).filter φ).card : ℝ) ≤ (Sx t).ncard + M := by
                    exact_mod_cast (by omega : ((Finset.range (g t)).filter φ).card ≤ (Sx t).ncard + M)
                  linarith
                · intro b hb
                  have hcont : Tendsto (fun ε => r * ρ / (μ - ε)) (𝓝[>] 0) (𝓝 (r * ρ / μ)) := by
                    apply tendsto_nhdsWithin_of_tendsto_nhds
                    have : ContinuousAt (fun ε => r * ρ / (μ - ε)) 0 :=
                      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simp; linarith)
                    simpa using this.tendsto
                  obtain ⟨ε, ⟨hε1, hε3⟩, hε2⟩ := (((hcont.eventually (gt_mem_nhds hb)).and
                    (Ioo_mem_nhdsGT hμ))).and self_mem_nhdsWithin |>.exists
                  change 0 < ε at hε2
                  change 0 < ε ∧ ε < μ at hε3
                  obtain ⟨M', hM'⟩ := hup ε hε2 hε3.2
                  set g : ℝ → ℕ := fun t => M' + ⌊(r / (μ - ε)) * t⌋₊ + 1 with hg
                  have hgt : Tendsto (fun t => (g t : ℝ) / t) atTop (𝓝 (0 + r / (μ - ε))) := by
                    have h1 := (tendsto_const_nhds (x := ((M' + 1 : ℕ) : ℝ))).div_atTop tendsto_id
                    have h2 : Tendsto (fun t : ℝ => (⌊(r / (μ - ε)) * t⌋₊ : ℝ) / t) atTop (𝓝 (r / (μ - ε))) :=
                      tendsto_nat_floor_mul_div_atTop (by have := hε3.2; positivity)
                    refine (h1.add h2).congr fun t => ?_
                    simp only [hg, id]; push_cast; ring
                  rw [zero_add] at hgt
                  have hgtop : Tendsto g atTop atTop := by
                    refine tendsto_atTop_mono (fun t => ?_) (tendsto_nat_floor_atTop.comp
                      (tendsto_id.const_mul_atTop (show 0 < r / (μ - ε) by have := hε3.2; positivity)))
                    simp only [hg, Function.comp, id]; omega
                  have hlim : ρ * (r / (μ - ε)) < b := by
                    have h' : r * ρ / (μ - ε) < b := hε1
                    linarith [show ρ * (r/(μ-ε)) = r*ρ/(μ-ε) by ring]
                  filter_upwards [(hCcomp g _ hgtop hgt).eventually (gt_mem_nhds hlim),
                    eventually_gt_atTop (0:ℝ)] with t ht htpos
                  refine lt_of_le_of_lt ?_ ht
                  apply div_le_div_of_nonneg_right _ htpos.le
                  have h5 := Set.ncard_le_ncard (hM' t) (Finset.finite_toSet _)
                  rw [Set.ncard_coe_finset] at h5
                  rw [hCcard]; exact_mod_cast h5
              have hmarks0 : ∀ j : Fin n, ∀ s : State, ∀ᵐ ω1 ∂(Measure.infinitePi fun k : Fin n × ℕ =>
                  bernoulliMeasure State.S State.R (clampProb (organicProbS (M.p k.1) y))),
                  Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, (if ω1 (j, k) = s then (1:ℝ) else 0)) / K)
                    atTop (𝓝 (if s = y then M.p j else 1 - M.p j)) := by
                intro j s
                have h := hgen (Fin n × ℕ) State (fun k : Fin n × ℕ =>
                  bernoulliMeasure State.S State.R (clampProb (organicProbS (M.p k.1) y))) (fun k => (j, k))
                  (fun a b h => by simpa using h) (fun k => rfl) (fun z => if z = s then (1:ℝ) else 0)
                  (measurable_of_finite _) (Integrable.of_finite)
                have hmean : ∫ z, (if z = s then (1:ℝ) else 0) ∂(bernoulliMeasure State.S State.R
                    (clampProb (organicProbS (M.p j) y))) = if s = y then M.p j else 1 - M.p j := by
                  have e1 : (fun z : State => if z = s then (1:ℝ) else 0) = Set.indicator {s} 1 := by
                    funext z; simp [Set.indicator_apply]
                  rw [e1, integral_indicator_one (measurableSet_singleton s)]
                  have hpj := hp j
                  have hcl : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → ((clampProb z : unitInterval) : ℝ) = z := by
                    intro z h0 h1; unfold clampProb; rw [Set.projIcc_of_mem _ ⟨h0, h1⟩]
                  cases s <;> cases y <;>
                    simp [bernoulliMeasure_real_apply, organicProbS, unitInterval.coe_symm_eq] <;>
                    rw [hcl] <;> linarith
                rw [hmean] at h
                exact h
              have hmarks : ∀ᵐ ω ∂(sampleMeasure M y), ∀ j s, Tendsto (fun K : ℕ =>
                  (∑ k ∈ Finset.range K, (if ω.1 (j, k) = s then (1:ℝ) else 0)) / K) atTop
                    (𝓝 (if s = y then M.p j else 1 - M.p j)) := by
                have := ae_all_iff.2 fun j => ae_all_iff.2 fun s => hmarks0 j s
                unfold sampleMeasure
                exact Measure.quasiMeasurePreserving_fst.ae this
              set μe : ℝ := ∫ x, x ∂(expMeasure 1) with hμe
              have hclk0 : ∀ᵐ e : ℕ → ℝ ∂(Measure.infinitePi fun _ : ℕ => expMeasure 1),
                  Tendsto (fun m : ℕ => (∑ l ∈ Finset.range m, e l) / (m:ℝ)) atTop (𝓝 μe) :=
                hgen ℕ ℝ (fun _ => expMeasure 1) id Function.injective_id (fun _ => rfl) id measurable_id
                  hexp_int
              have hclk : ∀ᵐ ω ∂(sampleMeasure M y),
                  Tendsto (fun m : ℕ => (∑ l ∈ Finset.range m, ω.2.1 l) / (m:ℝ)) atTop (𝓝 μe) ∧
                  Tendsto (fun m : ℕ => (∑ l ∈ Finset.range m, ω.2.2 l) / (m:ℝ)) atTop (𝓝 μe) := by
                unfold sampleMeasure
                have h2 := (Measure.quasiMeasurePreserving_fst.ae hclk0).and
                  (Measure.quasiMeasurePreserving_snd.ae hclk0)
                exact Measure.quasiMeasurePreserving_snd.ae h2
              filter_upwards [hmarks, hclk] with ω hmk hck
              intro i hi
              have hci : c i = (if x i then 1 else 0) * M.θ i := by simp [hc, influence, thetaVec, hi]
              rcases (hθ i hi).eq_or_lt with h0 | hθpos
              · rw [hci, ← h0]; simp
              have hp2 : 1/2 < M.p i := (hA4 i hi).1 hθpos
              obtain ⟨hp1, hp3⟩ := hp i
              set ρ := (1 - M.p i) / M.p i with hρ
              have hρ0 : 0 < ρ := div_pos (by linarith) (by linarith)
              have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by linarith)]; linarith
              have hO : ∀ s : State, Tendsto (fun t : ℝ =>
                  ({k : ℕ | arrivalTime ω.2.1 M.lam k ≤ t ∧ ω.1 (i, k) = s}.ncard : ℝ) / t) atTop
                  (𝓝 (M.lam * (if s = y then M.p i else 1 - M.p i) / μe)) :=
                fun s => hrenew ω.2.1 μe M.lam _ (fun k => ω.1 (i, k) = s) hexp_pos hlam hck.1 (hmk i s)
              have hP : Tendsto (fun t : ℝ => ({k : ℕ | arrivalTime ω.2.2 M.lamStar k ≤ t}.ncard : ℝ) / t)
                  atTop (𝓝 (M.lamStar * 1 / μe)) := by
                have h1 : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K,
                    if (fun _ : ℕ => True) k then (1:ℝ) else 0) / K) atTop (𝓝 1) := by
                  refine tendsto_const_nhds.congr' ?_
                  filter_upwards [eventually_gt_atTop 0] with K hK
                  have : (K:ℝ) ≠ 0 := by positivity
                  simp [this]
                have := hrenew ω.2.2 μe M.lamStar 1 (fun _ => True) hexp_pos hlamS hck.2 h1
                simpa [arrivalTime] using this
              set D : ℝ → ℝ := fun t => (countAt M yhat x ω i t yhat : ℝ) - countAt M yhat x ω i t y
                with hD
              set L : ℝ := M.lam * (1 - M.p i) / μe + (if x i then M.lamStar * 1 / μe else 0)
                - M.lam * M.p i / μe with hL
              have hDt : Tendsto (fun t => D t / t) atTop (𝓝 L) := by
                have e1 : ∀ t, D t / t =
                    ({k | arrivalTime ω.2.1 M.lam k ≤ t ∧ ω.1 (i, k) = yhat}.ncard : ℝ) / t
                    + (if x i then ({k : ℕ | arrivalTime ω.2.2 M.lamStar k ≤ t}.ncard : ℝ) / t else 0)
                    - ({k | arrivalTime ω.2.1 M.lam k ≤ t ∧ ω.1 (i, k) = y}.ncard : ℝ) / t := by
                  intro t
                  simp only [hD, countAt]
                  by_cases hxi : x i = true
                  · simp [hxi, hyhat, Ne.symm hyhat]; ring
                  · simp [hxi]; ring
                have hOy := hO y
                have hOh := hO yhat
                simp only [if_pos rfl, if_neg hyhat] at hOy hOh
                refine Tendsto.congr (fun t => (e1 t).symm) ((hOh.add ?_).sub hOy)
                split_ifs
                · exact hP
                · exact tendsto_const_nhds
              have hpost : ∀ (a b : ℕ) (w w' : ℝ), 0 < w → 0 < w' →
                  M.p i ^ a * (1 - M.p i) ^ b * w / (M.p i ^ a * (1 - M.p i) ^ b * w +
                    M.p i ^ b * (1 - M.p i) ^ a * w') = 1 / (1 + ρ ^ ((a:ℝ) - b) * (w' / w)) := by
                intro a b w w' hw hw'
                rw [Real.rpow_sub hρ0, Real.rpow_natCast, Real.rpow_natCast, hρ, div_pow, div_pow]
                have : 0 < M.p i := by linarith
                have : 0 < 1 - M.p i := by linarith
                field_simp
              set κ : ℝ := if yhat = State.S then (1 - M.q) / M.q else M.q / (1 - M.q) with hκdef
              have hκ : 0 < κ := by
                rw [hκdef]; split_ifs
                exacts [div_pos (sub_pos.2 hq1) hq0, div_pos hq0 (sub_pos.2 hq1)]
              have hfpost : ∀ t, f (personalR M yhat x ω i t) = 1 / (1 + ρ ^ (D t) * κ) := by
                intro t
                have hpi : 0 < M.p i := by linarith
                have hpi' : 0 < 1 - M.p i := by linarith
                simp only [hf, personalR, BUS, hD, hκdef]
                cases yhat <;> cases y <;> simp at hyhat ⊢
                · rw [← one_div]; exact hpost _ _ _ _ hq0 (by linarith)
                · rw [← one_div, ← hpost _ _ _ _ (by linarith) hq0]
                  have hA : 0 < M.p i ^ countAt M State.R x ω i t State.S *
                    (1 - M.p i) ^ countAt M State.R x ω i t State.R * M.q := by positivity
                  have hB : 0 < M.p i ^ countAt M State.R x ω i t State.R *
                    (1 - M.p i) ^ countAt M State.R x ω i t State.S * (1 - M.q) := by
                    have : 0 < 1 - M.q := by linarith
                    positivity
                  field_simp
                  ring
              rw [hci]
              simp_rw [hfpost]
              by_cases hx : x i = true
              · have hLpos : 0 < L := by
                  rw [hL, if_pos hx]
                  have h1 := hA1 i
                  rw [lt_div_iff₀ (by linarith)] at h1
                  rw [← sub_pos] at h1
                  have : M.lam * (1 - M.p i) / μe + M.lamStar * 1 / μe - M.lam * M.p i / μe =
                    (M.lamStar + M.lam - M.p i * (2 * M.lam)) / μe := by ring
                  rw [this]; exact div_pos h1 hexp_pos
                have hDtop : Tendsto D atTop atTop := by
                  refine (Tendsto.pos_mul_atTop hLpos hDt tendsto_id).congr' ?_
                  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
                  simp only [id]; field_simp
                have h1 := (tendsto_rpow_atTop_of_base_lt_one ρ (by linarith) hρ1).comp hDtop
                have h2 := ((tendsto_const_nhds (x := (1:ℝ))).div
                  (tendsto_const_nhds.add (h1.mul_const κ)) (by norm_num : (1:ℝ) + 0 * κ ≠ 0)).const_mul (M.θ i)
                simp only [hx, if_true]
                rw [show (1:ℝ) * M.θ i = M.θ i * (1 / (1 + 0 * κ)) by ring]
                exact h2
              · have hLneg : L < 0 := by
                  rw [hL, if_neg hx]
                  have : M.lam * (1 - M.p i) / μe + 0 - M.lam * M.p i / μe =
                    (M.lam * (1 - 2 * M.p i)) / μe := by ring
                  rw [this]
                  apply div_neg_of_neg_of_pos _ hexp_pos
                  apply mul_neg_of_pos_of_neg hlam; linarith
                have hDbot : Tendsto D atTop atBot := by
                  refine (Tendsto.neg_mul_atTop hLneg hDt tendsto_id).congr' ?_
                  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
                  simp only [id]; field_simp
                have h1 := (tendsto_rpow_atBot_of_base_lt_one ρ hρ0 hρ1).comp hDbot
                have h3 : Tendsto (fun t => 1 + ρ ^ (D t) * κ) atTop atTop :=
                  tendsto_atTop_add_const_left _ 1 (h1.atTop_mul_const hκ)
                have h2 := ((tendsto_const_nhds (x := (1:ℝ))).div_atTop h3).const_mul (M.θ i)
                rw [Bool.not_eq_true] at hx
                rw [hx, if_neg Bool.false_ne_true, show (0:ℝ) * M.θ i = M.θ i * 0 by ring]
                exact h2
            set Wm := W M.B M.α with hWm
            have hWnn : ∀ i j, 0 ≤ Wm i j := by
              intro i j
              simp only [hWm, W, Matrix.of_apply]
              split_ifs with h
              · exact le_rfl
              · exact hα i h j
            have hWrow : ∀ i, ∑ j, Wm i j ≤ 1 := by
              intro i
              simp only [hWm, W, Matrix.of_apply]
              split_ifs with h
              · simp
              · linarith [hsum i h, hθ i h]
            have hWleak : ∀ i, (i ∈ M.B ∨ 0 < M.θ i) → ∑ j, Wm i j < 1 := by
              intro i hi
              simp only [hWm, W, Matrix.of_apply]
              split_ifs with h
              · simp
              · rcases hi with hi | hi
                · exact absurd hi h
                · linarith [hsum i h]
            -- r k i = row sum of W^k
            set r : ℕ → Fin n → ℝ := fun k i => ∑ j, (Wm ^ k) i j with hr
            have hpownn : ∀ k i j, 0 ≤ (Wm ^ k) i j := fun k i j => Matrix.pow_apply_nonneg hWnn k i j
            have hrsucc : ∀ k i, r (k+1) i = ∑ l, Wm i l * r k l := by
              intro k i
              simp only [hr, pow_succ', Matrix.mul_apply, Finset.mul_sum]
              rw [Finset.sum_comm]
            have hrsucc' : ∀ k i, r (k+1) i = ∑ l, (Wm ^ k) i l * r 1 l := by
              intro k i
              show ∑ j, (Wm^(k+1)) i j = ∑ l, (Wm^k) i l * ∑ j, (Wm^1) l j
              rw [pow_succ, pow_one]
              simp only [Matrix.mul_apply, Finset.mul_sum]
              rw [Finset.sum_comm]
            have hrle : ∀ k i, r k i ≤ 1 := by
              intro k
              induction k with
              | zero => intro i; simp [hr, Matrix.one_apply]
              | succ k ih =>
                intro i
                rw [hrsucc]
                calc ∑ l, Wm i l * r k l ≤ ∑ l, Wm i l := Finset.sum_le_sum fun l _ =>
                        mul_le_of_le_one_right (hWnn i l) (ih l)
                  _ ≤ 1 := hWrow i
            have hrnn : ∀ k i, 0 ≤ r k i := fun k i => Finset.sum_nonneg fun j _ => hpownn k i j
            have hrmono : ∀ k i, r (k+1) i ≤ r k i := by
              intro k i
              rw [hrsucc']
              calc ∑ l, (Wm ^ k) i l * r 1 l ≤ ∑ l, (Wm ^ k) i l := Finset.sum_le_sum fun l _ =>
                      mul_le_of_le_one_right (hpownn k i l) (hrle 1 l)
                _ = r k i := rfl
            have hrmono' : ∀ k d i, r (k + d) i ≤ r k i := by
              intro k d
              induction d with
              | zero => intro i; simp
              | succ d ih => intro i; exact (hrmono (k+d) i).trans (ih i)
            have hleak1 : ∀ i, (i ∈ M.B ∨ 0 < M.θ i) → r 1 i < 1 := by
              intro i hi; simpa [hr] using hWleak i hi
            have hstep : ∀ k i j, i ∉ M.B → 0 < M.α i j → r k j < 1 → r (k+1) i < 1 := by
              intro k i j hi hij hj
              rw [hrsucc]
              calc ∑ l, Wm i l * r k l < ∑ l, Wm i l := by
                      apply Finset.sum_lt_sum
                      · intro l _; exact mul_le_of_le_one_right (hWnn i l) (hrle k l)
                      · refine ⟨j, Finset.mem_univ _, ?_⟩
                        have : Wm i j = M.α i j := by simp [hWm, W, hi]
                        rw [this]; exact mul_lt_of_lt_one_right hij hj
                _ ≤ 1 := hWrow i
            have hreach : ∀ i, ∃ k, r k i < 1 := by
              obtain ⟨l, hl⟩ : ∃ l, l ∈ M.B ∨ 0 < M.θ l := by
                by_cases hB : M.B.Nonempty
                · obtain ⟨b, hb⟩ := hB; exact ⟨b, Or.inl hb⟩
                · obtain ⟨i0, hi0⟩ := hA5
                  have hi0B : i0 ∉ M.B := fun h => hB ⟨i0, h⟩
                  exact ⟨i0, Or.inr ((hA4 i0 hi0B).2 hi0)⟩
              have hl1 : r 1 l < 1 := hleak1 l hl
              have key : ∀ a, Relation.TransGen adj a l → ∃ k, r k a < 1 := by
                intro a h
                induction h using Relation.TransGen.head_induction_on with
                | @single a hab =>
                  by_cases ha : a ∈ M.B
                  · exact ⟨1, hleak1 a (Or.inl ha)⟩
                  · exact ⟨2, hstep 1 a l ha ((hA2 a ha l).1 hab) hl1⟩
                | @head a b hab _ ih =>
                  by_cases ha : a ∈ M.B
                  · exact ⟨1, hleak1 a (Or.inl ha)⟩
                  · obtain ⟨k, hk⟩ := ih
                    exact ⟨k+1, hstep k a b ha ((hA2 a ha b).1 hab) hk⟩
              intro i
              by_cases hil : i = l
              · exact ⟨1, hil ▸ hl1⟩
              exact key i (hA3 i l hil)
            have hcontr : ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ i, r m i ≤ ρ := by
              choose kk hkk using hreach
              set m := ∑ i, kk i
              have hm : ∀ i, r m i < 1 := by
                intro i
                have hle : kk i ≤ m := Finset.single_le_sum (fun j _ => Nat.zero_le (kk j)) (Finset.mem_univ i)
                have := hrmono' (kk i) (m - kk i) i
                rw [Nat.add_sub_cancel' hle] at this
                exact lt_of_le_of_lt this (hkk i)
              by_cases hn : Nonempty (Fin n)
              · obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => r m i) Finset.univ_nonempty
                refine ⟨m, max (1/2) (r m i0), by positivity, max_lt (by norm_num) (hm i0), fun i => ?_⟩
                exact (hi0 i (Finset.mem_univ i)).trans (le_max_right _ _)
              · exact ⟨m, 1/2, by norm_num, by norm_num, fun i => (hn ⟨i⟩).elim⟩
            have hrsplit : ∀ a b i, r (a + b) i = ∑ l, (Wm ^ a) i l * r b l := by
              intro a b i
              simp only [hr, pow_add, Matrix.mul_apply, Finset.mul_sum]
              rw [Finset.sum_comm]
            obtain ⟨m0, ρ, hρ0, hρ1, hm0⟩ := hcontr
            set m := m0 + 1 with hmdef
            have hm : ∀ i, r m i ≤ ρ := fun i => (hrmono m0 i).trans (hm0 i)
            have hmpos : 0 < m := Nat.succ_pos _
            have hrq : ∀ q s i, r (m * q + s) i ≤ ρ ^ q := by
              intro q s
              induction q with
              | zero => intro i; simpa using hrle s i
              | succ q ih =>
                intro i
                have : m * (q+1) + s = m + (m * q + s) := by ring
                rw [this, hrsplit]
                calc ∑ l, (Wm ^ m) i l * r (m * q + s) l ≤ ∑ l, (Wm ^ m) i l * ρ ^ q :=
                      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (ih l) (hpownn m i l)
                  _ = r m i * ρ ^ q := by rw [← Finset.sum_mul]
                  _ ≤ ρ * ρ ^ q := mul_le_mul_of_nonneg_right (hm i) (by positivity)
                  _ = ρ ^ (q+1) := by ring
            set t : ℝ := ρ ^ ((1:ℝ) / m) with ht
            have ht0 : 0 ≤ t := by positivity
            have ht1 : t < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
            have htm : t ^ m = ρ := by
              rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
              field_simp
              simp
            have hrk : ∀ k i, r k i ≤ t ^ k / ρ := by
              intro k i
              have h1 := hrq (k / m) (k % m) i
              rw [Nat.div_add_mod] at h1
              rw [le_div_iff₀ hρ0]
              have h2 : t ^ k = ρ ^ (k / m) * t ^ (k % m) := by
                conv_lhs => rw [← Nat.div_add_mod k m]
                rw [pow_add, pow_mul, htm]
              have h3 : t ^ m ≤ t ^ (k % m) := pow_le_pow_of_le_one ht0 ht1.le (Nat.mod_lt k hmpos).le
              rw [htm] at h3
              rw [h2]
              calc r k i * ρ ≤ ρ ^ (k / m) * ρ := mul_le_mul_of_nonneg_right h1 hρ0.le
                _ ≤ ρ ^ (k / m) * t ^ (k % m) := mul_le_mul_of_nonneg_left h3 (by positivity)
            have hentry : ∀ k i j, (Wm ^ k) i j ≤ t ^ k / ρ := by
              intro k i j
              refine le_trans ?_ (hrk k i)
              exact Finset.single_le_sum (fun l _ => hpownn k i l) (Finset.mem_univ j)
            have hsumm : ∀ i j, Summable (fun k => (Wm ^ k) i j) := by
              intro i j
              exact Summable.of_nonneg_of_le (fun k => hpownn k i j) (fun k => hentry k i j)
                ((summable_geometric_of_lt_one ht0 ht1).div_const ρ)
            set N : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => ∑' k, (Wm ^ k) i j with hN
            have hNnn : ∀ i j, 0 ≤ N i j := fun i j => tsum_nonneg fun k => hpownn k i j
            have hNeq : (1 - Wm) * N = 1 := by
              ext i j
              rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply]
              have e1 : ∑ l, Wm i l * N l j = ∑' k, (Wm ^ (k+1)) i j := by
                simp only [hN, Matrix.of_apply]
                simp_rw [← tsum_mul_left]
                rw [← Summable.tsum_finsetSum (fun l _ => (hsumm l j).mul_left _)]
                congr 1; ext k
                rw [pow_succ', Matrix.mul_apply]
              rw [e1]
              have e2 : N i j = (Wm ^ 0) i j + ∑' k, (Wm ^ (k+1)) i j := (hsumm i j).tsum_eq_zero_add
              rw [e2]; simp
            have hNinv : (1 - Wm)⁻¹ = N := Matrix.inv_eq_right_inv hNeq
            have hpath : ∀ ℓ i j, (Wm ^ ℓ) i j = ∑ v : Fin (ℓ+1) → Fin n,
                if v 0 = i ∧ v (Fin.last ℓ) = j then ∏ k : Fin ℓ, Wm (v k.castSucc) (v k.succ) else 0 := by
              intro ℓ
              induction ℓ with
              | zero =>
                intro i j
                rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)).symm _ _ (fun _ => rfl)]
                rcases eq_or_ne i j with rfl | h
                · simp [Matrix.one_apply]
                · simp [h]
                  rw [eq_comm, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                  rintro a - ⟨rfl, rfl⟩; exact h rfl
              | succ ℓ ih =>
                intro i j
                rw [pow_succ', Matrix.mul_apply]
                simp_rw [ih]
                rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin n) _ _ (fun _ => rfl)]
                rw [Fintype.sum_prod_type]
                simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.prod_univ_succ, Finset.mul_sum]
                simp only [← Fin.succ_last, Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc]
                rw [Finset.sum_comm]
                simp only [ite_and, mul_ite, mul_zero]
                simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                rw [Fintype.sum_eq_single i (fun b hb => by simp [hb])]
                simp
            have hwalk : ∀ ℓ i j, j ∉ M.B → (∑ v ∈ (Finset.univ.filter fun v : Fin (ℓ + 1) → Fin n =>
                v 0 = i ∧ v (Fin.last ℓ) = j ∧ IsAvoidingWalk M.B M.α ℓ v),
                ENNReal.ofReal (walkWeight M.α ℓ v)) = ENNReal.ofReal ((Wm ^ ℓ) i j) := by
              intro ℓ i j hj
              rw [hpath, ENNReal.ofReal_sum_of_nonneg (fun v _ => by
                split_ifs
                · exact Finset.prod_nonneg fun k _ => hWnn _ _
                · exact le_rfl), Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro v _
              by_cases h0 : v 0 = i ∧ v (Fin.last ℓ) = j
              · rw [if_pos h0]
                by_cases hav : IsAvoidingWalk M.B M.α ℓ v
                · rw [if_pos ⟨h0.1, h0.2, hav⟩]
                  congr 1
                  unfold walkWeight
                  apply Finset.prod_congr rfl
                  intro k _
                  simp [hWm, W, hav.1 k.castSucc]
                · rw [if_neg (by tauto)]
                  symm
                  rw [ENNReal.ofReal_eq_zero]
                  apply le_of_eq
                  apply Finset.prod_eq_zero_iff.2
                  unfold IsAvoidingWalk at hav
                  push_neg at hav
                  by_cases hB : ∀ k, v k ∉ M.B
                  · obtain ⟨k, hk⟩ := hav hB
                    refine ⟨k, Finset.mem_univ _, ?_⟩
                    have := hα _ (hB k.castSucc) (v k.succ)
                    simp only [hWm, W, Matrix.of_apply, if_neg (hB k.castSucc)]
                    linarith
                  · push_neg at hB
                    obtain ⟨k, hk⟩ := hB
                    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
                    · exact ⟨k', Finset.mem_univ _, by simp [hWm, W, hk]⟩
                    · exact absurd (h0.2 ▸ hk) hj
              · rw [if_neg h0, if_neg (by tauto), ENNReal.ofReal_zero]
            set c : Fin n → ℝ := fun i => influence M.B x i * thetaVec M.B M.θ i with hc
            have hcnn : ∀ j, 0 ≤ c j := by
              intro j
              simp only [hc, influence, thetaVec]
              by_cases h1 : j ∈ M.B
              · simp [h1]
              · have := hθ j h1
                split_ifs <;> simp [this]
            have hcent : ∀ i, centrality M.B M.θ M.α (influence M.B x) i = ENNReal.ofReal ((N *ᵥ c) i) := by
              intro i
              unfold centrality
              rw [Matrix.mulVec, dotProduct, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hNnn i j) (hcnn j))]
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : j ∈ M.B
              · have : c j = 0 := by simp [hc, influence, hj]
                simp [this, influence, hj]
              · have hcj : M.θ j * influence M.B x j = c j := by simp [hc, thetaVec, hj, mul_comm]
                rw [hcj]
                unfold avoidingWalkSum
                simp_rw [hwalk _ i j hj]
                rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hpownn k i j) (hsumm i j),
                  ← ENNReal.ofReal_mul (hcnn j), mul_comm]
                rfl
            have hfin : ∀ i, centrality M.B M.θ M.α (influence M.B x) i ≠ ⊤ := fun i => by
              rw [hcent]; exact ENNReal.ofReal_ne_top
            have hvec : (fun i => (centrality M.B M.θ M.α (influence M.B x) i).toReal) = N *ᵥ c := by
              funext i
              rw [hcent, ENNReal.toReal_ofReal]
              show 0 ≤ ∑ j, N i j * c j
              exact Finset.sum_nonneg fun j _ => mul_nonneg (hNnn i j) (hcnn j)
            refine ⟨hfin, ?_, ?_⟩
            · rw [hvec, hNinv]
            rw [hvec]
            set f : ℝ → ℝ := fun z => if yhat = State.R then z else 1 - z with hf
            have hpers : ∀ᵐ ω ∂(sampleMeasure M y), ∀ i, i ∉ M.B →
                Tendsto (fun T : ℝ => M.θ i * f (personalR M yhat x ω i T)) atTop (𝓝 (c i)) := hpers0
            have hfB : f (truth y State.R) = 0 := by
              rw [hf]
              cases y <;> cases yhat <;> simp [truth] at hyhat ⊢
            have hflin : ∀ i, i ∉ M.B → ∀ (P : ℝ) (g : Fin n → ℝ),
                f (M.θ i * P + ∑ j, M.α i j * g j) = M.θ i * f P + ∑ j, Wm i j * f (g j) := by
              intro i hi P g
              have hs := hsum i hi
              simp only [hWm, W, Matrix.of_apply, if_neg hi, hf]
              split_ifs
              · rfl
              · simp only [mul_sub, Finset.sum_sub_distrib, mul_one]
                linarith
            filter_upwards [hpers] with ω hω
            set a : ℝ → Fin n → ℝ := fun T i => if i ∈ M.B then 0 else M.θ i * f (personalR M yhat x ω i T)
              with ha
            have haT : Tendsto a atTop (𝓝 c) := by
              rw [tendsto_pi_nhds]
              intro i
              by_cases hi : i ∈ M.B
              · have : c i = 0 := by simp [hc, influence, hi]
                simp only [ha, if_pos hi, this]; exact tendsto_const_nhds
              · simp only [ha, if_neg hi]; exact hω i hi
            set u : ℕ → Fin n → ℝ := fun k i => f (gridBeliefR M y yhat x ω k i) with hu
            have hurec : ∀ k, u (k+1) = a ((k+1 : ℕ) : ℝ) + Wm *ᵥ u k := by
              intro k; funext i
              simp only [hu, ha, gridBeliefR, Pi.add_apply]
              by_cases hi : i ∈ M.B
              · simp [hi, hfB, Matrix.mulVec, dotProduct, hWm, W]
              · rw [if_neg hi, if_neg hi, hflin i hi]; rfl
            have hbel : ∀ T : ℝ, 0 < T → (fun i => f (beliefR M y yhat x ω T i)) =
                a T + Wm *ᵥ u (⌈T⌉₊ - 1) := by
              intro T hT; funext i
              simp only [beliefR, ha, hu, Pi.add_apply]
              by_cases hi : i ∈ M.B
              · simp [hi, hfB, Matrix.mulVec, dotProduct, hWm, W]
              · rw [if_neg hi, if_neg hi, if_neg (not_le.2 hT), hflin i hi]; rfl
            have hfix : N *ᵥ c = c + Wm *ᵥ (N *ᵥ c) := by
              have : N = 1 + Wm * N := by
                have h := hNeq; rw [Matrix.sub_mul, Matrix.one_mul] at h
                exact sub_eq_iff_eq_add.1 h
              conv_lhs => rw [this]
              rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
            have hu_lim : Tendsto u atTop (𝓝 (N *ᵥ c)) := by
              set w : Fin n → ℝ := N *ᵥ (fun _ => 1) with hw
              have hw1 : ∀ i, (Wm *ᵥ w) i = w i - 1 := by
                intro i
                have h := congrArg (fun A => (A *ᵥ (fun _ : Fin n => (1:ℝ))) i) hNeq
                simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, Matrix.one_mulVec,
                  Pi.sub_apply, ← Matrix.mulVec_mulVec] at h
                rw [hw]; linarith
              have hwnn' : ∀ j, 0 ≤ w j := fun j => by
                show 0 ≤ ∑ l, N j l * 1
                exact Finset.sum_nonneg fun l _ => mul_nonneg (hNnn j l) zero_le_one
              have hwnn : ∀ i, 0 ≤ (Wm *ᵥ w) i := fun i => by
                show 0 ≤ ∑ j, Wm i j * w j
                exact Finset.sum_nonneg fun j _ => mul_nonneg (hWnn i j) (hwnn' j)
              have hwge : ∀ i, 1 ≤ w i := fun i => by linarith only [hw1 i, hwnn i]
              obtain ⟨Wx, hWx1, hWx⟩ : ∃ Wx : ℝ, 1 ≤ Wx ∧ ∀ i, w i ≤ Wx :=
                ⟨1 + ∑ i, w i, by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
                  (zero_le_one.trans (hwge i))], fun i => by
                    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => zero_le_one.trans (hwge j))
                      (Finset.mem_univ i)
                    linarith⟩
              set β : ℝ := 1 - 1 / Wx with hβ
              have hβ0 : 0 ≤ β := by rw [hβ, sub_nonneg]; exact div_le_one_of_le₀ hWx1 (by linarith)
              have hβ1 : β < 1 := by rw [hβ]; have : 0 < 1 / Wx := by positivity
                                     linarith
              set e : ℕ → Fin n → ℝ := fun k => u k - N *ᵥ c with he
              have herec : ∀ k i, e (k+1) i = (Wm *ᵥ e k) i + (a ((k+1:ℕ):ℝ) i - c i) := by
                intro k i
                simp only [he, hurec, Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub]
                have := congrFun hfix i
                simp only [Pi.add_apply] at this
                linarith
              have hδ : Tendsto (fun k : ℕ => a ((k+1:ℕ):ℝ)) atTop (𝓝 c) :=
                haT.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
              rw [Metric.tendsto_atTop] at hδ
              rw [tendsto_pi_nhds]
              intro i0
              rw [Metric.tendsto_atTop]
              intro ε hε
              set η : ℝ := ε / (3 * Wx) with hη
              have hη0 : 0 < η := by positivity
              obtain ⟨K, hK⟩ := hδ η hη0
              have hK' : ∀ k ≥ K, ∀ i, |a ((k+1:ℕ):ℝ) i - c i| < η := by
                intro k hk i
                have := hK k hk
                have h := dist_le_pi_dist (a ((k+1:ℕ):ℝ)) c i
                rw [Real.dist_eq] at h
                exact lt_of_le_of_lt h this
              set S0 : ℝ := 1 + ∑ i, |e K i| with hS0
              have hS0pos : 0 < S0 := by positivity
              have hind : ∀ j i, |e (K + j) i| ≤ (η + β ^ j * S0) * w i := by
                intro j
                induction j with
                | zero =>
                  intro i
                  have h1 : |e K i| ≤ S0 := by
                    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (e K j))
                      (Finset.mem_univ i)
                    linarith
                  simp only [add_zero, pow_zero, one_mul]
                  have e1 := mul_le_mul_of_nonneg_left (hwge i)
                    (show 0 ≤ η + S0 by linarith only [hη0, hS0pos])
                  linarith only [e1, h1, hη0]
                | succ j ih =>
                  intro i
                  rw [← add_assoc, herec]
                  have hdel := hK' (K + j) (Nat.le_add_right _ _) i
                  have hmv : |(Wm *ᵥ e (K + j)) i| ≤ (η + β ^ j * S0) * (w i - 1) := by
                    rw [← hw1 i]
                    calc |(Wm *ᵥ e (K + j)) i| ≤ ∑ l, Wm i l * |e (K+j) l| := by
                            show |∑ l, Wm i l * e (K+j) l| ≤ _
                            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
                            apply Finset.sum_congr rfl; intro l _
                            rw [abs_mul, abs_of_nonneg (hWnn i l)]
                      _ ≤ ∑ l, Wm i l * ((η + β ^ j * S0) * w l) :=
                            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (ih l) (hWnn i l)
                      _ = (η + β ^ j * S0) * (Wm *ᵥ w) i := by
                            simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
                            apply Finset.sum_congr rfl; intro l _; ring
                  have hbj : 0 ≤ β ^ j * S0 := by positivity
                  have hwi := hWx i
                  have hq : w i * (1 - β) ≤ 1 := by
                    rw [hβ, sub_sub_cancel, mul_one_div, div_le_one (by linarith)]; exact hwi
                  have hq2 := mul_le_mul_of_nonneg_left hq hbj
                  have hpw : β ^ (j+1) = β ^ j * β := pow_succ _ _
                  calc |(Wm *ᵥ e (K + j)) i + (a ((K + j + 1 : ℕ) : ℝ) i - c i)|
                      ≤ |(Wm *ᵥ e (K + j)) i| + |a ((K + j + 1 : ℕ) : ℝ) i - c i| := abs_add_le _ _
                    _ ≤ (η + β ^ j * S0) * (w i - 1) + η := by
                        have : |a ((K + j + 1 : ℕ) : ℝ) i - c i| < η := by simpa using hdel
                        linarith only [this, hmv]
                    _ ≤ (η + β ^ (j+1) * S0) * w i := by rw [hpw]; linarith only [hq2]
              obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show 0 < η / S0 by positivity) hβ1
              refine ⟨K + J, fun k hk => ?_⟩
              obtain ⟨j, rfl⟩ : ∃ j, k = K + j := ⟨k - K, by omega⟩
              have h1 := hind j i0
              have hjJ : β ^ j ≤ β ^ J := pow_le_pow_of_le_one hβ0 hβ1.le (by omega)
              have h2 : β ^ j * S0 < η := by
                exact (lt_div_iff₀ hS0pos).1 (lt_of_le_of_lt hjJ hJ)
              rw [Real.dist_eq]
              have h3 : (η + β ^ j * S0) * w i0 ≤ 2 * η * Wx := by
                have e1 := mul_le_mul_of_nonneg_right (show η + β ^ j * S0 ≤ 2 * η by linarith only [h2])
                  (show 0 ≤ w i0 by linarith only [hwge i0])
                have e2 := mul_le_mul_of_nonneg_left (hWx i0) (show 0 ≤ 2 * η by linarith only [hη0])
                exact e1.trans e2
              have h4 : 2 * η * Wx < ε := by
                have hWx0 : 0 < Wx := by linarith only [hWx1]
                rw [hη, mul_assoc, div_mul_eq_mul_div, mul_div_mul_right _ _ hWx0.ne']
                linarith only [hε]
              show |e (K + j) i0| < ε
              linarith only [h1, h3, h4]
            have hidx : Tendsto (fun T : ℝ => ⌈T⌉₊ - 1) atTop atTop :=
              (tendsto_sub_atTop_nat 1).comp tendsto_nat_ceil_atTop
            have hcont : Continuous (fun v : Fin n → ℝ => Wm *ᵥ v) := by fun_prop
            have hlim2 : Tendsto (fun T : ℝ => a T + Wm *ᵥ u (⌈T⌉₊ - 1)) atTop
                (𝓝 (c + Wm *ᵥ (N *ᵥ c))) :=
              haT.add ((hcont.tendsto _).comp (hu_lim.comp hidx))
            rw [← hfix] at hlim2
            refine hlim2.congr' ?_
            filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
            rw [← hbel T hT]
