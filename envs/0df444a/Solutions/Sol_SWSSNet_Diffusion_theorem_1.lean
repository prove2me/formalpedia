-- Prove2me | solution 1 for SWSSNet.Diffusion.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:48:21.827528+00:00
-- url     : https://prove2.me/submissions/2fe10669-9961-455b-a131-014dff53832f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network
import Definitions.Def_SWSSNet_Diffusion_Process
import Theorems.Thm_SWSSNet_Diffusion_theorem_5
import Theorems.Thm_SWSSNet_Diffusion_theorem_7_58
import Theorems.Thm_SWSSNet_Diffusion_eq_dieker_gao
import Theorems.Thm_SWSSNet_Diffusion_remark_1
import Theorems.Thm_SWSSNet_Diffusion_remark_8

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSThm1Aux

open SWSSNet.Diffusion

/-- Shifting a strong solution by a constant vector `c`, when the drifts are related by
`b₂(y + c) = b₁(y)`. -/
theorem strong_shift {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
    (b₁ b₂ : EthierKurtz.SDEState d → EthierKurtz.SDEState d) (σ : Matrix (Fin d) (Fin d) ℝ)
    (c : EthierKurtz.SDEState d) (hb : ∀ y, b₂ (y + c) = b₁ y)
    (B X : ℝ≥0 → Ω → EthierKurtz.SDEState d) (x : EthierKurtz.SDEState d)
    (hX : UnifErgHW.Diffusion.IsStrongSolution Pr b₁ σ B X x) :
    UnifErgHW.Diffusion.IsStrongSolution Pr b₂ σ B (fun t ω => X t ω + c) (x + c) := by
  obtain ⟨⟨hcont, heq⟩, hmeas, hF⟩ := hX
  refine ⟨⟨fun ω => (hcont ω).add continuous_const, fun ω t => ?_⟩, fun t => (hmeas t).add_const c,
    fun t => ?_⟩
  · have hfun : (fun s : ℝ => b₂ (X (Real.toNNReal s) ω + c)) =
        fun s : ℝ => b₁ (X (Real.toNNReal s) ω) := funext fun s => hb _
    simp only [hfun]
    rw [heq ω t]
    abel
  · obtain ⟨F, hFm, hFae⟩ := hF t
    refine ⟨fun w => F w + c, hFm.add_const c, ?_⟩
    filter_upwards [hFae] with ω hω
    rw [hω]

/-- Pushing a bind through a measurable equivalence. -/
theorem bind_map_equiv {α : Type*} [MeasurableSpace α] (e : α ≃ᵐ α) (μ : Measure α)
    (P : α → Measure α) :
    (μ.map e).bind (fun x => (P (e.symm x)).map e) = (μ.bind P).map e := by
  unfold Measure.bind
  have hcomp : ((fun x => (P (e.symm x)).map e) ∘ e) = (Measure.map e) ∘ P := by
    funext x; simp
  have hmap : Measure.map (fun x => (P (e.symm x)).map e) (μ.map e) =
      Measure.map ((Measure.map e) ∘ P) μ := by
    by_cases hg : AEMeasurable (fun x => (P (e.symm x)).map e) (μ.map e)
    · rw [AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable, hcomp]
    · rw [Measure.map_of_not_aemeasurable hg]
      have : ¬ AEMeasurable ((fun x => (P (e.symm x)).map e) ∘ e) μ := by
        rwa [← e.measurableEmbedding.aemeasurable_map_iff]
      rw [hcomp] at this
      rw [Measure.map_of_not_aemeasurable this]
  rw [hmap]
  by_cases hP : AEMeasurable P μ
  · rw [← AEMeasurable.map_map_of_aemeasurable (Measure.measurable_map _ e.measurable).aemeasurable hP,
      Measure.join_map_map e.measurable]
  · have h1 : ¬ AEMeasurable ((Measure.map e) ∘ P) μ := by
      intro h
      apply hP
      have h2 : AEMeasurable ((Measure.map e.symm) ∘ ((Measure.map e) ∘ P)) μ :=
        (Measure.measurable_map _ e.symm.measurable).comp_aemeasurable h
      have h3 : ((Measure.map e.symm) ∘ ((Measure.map e) ∘ P)) = P := by
        funext x; simp [MeasurableEquiv.map_symm_map]
      rwa [h3] at h2
    rw [Measure.map_of_not_aemeasurable h1, Measure.map_of_not_aemeasurable hP]
    simp

/-- Invariance of the weighted total variation norm under a common translation. -/
theorem tvNormWeighted_shift {d : ℕ} (W : EthierKurtz.SDEState d → ℝ) (c : EthierKurtz.SDEState d)
    (μ₁ μ₂ : Measure (EthierKurtz.SDEState d)) :
    GPhNGIDiffusion.EMError.tvNormWeighted (fun y => W (y - c))
        (μ₁.map (MeasurableEquiv.addRight c)) (μ₂.map (MeasurableEquiv.addRight c)) =
      GPhNGIDiffusion.EMError.tvNormWeighted W μ₁ μ₂ := by
  set e := MeasurableEquiv.addRight c with he
  have hlin : ∀ μ : Measure (EthierKurtz.SDEState d),
      (∫⁻ x, ENNReal.ofReal (1 + W (x - c)) ∂(μ.map e)) = ∫⁻ x, ENNReal.ofReal (1 + W x) ∂μ := by
    intro μ
    rw [lintegral_map_equiv]
    simp [he]
  have hint : ∀ (μ : Measure (EthierKurtz.SDEState d)) (ϕ : EthierKurtz.SDEState d → ℝ),
      ∫ x, ϕ x ∂(μ.map e) = ∫ x, ϕ (x + c) ∂μ := by
    intro μ ϕ
    rw [integral_map_equiv]
    simp [he]
  unfold GPhNGIDiffusion.EMError.tvNormWeighted
  rw [hlin, hlin]
  split_ifs with h
  · apply le_antisymm
    · refine iSup₂_le fun ϕ hϕ => ?_
      rw [hint, hint]
      refine le_iSup₂_of_le (fun y => ϕ (y + c)) ⟨hϕ.1.comp (measurable_add_const c), fun y => ?_⟩ le_rfl
      have := hϕ.2 (y + c)
      simpa using this
    · refine iSup₂_le fun ψ hψ => ?_
      refine le_iSup₂_of_le (fun y => ψ (y - c)) ⟨hψ.1.comp (measurable_sub_const c), fun y => hψ.2 _⟩ ?_
      rw [hint, hint]
      simp
  · rfl

end SWSSThm1Aux

open SWSSNet.Diffusion SWSSThm1Aux

theorem solution {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    (0 < swss N p → ∀ (î : Fin I) (ĵ : Fin J), N.adj î ĵ →
      HasStrongSolutions (markovDrift N (hvec N) (fun _ => constCtrl î ĵ)) (Sigma N) ∧
      ∃ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (hvec N) (fun _ => constCtrl î ĵ)) (Sigma N) P ∧
        ∃ π : Measure (EthierKurtz.SDEState I), GPhNGIDiffusion.EMError.IsInvariantMeasure P π ∧
          (∀ π', GPhNGIDiffusion.EMError.IsInvariantMeasure P π' → π' = π) ∧
          ∃ (c : EthierKurtz.SDEState I) (S : Matrix (Fin I) (Fin I) ℝ) (ε : ℝ), S.PosDef ∧ 0 < ε ∧
            (∫⁻ y, ENNReal.ofReal (lyapVS ε S (y - c)) ∂π) < ⊤ ∧
            ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState I),
              GPhNGIDiffusion.EMError.tvNormWeighted (fun y => lyapVS ε S (y - c)) (P t x) π
                ≤ ENNReal.ofReal (C * lyapVS ε S (x - c) * Real.exp (-γ * t))) ∧
    (swss N p < 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      IsTransient (markovDrift N (hvec N) v) (Sigma N)) ∧
    (swss N p = 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      ∀ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (hvec N) v) (Sigma N) P →
        ¬ ∃ π, GPhNGIDiffusion.EMError.IsInvariantMeasure P π) := by
  refine ⟨?_, (theorem_5 N p hp).1, (theorem_5 N p hp).2⟩
  intro hpos î ĵ hedge
  -- Dieker–Gao matrix `S`
  obtain ⟨S, κ, hS, hκ, hSB, hΦ⟩ := eq_dieker_gao N î ĵ hedge
  -- a positive probability vector `p'` with `⟨p', S e_î⟩ > 0`
  set s : Fin I → ℝ := S *ᵥ Pi.single î 1 with hs
  have hsî : s î = S î î := by simp [hs]
  have hSii : 0 < S î î := hS.diag_pos
  have hIpos : (0 : ℝ) < I := by
    have : 0 < I := Fin.pos î
    exact_mod_cast this
  set M : ℝ := ∑ k, |s k| + 1 with hM
  have hMpos : 0 < M := by
    have : 0 ≤ ∑ k, |s k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  set δ : ℝ := S î î / (2 * (S î î + M)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]
    linarith
  set p' : Fin I → ℝ := fun i => (1 - δ) * (if i = î then 1 else 0) + δ / I with hp'def
  have hp' : IsPosProb p' := by
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : 0 ≤ (1 - δ) * (if i = î then (1 : ℝ) else 0) := by
        apply mul_nonneg (by linarith); split_ifs <;> norm_num
      have h2 : 0 < δ / I := by positivity
      simp only [hp'def]; linarith
    · simp only [hp'def, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
      ring
  have hη' : 0 < p' ⬝ᵥ s := by
    have hexp : p' ⬝ᵥ s = (1 - δ) * s î + δ / I * ∑ k, s k := by
      simp only [dotProduct, hp'def, add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum]
      congr 1
      · congr 1
        simp [ite_mul]
    rw [hexp, hsî]
    have habs : |∑ k, s k| ≤ ∑ k, |s k| := Finset.abs_sum_le_sum_abs _ _
    have hdivle : δ / I ≤ δ := by
      rw [div_le_iff₀ hIpos]
      have : (1 : ℝ) ≤ I := by
        have : 1 ≤ I := Fin.pos î
        exact_mod_cast this
      nlinarith
    have hlow : -(δ * M) ≤ δ / I * ∑ k, s k := by
      have h1 : |δ / I * ∑ k, s k| ≤ δ * M := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < δ / I)]
        calc δ / I * |∑ k, s k| ≤ δ * |∑ k, s k| :=
              mul_le_mul_of_nonneg_right hdivle (abs_nonneg _)
          _ ≤ δ * M := mul_le_mul_of_nonneg_left (by linarith) hδpos.le
      linarith [neg_abs_le (δ / I * ∑ k, s k)]
    have hkey : δ * (S î î + M) = S î î / 2 := by
      rw [hδ]; field_simp
    nlinarith
  -- `ϑ_{p'} > 0` by Remark 1
  have hpos' : 0 < swss N p' := by
    have h1 := remark_1 N p p' hp hp'
    rw [sign_pos hpos] at h1
    exact sign_eq_one_iff.mp h1.symm
  have hη : 0 < swss N p' * (p' ⬝ᵥ (S *ᵥ Pi.single î 1)) := mul_pos hpos' hη'
  -- Theorem 7 (58) for the recentred diffusion
  obtain ⟨ε, hε, -, -, hstrong, P, hP, π, hπ, huniq, γ, C, hγ, hC, hbound⟩ :=
    theorem_7_58 N p' hp' hpos' î ĵ hedge S κ hS hκ hSB hΦ hη
  -- Remark 8: recentring
  have h8 := remark_8 N ĵ p' hp'
  obtain ⟨-, hdrift, -⟩ := h8
  set ζ : EthierKurtz.SDEState I := WithLp.toLp 2 ((B1 N ĵ)⁻¹ *ᵥ (hvec N + swss N p' • p'))
    with hζ
  set bt := markovDrift N (-(swss N p') • p') (fun _ => constCtrl î ĵ) with hbt
  set b := markovDrift N (hvec N) (fun _ => constCtrl î ĵ) with hb
  have hctrl : IsControlValue (constCtrl î ĵ) :=
    ⟨single_mem_stdSimplex ℝ î, single_mem_stdSimplex ℝ ĵ⟩
  have hbb : ∀ y, b (y + ζ) = bt y := fun y => hdrift (constCtrl î ĵ) y hctrl
  have hbb' : ∀ y, bt (y + -ζ) = b y := by
    intro y
    rw [← hbb]; congr 1; abel
  set e := MeasurableEquiv.addRight ζ with he
  have he_apply : ∀ y, e y = y + ζ := fun y => rfl
  have he_symm : ∀ y, e.symm y = y + -ζ := by
    intro y; simp [he, sub_eq_add_neg]
  -- the transition probability of the original diffusion
  set P' : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I) :=
    fun t x => (P t (e.symm x)).map e with hP'
  set π' : Measure (EthierKurtz.SDEState I) := π.map e with hπ'
  have hbindP : ∀ t (μ : Measure (EthierKurtz.SDEState I)),
      (μ.map e).bind (P' t) = (μ.bind (P t)).map e := fun t μ => bind_map_equiv e μ (P t)
  refine ⟨?_, P', ?_, π', ?_, ?_, ζ, S, ε, hS, hε, ?_, γ, C, hγ, hC, ?_⟩
  · -- strong solutions
    intro x
    obtain ⟨Ω, mΩ, Pr, hPr, B, X, hB, hX⟩ := hstrong (x + -ζ)
    refine ⟨Ω, mΩ, Pr, hPr, B, fun t ω => X t ω + ζ, hB, ?_⟩
    have := strong_shift Pr bt b (Sigma N) ζ hbb B X (x + -ζ) hX
    simpa using this
  · -- transition probability
    intro Ω _ Pr _ B Y x hB hY t
    have hY' := strong_shift Pr b bt (Sigma N) (-ζ) hbb' B Y x hY
    have hlaw := hP Ω Pr B (fun t ω => Y t ω + -ζ) (x + -ζ) hB hY' t
    have hmeas : Measurable (Y t) := hY.2.1 t
    simp only [hP', he_symm, ← hlaw]
    rw [Measure.map_map e.measurable (hmeas.add_const _)]
    congr 1
    funext ω
    simp [he_apply]
  · -- invariance
    refine ⟨?_, fun t => ?_⟩
    · have := hπ.1
      exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable
    · unfold GPhNGIDiffusion.EMError.dualAction
      rw [hπ', hbindP]
      have := hπ.2 t
      unfold GPhNGIDiffusion.EMError.dualAction at this
      rw [this]
  · -- uniqueness
    intro ρ hρ
    set ρ' := ρ.map e.symm with hρ'
    have hρeq : ρ = ρ'.map e := by rw [hρ', MeasurableEquiv.map_map_symm]
    have hinv : GPhNGIDiffusion.EMError.IsInvariantMeasure P ρ' := by
      refine ⟨?_, fun t => ?_⟩
      · have := hρ.1
        exact Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
      · have h1 := hρ.2 t
        unfold GPhNGIDiffusion.EMError.dualAction at h1 ⊢
        rw [hρeq, hbindP] at h1
        have h2 := congrArg (fun μ => μ.map e.symm) h1
        simp only [MeasurableEquiv.map_symm_map] at h2
        exact h2
    rw [hρeq, huniq ρ' hinv]
  · -- exponential tails
    have hfin := hbound 0 0
    unfold GPhNGIDiffusion.EMError.tvNormWeighted at hfin
    split_ifs at hfin with hcond
    · have h1 : (∫⁻ y, ENNReal.ofReal (lyapVS ε S y) ∂π) < ⊤ := by
        refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hcond.2
        apply ENNReal.ofReal_le_ofReal
        linarith
      rw [hπ', lintegral_map_equiv]
      simpa [he_apply] using h1
    · exact absurd hfin (by simp)
  · -- exponential ergodicity
    intro t x
    have h1 := tvNormWeighted_shift (lyapVS ε S) ζ (P t (e.symm x)) π
    simp only [hP', hπ']
    rw [he, h1]
    have h2 := hbound t (e.symm x)
    rw [he_symm, ← sub_eq_add_neg] at h2
    exact h2
