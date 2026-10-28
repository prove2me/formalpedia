-- Prove2me | solution 1 for StochConvexProg.FirstStage.eq_3_5_3_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:50:24.04254+00:00
-- url     : https://prove2.me/submissions/3f7c625e-cfb8-44b8-80c2-139f5e0c826a

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

open MeasureTheory

namespace Aux_SCPfs

lemma cube_mem {N : ℕ} (C : ℝ) (hC : 0 ≤ C) (v : Fin N → ℝ) (hv : ‖v‖ ≤ C) :
    v ∈ convexHull ℝ (Set.univ.pi (fun _ : Fin N => ({-C, C} : Set ℝ))) := by
  apply mem_convexHull_pi
  intro i _
  rw [convexHull_pair, segment_eq_Icc (by linarith)]
  have h1 : ‖v i‖ ≤ C := (norm_le_pi_norm v i).trans hv
  rw [Real.norm_eq_abs] at h1
  exact abs_le.mp h1

lemma convex_bound {N : ℕ} (F : (Fin N → ℝ) → ℝ) (hF : ConvexOn ℝ Set.univ F) (C : ℝ)
    (hC : 0 ≤ C) (hfin : (Set.univ.pi (fun _ : Fin N => ({-C, C} : Set ℝ))).Finite)
    (v : Fin N → ℝ) (hv : ‖v‖ ≤ C) :
    |F v| ≤ (∑ w ∈ hfin.toFinset, |F w|) + 2 * |F 0| := by
  have hU : ∀ u : Fin N → ℝ, ‖u‖ ≤ C → F u ≤ ∑ w ∈ hfin.toFinset, |F w| := by
    intro u hu
    obtain ⟨w, hw, hle⟩ :=
      hF.exists_ge_of_mem_convexHull (Set.subset_univ _) (cube_mem C hC u hu)
    have hw' : w ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr hw
    exact hle.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun w => |F w|) (fun _ _ => abs_nonneg _) hw'))
  have hmid : F 0 ≤ 1 / 2 * F v + 1 / 2 * F (-v) := by
    have := hF.2 (Set.mem_univ v) (Set.mem_univ (-v)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [smul_neg, add_neg_cancel, smul_eq_mul, smul_eq_mul] at this
    exact this
  have h1 := hU v hv
  have h2 := hU (-v) (by rwa [norm_neg])
  have hS : 0 ≤ ∑ w ∈ hfin.toFinset, |F w| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h0 := neg_abs_le (F 0)
  have h0' := le_abs_self (F 0)
  rw [abs_le]
  constructor <;> linarith

end Aux_SCPfs

open StochConvexProg.FirstStage Aux_SCPfs in
theorem solution {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    (∀ (x₁ : Fin n₁ → ℝ) (x₂ : Lp (Fin n₂ → ℝ) ⊤ σ), pr.j x₁ ≤ pr.f (x₁, x₂)) ∧
      pr.infQ ≤ pr.infP := by
  have part1 : ∀ (x₁ : Fin n₁ → ℝ) (x₂ : Lp (Fin n₂ → ℝ) ⊤ σ), pr.j x₁ ≤ pr.f (x₁, x₂) := by
    intro x₁ x₂
    unfold Problem.f Problem.F
    by_cases hfeas : pr.Feasible (x₁, x₂) 0
    swap
    · simp only [hfeas, ↓reduceIte]
      exact le_top
    simp only [hfeas, ↓reduceIte]
    obtain ⟨hC1, hf1, hae⟩ := hfeas
    have hF1 : pr.F₁ x₁ 0 = (pr.f₁₀ x₁ : EReal) := by
      unfold Problem.F₁
      have hc : x₁ ∈ pr.C₁ ∧ ∀ i, pr.f₁ i x₁ ≤ (0 : Fin m₁ → ℝ) i := ⟨hC1, hf1⟩
      first
        | rw [if_pos hc]
        | simp only [hc, and_self, ↓reduceIte]
    unfold Problem.j
    rw [hF1, if_pos (EReal.coe_lt_top _)]
    show (pr.f₁₀ x₁ : EReal) + DupacovaWets.Consistency.expect σ (fun s => pr.q s x₁)
      ≤ ((pr.f₁₀ x₁ + ∫ s, pr.f₂₀ s x₁ (x₂ s) ∂σ : ℝ) : EReal)
    rw [EReal.coe_add]
    -- pointwise bound q ≤ h
    have hq_le : ∀ᵐ s ∂σ, pr.q s x₁ ≤ ((pr.f₂₀ s x₁ (x₂ s) : ℝ) : EReal) := by
      filter_upwards [hae, Lp.coeFn_zero (Fin m₂ → ℝ) ⊤ σ] with s hs hz
      obtain ⟨hs1, hs2⟩ := hs
      have hs2' : ∀ i, pr.f₂ i s x₁ (x₂ s) ≤ 0 := by
        intro i
        have := hs2 i
        rw [Prod.snd_zero, hz] at this
        simpa using this
      unfold Problem.q
      refine iInf_le_of_le (x₂ s) ?_
      unfold Problem.F₂
      have hc : x₂ s ∈ pr.C₂ ∧ ∀ i, pr.f₂ i s x₁ (x₂ s) ≤ (0 : Fin m₂ → ℝ) i := ⟨hs1, hs2'⟩
      first
        | rw [if_pos hc]
        | simp only [hc, and_self, ↓reduceIte, le_refl]
    -- integrability of h
    have hconv : ∀ s, ConvexOn ℝ Set.univ (fun v : Fin n₂ → ℝ => pr.f₂₀ s x₁ v) := by
      intro s
      refine ⟨convex_univ, fun a _ b _ α β hα hβ hab => ?_⟩
      have := (pr.f₂₀_convex s).2 (Set.mem_univ (x₁, a)) (Set.mem_univ (x₁, b)) hα hβ hab
      have e : α • (x₁, a) + β • (x₁, b) = (x₁, α • a + β • b) := by
        rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
      rw [e] at this
      exact this
    have hcont : ∀ s, Continuous (fun v : Fin n₂ → ℝ => pr.f₂₀ s x₁ v) := fun s =>
      continuousOn_univ.mp ((hconv s).continuousOn isOpen_univ)
    have hmeasU : Measurable (Function.uncurry
        (fun (v : Fin n₂ → ℝ) (s : S) => pr.f₂₀ s x₁ v)) :=
      measurable_uncurry_of_continuous_of_measurable (fun s => hcont s)
        (fun v => pr.f₂₀_measurable x₁ v)
    have hAEm : AEStronglyMeasurable (fun s => pr.f₂₀ s x₁ (x₂ s)) σ := by
      have h1 : AEMeasurable (fun s => ((x₂ : S → Fin n₂ → ℝ) s, s)) σ :=
        (Lp.aestronglyMeasurable x₂).aemeasurable.prodMk aemeasurable_id
      exact (hmeasU.comp_aemeasurable h1).aestronglyMeasurable
    have hfinE : eLpNormEssSup (x₂ : S → Fin n₂ → ℝ) σ ≠ ⊤ := by
      have := Lp.eLpNorm_lt_top x₂
      rw [eLpNorm_exponent_top] at this
      exact this.ne
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (eLpNormEssSup (x₂ : S → Fin n₂ → ℝ) σ).toReal := ⟨_, rfl⟩
    have hC0 : 0 ≤ C := by rw [hC]; exact ENNReal.toReal_nonneg
    have hCae : ∀ᵐ s ∂σ, ‖x₂ s‖ ≤ C := by
      filter_upwards [enorm_ae_le_eLpNormEssSup (x₂ : S → Fin n₂ → ℝ) σ] with s hs
      rw [← ofReal_norm] at hs
      rw [hC]
      exact (ENNReal.ofReal_le_iff_le_toReal hfinE).mp hs
    have hfinT : (Set.univ.pi (fun _ : Fin n₂ => ({-C, C} : Set ℝ))).Finite :=
      Set.Finite.pi (fun _ => (Set.finite_singleton C).insert (-C))
    have hBd : Integrable (fun s => (∑ w ∈ hfinT.toFinset, |pr.f₂₀ s x₁ w|)
        + 2 * |pr.f₂₀ s x₁ 0|) σ :=
      (integrable_finsetSum hfinT.toFinset (f := fun w s => |pr.f₂₀ s x₁ w|)
        (fun w _ => (pr.f₂₀_integrable x₁ w).abs)).add
        ((pr.f₂₀_integrable x₁ 0).abs.const_mul 2)
    have hint : Integrable (fun s => pr.f₂₀ s x₁ (x₂ s)) σ := by
      refine hBd.mono' hAEm ?_
      filter_upwards [hCae] with s hs
      rw [Real.norm_eq_abs]
      exact convex_bound (fun v => pr.f₂₀ s x₁ v) (hconv s) C hC0 hfinT _ hs
    -- compare the expectations
    have key : DupacovaWets.Consistency.expect σ (fun s => pr.q s x₁)
        ≤ ((∫ s, pr.f₂₀ s x₁ (x₂ s) ∂σ : ℝ) : EReal) := by
      unfold DupacovaWets.Consistency.expect
      have hA : ∫⁻ s, (pr.q s x₁).toENNReal ∂σ
          ≤ ∫⁻ s, ENNReal.ofReal (pr.f₂₀ s x₁ (x₂ s)) ∂σ :=
        lintegral_mono_ae (hq_le.mono fun s hs => EReal.toENNReal_le_toENNReal hs)
      have hB : ∫⁻ s, ENNReal.ofReal (-pr.f₂₀ s x₁ (x₂ s)) ∂σ
          ≤ ∫⁻ s, (-pr.q s x₁).toENNReal ∂σ := by
        refine lintegral_mono_ae (hq_le.mono fun s hs => ?_)
        have h1 : -((pr.f₂₀ s x₁ (x₂ s) : ℝ) : EReal) ≤ -pr.q s x₁ :=
          EReal.neg_le_neg_iff.mpr hs
        rw [← EReal.coe_neg] at h1
        exact EReal.toENNReal_le_toENNReal h1
      have hA' : ∫⁻ s, ENNReal.ofReal (pr.f₂₀ s x₁ (x₂ s)) ∂σ < ⊤ := hint.lintegral_lt_top
      have hB' : ∫⁻ s, ENNReal.ofReal (-pr.f₂₀ s x₁ (x₂ s)) ∂σ < ⊤ :=
        hint.neg.lintegral_lt_top
      rw [if_neg (hA.trans_lt hA').ne, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
        EReal.coe_sub, EReal.coe_ennreal_toReal hA'.ne, EReal.coe_ennreal_toReal hB'.ne]
      exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hA)
        (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hB)
    exact add_le_add le_rfl key
  refine ⟨part1, ?_⟩
  unfold Problem.infQ Problem.infP
  refine le_iInf fun x => ?_
  exact (iInf_le _ x.1).trans (part1 x.1 x.2)
