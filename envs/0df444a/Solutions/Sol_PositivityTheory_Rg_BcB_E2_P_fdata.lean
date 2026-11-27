-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.fdata
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:18:48.161835+00:00
-- url     : https://prove2.me/submissions/53d0d57c-bb6e-47a2-97ba-acd0a1933da3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_MulLeWeightedSquares
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Fdata_mul_le_weighted_squares

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : RowsEx → RowsEig → FData := by
  intro hRx hRe X ι _ K _ _ _ J B _ _ _ _ R a₀ Φ g W S _ ν _ χ V hJ hΦ hT hS hne hW hW' hWc hg hg'
  obtain ⟨T₁, hT₁, hT₁J⟩ := hT 1
  obtain ⟨k, hk⟩ := hRx X ι (Φ 1) T₁ (hΦ 1) hT₁
  set L : Lp ℂ 2 ν →L[ℂ] X.Hs ι := J.comp V with hL
  have hLn : ∀ h, ‖L h‖ = ‖h‖ := fun h => (hJ _).trans (hS.iso h)
  have hL1 : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [hLn, one_mul]
  set A := ContinuousLinearMap.adjoint L with hA
  have hAn : ∀ v, ‖A v‖ ≤ ‖v‖ := fun v => by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ 1 * ‖v‖ := by
          gcongr
          rw [hA, LinearIsometryEquiv.norm_map]
          exact hL1
      _ = ‖v‖ := one_mul _
  have hAe : ∀ v, ‖A v‖ₑ ≤ ‖v‖ₑ := fun v => by
    rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hAn v)
  have hin : ∀ v h, inner ℂ (A v) h = inner ℂ v (L h) := fun v h =>
    ContinuousLinearMap.adjoint_inner_left L h v
  have hT1L : ∀ h, T₁ (L h) = J (R a₀ (V h)) := fun h => by
    show T₁ (J (V h)) = _
    rw [hT₁J, one_mul]
  have hmem : ∀ b (h : Lp ℂ 2 ν), MemLp (fun s => χ s b * h s) 2 ν := fun b h =>
    MemLp.of_le_mul (c := ‖R b‖) (Lp.memLp h)
      ((hS.meas b).aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
      (Filter.Eventually.of_forall fun s => by rw [norm_mul]; gcongr; exact hS.bdd b s)
  have hwt : ∀ i, ∫⁻ x, W x * ‖A (k i x)‖ₑ ^ 2 ∂X.ν ≠ ⊤ := by
    intro i
    obtain ⟨C, Ω, hC, hΩ, hkC⟩ := hk.norm
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (hWc Ω hΩ)) ?_
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_mono fun x => ?_
    calc W x * ‖A (k i x)‖ₑ ^ 2 ≤ W x * ‖k i x‖ₑ ^ 2 := by gcongr; exact hAe _
      _ ≤ W x * (C * cnt X.Γ Ω x) := by gcongr; exact hkC i x
      _ = C * (W x * cnt X.Γ Ω x) := by ring
  refine ⟨fun i x => A (k i x), ?_⟩
  refine ⟨fun i => A.continuous.comp (hk.cont i), fun i γ hγ x => by simp only [hk.inv i γ hγ x], ?_, hwt, ?_, ?_, ?_⟩
  ·
    intro hF0
    have hA0 : ∀ i x, A (k i x) = 0 := fun i x => congrFun (congrFun hF0 i) x
    have h0 : ∀ h, T₁ (L h) = 0 := fun h => by
      refine PiLp.ext fun i => ?_
      rw [PiLp.zero_apply]
      refine Lp.ext ?_
      filter_upwards [hk.rep (L h) i, Lp.coeFn_zero ℂ 2 X.ν] with x h1 h2
      rw [h1, h2, ← hin, hA0, inner_zero_left]
      rfl
    set h1 : Lp ℂ 2 ν := (memLp_const (1 : ℂ)).toLp _ with hh1
    set h' : Lp ℂ 2 ν := (hmem a₀ h1).toLp _ with hh'
    have hV : V h' = R a₀ (V h1) := hS.mul _ h1 _ (MemLp.coeFn_toLp _)
    have hJ0 : J (V h') = 0 := by rw [hV, ← hT1L, h0]
    have hn : ‖h'‖ = 0 := by rw [← hS.iso, ← hJ, hJ0, norm_zero]
    have hz : h' = 0 := norm_eq_zero.1 hn
    have hae : ∀ᵐ s ∂ν, False := by
      filter_upwards [hne, MemLp.coeFn_toLp (hmem a₀ h1), MemLp.coeFn_toLp (memLp_const (1 : ℂ) (μ := ν) (p := 2)),
        Lp.coeFn_zero ℂ 2 ν] with s hs e1 e2 e3
      apply hs
      have : (h' : S → ℂ) s = 0 := by rw [hz, e3]; rfl
      rw [hh', e1, hh1, e2] at this
      simpa using this
    exact hS.ne (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hae))
  ·
    intro c x i h
    set h' : Lp ℂ 2 ν := (hmem (c * a₀) h).toLp _ with hh'
    have hV : V h' = R (c * a₀) (V h) := hS.mul _ h _ (MemLp.coeFn_toLp _)
    obtain ⟨Tc, hTc, hTcJ⟩ := hT c
    have key : Tc (T₁ (L h)) = T₁ (L h') := by
      rw [hT1L, hT1L, hTcJ, hV]
      congr 1
      show (R (c * a₀) * R a₀) (V h) = (R a₀ * R (c * a₀)) (V h)
      rw [← map_mul, ← map_mul, mul_comm]
    have e := hRe X ι (Φ c) Tc T₁ k (L h) (L h') (hΦ c) hTc hk key x i
    simp only [hin]
    rw [e, ← hin, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hmem (c * a₀) h)] with s hs
    rw [hs, RCLike.inner_apply']
    ring
  ·
    intro n i
    have hgm : AEStronglyMeasurable (fun x => (g n i : X.G → ℂ) x) X.ν := Lp.aestronglyMeasurable _
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hgm, ?_⟩
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hg' n i, hwt i⟩) ?_
    have hm : AEMeasurable (fun x => (W x)⁻¹ * ‖(g n i : X.G → ℂ) x‖ₑ ^ 2) X.ν :=
      hW.inv.aemeasurable.mul (hgm.enorm.pow_const 2)
    rw [← lintegral_add_left' hm]
    refine lintegral_mono fun x => ?_
    rw [RCLike.enorm_conj]
    exact Fdata.mul_le_weighted_squares _ _ _ (hW' x).1 (hW' x).2
  ·
    intro n h
    have e : ∀ i, ∫ x, conj ((g n i : X.G → ℂ) x) * inner ℂ (A (k i x)) h ∂X.ν = inner ℂ (g n i) (T₁ (L h) i) := by
      intro i
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hk.rep (L h) i] with x hx
      rw [hx, hin, RCLike.inner_apply']
    simp only [e]
    rw [← PiLp.inner_apply, hT1L]
    exact inner_eq_zero_symm.1 (hg n _)
end PositivityTheory.Rg.BcB.E2.P
