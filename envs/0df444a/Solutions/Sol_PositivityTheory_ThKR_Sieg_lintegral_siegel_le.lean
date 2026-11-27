-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.lintegral_siegel_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:19.445859+00:00
-- url     : https://prove2.me/submissions/d1e1807a-9d56-4988-8a31-8a02904f027a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
import Theorems.Thm_PositivityTheory_ThKR_Sieg_isClosed_image_section
import Theorems.Thm_PositivityTheory_ThKR_Sieg_lintegral_tau
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_haarProductClosedCompact_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}
namespace PositivityTheory.ThKR.Sieg
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (P K : Subgroup G) (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) [LocallyCompactSpace P]
    (τ : P → Fin r → ℝ) (hτ : Continuous τ)
    (hτm : ∀ p q, τ (p * q) = τ p + τ q) (a : (Fin r → ℝ) → P) (ha : Continuous a) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hτa : ∀ t, τ (a t) = t) (ρ : (Fin r → ℝ) → ℝ) (hρ : Continuous ρ) (hρa : ∀ s t, ρ (s + t) = ρ s + ρ t)
    (hmod : ∀ s, (haar : Measure P).map (· * a s) = ENNReal.ofReal (Real.exp (ρ s)) • haar) {Ω : Set G}
    (hΩ : IsCompact Ω) (hΩτ : ∀ p ∈ Ω, ∃ h : p ∈ P, τ ⟨p, h⟩ = 0) (hc : ∀ m : P, m.1 ∈ K → ∀ t, a t * m = m * a t) :
    ∃ C : ℝ≥0, ∀ (D : Set (Fin r → ℝ)) (S : Set G), MeasurableSet D → MeasurableSet S →
      (∀ g ∈ S, ∃ p ∈ Ω, ∃ t ∈ D, ∃ k ∈ K, g = p * a t * k) →
      ∀ (f : G → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
        (∀ p ∈ Ω, ∀ t ∈ D, ∀ k ∈ K, f (p * a t * k) ≤ h t) →
        ∫⁻ g in S, f g ∂μ ≤ C * ∫⁻ t in D, h t * ENNReal.ofReal (Real.exp (-ρ t)) := by
  have hι : IsClosedEmbedding ((↑) : P → G) := hP.isClosedEmbedding_subtypeVal
  have : SecondCountableTopology P := hι.isEmbedding.secondCountableTopology
  have hL : IsCompact (((↑) : P → G) ⁻¹' K) := hι.isCompact_preimage hK
  have hτL : ∀ m : P, m.1 ∈ K → τ m = 0 := fun m hm => by
    obtain ⟨B, hB⟩ := (hL.image hτ).isBounded.exists_norm_le
    have h1 : τ 1 = 0 := by simpa using hτm 1 1
    have h2 : ∀ j : ℕ, τ (m ^ j) = (j : ℝ) • τ m := fun j => by
      induction j with
      | zero => simpa using h1
      | succ j ih => rw [pow_succ, hτm, ih]; simp [add_smul]
    by_contra h0
    obtain ⟨j, hj⟩ := exists_nat_gt (B / ‖τ m‖)
    have h3 := hB _ ⟨m ^ j, K.pow_mem hm j, rfl⟩
    rw [h2, norm_smul, Real.norm_natCast] at h3
    rw [div_lt_iff₀ (norm_pos_iff.2 h0)] at hj
    linarith
  have hΩ' : IsCompact (((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K) := (hι.isCompact_preimage hΩ).mul hL
  obtain ⟨C, hC⟩ := lintegral_tau (haar : Measure P) τ hτ hτm a ha hadd hτa ρ hρ hρa hmod hΩ' (by
    rintro _ ⟨p, hp, m, hm, rfl⟩
    obtain ⟨_, e⟩ := hΩτ _ hp
    rw [hτm, hτL m hm, e, add_zero])
  have hT : IsClosed (((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K * range a) := by
    rw [← image_univ]
    exact (isClosed_image_section τ hτ a ha hτa isClosed_univ).mul_left_of_isCompact hΩ'
  set T := ((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K * range a with hTdef
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let κ : Measure K := haarMeasure ⊤
  have hκ : κ univ = 1 := by simpa [κ] using haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  have hmP : Measurable ((↑) : P → G) := measurable_subtype_coe
  have hmK : Measurable ((↑) : K → G) := measurable_subtype_coe
  obtain ⟨c, -, hc', hΦ⟩ := GlobalTheory.CompanionTheory.HaarPK.haarProductClosedCompact_holds G μ inferInstance inferInstance
    (NeZero.ne μ) P K hP hK hPK ((haar : Measure P).map (↑)) (κ.map (↑))
    (by rw [Measure.map_apply hmP hP.measurableSet.compl]; simp [preimage])
    (fun p hp => by
      rw [Measure.map_map (measurable_const_mul p) hmP]
      conv_rhs => rw [← map_mul_left_eq_self (haar : Measure P) ⟨p, hp⟩, Measure.map_map hmP (measurable_const_mul _)]
      rfl)
    (fun s hs => by rw [Measure.map_apply hmP hs.measurableSet]; exact (hι.isCompact_preimage hs).measure_lt_top.ne)
    (by rw [Ne, Measure.map_eq_zero_iff hmP.aemeasurable]; exact NeZero.ne _)
    (by rw [Measure.map_apply hmK MeasurableSet.univ, preimage_univ, hκ])
    (by rw [Measure.map_apply hmK hK.measurableSet.compl]; simp [preimage])
    (fun p hp => by
      rw [Measure.map_map (measurable_const_mul p) hmK]
      conv_rhs => rw [← map_mul_left_eq_self κ ⟨p, hp⟩, Measure.map_map hmK (measurable_const_mul _)]
      rfl)
  refine ⟨c.toNNReal * C, fun D S hD hS hSΩ f h hh hf => ?_⟩
  rw [← lintegral_indicator hS, lintegral_eq_nnreal]
  refine iSup₂_le fun φ hφ => ?_
  have hφm : Measurable fun g => (φ g : ℝ≥0∞) := φ.measurable.coe_nnreal_ennreal
  rw [← SimpleFunc.lintegral_eq_lintegral]
  change ∫⁻ g, (φ g : ℝ≥0∞) ∂μ ≤ _
  rw [hΦ _ hφm, ENNReal.coe_mul, ENNReal.coe_toNNReal hc', mul_assoc, ← lintegral_indicator hD]
  have e : D.indicator (fun t => h t * ENNReal.ofReal (Real.exp (-ρ t))) =
      fun t => D.indicator h t * ENNReal.ofReal (Real.exp (-ρ t)) := funext fun t => by
    by_cases ht : t ∈ D <;> simp [ht]
  rw [e, ← hC _ (hh.indicator hD), ← lintegral_indicator hT.measurableSet]
  refine mul_le_mul_right ?_ _
  refine (lintegral_map_le _ ((↑) : P → G)).trans (lintegral_mono fun p => ?_)
  refine (lintegral_map_le _ ((↑) : K → G)).trans ?_
  refine (lintegral_mono (g := fun _ => T.indicator (fun p => D.indicator h (τ p)) p) fun k => ?_).trans
    (by rw [lintegral_const, hκ, mul_one])
  refine (hφ _).trans ?_
  by_cases hg : p.1 * k.1 ∈ S
  · obtain ⟨q, hq, t, ht, k', hk', e⟩ := hSΩ _ hg
    obtain ⟨hqP, hq0⟩ := hΩτ q hq
    let m : P := (⟨q, hqP⟩ * a t)⁻¹ * p
    have hm : m.1 = k' * k.1⁻¹ := by
      change (q * a t)⁻¹ * p.1 = _
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    have hmK : m.1 ∈ K := hm ▸ K.mul_mem hk' (K.inv_mem k.2)
    have hp : p = ⟨q, hqP⟩ * m * a t := by rw [mul_assoc, ← hc m hmK, ← mul_assoc, mul_inv_cancel_left]
    have hpT : p ∈ T := ⟨_, ⟨⟨q, hqP⟩, hq, m, hmK, rfl⟩, _, ⟨t, rfl⟩, hp.symm⟩
    have hτp : τ p = t := by rw [hp, hτm, hτm, hq0, hτL m hmK, hτa]; simp
    rw [indicator_of_mem hg, indicator_of_mem hpT, hτp, indicator_of_mem ht, e]
    exact hf q hq t ht k' hk'
  · rw [indicator_of_notMem hg]
    exact zero_le
end PositivityTheory.ThKR.Sieg
