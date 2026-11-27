-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.kunf.abs_unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:50.559825+00:00
-- url     : https://prove2.me/submissions/68d7e398-512b-47ed-bcae-74ab163d1056

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnfA
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnf
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_kunf_lintegral_fd_le
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_kunf_setIntegral_fd_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.kunf
namespace PositivityTheory.SiegelWeilFormula.kunf
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (lam : Measure V) [lam.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ]
    (𝓖 : Set V) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam)
    {Q : Type} [Countable Q] (act : Q → Λ → Q) (hact0 : ∀ q, act q 0 = q)
    (hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν'))
    (A : Q → V → ℂ) (hA : ∀ q, Continuous (A q)) (hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : V)))
    (χ₀ : V → ℂ) (hχc : Continuous χ₀) (hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β') (hχΛ : ∀ ν : Λ, χ₀ (ν : V) = 1)
    (C : Set V) (hC : IsCompact C) (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C)
    (u : Q → ℝ) (hu : Summable u) (hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q)
    (q₀ : Q) (hinj : Function.Injective (act q₀))
    (hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) → ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β) :
    Integrable (A q₀) lam ∧ Integrable (fun β => A q₀ β * χ₀ β) lam ∧
      ∫ β in 𝓖, (∑' q, A q β) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam := by
  classical
  have hactneg : ∀ q ν, act (act q ν) (-ν) = q := fun q ν => by rw [hact, add_neg_cancel, hact0]
  have hactneg' : ∀ q ν, act (act q (-ν)) ν = q := fun q ν => by rw [hact, neg_add_cancel, hact0]
  let e : Λ → Q ≃ Q := fun ν => ⟨fun q => act q ν, fun q => act q (-ν), fun q => hactneg q ν, fun q => hactneg' q ν⟩

  obtain ⟨M, hM⟩ : ∃ M, ∀ β, ‖χ₀ β‖ ≤ M := by
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hχc.continuousOn
    refine ⟨M, fun β => ?_⟩
    obtain ⟨ν, hν⟩ := hcov β
    have := hM _ hν
    rwa [hχadd, hχΛ, mul_one] at this

  have hu0 : ∀ q, 0 ≤ u q := fun q => by
    obtain ⟨ν, hν⟩ := hcov 0
    exact (norm_nonneg _).trans (hAu q _ hν)

  set S : V → ℝ≥0∞ := fun β => ∑' q, ‖A q β‖ₑ with hS
  have hSper : ∀ (ν : Λ) β, S (β + ν) = S β := fun ν β => by
    simp only [hS]
    calc ∑' q, ‖A q (β + ν)‖ₑ = ∑' q, ‖A (e ν q) β‖ₑ := tsum_congr fun q => by rw [← hAact]; rfl
      _ = ∑' q, ‖A q β‖ₑ := (e ν).tsum_eq (fun q => ‖A q β‖ₑ)
  have hSC : ∀ β ∈ C, S β ≤ ENNReal.ofReal (∑' q, u q) := fun β hβ => by
    rw [ENNReal.ofReal_tsum_of_nonneg hu0 hu]
    exact ENNReal.tsum_le_tsum fun q => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hAu q β hβ)
  have hS𝓖 : ∫⁻ β in 𝓖, S β ∂lam < ∞ := by
    refine (lintegral_fd_le h𝓖 S hSper hcov).trans_lt ?_
    calc ∫⁻ β in C, S β ∂lam ≤ ∫⁻ _ in C, ENNReal.ofReal (∑' q, u q) ∂lam := setLIntegral_mono measurable_const hSC
      _ = ENNReal.ofReal (∑' q, u q) * lam C := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top
  have hmeasA : ∀ q, Measurable fun β => ‖A q β‖ₑ := fun q => (hA q).measurable.enorm
  have hsumA : ∑' q, ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam < ∞ := by
    rw [← lintegral_tsum fun q => (hmeasA q).aemeasurable]
    exact hS𝓖
  have hsumAχ : ∑' q, ∫⁻ β in 𝓖, ‖A q β * χ₀ β‖ₑ ∂lam < ∞ := by
    calc ∑' q, ∫⁻ β in 𝓖, ‖A q β * χ₀ β‖ₑ ∂lam ≤ ∑' q, ∫⁻ β in 𝓖, ENNReal.ofReal M * ‖A q β‖ₑ ∂lam :=
          ENNReal.tsum_le_tsum fun q => lintegral_mono fun β => by
            rw [enorm_mul, mul_comm]
            refine mul_le_mul' ?_ le_rfl
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM β)
      _ = ENNReal.ofReal M * ∑' q, ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam := by
          simp_rw [lintegral_const_mul _ (hmeasA _)]
          exact ENNReal.tsum_mul_left
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsumA

  set J : Q → ℂ := fun q => ∫ β in 𝓖, A q β * χ₀ β ∂lam with hJ
  have hmeasAχ : ∀ q, AEStronglyMeasurable (fun β => A q β * χ₀ β) (lam.restrict 𝓖) := fun q =>
    ((hA q).mul hχc).aestronglyMeasurable
  have hLHS : ∫ β in 𝓖, (∑' q, A q β) * χ₀ β ∂lam = ∑' q, J q := by
    simp_rw [← tsum_mul_right]
    exact integral_tsum hmeasAχ hsumAχ.ne
  have hJs : Summable fun q => ‖J q‖ := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) (ENNReal.summable_toReal hsumAχ.ne)
    refine (norm_integral_le_lintegral_norm _).trans_eq ?_
    congr 1
    exact lintegral_congr fun β => ofReal_norm _
  have hJsum : Summable J := hJs.of_norm

  have hint : Integrable (A q₀) lam := by
    refine ⟨(hA q₀).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, h𝓖.lintegral_eq_tsum'']
    refine lt_of_le_of_lt ?_ hsumA
    calc ∑' ν : Λ, ∫⁻ β in 𝓖, ‖A q₀ (ν +ᵥ β)‖ₑ ∂lam = ∑' ν : Λ, ∫⁻ β in 𝓖, ‖A (act q₀ ν) β‖ₑ ∂lam :=
          tsum_congr fun ν => lintegral_congr fun β => by
            rw [hAact, AddSubgroup.vadd_def, vadd_eq_add, add_comm]
      _ ≤ ∑' q, ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun q => ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam)
  have hintχ : Integrable (fun β => A q₀ β * χ₀ β) lam := by
    refine Integrable.mono' (hint.norm.const_mul M) ((hA q₀).mul hχc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM β) (norm_nonneg _)
  refine ⟨hint, hintχ, ?_⟩
  rw [hLHS]

  letI s : Setoid Q :=
    { r := fun q q' => ∃ ν, act q ν = q'
      iseqv := ⟨fun q => ⟨0, hact0 q⟩, fun ⟨ν, h⟩ => ⟨-ν, by rw [← h, hactneg]⟩,
        fun ⟨ν, h⟩ ⟨ν', h'⟩ => ⟨ν + ν', by rw [← hact, h, h']⟩⟩ }
  have hmem : ∀ q q' : Q, (⟦q⟧ : Quotient s) = ⟦q'⟧ → ∃ ν, act q' ν = q := fun q q' h => by
    obtain ⟨ν, hν⟩ := Quotient.exact h
    exact ⟨-ν, by rw [← hν, hactneg]⟩
  have hdecomp : ∑' q, J q = ∑' c : Quotient s, ∑' x : {q // (⟦q⟧ : Quotient s) = c}, J x := by
    rw [← (Equiv.sigmaFiberEquiv (fun q : Q => (⟦q⟧ : Quotient s))).tsum_eq]
    exact Summable.tsum_sigma' (fun c => hJsum.comp_injective Subtype.val_injective)
      ((Equiv.sigmaFiberEquiv _).summable_iff.2 hJsum)
  have hbig : ∑' x : {q // (⟦q⟧ : Quotient s) = ⟦q₀⟧}, J x = ∫ β, A q₀ β * χ₀ β ∂lam := by
    let eb : Λ ≃ {q // (⟦q⟧ : Quotient s) = ⟦q₀⟧} :=
      Equiv.ofBijective (fun ν => ⟨act q₀ ν, Quotient.sound (s := s) ⟨-ν, hactneg q₀ ν⟩⟩)
        ⟨fun ν ν' h => hinj (congrArg Subtype.val h), fun x => by
          obtain ⟨ν, hν⟩ := hmem x q₀ x.2
          exact ⟨ν, Subtype.ext hν⟩⟩
    rw [← eb.tsum_eq, h𝓖.integral_eq_tsum'' _ hintχ]
    refine tsum_congr fun ν => ?_
    show ∫ β in 𝓖, A (act q₀ ν) β * χ₀ β ∂lam = _
    congr 1
    funext β
    rw [hAact, AddSubgroup.vadd_def, vadd_eq_add, add_comm (ν : V) β, hχadd β ν, hχΛ, mul_one]
  have hsmall0 : ∀ c : Quotient s, c ≠ ⟦q₀⟧ → ∑' x : {q // (⟦q⟧ : Quotient s) = c}, J x = 0 := by
    intro c hc
    have hq₁c : (⟦c.out⟧ : Quotient s) = c := Quotient.out_eq c
    have hnot : ∀ ν, act q₀ ν ≠ c.out := fun ν h => hc (by
      rw [← hq₁c, ← h]
      exact Quotient.sound (s := s) ⟨-ν, hactneg q₀ ν⟩)
    obtain ⟨β₀, hβ₀, hinv⟩ := hsmall c.out hnot
    have hmemc : ∀ x : {q // (⟦q⟧ : Quotient s) = c}, ∃ ν, act c.out ν = x := fun x =>
      hmem x c.out (x.2.trans hq₁c.symm)
    set H : V → ℂ := fun β => ∑' x : {q // (⟦q⟧ : Quotient s) = c}, A x β with hH
    have hfib : ∑' x : {q // (⟦q⟧ : Quotient s) = c}, J x = ∫ β in 𝓖, H β * χ₀ β ∂lam := by
      simp only [hH, hJ]
      simp_rw [← tsum_mul_right]
      refine (integral_tsum (f := fun (x : {q // (⟦q⟧ : Quotient s) = c}) β => A x β * χ₀ β)
        (fun x => hmeasAχ x.1) ?_).symm
      exact ne_top_of_le_ne_top hsumAχ.ne
        (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun q => ∫⁻ β in 𝓖, ‖A q β * χ₀ β‖ₑ ∂lam))
    rw [hfib]
    refine setIntegral_fd_eq_zero h𝓖 (fun β => H β * χ₀ β) (fun ν β => ?_) β₀ (χ₀ β₀) hβ₀ (fun β => ?_)
    · have hper : H (β + ν) = H β := by
        let ec : {q // (⟦q⟧ : Quotient s) = c} ≃ {q // (⟦q⟧ : Quotient s) = c} :=
          ⟨fun x => ⟨act x ν, (Quotient.sound (s := s) ⟨-ν, hactneg x ν⟩).trans x.2⟩,
            fun x => ⟨act x (-ν), (Quotient.sound (s := s) ⟨ν, hactneg' x ν⟩).trans x.2⟩,
            fun x => Subtype.ext (hactneg x ν), fun x => Subtype.ext (hactneg' x ν)⟩
        simp only [hH]
        rw [← ec.tsum_eq (fun x => A x β)]
        exact tsum_congr fun x => (hAact x ν β).symm
      show H (β + ν) * χ₀ (β + ν) = H β * χ₀ β
      rw [hper, hχadd, hχΛ, mul_one]
    · have htr : H (β + β₀) = H β := tsum_congr fun x => by
        obtain ⟨ν, hν⟩ := hmemc x
        rw [← hν]
        exact hinv ν β
      show H (β + β₀) * χ₀ (β + β₀) = χ₀ β₀ * (H β * χ₀ β)
      rw [htr, hχadd]
      ring
  rw [hdecomp, tsum_eq_single (⟦q₀⟧ : Quotient s) hsmall0, hbig]
end PositivityTheory.SiegelWeilFormula.kunf
