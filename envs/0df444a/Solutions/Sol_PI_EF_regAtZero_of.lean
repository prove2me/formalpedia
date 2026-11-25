-- Prove2me | solution 1 for PI.EF.regAtZero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:57.694881+00:00
-- url     : https://prove2.me/submissions/068b7de7-900b-4fe1-ad5b-8bcce84a3ea1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RegZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter Filter Topology
namespace PI.EF
theorem _root_.solution {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) :
    RegAtZero (Cw + Cl) := by
  intro N _ χ hχ x₁ T' H hx₁ hT' hH
  classical
  obtain ⟨hZ0, hZ0sum⟩ := hW N χ hχ 0
  have hlog : Real.log (N * (|(0:ℝ)| + 2)) = Real.log (2 * N) := by
    rw [abs_zero, zero_add, mul_comm]
  have hne0 : ∀ ρ ∈ ZerosNear χ 0, ρ ≠ 0 := by
    rintro ρ hρ rfl
    have := hρ.1
    simp at this
  have hB : (ZerosBelow χ T').Finite := by
    refine ((Finset.Icc ⌊-T'⌋ ⌊T'⌋).finite_toSet.biUnion
      (fun k _ => (hW N χ hχ (k : ℝ)).1)).subset ?_
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hρ
    rw [abs_lt] at h3
    refine Set.mem_iUnion₂.mpr ⟨⌊ρ.im⌋, ?_, h1, h2, ?_, h4⟩
    · rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨Int.floor_mono h3.1.le, Int.floor_mono h3.2.le⟩
    · rw [abs_le]
      constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]
  have hneB : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 0 := by
    rintro ρ hρ rfl
    have := hρ.1
    simp at this
  have hofR : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  have h0rect : (0 : ℂ) ∈ rect (-1 / 2) x₁ (-T') T' := by
    show (0 : ℂ) ∈ Set.Icc (-1 / 2 : ℝ) x₁ ×ℂ Set.Icc (-T') T'
    rw [Complex.mem_reProdIm]
    simp only [Complex.zero_re, Complex.zero_im, Set.mem_Icc]
    constructor <;> constructor <;> linarith
  have hrect : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → (ε : ℂ) ∈ rect (-1 / 2) x₁ (-T') T' := by
    intro ε h1 h2
    show (ε : ℂ) ∈ Set.Icc (-1 / 2 : ℝ) x₁ ×ℂ Set.Icc (-T') T'
    rw [Complex.mem_reProdIm]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Set.mem_Icc]
    constructor <;> constructor <;> linarith
  have hHt : Tendsto (fun ε : ℝ => ‖H ε - H 0‖) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousWithinAt H (rect (-1 / 2) x₁ (-T') T') 0 :=
      hH.1.continuousOn.continuousWithinAt h0rect
    have hr : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝[rect (-1 / 2) x₁ (-T') T'] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hofR, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num)] with ε hε
      exact hrect ε hε.1 hε.2
    have := ((hc.tendsto.comp hr).sub_const (H 0)).norm
    simpa using this
  have hevZ : ∀ᶠ ε : ℝ in 𝓝[>] 0, (ε : ℂ) ∉ ZerosNear χ 0 := by
    have hc : (ZerosNear χ 0)ᶜ ∈ 𝓝 (0 : ℂ) :=
      hZ0.isClosed.isOpen_compl.mem_nhds (fun h => hne0 0 h rfl)
    exact hofR.eventually_mem hc
  have hpt : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0‖ ≤
        ‖H ε - H 0‖ + ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖ +
          Cl * Real.log (2 * N) + ‖∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num), hevZ] with ε hε hεZ
    obtain ⟨hε0, hε1⟩ := hε
    have hLε : DirichletCharacter.LFunction χ ε ≠ 0 := by
      intro h
      apply hεZ
      refine ⟨?_, ?_, ?_, h⟩
      · simpa using hε0
      · simp only [Complex.ofReal_re]; linarith
      · simp
    have hε1' : (ε : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.one_re] at this
      linarith
    have hreg := hH.2 ε (hrect ε hε0 hε1) hLε hε1'
    have hloc := hL N χ hχ ε (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith) hLε hε1'
    simp only [Complex.ofReal_im] at hloc
    rw [hlog] at hloc
    have key : (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0 =
        (H ε - H 0) + ((∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)) -
        (logDeriv (DirichletCharacter.LFunction χ) ε -
          (∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)) - eps0 χ / ε +
            del1 χ / (ε - 1)) -
        ∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ) := by
      rw [hreg]; ring
    rw [key]
    have h4 : ∀ a b c d : ℂ, ‖a + b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := fun a b c d =>
      calc ‖a + b - c - d‖ ≤ ‖a + b - c‖ + ‖d‖ := norm_sub_le _ _
        _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
    refine (h4 _ _ _ _).trans ?_
    linarith [hloc]
  have hPt : Tendsto (fun ε : ℝ => ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
      ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ∑ ρ ∈ hB.toFinset,
        ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / ((ε : ℂ) - ρ))) (𝓝[>] 0)
        (𝓝 (∑ ρ ∈ hB.toFinset, ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / (0 - ρ)))) :=
      tendsto_finset_sum _ fun ρ hρ => tendsto_const_nhds.add
        (tendsto_const_nhds.div (hofR.sub_const ρ) (by
          rw [zero_sub, neg_ne_zero]; exact hneB ρ (by simpa using hρ)))
    have h0 : (∑ ρ ∈ hB.toFinset, ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / (0 - ρ))) = 0 :=
      Finset.sum_eq_zero fun ρ _ => by rw [zero_sub, div_neg, add_neg_cancel]
    rw [h0] at h
    have := h.norm
    rw [norm_zero] at this
    refine this.congr fun ε => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
      Finset.sum_add_distrib]
  have hQt : Tendsto (fun ε : ℝ => ‖∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖)
      (𝓝[>] 0) (𝓝 ‖∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ)‖) := by
    have h : Tendsto (fun ε : ℝ => ∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ))
        (𝓝[>] 0) (𝓝 (∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ))) :=
      tendsto_finset_sum _ fun ρ hρ => tendsto_const_nhds.div (hofR.sub_const ρ) (by
        rw [zero_sub, neg_ne_zero]; exact hne0 ρ (by simpa using hρ))
    refine h.norm.congr fun ε => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hZ0]
  have hlim := ((hHt.add hPt).add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => Cl * Real.log (2 * N)) (𝓝[>] 0) _)).add hQt
  have hmain := ge_of_tendsto hlim hpt
  have hB1 : ZerosBelow χ 1 ⊆ ZerosNear χ 0 := by
    rintro ρ ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by rw [sub_zero]; exact h3.le, h4⟩
  have hB1f : (ZerosBelow χ 1).Finite := hZ0.subset hB1
  have hQ0 : ‖∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ)‖ ≤
      S1 χ + Cw * Real.log (2 * N) := by
    refine (norm_sum_le _ _).trans ?_
    have hn : ∀ ρ, ‖(mult χ ρ : ℂ) / (0 - ρ)‖ = (mult χ ρ : ℝ) / ‖ρ‖ := fun ρ => by
      rw [norm_div, zero_sub, norm_neg, Complex.norm_natCast]
    simp only [hn]
    rw [← Finset.sum_filter_add_sum_filter_not hZ0.toFinset (fun ρ => ρ ∈ ZerosBelow χ 1)]
    have hS1 : S1 χ = ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∈ ZerosBelow χ 1),
        (mult χ ρ : ℝ) / ‖ρ‖ := by
      unfold S1
      rw [finsum_mem_eq_finite_toFinset_sum _ hB1f]
      congr 1
      ext ρ
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun h => ⟨hB1 h, h⟩, fun h => h.2⟩
    have hrest : ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∉ ZerosBelow χ 1),
        (mult χ ρ : ℝ) / ‖ρ‖ ≤ Cw * Real.log (2 * N) := by
      calc _ ≤ ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∉ ZerosBelow χ 1), (mult χ ρ : ℝ) := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            rw [Finset.mem_filter] at hρ
            obtain ⟨hρ1, hρ2⟩ := hρ
            have hρZ : ρ ∈ ZerosNear χ 0 := by simpa using hρ1
            obtain ⟨h1, h2, h3, h4⟩ := hρZ
            have him : 1 ≤ |ρ.im| := by
              by_contra hlt
              push_neg at hlt
              exact hρ2 ⟨h1, h2, hlt, h4⟩
            exact div_le_self (Nat.cast_nonneg _) (him.trans (Complex.abs_im_le_norm ρ))
        _ ≤ ∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Nat.cast_nonneg _)
        _ ≤ Cw * Real.log (2 * N) := by
            rw [← hlog, ← finsum_mem_eq_finite_toFinset_sum _ hZ0]
            exact hZ0sum
    linarith
  linarith
end PI.EF
