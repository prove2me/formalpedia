-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChange_posPart_eq_ae901a283544
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:02:59.352061+00:00
-- url     : https://prove2.me/submissions/45461e11-cdc6-4a88-8f18-9db6957ab05e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_zeroSet_diff_523cff7b1a84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_preimage_inter_72d7464be96d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_ae_split_edbb5f1af625
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_lintegral_split_22e51e01810a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChange
theorem _root_.solution (hNull : ChartChangeSheetNull.Statement) (hL : ChartChangeLocal.Statement)
    {J J' : Ideal (MvPolynomial (Fin n) ℂ)} {A A' : Matrix (Fin d) (Fin n) ℂ}
    {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)} {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ}
    {f f' : (Fin n → ℂ) → ℝ} {φ φ' : Fin d → (Fin n → ℂ) → ℝ} {c : Fin d → ℝ}
    {g : Fin d → (Fin n → ℂ) → ℂ}
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hJ' : J'.IsPrime) (hd' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d)
    (hu : linForm u ∉ J) (hu' : linForm u' ∉ J') (hA : IsFiniteProjection J A)
    (hA' : IsFiniteProjection J' A') (hU : IsOpen U) (hU' : IsOpen U')
    (hZU : zeroSet J \ {x | linEval u x = 0} ⊆ U) (hZU' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    (hf : Measurable f) (hf' : Measurable f')
    (hff : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, f' x = f (Φ x))
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) (hφ' : ∀ k, SmoothNear (zeroSet J') (φ' k))
    (hg : ∀ k, DifferentiableOn ℂ (g k) U') (hg0 : ∀ k, ∀ x ∈ U', g k x ≠ 0)
    (hφφ : ∀ k, ∀ x ∈ U', φ' k x = φ k (Φ x) + c k * Real.log ‖g k x‖) :
    ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' f' φ' y) =
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) := by
  set Z := zeroSet J \ {x | linEval u x = 0} with hZ
  set Z' := zeroSet J' \ {x | linEval u' x = 0} with hZ'

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      (x ∈ zeroSet J' → linEval u' x ≠ 0 → (∃ s', IsSheetAt J' A' x s') →
        (∃ s, IsSheetAt J A (Φ x) s) → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' (E.indicator f') φ' y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A ((Φ '' E).indicator f) φ y) := by
    intro x
    by_cases hx : x ∈ zeroSet J' ∧ linEval u' x ≠ 0 ∧ (∃ s', IsSheetAt J' A' x s') ∧
        ∃ s, IsSheetAt J A (Φ x) s
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J J' A A' u u' U U' Φ Ψ f f' φ φ' c g x hU hU' hZU hZU'
        hΦ hΨ hΦm hΨm hΨΦ hΦΨ hf hf' hff hφ hφ' hg hg0 hφφ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
      exact ⟨W, hW, fun _ _ _ _ => hxW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.image_empty, Set.indicator_empty]
      simp [chartPosDens, sheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E' : ℕ → Set (Fin n → ℂ) := fun k => Z' ∩ disjointed (fun k => W (e k)) k with hE'
  set E : ℕ → Set (Fin n → ℂ) := fun k => Φ '' E' k with hE
  have hE'm : ∀ k, MeasurableSet (E' k) := fun k =>
    (measurableSet_zeroSet_diff J' u').inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hE'W : ∀ k, E' k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hE'd : Pairwise (Function.onFun Disjoint E') := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right

  have hEeq : ∀ k, E k = Ψ ⁻¹' E' k ∩ Z := by
    intro k
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨by rw [Set.mem_preimage, hΨΦ x' hx'.1]; exact hx', hΦm hx'.1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Ψ x, h1, hΦΨ x h2⟩
  have hEm : ∀ k, MeasurableSet (E k) := fun k => by
    rw [hEeq k]
    exact measurableSet_preimage_inter hU hΨ.continuousOn hZU (measurableSet_zeroSet_diff J u)
      (hE'm k)
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have : b = a := by rw [← hΨΦ b hb.1, hab, hΨΦ a ha.1]
    exact Set.disjoint_left.1 (hE'd hij) ha (this ▸ hb)

  have hcov' : ∀ x ∈ zeroSet J', (∃ s', IsSheetAt J' A' x s') →
      (linEval u' x ≠ 0 ∧ ∃ s, IsSheetAt J A (Φ x) s) → ∃ k, x ∈ E' k := by
    rintro x hxZ h1 ⟨h2, h3⟩
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxZ h2 h1 h3⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, ⟨hxZ, h2⟩, hk⟩
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) →
      (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s') → ∃ k, x ∈ E k := by
    rintro x hxZ h1 ⟨h2, h3⟩
    have hx : x ∈ Z := ⟨hxZ, h2⟩
    have hΨx := hΨm hx
    obtain ⟨k, hk⟩ := hcov' (Ψ x) hΨx.1 h3 ⟨hΨx.2, by rw [hΦΨ x hx]; exact h1⟩
    exact ⟨k, Ψ x, hk, hΦΨ x hx⟩

  have hN := hNull n d J J' A A' u u' U U' Φ Ψ hJ hd hJ' hd' hu hu' hA hA' hU hU' hZU hZU' hΦ hΨ
    hΦm hΨm hΨΦ hΦΨ
  have hN' := hNull n d J' J A' A u' u U' U Ψ Φ hJ' hd' hJ hd hu' hu hA' hA hU' hU hZU' hZU hΨ hΦ
    hΨm hΦm hΦΨ hΨΦ
  rw [lintegral_split φ' hA' hf' hE'm (ae_split f' φ' E' _ hA' hE'd hN' hcov'),
    lintegral_split φ hA hf hEm (ae_split f φ E _ hA hEd hN hcov)]
  exact tsum_congr fun k => hWE (e k) (E' k) (hE'm k) (hE'W k)
end GroundTheory.Heights₂.Heights.ChartChange
