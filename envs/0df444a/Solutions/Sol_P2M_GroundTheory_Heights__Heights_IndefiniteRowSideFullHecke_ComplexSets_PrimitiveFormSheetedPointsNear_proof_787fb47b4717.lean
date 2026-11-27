-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_proof_787fb47b4717
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:21.837451+00:00
-- url     : https://prove2.me/submissions/33d58137-05e9-42fc-8d4c-760020f1b4cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedPointsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormSheetedPointsNear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_exists_root_9ba640ff292c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_derivative_ne_zero_9ba497f7095d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimitiveFormSheetedPointsNear
theorem _root_.solution (hmin : PrimitiveFormMinimalFactorPoints.Statement)
    (hbr : AnalyticSimpleRootBranch.Statement) : PrimitiveFormSheetedPointsNear.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel U hU
  obtain ⟨n, b, hb, hm, hsepm, hpts⟩ :=
    hmin σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel
  have hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (z ∈ X → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) := by
    filter_upwards [hU, hP, eventually_all.2 hrel] with z h1 h2 h3 using ⟨h1, h2, fun hz i => h3 i hz⟩
  obtain ⟨U₁, hU₁sub, hU₁o, hwU₁⟩ := mem_nhds_iff.1 hgood
  have hn : n ≠ 0 := by
    rintro rfl
    simpa using hm.self_of_nhds hirr.1
  have hE : ∀ᶠ y in 𝓝 (A w), (δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
        (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U₁ ∧
          A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
          ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ) ∧
      (δ y ≠ 0 → (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (δ y ≠ 0 → (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (∀ j, AnalyticAt ℂ (a j) y) ∧ (∀ j, AnalyticAt ℂ (b j) y) ∧ AnalyticAt ℂ δ y ∧
      (∀ i j, AnalyticAt ℂ (q i j) y) := by
    filter_upwards [hpts U₁ (hU₁o.mem_nhds hwU₁), hsepm, hsepP,
      eventually_all.2 fun j => (ha j).eventually_analyticAt, eventually_all.2 fun j => (hb j).eventually_analyticAt,
      hδ.eventually_analyticAt, eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt]
      with y h1 h2 h3 h4 h5 h6 h7 using ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨y, hyE, hyδ⟩ := (hE.eventually_nhds.and_frequently (not_eventually.1 hδ0)).exists
  obtain ⟨E, hEsub, hEo, hyE⟩ := mem_nhds_iff.1 hyE
  obtain ⟨hptsy, hsepmy, hsepPy, hay, hby, -, -⟩ := hEsub hyE
  obtain ⟨τ, hτ⟩ := PrimitiveFormSheetedPointsNear.exists_root n hn (fun j => b j y)
  obtain ⟨⟨hzX, hzU₁⟩, hAz, hℓz⟩ := hptsy hyδ τ hτ
  set z : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hz
  have hPτ : τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 := by
    simpa [hAz, hℓz] using (hU₁sub hzU₁).2.1 hzX
  obtain ⟨OP, BP, ψP, hOPo, hyOP, hBPo, hτBP, -, -, hψP⟩ :=
    hbr d N a y τ hay hPτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero N (fun j => a j y) τ (hsepPy hyδ) hPτ)
  obtain ⟨Om, Bm, ψm, hOmo, hyOm, -, -, hψman, hψmy, hψm⟩ :=
    hbr d n b y τ hby hτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero n (fun j => b j y) τ (hsepmy hyδ) hτ)
  have hδc : ContinuousOn δ E := fun t ht => (hEsub ht).2.2.2.2.2.1.continuousAt.continuousWithinAt
  set O : Set (Fin d → ℂ) := (Om ∩ ψm ⁻¹' BP) ∩ OP ∩ (E ∩ δ ⁻¹' {0}ᶜ) with hO
  have hOo : IsOpen O := ((hψman.continuousOn.isOpen_inter_preimage hOmo hBPo).inter hOPo).inter
    (hδc.isOpen_inter_preimage hEo isOpen_compl_singleton)
  set g : (Fin d → ℂ) → σ → ℂ := fun t i => (∑ j, q i j t * ψm t ^ (j : ℕ)) / δ t with hg
  have key : ∀ t ∈ O, g t ∈ X ∩ U₁ ∧ A (g t) = t ∧ ℓ (g t) = ψm t := fun t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩ =>
    (hEsub htE).1 htδ (ψm t) (((hψm t htm).2 (ψm t) (hψm t htm).1).2 rfl)
  have hPψ : ∀ t ∈ O, ψm t = ψP t := fun t ht => by
    obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
    have h := (hU₁sub hgU).2.1 hgX
    rw [hgA, hgℓ] at h
    exact ((hψP t ht.1.2).2 (ψm t) ht.1.1.2).1 h
  set V : Set (σ → ℂ) := U₁ ∩ A ⁻¹' O ∩ ℓ ⁻¹' BP with hV
  refine ⟨z, ⟨hzX, (hU₁sub hzU₁).1⟩, by rw [hAz]; exact hyδ, O, V, g, hOo,
    (hU₁o.inter (hOo.preimage A.continuous)).inter (hBPo.preimage ℓ.continuous),
    ⟨⟨hzU₁, by rw [Set.mem_preimage, hAz]; exact ⟨⟨⟨hyOm, by rw [Set.mem_preimage, hψmy]; exact hτBP⟩, hyOP⟩, hyE, hyδ⟩⟩,
      by rw [Set.mem_preimage, hℓz]; exact hτBP⟩, ?_, fun t ht => (key t ht).2.1, ?_⟩
  · rintro t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩
    obtain ⟨-, -, -, -, -, -, hqt⟩ := hEsub htE
    have hδt : AnalyticAt ℂ δ t := (hEsub htE).2.2.2.2.2.1
    refine AnalyticAt.pi fun i => AnalyticAt.fun_div ?_ hδt htδ
    exact Finset.analyticAt_fun_sum _ fun j _ => (hqt i j).mul ((hψman t htm).pow _)
  · ext z'
    constructor
    · rintro ⟨hz'X, ⟨hz'U, hz'O⟩, hz'B⟩
      refine ⟨A z', hz'O, ?_⟩
      have hs : ℓ z' = ψm (A z') := by
        rw [hPψ _ hz'O]; exact ((hψP _ hz'O.1.2).2 _ hz'B).1 ((hU₁sub hz'U).2.1 hz'X)
      have hδt : δ (A z') ≠ 0 := hz'O.2.2
      funext i
      rw [hg, div_eq_iff hδt, ← hs, ← (hU₁sub hz'U).2.2 hz'X i, mul_comm]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
      exact ⟨hgX, ⟨hgU, by rw [Set.mem_preimage, hgA]; exact ht⟩, by rw [Set.mem_preimage, hgℓ]; exact ht.1.1.2⟩
end PrimitiveFormSheetedPointsNear
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
