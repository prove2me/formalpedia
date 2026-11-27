-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeaklyHolomorphicIntegral_proof_c7693f6812f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:59:45.826701+00:00
-- url     : https://prove2.me/submissions/6e585999-4676-46a4-aea3-69a19e3a7152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_coeffs_extend_fb862d39adb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_zero_over_nonzero_868b0831d985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_sheets_nonzero_68832576f450
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isClosed_zeroSetIn_of_ideal_803675c815b8


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
namespace WeaklyHolomorphicIntegral
theorem _root_.solution (hbc : LocalBranchedCovering.Statement)
    (hnd : NormalZerosNowhereDense.Statement) : WeaklyHolomorphicIntegral.Statement := by
  intro σ _ I w N G f hI hnorm hw hNo hwN hG hGne hf hfb
  obtain ⟨U₀, hU₀o, hwU₀, hU₀N, hnd'⟩ := hnd σ I w N G hI hnorm hw hNo hwN hG hGne
  obtain ⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, -, -, hδd, hδne, hsheets, hopen⟩ :=
    hbc σ I w U₀ hI hw (hU₀o.mem_nhds hwU₀)
  have hWU₀ : W ⊆ U₀ := fun z hz => hWU (subset_closure hz)
  have hWN : W ⊆ N := hWU₀.trans hU₀N
  have hnd'' : ∀ z ∈ zeroSetIn I ∩ W, ∀ V ∈ 𝓝 z, ∃ x ∈ zeroSetIn I ∩ V, G x ≠ 0 :=
    fun z hz => hnd' z ⟨hz.1, hWU₀ hz.2⟩
  have hGat : ∀ z ∈ N, DifferentiableAt ℂ G z := fun z hz => hG.differentiableAt (hNo.mem_nhds hz)

  have hKc : IsCompact (zeroSetIn I ∩ closure W) := hWc.inter_left (isClosed_zeroSetIn_of_ideal I)
  obtain ⟨MG, hMG⟩ : ∃ MG, ∀ z ∈ zeroSetIn I ∩ closure W, ‖G z‖ ≤ MG :=
    hKc.exists_bound_of_continuousOn (hG.continuousOn.mono fun z hz => hU₀N (hWU hz.2))

  obtain ⟨cG, hcGd, hcGeq⟩ := fibre_coeffs_extend (zeroSetIn I) W A D δ δ G MG hDo hδd hδne
    (fun _ _ h => h) hsheets (fun z hz => ⟨N, hNo, hWN hz.1.2, G, hG, fun _ _ => rfl⟩)
    (fun x hx _ _ => hMG x ⟨hx.1, subset_closure hx.2⟩)

  have hGeq : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D →
      G x ^ m + ∑ j, cG j (A x) * G x ^ (j : ℕ) = 0 := by
    intro x hx hAx
    refine eq_zero_of_zero_over_nonzero (zeroSetIn I) W A D δ hWo hDo hδne hopen hx hAx
      (fun z => G z ^ m + ∑ j, cG j (A z) * G z ^ (j : ℕ)) ?_ Set.univ Filter.univ_mem ?_
    · refine DifferentiableAt.continuousAt (((hGat x (hWN hx.2)).pow m).add
        (DifferentiableAt.fun_sum fun j _ => ?_))
      exact (((hcGd j).differentiableAt (hDo.mem_nhds hAx)).comp x A.differentiableAt).mul
        ((hGat x (hWN hx.2)).pow _)
    · rintro z ⟨⟨hzZ, hzW⟩, -⟩ hAz hδz
      obtain ⟨O, s, -, hyO, -, hsO⟩ := hsheets (A z) hAz hδz
      obtain ⟨h1, h2, h3⟩ := hsO (A z) hyO
      rw [hcGeq (A z) hAz hδz (fun j => s j (A z)) h1 h2 h3 (G z)]
      obtain ⟨i, hi⟩ := h3 z ⟨hzZ, hzW⟩ rfl
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only at hi
      rw [hi, sub_self]

  set P : (Fin k → ℂ) → ℂ := fun y => (0 : ℂ) ^ m + ∑ j, cG j y * (0 : ℂ) ^ (j : ℕ) with hP
  have hPd : DifferentiableOn ℂ P D :=
    (differentiableOn_const _).add (DifferentiableOn.fun_sum fun j _ => (hcGd j).mul_const _)
  have hPzero : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D → G x = 0 → P (A x) = 0 := by
    intro x hx hAx hGx
    have := hGeq x hx hAx
    rw [hGx] at this
    exact this

  set g : (Fin k → ℂ) → ℂ := fun y => δ y * P y with hg
  have hgd : DifferentiableOn ℂ g D := hδd.mul hPd
  have hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0 := by
    intro V hVo hVD hVne
    obtain ⟨y, hyV, hδy⟩ := hδne V hVo hVD hVne
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y (hVD hyV) hδy
    have hQo : IsOpen ((V ∩ O) ∩ δ ⁻¹' {0}ᶜ) :=
      (hδd.continuousOn.mono (Set.inter_subset_left.trans hVD)).isOpen_inter_preimage (hVo.inter hOo)
        isOpen_compl_singleton
    obtain ⟨y', ⟨⟨hy'V, hy'O⟩, hy'δ⟩, hall⟩ := exists_sheets_nonzero (zeroSetIn I) W A G O _ s hWo hOo hQo
      (fun _ h => h.1.2) ⟨y, ⟨hyV, hyO⟩, hδy⟩ hsd hsO (hG.continuousOn.mono hWN) hnd''
    refine ⟨y', hy'V, mul_ne_zero hy'δ ?_⟩
    obtain ⟨h1, h2, h3⟩ := hsO y' hy'O
    have hval := hcGeq y' (hVD hy'V) hy'δ (fun j => s j y') h1 h2 h3 0
    show P y' ≠ 0
    rw [hP]
    dsimp only
    rw [hval]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by rw [zero_sub, neg_ne_zero]; exact hall j

  have hS : ∀ x ∈ zeroSetIn I ∩ W, A x ∈ D → g (A x) ≠ 0 →
      x ∈ (zeroSetIn I ∩ N) \ {z | G z = 0} := by
    intro x hx hAx hgx
    refine ⟨⟨hx.1, hWN hx.2⟩, fun hGx => hgx ?_⟩
    show δ (A x) * P (A x) = 0
    rw [hPzero x hx hAx hGx, mul_zero]
  have hfS : HolomorphicOnSubset f {x | x ∈ zeroSetIn I ∩ W ∧ A x ∈ D ∧ g (A x) ≠ 0} := by
    intro x hx
    obtain ⟨U, hU, hxU, F, hF, hfF⟩ := hf x (hS x hx.1 hx.2.1 hx.2.2)
    exact ⟨U, hU, hxU, F, hF, fun z hz => hfF ⟨hS z hz.1.1 hz.1.2.1 hz.1.2.2, hz.2⟩⟩
  obtain ⟨Mf, hMf⟩ := isBounded_iff_forall_norm_le.1 hfb

  obtain ⟨cf, hcfd, hcfeq⟩ := fibre_coeffs_extend (zeroSetIn I) W A D δ g f Mf hDo hgd hgne
    (fun _ _ h => left_ne_zero_of_mul h) hsheets hfS (fun x hx hAx hgx => hMf _ ⟨x, hS x hx hAx hgx, rfl⟩)
  refine ⟨W ∩ A ⁻¹' D, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩, fun z hz => hWN hz.1, m,
    fun j z => cf j (A z), fun j => (hcfd j).comp A.differentiableOn fun z hz => hz.2, ?_⟩
  rintro z ⟨⟨hzZ, hzW, hzD⟩, hGz⟩
  have hzS : z ∈ (zeroSetIn I ∩ N) \ {z | G z = 0} := ⟨⟨hzZ, hWN hzW⟩, hGz⟩
  obtain ⟨U, hUo, hzU, F, hFd, hfF⟩ := hf z hzS
  have hGc : ContinuousAt G z := (hGat z (hWN hzW)).continuousAt
  have hV₀ : U ∩ N ∩ {x | G x ≠ 0} ∈ 𝓝 z :=
    Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds hzU) (hNo.mem_nhds (hWN hzW))) (hGc.eventually_ne hGz)
  have key := eq_zero_of_zero_over_nonzero (zeroSetIn I) W A D g hWo hDo hgne hopen ⟨hzZ, hzW⟩ hzD
    (fun x => F x ^ m + ∑ j, cf j (A x) * F x ^ (j : ℕ)) ?_ _ hV₀ ?_
  · show f z ^ m + ∑ j, cf j (A z) * f z ^ (j : ℕ) = 0
    rw [hfF ⟨hzS, hzU⟩]
    exact key
  · have hFz : DifferentiableAt ℂ F z := hFd.differentiableAt (hUo.mem_nhds hzU)
    refine DifferentiableAt.continuousAt ((hFz.pow m).add (DifferentiableAt.fun_sum fun j _ => ?_))
    exact (((hcfd j).differentiableAt (hDo.mem_nhds hzD)).comp z A.differentiableAt).mul (hFz.pow _)
  · rintro x ⟨⟨hxZ, hxW⟩, ⟨hxU, hxN⟩, hxG⟩ hAx hgx
    have hxS : x ∈ (zeroSetIn I ∩ N) \ {z | G z = 0} := ⟨⟨hxZ, hxN⟩, hxG⟩
    show F x ^ m + ∑ j, cf j (A x) * F x ^ (j : ℕ) = 0
    rw [← hfF ⟨hxS, hxU⟩]
    obtain ⟨O, s, -, hyO, -, hsO⟩ := hsheets (A x) hAx (left_ne_zero_of_mul hgx)
    obtain ⟨h1, h2, h3⟩ := hsO (A x) hyO
    rw [hcfeq (A x) hAx hgx (fun j => s j (A x)) h1 h2 h3 (f x)]
    obtain ⟨i, hi⟩ := h3 x ⟨hxZ, hxW⟩ rfl
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only at hi
    rw [hi, sub_self]
end WeaklyHolomorphicIntegral
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
