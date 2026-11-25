-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalTrace_proof_fb74460c5495
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:21.203017+00:00
-- url     : https://prove2.me/submissions/b4b8c560-84ec-415e-8de0-4b017a6a4797

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isClosed_zeroSetIn_of_ideal_803675c815b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_continuousWithinAt_trace_091da22534d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_differentiableAt_comp_a8c1a300de3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_proof_9f4f3171a0d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4


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
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace LocalTrace
theorem _root_.solution (hbc : LocalBranchedCovering.Statement) : LocalTrace.Statement := by
  intro σ _ I w U g hI hw hU hg
  obtain ⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, hwonly, hprop, hδd, hδne, hsheets,
    hopen⟩ := hbc σ I w U hI hw hU
  have hZc : IsClosed (zeroSetIn I) := isClosed_zeroSetIn_of_ideal I
  have hKc : IsCompact (zeroSetIn I ∩ closure W) := hWc.inter_left hZc
  have hgc : ContinuousOn g (zeroSetIn I ∩ U) := fun z hz => hg.continuousWithinAt_trace hz
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ zeroSetIn I ∩ closure W, ‖g z‖ ≤ M :=
    hKc.exists_bound_of_continuousOn (hgc.mono (Set.inter_subset_inter_right _ hWU))

  obtain ⟨f, hf⟩ : ∃ f : (Fin k → ℂ) → ℂ,
      ∀ y, f y = ∑ᶠ z ∈ {z | z ∈ zeroSetIn I ∩ W ∧ A z = y}, g z := ⟨_, fun _ => rfl⟩
  have hfsum : ∀ (s : Fin m → σ → ℂ) (y : Fin k → ℂ),
      (∀ j, s j ∈ zeroSetIn I ∩ W ∧ A (s j) = y) → Function.Injective s →
      (∀ z ∈ zeroSetIn I ∩ W, A z = y → z ∈ Set.range s) → f y = ∑ j, g (s j) := by
    intro s y hs hinj hcov
    have hset : {z | z ∈ zeroSetIn I ∩ W ∧ A z = y} = Set.range s := by
      ext z
      constructor
      · rintro ⟨hz, hAz⟩
        exact hcov z hz hAz
      · rintro ⟨j, rfl⟩
        exact hs j
    rw [hf, hset, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  have hmemU : ∀ z ∈ zeroSetIn I ∩ W, z ∈ zeroSetIn I ∩ U := fun z hz =>
    ⟨hz.1, hWU (subset_closure hz.2)⟩
  have hfd : DifferentiableOn ℂ f (D ∩ {t | δ t ≠ 0}) := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    have hev : f =ᶠ[𝓝 y] fun y' => ∑ j, g (s j y') := by
      filter_upwards [hOo.mem_nhds hyO] with y' hy'
      exact hfsum (fun j => s j y') y' (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun j _ => ?_
    refine hg.differentiableAt_comp ((hsd j).differentiableAt (hOo.mem_nhds hyO)) ?_
    filter_upwards [hOo.mem_nhds hyO] with y' hy' using hmemU _ ((hsO y' hy').1 j).1
  have hfb : ∀ y ∈ D ∩ {t | δ t ≠ 0}, ‖f y‖ ≤ m * M := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    rw [hfsum (fun j => s j y) y (hsO y hyO).1 (hsO y hyO).2.1 (hsO y hyO).2.2]
    calc ‖∑ j, g (s j y)‖ ≤ ∑ j : Fin m, ‖g (s j y)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum fun j _ =>
          hM _ ⟨((hsO y hyO).1 j).1.1, subset_closure ((hsO y hyO).1 j).1.2⟩
      _ = m * M := by simp
  obtain ⟨T, hTd, hTf⟩ := RiemannExtensionAnalytic.proof k D δ f hDo hδd hδne hfd (fun τ _ =>
    ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨m * M, by
      rintro _ ⟨y, ⟨⟨_, hyD⟩, hyδ⟩, rfl⟩
      exact hfb y ⟨hyD, hyδ⟩⟩⟩)
  refine ⟨k, A, W ∩ A ⁻¹' D, D, m, T, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩,
    fun z hz => hWU (subset_closure hz.1), hDo, hAwD,
    fun z hz hAz => hwonly z ⟨hz.1, hz.2.1⟩ hAz, hTd, ?_⟩
  intro y hyD

  have hseq : ∀ n : ℕ, ∃ t ∈ D ∩ Metric.ball y (1 / ((n : ℝ) + 1)), δ t ≠ 0 := fun n =>
    hδne _ (hDo.inter Metric.isOpen_ball) Set.inter_subset_left
      ⟨y, hyD, Metric.mem_ball_self (by positivity)⟩
  choose t ht htδ using hseq
  have htD : ∀ n, t n ∈ D := fun n => (ht n).1
  have httend : Tendsto t atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (ht n).2)
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hX : ∀ n, ∃ X : Fin m → σ → ℂ, (∀ j, X j ∈ zeroSetIn I ∩ W ∧ A (X j) = t n) ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = t n → z ∈ Set.range X) ∧ T (t n) = ∑ j, g (X j) := by
    intro n
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets (t n) (htD n) (htδ n)
    obtain ⟨h1, h2, h3⟩ := hsO (t n) hyO
    exact ⟨fun j => s j (t n), h1, h3, by rw [hTf ⟨htD n, htδ n⟩, hfsum _ (t n) h1 h2 h3]⟩
  choose X hXmem hXcov hXT using hX

  have hKm : IsCompact (Set.univ.pi fun _ : Fin m => zeroSetIn I ∩ closure W) :=
    isCompact_univ_pi fun _ => hKc
  obtain ⟨x, hxK, φ, hφ, hXφ⟩ := hKm.tendsto_subseq (x := X) (fun n => Set.mem_univ_pi.2 fun j =>
    ⟨(hXmem n j).1.1, subset_closure (hXmem n j).1.2⟩)
  have hxK' : ∀ j, x j ∈ zeroSetIn I ∩ closure W := fun j => Set.mem_univ_pi.1 hxK j
  have hxj : ∀ j, Tendsto (fun n => X (φ n) j) atTop (𝓝 (x j)) := fun j => tendsto_pi_nhds.1 hXφ j
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 y) := httend.comp hφ.tendsto_atTop
  have hAx : ∀ j, A (x j) = y := fun j =>
    tendsto_nhds_unique ((A.continuous.tendsto _).comp (hxj j))
      (Tendsto.congr (fun n => ((hXmem (φ n) j).2).symm) htφ)
  have hxW : ∀ j, x j ∈ W := fun j => hprop (x j) (hxK' j) (by rw [hAx j]; exact hyD)
  have hT1 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (T y)) :=
    (hTd.differentiableAt (hDo.mem_nhds hyD)).continuousAt.tendsto.comp htφ
  have hT2 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (∑ j, g (x j))) := by
    have hs : Tendsto (fun n => ∑ j, g (X (φ n) j)) atTop (𝓝 (∑ j, g (x j))) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      exact (hgc (x j) ⟨(hxK' j).1, hWU (hxK' j).2⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hxj j, Filter.Eventually.of_forall fun n =>
          hmemU _ (hXmem (φ n) j).1⟩)
    exact Tendsto.congr (fun n => (hXT (φ n)).symm) hs
  refine ⟨x, fun j => ⟨⟨(hxK' j).1, hxW j, by show A (x j) ∈ D; rw [hAx j]; exact hyD⟩, hAx j⟩,
    ?_, tendsto_nhds_unique hT1 hT2⟩

  rintro z ⟨hzZ, hzW, -⟩ hAz
  by_contra hz
  have hne : ∀ j, 0 < dist z (x j) := fun j => dist_pos.2 fun h => hz ⟨j, h.symm⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo z hzW
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ r ∧ ∀ j, 2 * ε < dist z (x j) := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε) (Filter.Eventually.and (nhdsWithin_le_nhds (Iic_mem_nhds hr) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ r)
      (Filter.eventually_all.2 fun j => nhdsWithin_le_nhds ?_))
    have h2 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
    exact h2.eventually (gt_mem_nhds (hne j))
  obtain ⟨ε, hε0, hεr, hεd⟩ := hε.exists
  have hnbhd := hopen z ⟨hzZ, hzW⟩ ε hε0
  rw [hAz] at hnbhd
  have hev1 : ∀ᶠ n in atTop, t (φ n) ∈ A '' (zeroSetIn I ∩ Metric.ball z ε) := htφ hnbhd
  have hev2 : ∀ᶠ n in atTop, ∀ j, dist (X (φ n) j) (x j) < ε :=
    Filter.eventually_all.2 fun j => Metric.tendsto_nhds.1 (hxj j) ε hε0
  obtain ⟨n, ⟨z', ⟨hz'Z, hz'b⟩, hAz'⟩, hd⟩ := (hev1.and hev2).exists
  have hz'W : z' ∈ W := hrW (Metric.ball_subset_ball hεr hz'b)
  obtain ⟨j, hj⟩ := hXcov (φ n) z' ⟨hz'Z, hz'W⟩ hAz'
  have h1 := hd j
  rw [hj] at h1
  rw [Metric.mem_ball] at hz'b
  have h3 := dist_triangle z z' (x j)
  have h4 := hεd j
  rw [dist_comm] at hz'b
  linarith
end LocalTrace
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
