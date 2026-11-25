-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_proof_223c44725f20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:16:57.263164+00:00
-- url     : https://prove2.me/submissions/48ff3a01-bf09-4a59-b7c2-f654a4afe04e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_eventually_exists_root_6bab1ffe8624
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_norm_le_of_monic_root_673655a91a77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalAt_mk_4e3d1e4fb648
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalYT_eq_zero_a0591a1126ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_exists_point_of_evalYT_eq_zero_7a5ea48e4f32

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
open MvPolynomial Filter Topology
noncomputable section
set_option synthInstance.maxHeartbeats 400000
open FiniteMapOpen
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteMapOpen
theorem _root_.solution : FiniteMapOpen.Statement := by
  classical
  intro n d J p hJ hinj hfin x hx U hU
  set f := (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) with hf
  set φ : (Fin n → ℂ) → (Fin d → ℂ) := fun z i => eval z (p i) with hφ
  set y₀ := φ x with hy₀
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := f.toRingHom.toAlgebra
  have hint : ∀ s : MvPolynomial (Fin n) ℂ ⧸ J, IsIntegral (MvPolynomial (Fin d) ℂ) s :=
    fun s => RingHom.IsIntegral.of_finite hfin s

  choose g hgm hg0 using fun j : Fin n => hint (Ideal.Quotient.mk J (X j))
  have hcoord : ∀ z (hz : z ∈ zeroLocus J) j, evalYT (g j) (φ z) (z j) = 0 := by
    intro z hz j
    have := evalYT_eq_zero J p (hg0 j) hz
    simpa [evalAt_mk] using this

  have hfib : {w | w ∈ zeroLocus J ∧ φ w = y₀}.Finite := by
    refine (Set.Finite.pi (t := fun j => {t : ℂ | evalYT (g j) y₀ t = 0}) fun j => ?_).subset ?_
    · exact Polynomial.finite_setOfPred_isRoot ((hgm j).map _).ne_zero
    · rintro w ⟨hw, hwy⟩ j -
      rw [← hwy]
      exact hcoord w hw j

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ w, w ∈ zeroLocus J ∧ φ w = y₀ → w ≠ x →
      ∑ j : Fin n, c ^ (j : ℕ) * w j ≠ ∑ j : Fin n, c ^ (j : ℕ) * x j := by
    let P : (Fin n → ℂ) → Polynomial ℂ := fun w => ∑ j : Fin n, Polynomial.monomial (j : ℕ) (w j - x j)
    have hP : ∀ w c, (P w).eval c = ∑ j : Fin n, c ^ (j : ℕ) * w j - ∑ j : Fin n, c ^ (j : ℕ) * x j := by
      intro w c
      simp [P, Polynomial.eval_finsetSum, Finset.sum_sub_distrib, mul_comm]
    have hP0 : ∀ w, w ≠ x → P w ≠ 0 := by
      intro w hw h0
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
      have h1 := congrArg (fun q => Polynomial.coeff q j) h0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single j (fun k _ hk => if_neg (fun h => hk (Fin.ext h))) (by simp)] at h1
      simp only [if_true] at h1
      exact hj (sub_eq_zero.1 h1)
    have hbad : (⋃ w ∈ {w | (w ∈ zeroLocus J ∧ φ w = y₀) ∧ w ≠ x},
        {c : ℂ | (P w).eval c = 0}).Finite :=
      (hfib.subset fun w hw => hw.1).biUnion fun w hw =>
        Polynomial.finite_setOfPred_isRoot (hP0 w hw.2)
    obtain ⟨c, hc⟩ := hbad.infinite_compl.nonempty
    refine ⟨c, fun w hw hwx h => hc ?_⟩
    exact Set.mem_biUnion (x := w) ⟨hw, hwx⟩ (by simp [hP, h])
  set L : MvPolynomial (Fin n) ℂ := ∑ j : Fin n, C (c ^ (j : ℕ)) * X j with hL
  have hLz : ∀ z, eval z L = ∑ j : Fin n, c ^ (j : ℕ) * z j := by
    intro z
    simp [hL]

  set ℓ := Ideal.Quotient.mk J L with hℓ
  set μ := minpoly (MvPolynomial (Fin d) ℂ) ℓ with hμ
  have hμm : μ.Monic := minpoly.monic (hint ℓ)
  have : Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hdvd : ∀ F, Polynomial.eval₂ f.toRingHom ℓ F = 0 → μ ∣ F := fun F hF =>
    minpoly.isIntegrallyClosed_dvd (hint ℓ) (by rw [Polynomial.aeval_def]; exact hF)
  have hμx : evalYT μ y₀ (eval x L) = 0 := by
    have h0 := minpoly.aeval (MvPolynomial (Fin d) ℂ) ℓ
    rw [Polynomial.aeval_def] at h0
    have := evalYT_eq_zero J p (F := μ) (s := ℓ) h0 hx
    rw [hℓ, evalAt_mk] at this
    exact this

  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hφc : Continuous φ := continuous_pi fun i => MvPolynomial.continuous_eval _
  have hZc : IsClosed (zeroLocus J) := by
    have hZ : zeroLocus J = ⋂ q ∈ J, {z : Fin n → ℂ | eval z q = 0} := by
      ext z
      simp [zeroLocus]
    rw [hZ]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  set K := zeroLocus J ∩ (φ ⁻¹' Metric.closedBall y₀ 1 ∩ (Metric.ball x r)ᶜ) with hK
  have hKc : IsClosed K :=
    hZc.inter ((Metric.isClosed_closedBall.preimage hφc).inter Metric.isOpen_ball.isClosed_compl)
  let B : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, ∑ k ∈ Finset.range (g j).natDegree, ‖MvPolynomial.eval y ((g j).coeff k)‖
  have hBc : Continuous B := continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).norm
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall y₀ 1).exists_bound_of_continuousOn hBc.continuousOn
  have hKb : Bornology.IsBounded K := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C0 + 1, fun z hz => ?_⟩
    have hB := hC0 _ hz.2.1
    have hB0 : 0 ≤ B (φ z) := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hB0] at hB
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_
    have h1 := norm_le_of_monic_root ((hgm j).map (MvPolynomial.eval (φ z))) (hcoord z hz.1 j)
    rw [(hgm j).natDegree_map] at h1
    simp only [Polynomial.coeff_map] at h1
    have h2 : ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖ ≤ B (φ z) :=
      Finset.single_le_sum
        (f := fun j => ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    linarith
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  set Ψ : (Fin n → ℂ) → (Fin d → ℂ) × ℂ := fun z => (φ z, eval z L) with hΨ
  have hΨc : Continuous Ψ := hφc.prodMk (MvPolynomial.continuous_eval L)
  have hCcl : IsClosed (Ψ '' K) := (hKcpt.image hΨc).isClosed
  have hnot : (y₀, eval x L) ∉ Ψ '' K := by
    rintro ⟨z, hzK, hz⟩
    simp only [Ψ, Prod.mk.injEq] at hz
    have hzx : z ≠ x := fun h => hzK.2.2 (h ▸ Metric.mem_ball_self hr)
    exact hc z ⟨hzK.1, hz.1⟩ hzx (by rw [← hLz, ← hLz, hz.2])
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hCcl.isOpen_compl.mem_nhds hnot)
  filter_upwards [eventually_exists_root hμm hμx hv, hu, Metric.closedBall_mem_nhds y₀ one_pos]
    with y hyt hyu hyB
  obtain ⟨t, htv, ht⟩ := hyt
  obtain ⟨z, hz, hzy, hzt⟩ := exists_point_of_evalYT_eq_zero J p hfin L μ hdvd ht
  by_cases hzr : z ∈ Metric.ball x r
  · exact ⟨z, ⟨hz, hrU hzr⟩, hzy⟩
  · exfalso
    refine huv (Set.mk_mem_prod hyu htv) ⟨z, ⟨hz, ?_, hzr⟩, ?_⟩
    · change φ z ∈ Metric.closedBall y₀ 1
      rw [← hzy] at hyB
      exact hyB
    · simp only [Ψ, Prod.mk.injEq]
      exact ⟨hzy, hzt⟩
end FiniteMapOpen
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
