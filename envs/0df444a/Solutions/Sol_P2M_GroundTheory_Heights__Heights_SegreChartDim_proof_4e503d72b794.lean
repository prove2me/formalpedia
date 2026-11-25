-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartDim_proof_4e503d72b794
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:37.698798+00:00
-- url     : https://prove2.me/submissions/f64f2a54-50bd-4279-acf5-4d411634ce32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_minimalPrimes_transfer_3c8e8c5d49f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_of_mem_minimalPrimes_chartIdeal_a7d2838e47ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_mem_mcPts_iff_053177c2ad13
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVarQ_of_isArithVar_5640a3c8ef08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_R_conePts_of_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_conePts_iff_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_of_mem_minimalPrimes_extC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open SegreChartDim
namespace GroundTheory.Heights₂.Heights
namespace SegreChartDim
theorem _root_.solution : SegreChartDim.Statement := by
  classical
  intro K _ ι _ P e m σ i hP J hJ

  set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
  have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  have : PQ.IsPrime := hvar.1.isPrime
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
    rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      congr 1
    · simp
  have hdim : ∀ Q ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hext] at hQ
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]
    exact hvar.2
  have hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩

  set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal PC i) with hT
  set S := segreChartSet P σ i with hS
  have hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal PC i, eval y h = 0 := fun y => by
    simp [hT, MvPolynomial.mem_zeroLocus_iff]
  have hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S := by
    intro y hy
    obtain ⟨hc, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    exact ⟨y, (mem_mcPts_iff y).2 hc, by simp [segre, h1], rfl⟩
  have hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 →
      chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z := by
    intro z hz
    funext q
    rw [chartLift_segre_apply σ i z hz q.1 q.2]
    simp [ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]
  have hliftS : ∀ x ∈ S, chartLift σ i x ∈ T := by
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
      rw [hzi] at this
      exact one_ne_zero this
    rw [hTmem, hlift_apply z hzi]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 ((mem_mcPts_iff z).1 hz)
  have hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x := by
    rintro _ ⟨z, -, hzi, rfl⟩
    rw [segre_chartLift σ i z hzi]
  have hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y := by
    intro y hy
    obtain ⟨-, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    have hyi : segre y i = 1 := by simp [segre, h1]
    funext q
    rw [chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]

  let α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
    aeval fun a => ∏ k, X ⟨k, σ a k⟩
  let β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval fun q => X (σ.symm (Function.update i q.1 q.2))
  have hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f := by
    intro y f
    induction f using MvPolynomial.induction_on with
    | C c => simp [α]
    | add f g hf hg => simp [hf, hg]
    | mul_X f a hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [α, segre, map_prod]
  have hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g := by
    intro x g
    induction g using MvPolynomial.induction_on with
    | C c => simp [β]
    | add f g hf hg => simp [hf, hg]
    | mul_X f q hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [β, chartLift]
  have hvanS : ∀ f, f ∈ segreChartIdeal P σ i ↔ ∀ x ∈ S, eval x f = 0 := fun f => by
    simp [segreChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]
  have hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0 := fun g => by
    simp [MvPolynomial.mem_vanishingIdeal_iff]
  have htr := minimalPrimes_transfer α.toRingHom β.toRingHom (segreChartIdeal P σ i)
    (MvPolynomial.vanishingIdeal ℂ T)
    (fun f hf => by
      rw [Ideal.mem_comap, hvanT]
      intro y hy
      show eval y (α f) = 0
      rw [hα]
      exact (hvanS f).1 hf _ (hsegT y hy))
    (fun g hg => by
      rw [Ideal.mem_comap, hvanS]
      intro x hx
      show eval x (β g) = 0
      rw [hβ]
      exact (hvanT g).1 hg _ (hliftS x hx))
    (fun f => by
      rw [hvanS]
      intro x hx
      show eval x (β (α f) - f) = 0
      rw [map_sub, hβ, hα, hsegLift x hx, sub_self])
    (fun g => by
      rw [hvanT]
      intro y hy
      show eval y (α (β g) - g) = 0
      rw [map_sub, hα, hβ, hliftSeg y hy, sub_self])
    J (mem_segreChartComponents.1 hJ)
  obtain ⟨hmin, hd⟩ := htr
  rw [hd]
  rw [hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes] at hmin
  exact ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin
end SegreChartDim
end GroundTheory.Heights₂.Heights
