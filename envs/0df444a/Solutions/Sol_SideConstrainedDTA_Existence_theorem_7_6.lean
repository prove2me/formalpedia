-- Prove2me | solution 1 for SideConstrainedDTA.Existence.theorem_7_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:34:40.002634+00:00
-- url     : https://prove2.me/submissions/da0da214-86dd-4189-8026-fa77f48dd8c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting
import Theorems.Thm_SideConstrainedDTA_Existence_theorem_3_5
import Theorems.Thm_SideConstrainedDTA_Existence_claim_5
import Theorems.Thm_SideConstrainedDTA_Existence_claim_6
import Theorems.Thm_SideConstrainedDTA_Existence_claim_7
import Theorems.Thm_SideConstrainedDTA_Existence_proposition_7_3_mns_lp
import Theorems.Thm_SideConstrainedDTA_Existence_lam_weak_seq_compact

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence.Sol76

open SideConstrainedDTA.Existence

variable {I W E : Type*} [Fintype W] [DecidableEq I]

/-- Measurability of the penalised, truncated delay operator. -/
lemma trunc_meas (N : Model I W E) (hN : N.Standing) (h13 : A13 N) (h18 : A18 N)
    (h22 : A22 N) (lam K : ℝ) (h : W → ℝ → ℝ) (hh : Lam N h) (p : W) :
    AEStronglyMeasurable (PsiTrunc (PsiPen N lam) K h p) (volume.restrict (Icc N.t0 N.tf)) := by
  refine AEMeasurable.aestronglyMeasurable ?_
  have hPsi : AEMeasurable (N.Psi h p) (volume.restrict (Icc N.t0 N.tf)) :=
    (h18.1 h hh p).aemeasurable measurableSet_Icc
  have hxi : ∀ j : Fin (N.edges p).length, AEMeasurable
      (fun t => xi N h ((N.edges p)[j]) (N.tau h p j t)) (volume.restrict (Icc N.t0 N.tf)) := by
    intro j
    obtain ⟨hτm, hτ0⟩ := (hN.2 h hh p).2 j j.isLt.le
    rw [aemeasurable_restrict_iff_comap_subtype measurableSet_Icc]
    refine Measurable.aemeasurable ?_
    have hT : Measurable (fun t : Icc N.t0 N.tf =>
        (⟨N.tau h p j t, hτ0 t t.2⟩ : Ici (0:ℝ))) := hτm.subtype_mk
    have hf : Measurable (fun t : Icc N.t0 N.tf => N.f h ((N.edges p)[j]) (N.tau h p j t)) :=
      (h13 _ h hh).domRestrict.measurable.comp hT
    have hc : Measurable (fun t : Icc N.t0 N.tf => N.c ((N.edges p)[j]) (N.tau h p j t)) :=
      (h22 _).domRestrict.measurable.comp hT
    exact measurable_const.max (hf.sub hc)
  have hsum : AEMeasurable (xiWalk N h p) (volume.restrict (Icc N.t0 N.tf)) := by
    have := Finset.aemeasurable_sum (Finset.univ : Finset (Fin (N.edges p).length))
      (fun j _ => hxi j)
    convert this using 1
    funext t
    simp [xiWalk, Finset.sum_apply]
  exact ((hPsi.add (hsum.const_mul lam)).min aemeasurable_const)

lemma pen_nonneg (N : Model I W E) (hN : N.Standing) (lam : ℝ) (hl : 0 ≤ lam)
    (h : W → ℝ → ℝ) (hh : Lam N h) (p : W) (t : ℝ) (ht : t ∈ Icc N.t0 N.tf) :
    0 ≤ PsiPen N lam h p t := by
  have h1 := (hN.2 h hh p).1 t ht
  have h2 : 0 ≤ xiWalk N h p t := Finset.sum_nonneg fun j _ => le_max_left _ _
  unfold PsiPen
  positivity

lemma trunc_A1 (N : Model I W E) (hN : N.Standing) (lam K : ℝ) (hl : 0 ≤ lam) (hK : 0 ≤ K) :
    A1 N (PsiTrunc (PsiPen N lam) K) := by
  intro h hh p
  refine ⟨K, fun t ht => ?_⟩
  have h0 := pen_nonneg N hN lam hl h hh p t ht
  unfold PsiTrunc
  rw [abs_le]
  constructor
  · have := le_min h0 hK; linarith
  · exact min_le_right _ _

lemma pen_tendsto (N : Model I W E) (hN : N.Standing) (h13 : A13 N) (h14 : A14 N)
    (h16 : A16 N) (h18 : A18 N) (h22 : A22 N) (lam : ℝ) (hs : ℕ → W → ℝ → ℝ) (h : W → ℝ → ℝ)
    (hc : WeakConvSeq N hs h) (p : W) (t : ℝ) (ht : t ∈ Icc N.t0 N.tf) :
    Tendsto (fun n => PsiPen N lam (hs n) p t) atTop (𝓝 (PsiPen N lam h p t)) := by
  have hPsi := (h18.2 hs h hc p).tendsto_at ht
  have hxi : ∀ j : Fin (N.edges p).length,
      Tendsto (fun n => xi N (hs n) ((N.edges p)[j]) (N.tau (hs n) p j t)) atTop
        (𝓝 (xi N h ((N.edges p)[j]) (N.tau h p j t))) := by
    intro j
    have hτ := (h16 hs h hc p j j.isLt.le).tendsto_at ht
    have hτ0 : 0 ≤ N.tau h p j t := ((hN.2 h hc.2.1 p).2 j j.isLt.le).2 t ht
    have hτw : Tendsto (fun n => N.tau (hs n) p j t) atTop (𝓝[Ici 0] (N.tau h p j t)) :=
      tendsto_nhdsWithin_iff.2 ⟨hτ, Eventually.of_forall fun n =>
        ((hN.2 (hs n) (hc.1 n) p).2 j j.isLt.le).2 t ht⟩
    have hf := (h14 hs h hc ((N.edges p)[j])).tendsto_comp
      (h13 ((N.edges p)[j]) h hc.2.1 _ hτ0) hτw
    have hcc := ((h22 ((N.edges p)[j])) _ hτ0).tendsto.comp hτw
    exact tendsto_const_nhds.max (hf.sub hcc)
  unfold PsiPen xiWalk
  exact hPsi.add (tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _ => hxi j))

lemma trunc_A4 (N : Model I W E) (hN : N.Standing) (h13 : A13 N) (h14 : A14 N)
    (h16 : A16 N) (h18 : A18 N) (h22 : A22 N) (lam K : ℝ) (hl : 0 ≤ lam) (hK : 0 ≤ K) :
    A4 N (PsiTrunc (PsiPen N lam) K) := by
  intro hs h hc p
  have hb : ∀ g, Lam N g → ∀ᵐ t ∂(volume.restrict (Icc N.t0 N.tf)),
      ‖PsiTrunc (PsiPen N lam) K g p t‖ ≤ K := by
    intro g hg
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    have h0 := pen_nonneg N hN lam hl g hg p t ht
    unfold PsiTrunc
    rw [abs_le]
    exact ⟨by have := le_min h0 hK; linarith, min_le_right _ _⟩
  refine tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by simp)
    (fun n => trunc_meas N hN h13 h18 h22 lam K (hs n) (hc.1 n) p)
    (MemLp.of_bound (trunc_meas N hN h13 h18 h22 lam K h hc.2.1 p) K (hb h hc.2.1)) ?_ ?_
  · refine unifIntegrable_of (by norm_num) (by simp)
      (fun n => trunc_meas N hN h13 h18 h22 lam K (hs n) (hc.1 n) p) fun ε hε => ?_
    refine ⟨Real.toNNReal (K + 1), fun n => ?_⟩
    have : ({x | Real.toNNReal (K + 1) ≤ ‖PsiTrunc (PsiPen N lam) K (hs n) p x‖₊}.indicator
        (PsiTrunc (PsiPen N lam) K (hs n) p)) =ᵐ[volume.restrict (Icc N.t0 N.tf)] 0 := by
      filter_upwards [hb (hs n) (hc.1 n)] with t ht
      refine indicator_of_notMem ?_ _
      simp only [mem_ofPred_eq, not_le]
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.coe_toNNReal _ (by linarith)]
      linarith
    rw [eLpNorm_congr_ae this]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (pen_tendsto N hN h13 h14 h16 h18 h22 lam hs h hc p t ht).min tendsto_const_nhds

lemma trunc_eq (N : Model I W E) (M lam : ℝ)
    (hM : ∀ i h, Lam N h → ∃ p, N.com p = i ∧
      ∃ J ⊆ Icc N.t0 N.tf, MeasurableSet J ∧ 0 < volume J ∧
        ∀ t ∈ J, h p t < N.B p ∧ PsiPen N lam h p t ≤ M)
    (h : W → ℝ → ℝ) (hh : IsDTCEq N (PsiTrunc (PsiPen N lam) (M + 1)) h) :
    IsDTCEq N (PsiPen N lam) h := by
  refine ⟨hh.1, fun i => ?_⟩
  obtain ⟨ν, hν⟩ := hh.2 i
  obtain ⟨p, hpi, J, hJI, hJm, hJpos, hJ⟩ := hM i h hh.1
  have hνM : ν ≤ M := by
    by_contra hcon
    have hsub : J ⊆ {t | ¬ ((0 < h p t → PsiTrunc (PsiPen N lam) (M + 1) h p t ≤ ν) ∧
        (h p t < N.B p → ν ≤ PsiTrunc (PsiPen N lam) (M + 1) h p t))} := by
      intro t htJ hP
      obtain ⟨hlt, hle⟩ := hJ t htJ
      have := hP.2 hlt
      have : PsiTrunc (PsiPen N lam) (M + 1) h p t ≤ M := (min_le_left _ _).trans hle
      exact hcon (by linarith)
    have h0 := measure_mono_null hsub (ae_iff.1 (hν p hpi))
    rw [Measure.restrict_apply hJm, inter_eq_left.2 hJI] at h0
    exact (ne_of_gt hJpos) h0
  refine ⟨ν, fun q hq => ?_⟩
  filter_upwards [hν q hq] with t ht
  refine ⟨fun hpos => ?_, fun hlt => ?_⟩
  · have h1 := ht.1 hpos
    unfold PsiTrunc at h1
    rcases min_le_iff.1 h1 with h1 | h1
    · exact h1
    · linarith
  · have h1 := ht.2 hlt
    unfold PsiTrunc at h1
    exact (le_min_iff.1 h1).1

end SideConstrainedDTA.Existence.Sol76

open SideConstrainedDTA.Existence SideConstrainedDTA.Existence.Sol76

theorem solution {I W E : Type*} [Fintype I] [Fintype W] [Fintype E] [DecidableEq I]
    [DecidableEq W] [DecidableEq E] (N : Model I W E) (hN : N.Standing)
    (h2 : A2 N) (h3 : A3 N) (h5 : A5 N) (h9 : A9 N) (h10 : A10 N) (h11 : A11 N) (h12 : A12 N)
    (h13 : A13 N) (h14 : A14 N) (h15 : A15 N) (h16 : A16 N) (h17 : A17 N) (h18 : A18 N)
    (h19 : A19 N) (h22 : A22 N) :
    ∃ h, IsSCDE N N.Psi (capFeasible N) (devMNS N) h ∧
      IsSCDE N N.Psi (capFeasible N) (devLP N) h := by
  obtain ⟨M, hM0, hM⟩ := claim_5 N hN h2 h10 h18 h19
  have hex : ∀ n : ℕ, ∃ h, IsDTCEq N (PsiPen N ((n : ℝ) + 1)) h := by
    intro n
    have hl : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hK : (0 : ℝ) ≤ M + 1 := by linarith
    obtain ⟨h, hh⟩ := theorem_3_5 N hN.1 (PsiTrunc (PsiPen N ((n : ℝ) + 1)) (M + 1))
      (fun h hh p => trunc_meas N hN h13 h18 h22 _ _ h hh p)
      (trunc_A1 N hN _ _ hl hK) h2 h3 (trunc_A4 N hN h13 h14 h16 h18 h22 _ _ hl hK)
    exact ⟨h, trunc_eq N M _ (hM _ hl) h hh⟩
  choose hs hhs using hex
  obtain ⟨φ, hφ, hstar, hLam, hweak⟩ := lam_weak_seq_compact N hs (fun n => (hhs n).1)
  have hlam : ∀ n, (0 : ℝ) < ((φ n : ℕ) : ℝ) + 1 := fun n => by positivity
  have hlam' : Tendsto (fun n => ((φ n : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hfeas := claim_6 N hN h2 h3 h5 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
    (fun n => ((φ n : ℕ) : ℝ) + 1) hlam hlam' (fun n => hs (φ n)) (fun n => hhs (φ n))
    hstar hLam hweak
  have hmns := claim_7 N hN h2 h3 h5 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h22
    (fun n => ((φ n : ℕ) : ℝ) + 1) hlam hlam' (fun n => hs (φ n)) (fun n => hhs (φ n))
    hstar hLam hweak hfeas
  exact ⟨hstar, hmns, proposition_7_3_mns_lp N hN _ hstar hmns⟩
