-- Prove2me | solution 1 for ProbMetricStab.General.theorem_2_2_d_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:11:04.416179+00:00
-- url     : https://prove2.me/submissions/77f137b1-f48e-4a75-997e-3165260df441

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

private lemma expect_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → EReal} (hfg : ∀ ω, f ω ≤ g ω)
    (hg : DupacovaWets.Consistency.expect μ g < ⊤) :
    DupacovaWets.Consistency.expect μ f ≤ DupacovaWets.Consistency.expect μ g := by
  have hgp : (∫⁻ ω, (g ω).toENNReal ∂μ) ≠ ∞ := by
    intro he
    simp [DupacovaWets.Consistency.expect, he] at hg
  have hp : (∫⁻ ω, (f ω).toENNReal ∂μ) ≤ ∫⁻ ω, (g ω).toENNReal ∂μ :=
    lintegral_mono (fun ω => EReal.toENNReal_le_toENNReal (hfg ω))
  have hfp : (∫⁻ ω, (f ω).toENNReal ∂μ) ≠ ∞ := ne_top_of_le_ne_top hgp hp
  rw [DupacovaWets.Consistency.expect, if_neg hfp,
      DupacovaWets.Consistency.expect, if_neg hgp]
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hp
  · apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    exact lintegral_mono (fun ω => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hfg ω)))

private lemma local_bounds {m s : ℕ} (P : Model m s 0)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : Bornology.IsBounded U)
    {ν : Measure ↥P.Ξ} (hν : ν ∈ P.PFU U) :
    ∃ L : EReal, ⊥ < L ∧ ∀ x ∈ P.X ∩ closure U,
      L ≤ P.integral ν 0 x ∧ P.integral ν 0 x < ⊤ := by
  obtain ⟨r, hr, hnorm⟩ := hU.closure.exists_pos_norm_le
  let L := DupacovaWets.Consistency.expect ν
    (fun ξ => ⨅ x ∈ {x : EuclideanSpace ℝ (Fin m) | x ∈ P.X ∧ ‖x‖ ≤ r}, P.f 0 ξ x)
  refine ⟨L, (hν.2 0).1 r hr, ?_⟩
  intro x hx
  have htop : P.integral ν 0 x < ⊤ :=
    (le_iSup₂ x hx).trans_lt
      (hν.2 0).2
  refine ⟨expect_mono ν ?_ htop, htop⟩
  intro ξ
  exact iInf_le_of_le x (iInf_le_of_le ⟨hx.1, hnorm x hx.2⟩ le_rfl)

end ProbMetricStab.General
open ProbMetricStab.General

theorem solution {m s : ℕ} {P : Model m s 0}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∀ ν ∈ P.PFU U,
      P.v μ ≠ ⊤ ∧ P.v μ ≠ ⊥ ∧ P.vU U ν ≠ ⊤ ∧ P.vU U ν ≠ ⊥ ∧
      EReal.abs (P.v μ - P.vU U ν) ≤ P.dFU U μ ν := by
  obtain ⟨xbar, hxbar⟩ := h.S_nonempty
  have hxT : xbar ∈ P.X ∩ closure U :=
    ⟨hxbar.1.1, subset_closure (h.S_subset_U hxbar)⟩
  obtain ⟨Lμ, hLμ, hbμ⟩ := local_bounds P h.U_bounded h.mem_PFU
  have hμtop : P.v μ < ⊤ := hxbar.2 ▸ (hbμ xbar hxT).2
  have hμbot : ⊥ < P.v μ := hxbar.2 ▸ hLμ.trans_le (hbμ xbar hxT).1
  intro ν hν
  obtain ⟨Lν, hLν, hbν⟩ := local_bounds P h.U_bounded hν
  have hxMU : xbar ∈ P.MU U ν := ⟨hxT, fun i => Fin.elim0 i⟩
  have hvtop : P.vU U ν < ⊤ :=
    (iInf_le_of_le xbar (iInf_le_of_le hxMU le_rfl)).trans_lt (hbν xbar hxT).2
  have hvbot : ⊥ < P.vU U ν := hLν.trans_le (le_iInf₂ fun x hx => (hbν x hx.1).1)
  refine ⟨hμtop.ne, hμbot.ne', hvtop.ne, hvbot.ne', ?_⟩
  by_cases hD : P.dFU U μ ν = ∞
  · simp [hD]
  have hpoint (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ P.X ∩ closure U) :
      |(P.integral μ 0 x).toReal - (P.integral ν 0 x).toReal| ≤ (P.dFU U μ ν).toReal := by
    have hb : EReal.abs (P.integral μ 0 x - P.integral ν 0 x) ≤ P.dFU U μ ν :=
      le_iSup_of_le x (le_iSup_of_le hx (le_iSup (fun j => EReal.abs (P.integral μ j x - P.integral ν j x)) 0))
    rw [← EReal.coe_toReal (hbμ x hx).2.ne (hLμ.trans_le (hbμ x hx).1).ne',
        ← EReal.coe_toReal (hbν x hx).2.ne (hLν.trans_le (hbν x hx).1).ne',
        ← EReal.coe_sub, EReal.abs_def] at hb
    exact (ENNReal.ofReal_le_iff_le_toReal hD).mp hb
  have hupper : (P.vU U ν).toReal ≤ (P.v μ).toReal + (P.dFU U μ ν).toReal := by
    have hh := EReal.toReal_le_toReal
      (show P.vU U ν ≤ P.integral ν 0 xbar from
        iInf_le_of_le xbar (iInf_le_of_le hxMU le_rfl)) hvbot.ne' (hbν xbar hxT).2.ne
    have hp := (abs_le.mp (hpoint xbar hxT)).1
    rw [hxbar.2] at hp
    linarith
  have hlower : (P.v μ).toReal - (P.dFU U μ ν).toReal ≤ (P.vU U ν).toReal := by
    have he : ((P.v μ).toReal - (P.dFU U μ ν).toReal : ℝ) ≤ P.vU U ν := by
      apply le_iInf₂
      intro x hx
      have hxT' := hx.1
      have hh := EReal.toReal_le_toReal
        (show P.v μ ≤ P.integral μ 0 x from
          iInf_le_of_le x (iInf_le_of_le ⟨hxT'.1, fun i => Fin.elim0 i⟩ le_rfl))
        hμbot.ne' (hbμ x hxT').2.ne
      have hp := (abs_le.mp (hpoint x hxT')).2
      have hf : ((P.v μ).toReal - (P.dFU U μ ν).toReal : ℝ) ≤ (P.integral ν 0 x).toReal := by linarith
      exact (EReal.coe_le_coe_iff.mpr hf).trans (EReal.coe_toReal_le (hLν.trans_le (hbν x hxT').1).ne')
    exact_mod_cast EReal.toReal_le_toReal he (EReal.coe_ne_bot _) hvtop.ne
  rw [← EReal.coe_toReal hμtop.ne hμbot.ne', ← EReal.coe_toReal hvtop.ne hvbot.ne',
    ← EReal.coe_sub, EReal.abs_def]
  apply (ENNReal.ofReal_le_iff_le_toReal hD).2
  apply abs_le.mpr
  constructor <;> linarith

#print axioms solution
