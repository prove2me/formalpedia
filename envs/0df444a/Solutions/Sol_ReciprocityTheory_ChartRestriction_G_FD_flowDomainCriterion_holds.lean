-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.flowDomainCriterion_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:50.47807+00:00
-- url     : https://prove2.me/submissions/078c6716-e3a1-42d1-98f3-9de83d683df8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantFamilyNorms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_det_flowMat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_dmin_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_dmin_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hG_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hsg_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_maj_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_maj_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_bounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open Complex ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
private theorem minors_iff {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (τ : X.Ψ) :
    (∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re) ↔
      0 < 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have hG := MajorantFamilyNorms.hG_of X τ
  have hdet : (mat x τ).det ≠ 0 := (hx τ).1
  have hsg := MajorantFamilyNorms.hsg_of X hx τ
  have he0 := (he τ).1
  have key : ∀ i : Fin (r + 1), (dmin X.Gm (X.flowV e s x) τ i).re =
      (dmin X.Gm x τ i).re * (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i) := by
    intro i
    rw [MajorantFamilyNorms.dmin_eq X (X.flowV e s x), MajorantFamilyNorms.dmin_flow X hx e τ he0 s,
      ← MajorantFamilyNorms.dmin_eq X x, Complex.re_mul_ofReal]
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := (hx τ).2
  have hb := fun (i : ℕ) (hi : i ≤ r) =>
    mN_bounds hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 i hi
  have hmp := mN_pos hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 (he τ).2
  constructor
  · intro h
    have h0 := h ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    rw [key, ← mul_assoc] at h0
    exact pos_of_mul_pos_right h0 (hpos _).le
  · intro h i
    rw [key, ← mul_assoc]
    refine mul_pos (hpos i) ?_
    obtain ⟨h0, h1⟩ := hb i (Nat.le_of_lt_succ i.isLt)
    rcases le_or_gt 0 (2 * X.c τ * (s τ).im) with hk | hk
    · nlinarith [mul_nonneg hk h0]
    · nlinarith [mul_le_mul_of_nonpos_left h1 hk.le]
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : FlowDomainCriterion (E := E) := by
  intro r X e he x hx s
  have hmp : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (MajorantFamilyNorms.hsg_of X hx τ) (e τ)
      (he τ).1 (he τ).2
  have hm : ∀ τ, 1 + (s τ).im / X.ttV e x τ =
      1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
    intro τ
    rw [Data.ttV, MajorantFamilyNorms.maj_eq X hx e τ (he τ).1, one_div, div_inv_eq_mul]
    ring
  have hdom : X.flowV e s x ∈ X.dom ↔
      ∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re := by
    constructor
    · intro h τ
      exact (h τ).2
    · intro h τ
      refine ⟨?_, h τ⟩
      show (X.flowMatV (e τ) τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, MajorantFamilyNorms.det_flowMat X (e τ) τ (s τ) (he τ).1, one_mul]
      exact (hx τ).1
  refine ⟨?_, ?_⟩
  · rw [hdom]
    refine forall_congr' fun τ => ?_
    rw [hm τ]
    exact minors_iff X e he hx s τ
  · intro hf τ
    have hpos := (minors_iff X e he hx s τ).1 (hdom.1 hf τ)
    have hc := MajorantFamilyNorms.c_pos X τ
    have hm0 := hmp τ
    simp only [Data.ttV]
    rw [MajorantFamilyNorms.maj_flow X hx e τ (he τ).1 s hpos.ne', MajorantFamilyNorms.maj_eq X hx e τ (he τ).1]
    field_simp
end ReciprocityTheory.ChartRestriction.G.FD
