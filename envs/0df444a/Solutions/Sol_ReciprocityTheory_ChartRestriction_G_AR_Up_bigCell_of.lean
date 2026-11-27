-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.bigCell_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:31:04.776633+00:00
-- url     : https://prove2.me/submissions/d93810d7-799f-4cd2-aa15-44d8d8635c94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BigCellPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution (hLU : LUStatement (E := E)) : BigCellStatement (E := E) := by
  intro r X x0 hx0 la P hP hvan x hx
  obtain ⟨Δ, zOf, bOf, -, hdense, -, -, hdec, -⟩ := hLU r X x0 hx0

  have hgood : ∀ y ∈ X.dom, Δ y ≠ 0 → P y = 0 := by
    intro y hy hΔ
    obtain ⟨hz, hb, hyeq⟩ := hdec y hy hΔ
    have h1 : P (rmul (cpt X x0 (zOf y)) (bOf y)) = bchar la (bOf y) * P (cpt X x0 (zOf y)) :=
      hP.2 (cpt X x0 (zOf y)) hz (bOf y) hb
    have h2 : P (cpt X x0 (zOf y)) = 0 := hvan (zOf y) hz
    rw [hyeq, h1, h2, mul_zero]

  have hopen : IsOpen X.dom := by
    have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := by
      intro τ
      first
      | exact continuous_apply τ
      | (unfold mat; exact continuous_apply τ)
      | fun_prop
      | continuity
    have hgram : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
      intro τ
      refine continuous_matrix fun a b => ?_
      simp only [gram, hermC, col, Matrix.of_apply]
      have h := hmat τ
      first
      | fun_prop
      | continuity
    have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
      fun τ => (hmat τ).matrix_det
    have hmin : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
      intro τ i
      unfold dmin lminor
      exact Complex.continuous_re.comp ((hgram τ).matrix_submatrix _ _).matrix_det
    show IsOpen (GG X.Ψ X.Gm X.p0)
    have hset : GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp only [GG, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [hset]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (hmin τ i)))
  have hcont : ContinuousOn P X.dom := hP.1.continuousOn
  by_contra hne
  have hU : IsOpen (X.dom ∩ P ⁻¹' {0}ᶜ) := hcont.isOpen_inter_preimage hopen isOpen_compl_singleton
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x ⟨hx, hne⟩
  obtain ⟨y, hy, hΔ⟩ := hdense x hx ε hε
  have hy' := hball hy
  have h0 := hgood y hy'.1 hΔ
  exact hy'.2 h0
end ReciprocityTheory.ChartRestriction.G.AR.Up
