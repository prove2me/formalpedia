-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.add_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:54.954163+00:00
-- url     : https://prove2.me/submissions/ef494de9-08d9-4975-b12e-1d0d676197db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_pt
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_add__bceb3bffa58a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {d : ℕ} (G : FGLaw k d) (ℓ : Pt k 1 d)
    (hadd : comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1))
    {n : ℕ} (u v : Pt k n d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    comp1 ℓ (addOf G.F u v) = comp1 ℓ u + comp1 ℓ v := by
  funext i
  have e : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ i) =
      ev (n := 2) ![pt k d 0] (ℓ i) + ev (n := 2) ![pt k d 1] (ℓ i) := congrFun hadd i
  let b : Fin 2 → Pt k n d := ![u, v]
  have hb : ∀ j i, constantCoeff (b j i) = 0 := by
    intro j i
    fin_cases j
    · exact hu i
    · exact hv i
  have hadd0 : ∀ j i, constantCoeff ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ (fun j i => by fin_cases j <;> exact cc_pt _ i) (G.const i)
  have hp0 : ∀ (l : Fin 2) j i, constantCoeff ((![pt k d l] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro l j i
    fin_cases j
    exact cc_pt l i
  have e2 := congrArg (ev b) e
  rw [ev_ev _ _ hadd0 hb, ev_add' _ hb, ev_ev _ _ (hp0 0) hb, ev_ev _ _ (hp0 1) hb] at e2
  have L1 : (fun (j : Fin 1) (m : Fin d) => ev b ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j m)) =
      ![addOf G.F u v] := by
    funext j m
    fin_cases j
    show ev b (ev ![pt k d 0, pt k d 1] (G.F m)) = ev b (G.F m)
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> exact cc_pt _ i) hb]
    congr 1
    funext j' m'
    fin_cases j' <;> exact ev_X b hb _ m'
  have L2 : (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d 0] : Fin 1 → Pt k 2 d) j m)) = ![u] := by
    funext j m
    fin_cases j
    exact ev_X b hb 0 m
  have L3 : (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d 1] : Fin 1 → Pt k 2 d) j m)) = ![v] := by
    funext j m
    fin_cases j
    exact ev_X b hb 1 m
  rw [L1, L2, L3] at e2
  exact e2
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
