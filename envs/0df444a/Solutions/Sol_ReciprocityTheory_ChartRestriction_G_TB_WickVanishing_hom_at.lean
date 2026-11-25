-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.hom_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:39:56.989917+00:00
-- url     : https://prove2.me/submissions/5153b46e-3dec-4df2-88a8-82c4d02f7471

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_ev
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {d : ℕ} {O : Type} [CommRing O] (G : FGLaw k d) (A : OAct O G) (a : O) {n : ℕ}
    (u v : Pt k n d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    comp1 (A.act a) (addOf G.F u v) = addOf G.F (comp1 (A.act a) u) (comp1 (A.act a) v) := by
  have huv : ∀ j i, constantCoeff ((![u, v] : Fin 2 → Pt k n d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact hu i
    · exact hv i
  have hpt : ∀ (m : ℕ) (j : Fin m) (i : Fin d), constantCoeff (pt k (n := m) d j i) = 0 := fun m j i =>
    MvPowerSeries.constantCoeff_X _
  have hp01 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j <;> exact hpt _ _ _
  have hp0 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hp1 : ∀ j i, constantCoeff ((![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hadd01 : ∀ j i, constantCoeff ((![addOf G.F (pt k (n := 2) d 0) (pt k (n := 2) d 1)] :
      Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ hp01 (G.const i)
  have hc01 : ∀ j i, constantCoeff ((![comp1 (A.act a) (pt k (n := 2) d 0), comp1 (A.act a) (pt k (n := 2) d 1)] :
      Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_ev _ hp0 (A.const a i)
    · exact cc_ev _ hp1 (A.const a i)
  have hev2 : ∀ (j : Fin 2) (l : Fin d), ev (![u, v] : Fin 2 → Pt k n d)
      ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j l) = (![u, v] : Fin 2 → Pt k n d) j l := by
    intro j l
    fin_cases j
    · exact ev_X _ huv 0 l
    · exact ev_X _ huv 1 l
  funext i
  have h := congrArg (ev (![u, v] : Fin 2 → Pt k n d)) (congrFun (A.hom a) i)
  simp only [comp1, FGLaw.add, addOf] at h ⊢
  rw [ev_ev _ _ hadd01 huv, ev_ev _ _ hc01 huv] at h
  convert h using 2
  · funext j l
    fin_cases j
    simp only [addOf, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
    rw [ev_ev _ _ hp01 huv]
    congr 1
    funext j' l'
    exact (hev2 j' l').symm
  · funext j l
    fin_cases j
    · simp only [comp1, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
      rw [ev_ev _ _ hp0 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 0 l').symm
    · simp only [comp1, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue]
      rw [ev_ev _ _ hp1 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 1 l').symm
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
