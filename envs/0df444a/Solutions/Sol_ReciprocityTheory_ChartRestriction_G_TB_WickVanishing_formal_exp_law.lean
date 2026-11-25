-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.formal_exp_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:56.486548+00:00
-- url     : https://prove2.me/submissions/a9ea6438-517c-4622-ad36-c1b714e15b2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_idMod2_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_single_point_family
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_germComp1_germComp1_eq_substitute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_germCompOne_identityPoint_left
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_solve_exists_vector
import Theorems.Thm_Formalism_FG_subst_injective_vector
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
theorem _root_.solution : ExpLawSt := by
  intro k _ _ d G ℓ h0 h1 hadd
  have hid := idMod2_of ℓ h0 h1
  obtain ⟨h, hh0, hh⟩ := Formalism.FG.solve_exists_vector k (Fin 1 × Fin d) (Fin 1 × Fin d) (fun p => ℓ p.2) X hid
    (fun j => by simp)
  let ε : Pt k 1 d := fun i => h (0, i)
  have hε0 : ∀ i, constantCoeff (ε i) = 0 := fun i => hh0 (0, i)
  have hhε : h = fun p => ε p.2 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    rfl
  have hLε : comp1 ℓ ε = pt k d 0 := by
    funext i
    show ev ![ε] (ℓ i) = X (0, i)
    unfold ev
    rw [subst_single_point_family, ← hhε]
    exact hh (0, i)
  have hsL : HasSubst (fun p : Fin 1 × Fin d => ℓ p.2) := hasSubst_of_constantCoeff_zero fun p => h0 p.2
  have hsh : HasSubst h := hasSubst_of_constantCoeff_zero hh0
  have hinj := Formalism.FG.subst_injective_vector k (Fin 1 × Fin d) (Fin 1 × Fin d) (fun p => ℓ p.2)
    (fun p => subst (fun q : Fin 1 × Fin d => ℓ q.2) (h p)) X hid
    (fun p => constantCoeff_subst_eq_zero hsL (fun q => h0 q.2) (hh0 p)) (fun p => by simp) (fun j => by
      rw [← subst_comp_subst_apply hsh hsL, hh j, subst_X hsL, subst_self]
      rfl)
  have hεL : comp1 ε ℓ = pt k d 0 := by
    funext i
    show ev ![ℓ] (ε i) = X (0, i)
    unfold ev
    rw [subst_single_point_family]
    exact congrFun hinj (0, i)
  refine ⟨ε, ⟨hε0, h0, hεL, hLε⟩, ?_⟩
  funext i
  have e : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ i) =
      ev (n := 2) ![pt k d 0] (ℓ i) + ev (n := 2) ![pt k d 1] (ℓ i) := congrFun hadd i
  let b : Fin 2 → Pt k 2 d := ![comp1 ε (pt k d 0), comp1 ε (pt k d 1)]
  have hb : ∀ j i, constantCoeff (b j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_comp1 ε _ hε0 (cc_pt 0) i
    · exact cc_comp1 ε _ hε0 (cc_pt 1) i
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
      ![addOf G.F (comp1 ε (pt k d 0)) (comp1 ε (pt k d 1))] := by
    funext j m
    fin_cases j
    show ev b (ev ![pt k d 0, pt k d 1] (G.F m)) = ev b (G.F m)
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> exact cc_pt _ i) hb]
    congr 1
    funext j' m'
    fin_cases j' <;> exact ev_X b hb _ m'
  have L2 : ∀ l : Fin 2, (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d l] : Fin 1 → Pt k 2 d) j m)) =
      ![comp1 ε (pt k d l)] := by
    intro l
    funext j m
    fin_cases j
    fin_cases l <;> exact ev_X b hb _ m
  have L3 : ∀ l : Fin 2, ev (n := 2) ![comp1 ε (pt k d l)] (ℓ i) = pt k d l i := by
    intro l
    have := congrFun (germComp1_germComp1_eq_substitute ℓ ε (pt k (n := 2) d l) hε0 (cc_pt l)) i
    rw [hLε, germCompOne_identityPoint_left _ (cc_pt l)] at this
    exact this
  rw [L1, L2 0, L2 1, L3 0, L3 1] at e2
  exact e2
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
