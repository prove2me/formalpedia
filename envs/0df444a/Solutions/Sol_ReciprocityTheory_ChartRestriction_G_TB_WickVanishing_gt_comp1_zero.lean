-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:54.913396+00:00
-- url     : https://prove2.me/submissions/1074807c-0981-4820-a08c-f8df2da205ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Exp2
variable (A : Type) [CommRing A] [Algebra ℚ A]
end Exp2
section Ev
variable {k : Type} [CommRing k] {d : ℕ}
end Ev
section Calc
variable {k : Type} [CommRing k] {d : ℕ}
end Calc
section Calc2
variable {k : Type} [CommRing k] {d : ℕ}
private theorem gt_evz_lemma {m n : ℕ} (f : PS k m d) (hf : constantCoeff f = 0) :
    ev (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) f = 0 := by
  have hz : ∀ j, GP ((fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) j) := by
    intro j
    show ∀ i, _
    intro i
    simp
  have he : ∀ j, GP ((Fin.elim0 : Fin 0 → Pt k n d) j) := fun j => Fin.elim0 j
  have h1 := gt_ev_ev (Fin.elim0 : Fin 0 → Pt k n d) (fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) he hz f
  have h2 : ev (fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) f = 0 := by
    ext e
    rw [Subsingleton.elim e 0]
    simpa using gt_const_ev (fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) hz f hf
  simp only [h2, gt_ev_zero _ he] at h1
  first
    | exact h1.symm
    | exact h1
end Calc2
section Main
end Main
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) : comp1 φ (0 : Pt k n d) = 0 := by
  funext i
  have h0 : (![(0 : Pt k n d)] : Fin 1 → Pt k n d) = fun _ _ => 0 := by
    funext j l
    fin_cases j
    rfl
  show ev ![(0 : Pt k n d)] (φ i) = 0
  rw [h0]
  exact gt_evz_lemma (φ i) (hφ i)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
