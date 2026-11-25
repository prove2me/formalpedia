-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.jac_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:49.773703+00:00
-- url     : https://prove2.me/submissions/5c873187-9820-44d5-a053-8c60dd25dde9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz_F
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czFF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz01
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formal_ev_second_point_of_x_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_z_yz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formalGroupLaw_ev_y_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
section Fams
end Fams
private theorem ev_zero_of_CZ {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  simpa using ev_sub ha (0 : PS k m d) 0
private theorem ev_two_identity (f : PS k 2 d) : ev (n := 2) ![pt k d 0, pt k d 1] f = f := by
  have h : (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) = fun j => pt k d j := by
    funext j
    fin_cases j <;> rfl
  rw [h, ev_pt]
private theorem ev_finset_sum_of_CZ {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : Fin d → PS k m d) :
    ev a (∑ c, f c) = ∑ c, ev a (f c) :=
  map_sum (AddMonoidHom.mk' (ev a) (ev_add ha)) f Finset.univ
private theorem ev_zero_one_identity (g : PS k 2 d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) (ev (n := 3) ![pt k d 0, pt k d 1] g) = g := by
  rw [ev_ev czZ cz01]
  have e : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j l)) = (![pt k d 0, pt k d 1] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  rw [e, ev_two_identity]
private theorem pderiv_two_ev (b : Fin d) (g : PS k 2 d) :
    pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] g) =
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) g) := by
  rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pderiv_pt]
private theorem ev_jacobian_left (i b : Fin d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      (pderiv k ((2 : Fin 3), b)
        (ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] (G.F i))) =
      ev (n := 2) ![G.F] (Jac G i b) := by
  have hA : CZ (![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (fun l => constantCoeff_ev cz01 (cz_F G l)) (CZ.cons (cc_pt _) CZ.nil)
  have h0 : ∀ l, pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] (G.F l)) = 0 := fun l =>
    pderiv_ev_zero cz01 _ _ (fun j i => by fin_cases j <;> simp [pderiv_pt])
  have hs : pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] (G.F i)) =
      ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2]
        (pderiv k ((1 : Fin 2), b) (G.F i)) := by
    rw [pderiv_ev hA, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [h0, pderiv_pt]
  have e1 : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] : Fin 2 → Pt k 3 d) j l)) =
      (![G.F, 0] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [ev_zero_one_identity]
    · simp [pt_apply, ev_X czZ]
  have e2 : (fun j l => ev (n := 2) (![G.F] : Fin 1 → Pt k 2 d) ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j l)) =
      (![G.F, 0] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [pt_apply, ev_X (czFF G)]
    · simp [ev_zero_of_CZ (czFF G)]
  rw [hs, ev_ev czZ hA, e1]
  simp only [Jac]
  rw [ev_ev (czFF G) cz1, e2]
private theorem ev_jacobian_right (i b : Fin d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      (pderiv k ((2 : Fin 3), b)
        (ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] (G.F i))) =
      ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  have hB : CZ (![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt _) (CZ.cons (fun l => constantCoeff_ev cz12 (cz_F G l)) CZ.nil)
  have hs : pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] (G.F i)) =
      ∑ c, ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)]
          (pderiv k ((1 : Fin 2), c) (G.F i)) *
        ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := by
    rw [pderiv_ev hB, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [pderiv_pt, pderiv_two_ev]
  have e1 : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] : Fin 2 → Pt k 3 d) j l)) =
      (![pt k d 0, pt k d 1] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [pt_apply, ev_X czZ]
    · simp [ev_z_yz, formalGroupLaw_ev_y_zero, pt_apply]
  rw [hs, ev_finset_sum_of_CZ czZ]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [ev_mul czZ, ev_ev czZ hB, e1, ev_two_identity, ev_z_yz]
  simp only [Ar, Jac, formal_ev_second_point_of_x_zero]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (i b : Fin d) :
    ev (n := 2) ![G.F] (Jac G i b) = ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  rw [← ev_jacobian_left, ← ev_jacobian_right, G.assoc i]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
