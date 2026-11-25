-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.om_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:42.202844+00:00
-- url     : https://prove2.me/submissions/e0d2f3bf-4ce4-456d-a1d7-96cf3746f38d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_om_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_om_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_d_evF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ez_F
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ez_dx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ez_dy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
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
private theorem CZ_pt_vector : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := by
  intro j i
  fin_cases j <;> simp [pt]
private theorem mvPowerSeries_pderiv_comm {σ : Type} (i j : σ) (f : MvPowerSeries σ k) :
    pderiv k i (pderiv k j f) = pderiv k j (pderiv k i f) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
    MvPowerSeries.coeff_pderiv]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [add_right_comm n (Finsupp.single i 1) (Finsupp.single j 1)]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg hij, if_neg (Ne.symm hij), add_zero]
    ring
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
theorem _root_.solution (i a b : Fin d) :
    ∑ j, Jac G j b * pderiv k ((0 : Fin 1), a) (Om G i j) = ∑ c, pderiv k ((0 : Fin 1), c) (Om G i a) * Jac G c b := by
  have hE := CZ_pt_vector (k := k) (d := d)
  let fE : PS k 2 d →+* PS k 1 d :=
    { toFun := ev (n := 1) ![pt k d 0, 0]
      map_one' := by simpa using ev_C hE (1 : k)
      map_mul' := ev_mul hE
      map_zero' := by simpa using ev_C hE (0 : k)
      map_add' := ev_add hE }
  have hsE : ∀ g : Fin d → PS k 2 d,
      ev (n := 1) ![pt k d 0, 0] (∑ j, g j) = ∑ j, ev (n := 1) ![pt k d 0, 0] (g j) :=
    fun g => map_sum fE g Finset.univ
  have hz0 : ev (n := 1) ![pt k d 0, 0] (0 : PS k 2 d) = 0 := map_zero fE
  have hdJ : ∀ j, pderiv k ((0 : Fin 1), a) (Jac G j b) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (pderiv k ((1 : Fin 2), b) (G.F j))) := by
    intro j
    show pderiv k ((0 : Fin 1), a) (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F j))) = _
    rw [pderiv_ev hE, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply]
  have hR : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] (Om G i a)) = 0 := by
    rw [pderiv_ev czX, Fintype.sum_prod_type]
    simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply]
  have hP := congrArg (⇑(pderiv k ((1 : Fin 2), b))) (om_P G i a)
  rw [hR, map_sum] at hP
  simp only [Derivation.leibniz, smul_eq_mul, d_evF] at hP
  have hP2 := congrArg (ev (n := 1) ![pt k d 0, 0]) hP
  simp only [hsE, hz0, ev_mul hE, ev_add hE, ez_F, ez_dx, ez_dy,
    mvPowerSeries_pderiv_comm ((1 : Fin 2), b) ((0 : Fin 2), a), ← hdJ] at hP2
  rw [Finset.sum_add_distrib] at hP2
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hP2
  have hM := congrFun (congrFun (om_mul G) i) b
  rw [Matrix.mul_apply] at hM
  simp only [JM, Matrix.of_apply] at hM
  have hM2 := congrArg (⇑(pderiv k ((0 : Fin 1), a))) hM
  have hone : pderiv k ((0 : Fin 1), a) ((1 : Matrix (Fin d) (Fin d) (PS k 1 d)) i b) = 0 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [hone, map_sum] at hM2
  simp only [Derivation.leibniz, smul_eq_mul] at hM2
  rw [Finset.sum_add_distrib] at hM2
  linear_combination hM2 - hP2
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
