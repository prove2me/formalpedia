-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.MV.dof_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:34.295727+00:00
-- url     : https://prove2.me/submissions/b86e82f3-bc78-4a72-bbeb-5386cbb1fc92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_MV_ev_zero

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.MV
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.MV
theorem _root_.solution (d : ℕ) (i : Fin d) :
    (Dof (addF k d) (Pi.single i (1 : k)) : PS k 1 d → PS k 1 d) = pderiv k ((0 : Fin 1), i) := by
  classical
  funext f
  have ev1 : ev (n := 1) ![pt k d 0, 0] (1 : PS k 2 d) = 1 := by
    have h := MvPowerSeries.subst_C (a := fun p : Fin 2 × Fin d => (![pt k d 0, 0] : Fin 2 → Pt k 1 d) p.1 p.2) (1 : k)
    rw [map_one, map_one] at h
    exact h
  have ev0 : ev (n := 1) ![pt k d 0, 0] (0 : PS k 2 d) = 0 := ev_zero _
  have hinner : ∀ j : Fin d, (∑ i' : Fin d, MvPowerSeries.C ((Pi.single i (1 : k) : Fin d → k) i') *
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i') (addF k d j))) =
      if j = i then 1 else 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · have hd : pderiv k ((1 : Fin 2), j) (addF k d j) = 1 := by
        simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply]
      rw [hd, ev1, mul_one]
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_apply, hji]
    · intro b _ hb
      have hd : pderiv k ((1 : Fin 2), b) (addF k d j) = 0 := by
        simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply, Ne.symm hb]
      rw [hd, ev0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hD : Dof (addF k d) (Pi.single i (1 : k)) f =
      ∑ j, (if j = i then (1 : PS k 1 d) else 0) * pderiv k ((0 : Fin 1), j) f := by
    simp only [Dof, hinner]
  rw [hD]
  simp [ite_mul, Finset.sum_ite_eq']
end ReciprocityTheory.ChartRestriction.G.TB.MV
