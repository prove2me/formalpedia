-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:04.306258+00:00
-- url     : https://prove2.me/submissions/90703bea-eb7e-45c7-8fd7-f192cab7e8e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_subst_killCompl

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (h : PS k 2 d) (x : Fin 1 × Fin d →₀ ℕ) :
    coeff x (ev (n := 1) ![0, pt k d 0] h) = coeff (embDomain (eZ d) x) h := by
  have hnr : ∀ i : Fin d, ((0 : Fin 2), i) ∉ Set.range (eZ d) := by
    rintro i ⟨⟨c, j⟩, hc⟩
    have h10 : (1 : Fin 2) = 0 := congrArg Prod.fst hc
    exact absurd h10 (by decide)
  apply coeff_subst_killCompl (eZ d) h
  rintro ⟨b, i⟩
  fin_cases b
  · show (0 : PS k 1 d) = killCompl (eZ d) (X ((0 : Fin 2), i))
    ext m
    rw [coeff_killCompl, coeff_X, if_neg]
    · simp
    · intro hm
      have h1 := congrArg (fun g => g ((0 : Fin 2), i)) hm
      rw [Finsupp.embDomain_notin_range _ _ _ (hnr i), Finsupp.single_eq_same] at h1
      exact zero_ne_one h1
  · show X ((0 : Fin 1), i) = killCompl (eZ d) (X ((1 : Fin 2), i))
    exact (killCompl_X (e := eZ d) ((0 : Fin 1), i)).symm
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
