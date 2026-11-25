-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_xz_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:55.516581+00:00
-- url     : https://prove2.me/submissions/f21bc4df-c417-4e2b-9dc1-8accb75b760d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_mul_X_eq_zero

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
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (ψ : PS k 1 d) (j i l : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (X ((0 : Fin 2), l) * rename (eZ d) ψ) =
      if l = j then coeff (single ((0 : Fin 1), i) 1) ψ else 0 := by
  classical
  rw [mul_comm, add_comm]
  by_cases hl : l = j
  · subst hl
    rw [if_pos rfl]
    have e : single ((1 : Fin 2), i) 1 = embDomain (eZ d) (single ((0 : Fin 1), i) 1) := by
      rw [embDomain_single]; rfl
    rw [e]
    show coeff _ (_ * monomial (single ((0 : Fin 2), l) 1) 1) = _
    rw [coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right]
    try rw [mul_one]
    rw [coeff_embDomain_rename]
  · rw [if_neg hl]
    apply coeff_mul_X_eq_zero
    simp [single_apply, Ne.symm hl]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
