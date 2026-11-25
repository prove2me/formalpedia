-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_xz_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:02.569001+00:00
-- url     : https://prove2.me/submissions/728aa915-6cc7-4e6a-bc43-e0c387727b8d

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
theorem _root_.solution (φ : PS k 1 d) (j i m : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (rename (eXv d) φ * X ((1 : Fin 2), m)) =
      if m = i then coeff (single ((0 : Fin 1), j) 1) φ else 0 := by
  classical
  by_cases hm : m = i
  · subst hm
    rw [if_pos rfl]
    have e : single ((0 : Fin 2), j) 1 = embDomain (eXv d) (single ((0 : Fin 1), j) 1) := by
      rw [embDomain_single]; rfl
    rw [e]
    show coeff _ (_ * monomial (single ((1 : Fin 2), m) 1) 1) = _
    rw [coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right]
    try rw [mul_one]
    rw [coeff_embDomain_rename]
  · rw [if_neg hm]
    apply coeff_mul_X_eq_zero
    simp [single_apply, Ne.symm hm]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
