-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.eval_first_axis_of_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:33.012964+00:00
-- url     : https://prove2.me/submissions/124b3c16-3f35-44b5-8b9e-9437ead3723d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (g : PS k 2 d) (c : Fin d) (hg : ev (n := 1) ![pt k d 0, 0] g = X ((0 : Fin 1), c)) :
    ev (n := 2) ![pt k d 0, 0] g = X ((0 : Fin 2), c) := by
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (X ((0 : Fin 2), q.2) : PS k 2 d)) :=
    by
      first
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by simp)
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun q => by simp)
  have h1 : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin d => (![pt k d 0, 0] : Fin 2 → Pt k 1 d) p.1 p.2) :=
    by
      first
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by rcases p with ⟨i, j⟩; fin_cases i <;> simp [pt])
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => by rcases p with ⟨i, j⟩; fin_cases i <;> simp [pt])
  have key : (fun p : Fin 2 × Fin d => (![pt k d 0, 0] : Fin 2 → Pt k 2 d) p.1 p.2) =
      fun p => MvPowerSeries.subst (fun q : Fin 1 × Fin d => (X ((0 : Fin 2), q.2) : PS k 2 d))
        ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) p.1 p.2) := by
    funext ⟨i, j⟩
    fin_cases i
    · show (X ((0 : Fin 2), j) : PS k 2 d) = MvPowerSeries.subst _ (X ((0 : Fin 1), j) : PS k 1 d)
      rw [MvPowerSeries.subst_X hb]
    · show (0 : PS k 2 d) = MvPowerSeries.subst _ (0 : PS k 1 d)
      rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]
  unfold ev at hg ⊢
  rw [key, ← MvPowerSeries.subst_comp_subst_apply h1 hb, hg, MvPowerSeries.subst_X hb]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
