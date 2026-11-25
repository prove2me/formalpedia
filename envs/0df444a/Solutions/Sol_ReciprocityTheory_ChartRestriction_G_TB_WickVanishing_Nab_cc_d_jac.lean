-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_d_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:11.940546+00:00
-- url     : https://prove2.me/submissions/d4f03f5a-4278-4803-b392-b5477ce25441

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_zeroFam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
section VF
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]
end VF
section Law
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
private theorem cc_ev_lemma {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have h0 : CZ (fun _ _ => (0 : PS k n d) : Fin n → Pt k n d) := by
    intro j i
    simp
  have h1 := ev_ev (a := (fun _ _ => (0 : PS k n d) : Fin n → Pt k n d)) h0 ha f
  rw [ev_zeroFam] at h1
  have h2 : (fun j i => ev (fun _ _ => (0 : PS k n d)) (a j i)) = fun _ _ => (0 : PS k n d) := by
    funext j i
    rw [ev_zeroFam, ha j i, map_zero]
  rw [h2, ev_zeroFam] at h1
  simpa using congrArg constantCoeff h1
private theorem constantCoeff_pderiv_eq_coeff_single {σ : Type} (p : σ) (f : MvPowerSeries σ k) :
    constantCoeff (pderiv k p f) = coeff (Finsupp.single p 1) f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp
private theorem pderiv_fin_one_ev (g : PS k 2 d) (b : Fin d) :
    pderiv k ((0 : Fin 1), b) (ev (n := 1) ![pt k d 0, 0] g) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), b) g) := by
  rw [pderiv_ev cz1, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]
end Law
section Transfer
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
end Transfer
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (b c i : Fin d) : constantCoeff (pderiv k ((0 : Fin 1), b) (Jac G c i)) =
    coeff (Finsupp.single ((0 : Fin 2), b) 1 + Finsupp.single ((1 : Fin 2), i) 1) (G.F c) := by
  show constantCoeff (pderiv k ((0 : Fin 1), b)
    (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (G.F c)))) = _
  rw [pderiv_fin_one_ev, cc_ev_lemma cz1, constantCoeff_pderiv_eq_coeff_single, MvPowerSeries.coeff_pderiv]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
