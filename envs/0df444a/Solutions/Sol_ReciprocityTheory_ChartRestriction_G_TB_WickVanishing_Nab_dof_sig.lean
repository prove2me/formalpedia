-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dof_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:19.904684+00:00
-- url     : https://prove2.me/submissions/aa41accd-b258-4bd0-b073-0053067b985a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_lawK_F
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_sig_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_C


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
theorem _root_.solution {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (u : Fin d → R) (i : Fin d) :
    Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) -
      C (∑ j, sg1 k h i j * algebraMap R k (u j)) ∈ Ig R k (Fin 1 × Fin d) := by
  have e1 : Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) =
      ∑ b, C (algebraMap R k (u b)) * ∑ c, pderiv k ((0 : Fin 1), c) (sgOf k h i) * Jac (lawK k B) c b := by
    simp only [Dof, Jac, lawK_F, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e2 : (C (∑ j, sg1 k h i j * algebraMap R k (u j)) : PS k 1 d) =
      ∑ b, C (algebraMap R k (u b)) * C (sg1 k h i b) := by
    simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine sum_mem fun b _ => ?_
  rw [← mul_sub]
  exact mul_mem (ig_C _) (sig_lin hc i b)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
