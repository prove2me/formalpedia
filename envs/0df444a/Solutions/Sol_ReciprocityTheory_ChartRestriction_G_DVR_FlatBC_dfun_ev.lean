-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.dfun_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:57.099129+00:00
-- url     : https://prove2.me/submissions/ebb25423-2567-43a0-b72f-79ff160dafba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_units


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
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {Y : Scheme.{0}} (L : LB Y) {n : ℕ} (V : Fin n → Y.Opens) (c : Fin n → L.ι) (hVc : ∀ k, V k ≤ L.U (c k))
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution (σ : LB.Sec L) : dfun L V c hVc (ev L V c hVc σ) = 0 := by
  funext k l
  have e := congrArg (rs (pair_le L V c hVc k l)) (σ.compat (c k) (c l))
  simp only [rs_mul, rs_rs, rs_units] at e
  simp only [dfun, ev, rs_rs, Pi.zero_apply]
  rw [sub_eq_zero]
  exact e
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
