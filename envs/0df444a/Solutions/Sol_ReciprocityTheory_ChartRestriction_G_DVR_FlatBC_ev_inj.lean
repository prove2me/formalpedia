-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.ev_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:05.136135+00:00
-- url     : https://prove2.me/submissions/e0e2b670-3e13-444d-b455-29ee76d9a68b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_gs_sec

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution (hcov : ⨆ k, V k = ⊤) {σ τ : LB.Sec L} (h : ev L V c hVc σ = ev L V c hVc τ) : σ = τ := by
  have hf : σ.f = τ.f := by
    funext i
    refine fn_ext fun y hy => ?_
    have : y ∈ (⨆ k, V k : Y.Opens) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    have hk' := congrArg (gs (𝟙 Y) y (V k)) (congrFun h k)
    simp only [ev] at hk'
    rw [gs_res _ y _ hk, gs_res _ y _ hk] at hk'
    rw [gs_sec L σ i (c k) y hy (hVc k hk), gs_sec L τ i (c k) y hy (hVc k hk), hk']
  cases σ; cases τ
  simp only at hf
  subst hf
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
