-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:08:52.958239+00:00
-- url     : https://prove2.me/submissions/d284a111-634b-4034-ad88-edc4d91e7d3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_gs_dfun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_glue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution (hL : L.IsLB) (hcov : ⨆ k, V k = ⊤) (f : ∀ k, Γ(Y, V k)) (hf : dfun L V c hVc f = 0) :
    ∃ σ : LB.Sec L, ev L V c hVc σ = f := by
  classical
  have hcovi : ∀ i, L.U i ≤ ⨆ k, L.U i ⊓ V k := fun i y hy => by
    have : y ∈ (⨆ k, V k : Y.Opens) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  have hle : ∀ i k, L.U i ⊓ V k ≤ L.U i ⊓ L.U (c k) := fun i k => inf_le_inf le_rfl (hVc k)
  let cand : ∀ i k, Γ(Y, L.U i ⊓ V k) := fun i k =>
    (res (hle i k) (L.g i (c k))).val * rs inf_le_right (f k)
  have gcand : ∀ i k y (hy : y ∈ L.U i ⊓ V k), gs (𝟙 Y) y _ (cand i k) =
      (gm (𝟙 Y) y (L.U i ⊓ L.U (c k)) (L.g i (c k))).val * gs (𝟙 Y) y (V k) (f k) := fun i k y hy => by
    simp only [cand]
    rw [gs_mul _ y _ hy, gs_unit _ y _ hy, gm_res _ y _ hy, gs_res _ y _ hy]
  have hcompat : ∀ i k l, rs (inf_le_left : (L.U i ⊓ V k) ⊓ (L.U i ⊓ V l) ≤ _) (cand i k) =
      rs (inf_le_right : (L.U i ⊓ V k) ⊓ (L.U i ⊓ V l) ≤ _) (cand i l) := fun i k l => fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_res _ y _ hy, gcand i k y hy.1, gcand i l y hy.2,
      gs_dfun L V c hVc hf k l y hy.1.2 hy.2.2, ← mul_assoc, ← Units.val_mul,
      gm_cocycle hL (𝟙 Y) y (i := i) (j := c k) (k := c l) hy.1.1 (hVc k hy.1.2) (hVc l hy.2.2)]
  choose F hF _ using fun i => sec_glue (L.U i) (fun k => L.U i ⊓ V k) (fun _ => inf_le_left) (hcovi i)
    (cand i) (hcompat i)
  have gF : ∀ i k y (hyi : y ∈ L.U i) (hyk : y ∈ V k), gs (𝟙 Y) y (L.U i) (F i) =
      (gm (𝟙 Y) y (L.U i ⊓ L.U (c k)) (L.g i (c k))).val * gs (𝟙 Y) y (V k) (f k) := fun i k y hyi hyk => by
    have hyik : y ∈ L.U i ⊓ V k := ⟨hyi, hyk⟩
    have e := congrArg (gs (𝟙 Y) y (L.U i ⊓ V k)) (hF i k)
    rw [gs_res _ y _ hyik] at e
    rw [e, gcand i k y hyik]
  have hmemV : ∀ y : Y, ∃ k, y ∈ V k := fun y => by
    have : y ∈ (⨆ k, V k : Y.Opens) := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨⟨F, fun i j => fn_ext fun y hy => ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := hmemV y
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gF i k y hy.1 hk, gF j k y hy.2 hk,
      ← mul_assoc, ← Units.val_mul, gm_cocycle hL (𝟙 Y) y (i := i) (j := j) (k := c k) hy.1 hy.2 (hVc k hk)]
  · funext k
    refine fn_ext fun y hy => ?_
    show gs (𝟙 Y) y (V k) (rs (hVc k) (F (c k))) = _
    rw [gs_res _ y _ hy, gF (c k) k y (hVc k hy) hy, gm_self hL (𝟙 Y) y (hVc k hy), Units.val_one, one_mul]
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
