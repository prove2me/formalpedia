-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actP_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:02.821918+00:00
-- url     : https://prove2.me/submissions/2c8ca41f-52da-4121-a2a1-342407153e80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gauge_stable


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) {n : ℕ}
    (b : Fin n → O) (a : Fin n → R) {ξ : (Fin d → k) × (Fin d → k)} (hξ : ξ ∈ Hset (R := R) k h) :
    actP B b (fun i => algebraMap R k (a i)) ξ ∈ Hset (R := R) k h := by
  rw [actP_eq_sum]
  have hmem : ∀ i, OactH k B (b i) ξ ∈ Hset (R := R) k h := fun i =>
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gauge_stable R d O k hRQ B h hc (b i) ξ hξ
  choose u φ hu using hmem
  refine ⟨∑ i, a i • u i, ∑ i, a i • φ i, ?_⟩
  have hvec : (fun j => algebraMap R k ((∑ i, a i • u i) j)) =
      ∑ i, algebraMap R k (a i) • fun j => algebraMap R k (u i j) := by
    funext j
    simp [Finset.sum_apply, map_sum, map_mul, smul_eq_mul, Algebra.smul_def]
  simp_rw [hu]
  refine Prod.ext ?_ ?_
  · funext j
    simp [Prod.fst_sum, Finset.sum_apply, map_sum, map_mul, smul_eq_mul, Algebra.smul_def]
  · rw [hvec, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    funext j
    simp [Prod.snd_sum, Finset.sum_apply, map_sum, map_mul, smul_eq_mul, Matrix.mulVec_smul, mul_sub,
      Finset.sum_sub_distrib, Algebra.smul_def]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
