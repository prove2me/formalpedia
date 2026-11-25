-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.denseRange_finiteAdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:31.532996+00:00
-- url     : https://prove2.me/submissions/e3c9c149-c3e6-43ab-b9d2-3612b2357e79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_nhds_zero_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_exists_approx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_exists_approx_adele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology WithZero Filter
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by
  intro b
  rw [mem_closure_iff_nhds]
  intro N hN
  have h0 : (fun y => b + y) ⁻¹' N ∈ 𝓝 (0 : FiniteAdeleRing R K) := by
    have ht := (continuous_add_left b).tendsto (0 : FiniteAdeleRing R K)
    rw [add_zero] at ht
    exact ht hN
  obtain ⟨r, hr, hrN⟩ := nhds_zero_int h0
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_adele b
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx (b - algebraMap K _ u) hu r hr
  refine ⟨algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a), ?_, ⟨_, rfl⟩⟩
  have hx : algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a) - b =
      -((b - algebraMap K (FiniteAdeleRing R K) u) -
        algebraMap K (FiniteAdeleRing R K) (algebraMap R K a)) := by
    rw [map_add]; ring
  have hmem := hrN (algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a) - b) (by
    rw [hx]
    intro v
    have hv : (-((b - algebraMap K (FiniteAdeleRing R K) u) -
        algebraMap K (FiniteAdeleRing R K) (algebraMap R K a))) v =
        -((b - algebraMap K (FiniteAdeleRing R K) u) v - algebraMap K _ (algebraMap R K a)) := by
      first
      | rfl
      | simp
    rw [hv, Valuation.map_neg]
    exact ha v)
  simpa using hmem
end ReciprocityTheory.ChartRestriction.G.SA
