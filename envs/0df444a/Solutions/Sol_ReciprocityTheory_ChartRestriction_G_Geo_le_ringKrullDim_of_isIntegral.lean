-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.le_ringKrullDim_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:11:45.834075+00:00
-- url     : https://prove2.me/submissions/0095a520-a51b-454f-84d7-d6458c14196a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_ltSeries_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) (hinj : Function.Injective f) (n : ℕ)
    (h : (n : WithBot ℕ∞) ≤ ringKrullDim R) : (n : WithBot ℕ∞) ≤ ringKrullDim S := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h
  obtain ⟨q, hq, -⟩ := exists_ltSeries_lift hinj n p hp
  exact Order.le_krullDim_iff.mpr ⟨q, hq⟩
end ReciprocityTheory.ChartRestriction.G.Geo
