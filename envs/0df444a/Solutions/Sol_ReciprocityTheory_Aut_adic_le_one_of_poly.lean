-- Prove2me | solution 1 for ReciprocityTheory.Aut.adic_le_one_of_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:40.604103+00:00
-- url     : https://prove2.me/submissions/bd781a80-9536-4121-89a6-14d69cbbb4ea

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace ReciprocityTheory.Aut
theorem _root_.solution {x : v.adicCompletion K} (p : Polynomial ℤ) (hm : p.Monic)
    (hp : p.eval₂ (Int.castRingHom _) x = 0) : Valued.v x ≤ 1 := by
  have hint : IsIntegral (Valued.v : Valuation (v.adicCompletion K) _).integer x := by
    refine ⟨p.map (Int.castRingHom _), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact hp
  have hmem := (Valuation.integer.integers _).mem_of_integral hint
  exact hmem
end ReciprocityTheory.Aut
