-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.isInt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:09.711803+00:00
-- url     : https://prove2.me/submissions/78dbc658-ad93-4461-a8ca-ba1b25a0e18f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
theorem _root_.solution {a b : FiniteAdeleRing R K} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  intro v
  first
  | exact mul_mem (ha v) (hb v)
  | simpa using mul_mem (ha v) (hb v)
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
