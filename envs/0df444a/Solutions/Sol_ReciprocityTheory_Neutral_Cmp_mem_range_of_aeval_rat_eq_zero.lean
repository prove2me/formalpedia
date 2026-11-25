-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.mem_range_of_aeval_rat_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:15.135807+00:00
-- url     : https://prove2.me/submissions/4f60431b-740d-428b-9970-b4b008187d1a

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] {g : Polynomial ℚ} (hg : g ≠ 0)
    {b : PadicAlgCl p} (hb : Polynomial.aeval b g = 0) : b ∈ ι.range := by
  classical
  haveI : CharZero Ω := RingHom.charZero ι
  have hmap : (g.map (algebraMap ℚ Ω)).map ι = g.map (algebraMap ℚ (PadicAlgCl p)) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hroot : ((g.map (algebraMap ℚ Ω)).map ι).IsRoot b := by
    rw [hmap, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hb
  exact Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits _) (Polynomial.map_ne_zero hg) hroot
end ReciprocityTheory.Neutral.Cmp
