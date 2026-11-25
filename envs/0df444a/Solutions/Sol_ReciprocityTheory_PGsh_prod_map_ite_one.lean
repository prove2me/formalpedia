-- Prove2me | solution 1 for ReciprocityTheory.PGsh.prod_map_ite_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:36.651862+00:00
-- url     : https://prove2.me/submissions/b108c9a5-afb8-4d98-8058-e81f1e0c96a1

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {M ι : Type*} [Monoid M] (l : List ι) (p : ι → Prop) [DecidablePred p]
    (d : ι → M) :
    (l.map fun j => if p j then d j else 1).prod = ((l.filter fun j => p j).map d).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]
end ReciprocityTheory.PGsh
