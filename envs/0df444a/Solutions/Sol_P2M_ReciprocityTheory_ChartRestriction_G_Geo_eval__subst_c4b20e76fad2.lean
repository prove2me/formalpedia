-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Geo_eval__subst_c4b20e76fad2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:02.306413+00:00
-- url     : https://prove2.me/submissions/b92c308d-d70c-4971-b29e-e7082b19aa63

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (lam : Fin r → k)
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) :
    Polynomial.eval₂ ((aeval (fun i => ℓ i.succ - lam i • ℓ 0) : MvPolynomial (Fin r) k →ₐ[k] R) :
      MvPolynomial (Fin r) k →+* R) (ℓ 0) (subst lam F) =
      aeval ℓ F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp [subst, Polynomial.eval₂_C, Polynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, Polynomial.eval₂_add, hp, hq, map_add]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp, map_mul]
    congr 1
    simp only [subst, aeval_X]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [substFun]
    · simp [substFun, Algebra.smul_def]
end ReciprocityTheory.ChartRestriction.G.Geo
