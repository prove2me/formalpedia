-- Prove2me | solution 1 for PIW.ENSpec.emb_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:05.004794+00:00
-- url     : https://prove2.me/submissions/ddf4f1af-d6e7-4477-980c-34948659bdbc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))
namespace PIW.ENSpec
theorem _root_.solution (a : ℕ) (x : Fin D → R) (i : Fin D) (h : homogeneousSubmodule (Fin D) R a) :
    emb a ((-x i) • h) = (MvPolynomial.X i - MvPolynomial.C (x i)) • emb a h := by
  apply Subtype.ext
  change (Submodule.Quotient.mk ((-x i) • h.1) : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) =
    (MvPolynomial.X i - MvPolynomial.C (x i)) • Submodule.Quotient.mk h.1
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_C_mul, smul_eq_mul]
  have : MvPolynomial.C (-x i) * h.1 - (MvPolynomial.X i - MvPolynomial.C (x i)) * h.1 =
      -(MvPolynomial.X i * h.1) := by rw [map_neg]; ring
  rw [this, pow_succ']
  exact neg_mem (Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (homog_mem_pow h.2))
end PIW.ENSpec
