-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCenteredEuclideanHeckeOperator_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:01:21.827751+00:00
-- url     : https://prove2.me/submissions/177932f7-3cf3-4d85-8b39-001c4e0bc0cb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_centeredAdjacencyEuclidean_rightCayleyGraph_eq_conj


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredEuclideanHeckeOperator a n =
      (cayleyEuclideanLinearEquiv (G := PSL(2, ZMod a.q))).conj
        (lpsCenteredHeckeOperator a n) := by
  rw [lpsCenteredEuclideanHeckeOperator,
    centeredAdjacencyEuclidean_rightCayleyGraph_eq_conj]
  unfold lpsCenteredHeckeOperator
  symm
  change (cayleyEuclideanLinearEquiv
      (G := PSL(2, ZMod a.q))).conjRingEquiv
        ((lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
          (algebraMap ℂ (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
          (cayleyRightRegularRepresentation.asAlgebraHom
            (cayleyCenteredGeneratorSum (lpsQuaternionLabel a)))) = _
  have hAlg :
      (cayleyEuclideanLinearEquiv
          (G := PSL(2, ZMod a.q))).conjRingEquiv.toRingHom.comp
          (algebraMap ℂ
            (Module.End ℂ (PSL(2, ZMod a.q) → ℂ))) =
        algebraMap ℂ
          (Module.End ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))) := by
    ext c f
    rfl
  have h :=
    Polynomial.hom_eval₂
      (p := lpsHeckePolynomial ℂ (p : ℂ) n)
      (algebraMap ℂ
        (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
      (cayleyEuclideanLinearEquiv
        (G := PSL(2, ZMod a.q))).conjRingEquiv.toRingHom
      (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum (lpsQuaternionLabel a)))
  rw [hAlg] at h
  exact h
end QEC.Coding.TannerLiftedProduct
