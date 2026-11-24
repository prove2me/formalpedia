-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DominantFibreBound_exists_poly_0a4987dfdbda
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:22.588819+00:00
-- url     : https://prove2.me/submissions/2da73267-2095-4ac6-8121-cbd3b4394ff3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantFibreBound_trdeg_le_5ed0a4f11660

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DominantFibreBound
theorem _root_.solution (hG : ComplexSets.GenericProjectionFinite.Statement) {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (hP : P.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)))
    (b : MvPolynomial (Fin n) ℂ ⧸ P) :
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧
      (g.map (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom).eval b = 0 := by
  obtain ⟨A, hA⟩ := (hG n d P hP hdim).2.1
  set q : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (p i) with hq_def
  have hind : AlgebraicIndependent ℂ q := by
    rw [algebraicIndependent_iff_injective_aeval]
    rw [comp_aeval] at hinj
    exact hinj
  have hbasis : IsTranscendenceBasis ℂ q :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (DominantFibreBound.trdeg_le P A hA)
  obtain ⟨f, hf0, hfb⟩ := hbasis.isAlgebraic.isAlgebraic b
  refine ⟨f.map (hind.aevalEquiv.symm : Algebra.adjoin ℂ (Set.range q) →+* MvPolynomial (Fin d) ℂ),
    (Polynomial.map_ne_zero_iff hind.aevalEquiv.symm.injective).2 hf0, ?_⟩
  rw [Polynomial.map_map, ← hfb, Polynomial.aeval_def, Polynomial.eval_map]
  congr 1
  ext y
  simp [← hind.algebraMap_aevalEquiv]
end DominantFibreBound
end GroundTheory.Heights₂.Heights
