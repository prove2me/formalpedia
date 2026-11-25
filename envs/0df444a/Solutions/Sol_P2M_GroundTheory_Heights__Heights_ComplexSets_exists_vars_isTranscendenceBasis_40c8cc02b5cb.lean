-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_exists_vars_isTranscendenceBasis_40c8cc02b5cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:38.764548+00:00
-- url     : https://prove2.me/submissions/c216319c-1e38-45f1-b9e8-9f84515e3bc4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime] :
    ∃ u : Set (Fin n), AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk P (X (i : Fin n))) ∧
      Cardinal.mk u = Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set x : Fin n → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (X i) with hx
  have hrange : Set.range x = Ideal.Quotient.mkₐ ℂ P '' Set.range X := by
    rw [← Set.range_comp]; rfl
  have hadj : Algebra.adjoin ℂ (Set.range x) = ⊤ := by
    rw [hrange, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℂ P
  have _ : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range x)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    ⟨fun a => isAlgebraic_algebraMap (R := Algebra.adjoin ℂ (Set.range x))
      (⟨a, hadj ▸ Algebra.mem_top⟩ : Algebra.adjoin ℂ (Set.range x))⟩
  have _ := (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Fin n) ℂ ⧸ P)).mpr
    (algebraMap ℂ _).injective
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range x)
  obtain ⟨u, hu, hinj⟩ := Set.exists_image_eq_injOn_of_subset_range hts
  let g : u → t := fun i => ⟨x i, hu ▸ Set.mem_image_of_mem x i.2⟩
  have hg : Function.Injective g := fun i j hij =>
    Subtype.ext (hinj i.2 j.2 (congrArg Subtype.val hij))
  refine ⟨u, ht.1.comp g hg, ?_⟩
  rw [← ht.cardinalMk_eq_trdeg, ← hu, Cardinal.mk_image_eq_of_injOn _ _ hinj]
end GroundTheory.Heights₂.Heights.ComplexSets
