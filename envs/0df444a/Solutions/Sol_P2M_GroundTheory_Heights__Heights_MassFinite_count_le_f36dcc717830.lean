-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MassFinite_count_le_f36dcc717830
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:01.696428+00:00
-- url     : https://prove2.me/submissions/95a2fd1d-a9aa-436a-831a-96e9252f8115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite

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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite
namespace GroundTheory.Heights₂.Heights.MassFinite
theorem _root_.solution {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I : Finset (Fin n)) (hI : I.card = d) (S : Set (EuclideanSpace ℂ (Fin n)))
    (hS : S ⊆ zeroSetEuc J) (N : ℕ)
    (hN : ∀ y, (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).Finite ∧
      (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).ncard ≤ N)
    (x : I → ℂ) : frameFibreCount b I S x ≤ N := by
  set e := I.orderIsoOfFin hI
  set A := U.submatrix (I.orderEmbOfFin hI) id
  let y : Fin d → ℂ := fun k => x (e k)
  have hsub : WithLp.ofLp '' {z ∈ S | frameProj b I z = x} ⊆ ComplexSets.fibre J A y := by
    rintro _ ⟨z, ⟨hzS, hzx⟩, rfl⟩
    refine ⟨fun q hq => hS hzS q hq, ?_⟩
    funext k
    have h1 := congrFun hzx (e k)
    simp only [frameProj, hb] at h1
    simp only [y, ← h1, A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id,
      Finset.coe_orderIsoOfFin_apply, e]
  have hinj : Set.InjOn (WithLp.ofLp (p := 2)) {z ∈ S | frameProj b I z = x} :=
    (WithLp.ofLp_injective 2).injOn
  unfold frameFibreCount
  rw [← hinj.encard_image, ← (hN y).1.subset hsub |>.cast_ncard_eq]
  have h2 := Set.ncard_le_ncard hsub (hN y).1
  have h3 := (hN y).2
  exact_mod_cast h2.trans h3
end GroundTheory.Heights₂.Heights.MassFinite
