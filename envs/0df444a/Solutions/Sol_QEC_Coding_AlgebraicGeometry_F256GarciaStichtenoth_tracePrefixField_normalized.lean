-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.tracePrefixField_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:20:55.9092+00:00
-- url     : https://prove2.me/submissions/94619c10-2aa3-4a11-a789-80054cd3e26b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_tracePrefixField_le_succ
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_in_subfield_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_normalizedLiteralRoot_order


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "P" => IntermediateIntegralModels.prime A F E Q
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (K : IntermediateField F E) (t : ℕ → E) (ht : t 0 ∈ K) (n : ℕ)
    (heq : ∀ j < n, t (j + 1) ^ 2 + t (j + 1) = t j)
    (hzero : (heightOnePlace (k := F256) (K := K) (P K)).order ⟨t 0, ht⟩ = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order ⟨t 0, ht⟩) :
    NormalizedRefinement A F E Q K (tracePrefixField K t n) ∧
      ((heightOnePlace (k := F256) (K := tracePrefixField K t n)
        (P (tracePrefixField K t n))).order
          ⟨t n, tracePrefixField_coordinate_mem K t ht n⟩ = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := tracePrefixField K t n)
          (P (tracePrefixField K t n))).order
            ⟨t n, tracePrefixField_coordinate_mem K t ht n⟩) := by
  induction n with
  | zero => exact ⟨.refl, hzero⟩
  | succ n ih =>
      obtain ⟨hchain, horder⟩ := ih (fun j hj => heq j (by omega))
      let L := tracePrefixField K t n
      let M := tracePrefixField K t (n + 1)
      letI : Fact (L ≤ M) := ⟨tracePrefixField_le_succ K t n⟩
      let a : L := ⟨t n, tracePrefixField_coordinate_mem K t ht n⟩
      let y : M := ⟨t (n + 1), tracePrefixField_coordinate_mem K t ht (n + 1)⟩
      have hy : y ^ 2 + y = algebraMap L M a := by
        apply Subtype.ext
        exact heq n (by omega)
      have hgen : L⟮y⟯ = ⊤ :=
        adjoin_in_subfield_eq_top L M (t (n + 1)) y.property rfl
      have hedge : NormalizedEdge A F E Q L M :=
        ⟨a, t (n + 1), heq n (by omega), horder, rfl⟩
      exact ⟨hchain.tail hedge, normalizedLiteralRoot_order A F E Q a y hy hgen horder⟩
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
