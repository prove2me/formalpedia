-- Prove2me | solution 1 for WeilConjectures.rationality
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T07:07:31.115987+00:00
-- url     : https://prove2.me/submissions/d57eb252-3621-4127-8185-918346915302

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Devissage
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_FiniteFields_dwork_rationality_explicit
section
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k] [CharP k p]
  {X : Scheme} (f : X ⟶ Spec (.of k))
theorem pointCount_of_neZero (m : ℕ) [NeZero m] :
    pointCount p f m = pointsOver f (FiniteField.Extension k p m) := by
  rw [pointCount, dif_neg (NeZero.ne m)]
theorem pointCount_succ (n : ℕ) :
    pointCount p f (n + 1) = pointsOver f (FiniteField.Extension k p (n + 1)) :=
  pointCount_of_neZero p f (n + 1)
theorem zetaFunction_eq : zetaFunction p f = zetaOfCounts (pointCount p f) := rfl
end WeilConjectures.Bridge
end
end
section
noncomputable section
open PowerSeries
namespace WeilConjectures.Bridge
def zetaLog (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ)
theorem zetaOfCounts_eq (N : ℕ → ℕ) :
    zetaOfCounts N = (PowerSeries.exp ℚ).subst (zetaLog N) := rfl
end WeilConjectures.Bridge
end
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
attribute [local instance] MvPolynomial.gradedAlgebra
section Proper
variable {k : Type} [Field k]
theorem surjective_algebraMap_grade_zero (N : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) := by
  intro x
  have hx : (x : MvPolynomial (Fin (N + 1)) k) ∈ (1 : Submodule k _) := by
    rw [← MvPolynomial.homogeneousSubmodule_zero]
    exact x.2
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hx
  exact ⟨y, Subtype.ext hy⟩
theorem isProper_of_isProjectiveOver {X : Scheme} (f : X ⟶ Spec (.of k))
    (h : IsProjectiveOver k f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.Finite.of_surjective _ (surjective_algebraMap_grade_zero N)
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
      (MvPolynomial (Fin (N + 1)) k) :=
    haveI : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (MvPolynomial (Fin (N + 1)) k) :=
      IsScalarTower.of_algebraMap_eq (R := k)
        (S := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (A := MvPolynomial (Fin (N + 1)) k) fun _ ↦ rfl
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  unfold projectiveSpace.toSpec
  infer_instance
end Proper
end WeilConjectures.Bridge
end
section
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
theorem finiteType_and_isSeparated_of_isProjectiveOver (h : IsProjectiveOver k f) :
    FiniteFields.Schemes.FiniteType f ∧ IsSeparated f := by
  have := isProper_of_isProjectiveOver f h
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
def rationalPointEquiv (K : Type) [Field K] [Algebra k K] :
    FiniteFields.RationalPoint k X f K ≃
      {x : Spec (.of K) ⟶ X // x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} where
  toFun x := ⟨x.hom, x.over_base⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p]
theorem pointCount_succ_eq (n : ℕ)
    [Finite (FiniteFields.ExtensionPoint (k := k) (p := p) X f n)] :
    pointCount p f (n + 1) = FiniteFields.pointCount k p X f n := by
  rw [pointCount_succ, pointsOver, FiniteFields.pointCount]
  exact (Nat.card_congr (rationalPointEquiv f _)).symm
theorem pointCount_succ_eq_of_finiteType (hf : FiniteFields.Schemes.FiniteType f) (n : ℕ) :
    pointCount p f (n + 1) = FiniteFields.pointCount_of_finiteType k p X f hf n := by
  let := hf.1
  let := hf.2
  exact pointCount_succ_eq f p n
theorem zetaLog_eq_dwork (N : ℕ → ℕ) :
    zetaLog N = FiniteFields.Dwork.zetaLog (fun n ↦ N (n + 1)) := by
  ext m
  rw [zetaLog, FiniteFields.Dwork.zetaLog, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rcases m with _ | m
  · simp
  · simp
theorem zetaOfCounts_eq_zetaSeriesOf (N : ℕ → ℕ) :
    zetaOfCounts N = FiniteFields.Dwork.zetaSeriesOf (fun n ↦ N (n + 1)) := by
  rw [zetaOfCounts_eq, zetaLog_eq_dwork]
  rfl
theorem zetaFunction_eq_zetaSeriesOf (hf : FiniteFields.Schemes.FiniteType f) :
    zetaFunction p f = FiniteFields.Dwork.zetaSeriesOf
      (fun n ↦ FiniteFields.pointCount_of_finiteType k p X f hf n) := by
  rw [zetaFunction_eq, zetaOfCounts_eq_zetaSeriesOf]
  congr 1
  funext n
  exact pointCount_succ_eq_of_finiteType f p hf n
theorem rationality_of_presentation (hf : FiniteFields.Schemes.FiniteType f)
    (h : ∃ P Q : Polynomial ℚ, Q.eval 0 = 1 ∧
      (Q : PowerSeries ℚ) * FiniteFields.Dwork.zetaSeriesOf
        (fun n ↦ FiniteFields.pointCount_of_finiteType k p X f hf n) = (P : PowerSeries ℚ)) :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      zetaFunction p f * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
  obtain ⟨P, Q, hQ, hPQ⟩ := h
  refine ⟨P, Q, fun h0 ↦ by simp [h0] at hQ, ?_⟩
  rw [zetaFunction_eq_zetaSeriesOf f p hf, mul_comm, hPQ]
end WeilConjectures.Bridge
end
section
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
theorem rationality_proof (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (hproj : IsProjectiveOver k f) :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      zetaFunction p f * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
  obtain ⟨hf, hsep⟩ := finiteType_and_isSeparated_of_isProjectiveOver f hproj
  obtain ⟨P, Q, hQ, -, -, hPQ⟩ := FiniteFields.dwork_rationality_explicit k p f hf hsep
  exact rationality_of_presentation f p hf ⟨P, Q, hQ, hPQ⟩
end WeilConjectures.Bridge
end
open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures
theorem solution (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (n : ℕ) (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ P Q : ℚ[X], Q ≠ 0 ∧ zetaFunction p f * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) :=
  WeilConjectures.Bridge.rationality_proof p k f hproj
