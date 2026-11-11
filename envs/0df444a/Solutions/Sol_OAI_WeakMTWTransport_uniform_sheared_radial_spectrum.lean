-- Prove2me | solution 1 for OAI.WeakMTWTransport.uniform_sheared_radial_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:20.345531+00:00
-- url     : https://prove2.me/submissions/e3de90e5-4026-40be-bfb1-ba08796772c3

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A020
import Definitions.Def_OAIQ232A029
import Theorems.Thm_OAI_WeakMTWTransport_uniform_endpoint_middle_singular_comparison
import Theorems.Thm_OAI_WeakMTWTransport_uniform_join_exp_ordered_comparison
import Theorems.Thm_OAI_WeakMTWTransport_uniform_radial_Schur_background

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MinMax
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section MinMax
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma paired_basis_slice {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    ∃ v : E, v ≠ 0 ∧ (∀ j : Fin n, i < j → a.repr v j = 0) ∧
      (∀ j : Fin n, j < i → b.repr v j = 0) :=  by
  classical
  let f : Fin (i.val+1) → Fin n :=  fun j  => ⟨j.val,by omega⟩
  have hf : Function.Injective f :=  by
    intro j k h
    apply Fin.ext
    simpa only [f] using congrArg (fun z : Fin n => z.val) h
  let V :=  Submodule.span ℝ (range (fun j : Fin (i.val+1)  => a (f j)))
  have hdim : Module.finrank ℝ V = i.val+1 :=  by
    exact (finrank_span_eq_card (a.toBasis.linearIndependent.comp f hf)).trans (Fintype.card_fin _)
  let L : V →ₗ[ℝ] (Fin i.val → ℝ) :=
    { toFun :=  fun v j  => b.repr v ⟨j.val,lt_trans j.isLt i.isLt⟩
      map_add' :=  by intros; ext j; simp
      map_smul' :=  by intros; ext j; simp }
  have hk :=  LinearMap.ker_ne_bot_of_finrank_lt (f :=  L) (by
    rw [hdim,Module.finrank_pi,Fintype.card_fin]; omega)
  obtain ⟨v,hv,hv0⟩ :=  (Submodule.ne_bot_iff _).mp hk
  have hvE : (v:E) ≠ 0 :=  by
    intro h
    exact hv0 (Subtype.ext h)
  refine ⟨v,hvE,?_,?_⟩
  · intro j hj
    have H : ∀ w∈V, a.repr w j = 0 :=  by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw  =>
          obtain ⟨k,rfl⟩ :=  hw
          have hne : f k ≠ j :=  by intro h; have :=  congrArg Fin.val h; dsimp [f] at this; omega
          simp [Ne.symm hne]
      | zero  => simp
      | add x y hx hy ihx ihy  => simp [ihx,ihy]
      | smul c x hx ih  => simp [ih]
    exact H v v.property
  · intro j hj
    have H :=  congrFun (show L v = 0 from hv) (⟨j.val,hj⟩ : Fin i.val)
    exact H

lemma eigenvalue_quadratic_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (v : E) :
    inner ℝ (A v) v = ∑ j, hA.eigenvalues hn j*((hA.eigenvectorBasis hn).repr v j)^2 :=  by
  have H :=  (hA.eigenvectorBasis hn).repr.inner_map_map (A v) v
  rw [←H,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.inner_apply,conj_trivial,RCLike.ofReal_real_eq_id,id_eq]
  ring

omit [FiniteDimensional ℝ E] in
lemma eigenbasis_norm_expansion {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (v : E) :
    ‖v‖^2 = ∑ j, (b.repr v j)^2 :=  by
  rw [←b.repr.norm_map v,EuclideanSpace.real_norm_sq_eq]

lemma ordered_eigenvalue_quadratic_comparison {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ v, inner ℝ (A v) v ≤ a*inner ℝ (B v) v+b*‖v‖^2)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    hA.eigenvalues hn i ≤ a*hB.eigenvalues hn i+b :=  by
  obtain ⟨v,hv,hav,hbv⟩ :=  paired_basis_slice (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn) i
  have hAv : hA.eigenvalues hn i*‖v‖^2 ≤ inner ℝ (A v) v :=  by
    rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hji) (sq_nonneg _)
    · rw [hav j (lt_of_not_ge hji)]; simp
  have hBv : inner ℝ (B v) v ≤ hB.eigenvalues hn i*‖v‖^2 :=  by
    rw [eigenvalue_quadratic_expansion hB hn,eigenbasis_norm_expansion (hB.eigenvectorBasis hn),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hB.eigenvalues_antitone hn hij) (sq_nonneg _)
    · rw [hbv j (lt_of_not_ge hij)]; simp
  have H := h v
  have Hmul := mul_le_mul_of_nonneg_left hBv ha
  have hpos : 0 < ‖v‖^2 :=  sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  nlinarith

end MinMax
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormMinMax
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section NormMinMax
variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ F] in
lemma paired_basis_slice_map {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : OrthonormalBasis (Fin n) ℝ F) (K : E →ₗ[ℝ] F) (i : Fin n) :
    ∃ v : E, v ≠ 0 ∧ (∀ j : Fin n, i < j → a.repr v j = 0) ∧
      (∀ j : Fin n, j < i → b.repr (K v) j = 0) :=  by
  classical
  let f : Fin (i.val+1) → Fin n :=  fun j  => ⟨j.val,by omega⟩
  have hf : Function.Injective f :=  by
    intro j k h
    apply Fin.ext
    simpa only [f] using congrArg (fun z : Fin n => z.val) h
  let V :=  Submodule.span ℝ (range (fun j : Fin (i.val+1)  => a (f j)))
  have hdim : Module.finrank ℝ V = i.val+1 :=  by
    exact (finrank_span_eq_card (a.toBasis.linearIndependent.comp f hf)).trans (Fintype.card_fin _)
  let L : V →ₗ[ℝ] (Fin i.val → ℝ) :=
    { toFun :=  fun v j  => b.repr (K v) ⟨j.val,lt_trans j.isLt i.isLt⟩
      map_add' :=  by intros; ext j; simp
      map_smul' :=  by intros; ext j; simp }
  have hk :=  LinearMap.ker_ne_bot_of_finrank_lt (f :=  L) (by
    rw [hdim,Module.finrank_pi,Fintype.card_fin]; omega)
  obtain ⟨v,hv,hv0⟩ :=  (Submodule.ne_bot_iff _).mp hk
  have hvE : (v:E) ≠ 0 :=  by
    intro h
    exact hv0 (Subtype.ext h)
  refine ⟨v,hvE,?_,?_⟩
  · intro j hj
    have H : ∀ w∈V, a.repr w j = 0 :=  by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw  =>
          obtain ⟨k,rfl⟩ :=  hw
          have hne : f k ≠ j :=  by intro h; have :=  congrArg Fin.val h; dsimp [f] at this; omega
          simp [Ne.symm hne]
      | zero  => simp
      | add x y hx hy ihx ihy  => simp [ihx,ihy]
      | smul c x hx ih  => simp [ih]
    exact H v v.property
  · intro j hj
    have H :=  congrFun (show L v = 0 from hv) (⟨j.val,hj⟩ : Fin i.val)
    exact H

lemma quadratic_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, i < j → (hA.eigenvectorBasis hn).repr v j = 0) :
    hA.eigenvalues hn i * ‖v‖^2 ≤ inner ℝ (A v) v := by
  rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hji) (sq_nonneg _)
  · rw [hv j (lt_of_not_ge hji)]; simp

lemma quadratic_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, j < i → (hA.eigenvectorBasis hn).repr v j = 0) :
    inner ℝ (A v) v ≤ hA.eigenvalues hn i * ‖v‖^2 := by
  rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hij) (sq_nonneg _)
  · rw [hv j (lt_of_not_ge hij)]; simp

lemma ordered_eigenvalue_pullback_comparison {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
    (hA : A.IsSymmetric) (hB : B.IsPositive) (K : E →ₗ[ℝ] F)
    {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hK : ∀ v, ‖K v‖ ≤ c * ‖v‖)
    (h : ∀ v, inner ℝ (A v) v ≤ a * inner ℝ (B (K v)) (K v) + b * ‖v‖^2)
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
    hA.eigenvalues hnE i ≤ a * c^2 * hB.isSymmetric.eigenvalues hnF i + b := by
  obtain ⟨v,hv,hav,hbv⟩ := paired_basis_slice_map (hA.eigenvectorBasis hnE)
    (hB.isSymmetric.eigenvectorBasis hnF) K i
  have hAv := quadratic_lower_spectral_slice hA hnE i v hav
  have hBv := quadratic_upper_spectral_slice hB.isSymmetric hnF i (K v) hbv
  have hBp := hB.nonneg_eigenvalues hnF i
  have hnorm := sq_le_sq₀ (norm_nonneg (K v)) (mul_nonneg hc (norm_nonneg v)) |>.mpr (hK v)
  have hmul := mul_le_mul_of_nonneg_left hnorm hBp
  have hmul' := mul_le_mul_of_nonneg_left (hBv.trans hmul) ha
  have hpos : 0 < ‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  have H := h v
  nlinarith

lemma ordered_singularValues_pullback {A : E →ₗ[ℝ] G} {B : F →ₗ[ℝ] H}
    (K : E →ₗ[ℝ] F) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hK : ∀ v, ‖K v‖ ≤ c * ‖v‖) (h : ∀ v, ‖A v‖ ≤ a * ‖B (K v)‖)
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n)
    (i : Fin n) : A.singularValues i ≤ a * c * B.singularValues i := by
  have H := ordered_eigenvalue_pullback_comparison A.isSymmetric_adjoint_comp_self
    B.isPositive_adjoint_comp_self K (sq_nonneg a) hc hK (b := 0) (fun v => by
      simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq,
        zero_mul,add_zero]
      nlinarith [h v,norm_nonneg (A v),norm_nonneg (B (K v))]) hnE hnF i
  rw [←A.sq_singularValues_fin hnE,←B.sq_singularValues_fin hnF] at H
  have hAp := A.singularValues_nonneg i
  have hBp := B.singularValues_nonneg i
  have hprod := mul_nonneg (mul_nonneg ha hc) hBp
  nlinarith

end NormMinMax
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveSingular
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace WeakMTWTransport
section PositiveSingular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma eigenbasis_operator_norm_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (v : E) :
    ‖A v‖^2 = ∑ j, (hA.eigenvalues hn j)^2*((hA.eigenvectorBasis hn).repr v j)^2 := by
  rw [eigenbasis_norm_expansion (hA.eigenvectorBasis hn)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id,id_eq,mul_pow]

lemma positive_norm_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, i < j → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    (hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2≤‖A v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn i)
      (hA.isSymmetric.eigenvalues_antitone hn hji) 2
  · rw [hv j (lt_of_not_ge hji)]; simp

lemma positive_norm_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, j < i → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    ‖A v‖^2≤(hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn j)
      (hA.isSymmetric.eigenvalues_antitone hn hij) 2
  · rw [hv j (lt_of_not_ge hij)]; simp

lemma positive_singularValues_eq_eigenvalues {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    A.singularValues i=hA.isSymmetric.eigenvalues hn i := by
  have hG := A.isSymmetric_adjoint_comp_self
  have hApos := hA.nonneg_eigenvalues hn i
  have hspos := A.singularValues_nonneg i
  apply le_antisymm
  · obtain ⟨v,hv,hgv,hav⟩ := paired_basis_slice (hG.eigenvectorBasis hn)
      (hA.isSymmetric.eigenvectorBasis hn) i
    have h1 := quadratic_lower_spectral_slice hG hn i v hgv
    have h2 := positive_norm_upper_spectral_slice hA hn i v hav
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h1
    rw [←A.sq_singularValues_fin hn] at h1
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith
  · obtain ⟨v,hv,hav,hgv⟩ := paired_basis_slice (hA.isSymmetric.eigenvectorBasis hn)
      (hG.eigenvectorBasis hn) i
    have h1 := positive_norm_lower_spectral_slice hA hn i v hav
    have h2 := quadratic_upper_spectral_slice hG hn i v hgv
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h2
    rw [←A.sq_singularValues_fin hn] at h2
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith

end PositiveSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SpectralContinuity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Filter
open scoped Topology

namespace WeakMTWTransport
section SpectralContinuity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ordered_eigenvalues_positive_crossing {A B : E →L[ℝ] E}
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {c C : ℝ}
    (h : ∀ v, c*‖v‖^2 ≤ inner ℝ (B v) v-inner ℝ (A v) v ∧
      inner ℝ (B v) v-inner ℝ (A v) v ≤ C*‖v‖^2)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    hA.eigenvalues hn i+c ≤ hB.eigenvalues hn i ∧
      hB.eigenvalues hn i ≤ hA.eigenvalues hn i+C := by
  have H1 := ordered_eigenvalue_quadratic_comparison hA hB (a := 1) (b := -c)
    (by norm_num) (fun v => by have := (h v).1; change inner ℝ (A v) v ≤ 1*inner ℝ (B v) v+(-c)*‖v‖^2; linarith) hn i
  have H2 := ordered_eigenvalue_quadratic_comparison hB hA (a := 1) (b := C)
    (by norm_num) (fun v => by have := (h v).2; change inner ℝ (B v) v ≤ 1*inner ℝ (A v) v+C*‖v‖^2; linarith) hn i
  constructor <;> linarith

end SpectralContinuity
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_5
lemma uniform_middle_ordered_crossing :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      ∀ hz : z.2 ∈ minimizingVectors z.1, ∀ δ : ℝ, ∀ hd : 0 ≤ δ, ∀ hdhalf : δ ≤ 1/2,
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) (sprayFlow (1/4) z).1)),
      (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
        (show (0:ℝ) ≤ 1/2 by norm_num)).isSymmetric.eigenvalues rfl i + c*δ ≤
        (shortened_middle_operator_positive hz hd hdhalf).isSymmetric.eigenvalues rfl i ∧
      (shortened_middle_operator_positive hz hd hdhalf).isSymmetric.eigenvalues rfl i ≤
        (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
          (show (0:ℝ) ≤ 1/2 by norm_num)).isSymmetric.eigenvalues rfl i + C*δ := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middleHessian_crossing (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd hdhalf i
  apply ordered_eigenvalues_positive_crossing
  intro v
  simpa only [inner_middleHessianOperator,sub_zero,mul_assoc] using H z hz δ hd hdhalf v

end MiddleSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CongruenceSpectrum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport
section CongruenceSpectrum
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma ordered_eigenvalues_bounded_congruence {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
    (hA : A.IsPositive) (hB : B.IsPositive) (P : E →ₗ[ℝ] F)
    (hP : Function.Bijective P) {l u : ℝ} (hl : 0 < l) (hu : 0 ≤ u)
    (hPn : ∀ v, l*‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ u*‖v‖)
    (h : ∀ v, inner ℝ (A v) v = inner ℝ (B (P v)) (P v))
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
    hA.isSymmetric.eigenvalues hnE i ≤ u^2 * hB.isSymmetric.eigenvalues hnF i ∧
    hB.isSymmetric.eigenvalues hnF i ≤ (1/l)^2 * hA.isSymmetric.eigenvalues hnE i := by
  constructor
  · have H := ordered_eigenvalue_pullback_comparison hA.isSymmetric hB P
      (by norm_num : (0:ℝ) ≤ 1) hu (fun v => (hPn v).2)
      (a := 1) (b := 0) (fun v => by simp [h]) hnE hnF i
    simpa only [one_mul,add_zero] using H
  · let e := LinearEquiv.ofBijective P hP
    have hnorm : ∀ w, ‖e.symm w‖ ≤ (1/l)*‖w‖ := by
      intro w
      rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
      have H := (hPn (e.symm w)).1
      change l*‖e.symm w‖ ≤ ‖e (e.symm w)‖ at H
      simpa only [e.apply_symm_apply,mul_comm] using H
    have heq : ∀ w, inner ℝ (B w) w = inner ℝ (A (e.symm w)) (e.symm w) := by
      intro w
      have H := h (e.symm w)
      change inner ℝ (A (e.symm w)) (e.symm w) = inner ℝ (B (e (e.symm w))) (e (e.symm w)) at H
      simpa only [e.apply_symm_apply] using H.symm
    have H := ordered_eigenvalue_pullback_comparison hB.isSymmetric hA e.symm.toLinearMap
      (by norm_num : (0:ℝ) ≤ 1) (div_nonneg (by norm_num) hl.le) hnorm
      (a := 1) (b := 0) (fun v => by simp [heq]) hnF hnE i
    simpa only [one_mul,add_zero] using H

end CongruenceSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MiddleScaling
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleScaling
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleHessian_scaled_ray (z : TangentBundle 𝓘(ℝ,Model n) M)
    (h T : ℝ) (hT : T ≠ 0) :
    HEq (middleHessian (tangentScale T z) (h/T) 1) (T • middleHessian z h T) := by
  unfold middleHessian
  rw [sprayFlow_scale,mul_div_cancel₀ _ hT]
  change HEq
    ((h/T)⁻¹ • normalHessian (sprayFlow h z).1 (-(h/T) • (T • (sprayFlow h z).2)) +
      (1-h/T)⁻¹ • normalHessian (sprayFlow h z).1 ((1-h/T) • (T • (sprayFlow h z).2)))
    (T • (h⁻¹ • normalHessian (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) +
      (T-h)⁻¹ • normalHessian (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2)))
  simp only [smul_smul]
  have h1 : -(h/T)*T = -h := by field_simp
  have h2 : (1-h/T)*T = T-h := by field_simp
  rw [h1,h2]
  apply heq_of_eq
  ext v w
  simp only [add_apply,smul_apply,smul_eq_mul]
  have h3 : (h/T)⁻¹ = T*h⁻¹ := by simp [div_eq_mul_inv]
  have h4 : (1-h/T)⁻¹ = T*(T-h)⁻¹ := by
    rw [show 1-h/T=(T-h)/T by field_simp]
    simp [div_eq_mul_inv]
  rw [h3,h4]
  ring

end MiddleScaling
end WeakMTWTransport

end

end

section

noncomputable section
namespace WeakMTWTransport
section SpectralScaling
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma ordered_singularValues_positive_smul (A : E →ₗ[ℝ] F) {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    (t • A).singularValues i = t * A.singularValues i := by
  have h1 := ordered_singularValues_pullback (A := t • A) (B := A)
    (LinearMap.id) ht.le (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1*‖v‖; simp)
    (fun v => by simp only [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_pos ht,LinearMap.id_apply]; exact le_rfl) hn hn i
  have h2 := ordered_singularValues_pullback (A := A) (B := t • A)
    (LinearMap.id) (inv_nonneg.mpr ht.le) (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1*‖v‖; simp)
    (fun v => by simp only [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_pos ht,LinearMap.id_apply]; rw [←mul_assoc,inv_mul_cancel₀ ht.ne',one_mul]) hn hn i
  simp only [mul_one] at h1 h2
  apply le_antisymm h1
  have H := mul_le_mul_of_nonneg_left h2 ht.le
  simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] using H
end SpectralScaling
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearSingular_heq {x y : M} (hxy : x=y)
    {B : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ}
    {C : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ}
    (hBC : HEq B C) (i : ℕ) :
    intrinsicBilinearSingular x B i=intrinsicBilinearSingular y C i := by
  subst y
  cases hBC
  rfl

local instance localInst_r51bd0a_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearOperator_smul (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)
    (t : ℝ) : intrinsicBilinearOperator y (t • B)=t • intrinsicBilinearOperator y B := by
  ext v
  simp only [intrinsicBilinearOperator,comp_apply,smul_apply,map_smul]

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearSingular_pos_smul (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) (i : Fin (Module.finrank ℝ (Model n))) :
    intrinsicBilinearSingular y (t • B) i=t*intrinsicBilinearSingular y B i := by
  unfold intrinsicBilinearSingular
  rw [intrinsicBilinearOperator_smul]
  exact ordered_singularValues_positive_smul (intrinsicBilinearOperator y B).toLinearMap ht rfl i

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleSingularValue_scaled_ray (z : TangentBundle 𝓘(ℝ,Model n) M)
    (h T : ℝ) (hT : 0 < T) (i : Fin (Module.finrank ℝ (Model n))) :
    middleSingularValue (tangentScale T z) (h/T) 1 i = T*middleSingularValue z h T i := by
  have hbase : (sprayFlow (h/T) (tangentScale T z)).1=(sprayFlow h z).1 := by
    rw [sprayFlow_scale,mul_div_cancel₀ _ hT.ne']
    rfl
  have H := intrinsicBilinearSingular_heq hbase (middleHessian_scaled_ray z h T hT.ne') i
  change middleSingularValue (tangentScale T z) (h/T) 1 i = _ at H
  rw [H,intrinsicBilinearSingular_pos_smul _ _ hT]
  rfl

end MiddleSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_RadialSingular
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section RadialSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_8
lemma uniform_middle_singular_crossing :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2 ∈ minimizingVectors z.1 → ∀ δ ∈ Icc (0:ℝ) (1/2),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      middleSingularValue z (1/4) 1 i+c*δ ≤ middleSingularValue z (1/4) (1-δ) i ∧
      middleSingularValue z (1/4) (1-δ) i ≤ middleSingularValue z (1/4) 1 i+C*δ := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middle_ordered_crossing (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd i
  have h0 := positive_singularValues_eq_eigenvalues
    (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num)) rfl i
  have h1 := positive_singularValues_eq_eigenvalues
    (shortened_middle_operator_positive hz hd.1 hd.2) rfl i
  simp only [sub_zero] at h0
  change middleSingularValue z (1/4) 1 i = _ at h0
  change middleSingularValue z (1/4) (1-δ) i = _ at h1
  simpa only [h0,h1,sub_zero] using H z hz δ hd.1 hd.2 i

lemma uniform_radial_singular_shortening :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ δ ∈ Icc (0:ℝ) (1/2),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      c*((endpointExpDifferential x p).toLinearMap.singularValues i+δ) ≤
        (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i ∧
      (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i ≤
        C*((endpointExpDifferential x p).toLinearMap.singularValues i+δ) := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_endpoint_middle_singular_comparison (n := n) (M := M)
  obtain ⟨l,u,hl,hu,J⟩ := uniform_middle_singular_crossing (n := n) (M := M)
  refine ⟨1/(2*a*(b+1/l)),b*(a+u),div_pos (by norm_num)
    (by positivity),mul_pos hb (add_pos ha hu),?_⟩
  intro x p hp δ hd i
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let T := 1-δ
  have hT : 0 < T := by dsimp [T] <;> linarith [hd.2]
  have hT1 : T ≤ 1 := by dsimp [T] <;> linarith [hd.1]
  have hThalf : (1/2:ℝ) ≤ T := by dsimp [T] <;> linarith [hd.2]
  have ht : (1/4:ℝ)/T ∈ Icc (1/4:ℝ) (3/4) := by
    constructor
    · rw [le_div_iff₀ hT]; nlinarith
    · rw [div_le_iff₀ hT]; nlinarith
  have H0 := H x p hp (1/4) (by constructor <;> norm_num) i
  have H1 := H x (T • p) (minimizingVectors_smul hp hT.le hT1) ((1/4)/T) ht i
  have HS := middleSingularValue_scaled_ray z (1/4) T hT i
  change middleSingularValue (⟨x,T • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) ((1/4)/T) 1 i = _ at HS
  rw [HS] at H1
  have J1 := J z hp δ hd i
  let S := (endpointExpDifferential x p).toLinearMap.singularValues i
  let R := (endpointExpDifferential x (T • p)).toLinearMap.singularValues i
  let d0 := middleSingularValue z (1/4) 1 i
  let d1 := middleSingularValue z (1/4) T i
  change S ≤ b*d0 ∧ d0 ≤ a*S at H0
  change R ≤ b*(T*d1) ∧ T*d1 ≤ a*R at H1
  change d0+l*δ ≤ d1 ∧ d1 ≤ d0+u*δ at J1
  have hd0 : 0 ≤ d0 := (middleHessianOperator z (1/4) 1).toLinearMap.singularValues_nonneg i
  have hd1 : 0 ≤ d1 := (middleHessianOperator z (1/4) T).toLinearMap.singularValues_nonneg i
  have hS : 0 ≤ S := (endpointExpDifferential x p).toLinearMap.singularValues_nonneg i
  have hR : 0 ≤ R := (endpointExpDifferential x (T • p)).toLinearMap.singularValues_nonneg i
  have hlowD : d1 ≤ 2*a*R := by
    have hh := mul_le_mul_of_nonneg_right hThalf hd1
    nlinarith [H1.2]
  have hupD : d1 ≤ a*S+u*δ := J1.2.trans (add_le_add H0.2 le_rfl)
  have hSle : S ≤ b*d1 := H0.1.trans (mul_le_mul_of_nonneg_left
    (by nlinarith [J1.1,mul_nonneg hl.le hd.1]) hb.le)
  have hdle : δ ≤ (1/l)*d1 := by
    rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
    nlinarith [J1.1]
  constructor
  · change (1/(2*a*(b+1/l)))*(S+δ) ≤ R
    rw [one_div,mul_comm,←div_eq_mul_inv,div_le_iff₀ (by positivity : 0 < 2*a*(b+1/l))]
    calc
      S+δ ≤ (b+1/l)*d1 := by nlinarith only [hSle,hdle]
      _ ≤ (b+1/l)*(2*a*R) := mul_le_mul_of_nonneg_left hlowD (by positivity)
      _ = R*(2*a*(b+1/l)) := by ring
  · change R ≤ b*(a+u)*(S+δ)
    have hh := mul_le_mul_of_nonneg_right hT1 hd1
    have hh2 := H1.1.trans (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hh) hb.le)
    calc
      R ≤ b*d1 := hh2
      _ ≤ b*(a*S+u*δ) := mul_le_mul_of_nonneg_left hupD hb.le
      _ ≤ b*(a+u)*(S+δ) := by
        have h1 := mul_nonneg ha.le hd.1
        have h2 := mul_nonneg hu.le hS
        nlinarith [mul_nonneg hb.le h1,mul_nonneg hb.le h2]

end RadialSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ShearConvexity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearConvexity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma radialHessianDefect_apply (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (δ : ℝ) (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    radialHessianDefectBilinear x p δ u v =
      -δ*(normalHessian x ((1-δ) • p) u v-inner ℝ u v) := rfl

lemma radialHessianDefect_symm {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {δ : ℝ}
    (hp : (1-δ) • p∈injectivityDomain x) (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    radialHessianDefectBilinear x p δ u v=radialHessianDefectBilinear x p δ v u := by
  simp only [radialHessianDefect_apply,normalHessian_symm hp u v,real_inner_comm u v]

lemma spectralShear_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q z : E) (t : ℝ) : spectralShear p q t z=z+(t*(inner ℝ z q/inner ℝ p q)) • q := by
  simp only [spectralShear,add_apply,ContinuousLinearMap.id_apply,
    smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    smul_smul,real_inner_comm q z]
  congr 2
  ring

end ShearConvexity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SchurBackground
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open scoped BigOperators

namespace WeakMTWTransport
section InverseSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma diagonal_quadratic_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (μ : Fin n → ℝ)
    (hμ : ∀ j, A (b j)=μ j • b j) (v : E) :
    inner ℝ (A v) v=∑ j, μ j*(b.repr v j)^2 := by
  have hcoord (j : Fin n) : b.repr (A v) j=μ j*b.repr v j := by
    rw [b.repr_apply_apply,b.repr_apply_apply,←hA _ _,hμ,real_inner_smul_left]
  have H := b.repr.inner_map_map (A v) v
  rw [←H,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcoord]
  simp only [RCLike.inner_apply,conj_trivial]
  ring

lemma ordered_eigenvalues_of_diagonal_basis {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (b : OrthonormalBasis (Fin n) ℝ E)
    (μ : Fin n → ℝ) (hμ : ∀ j, A (b j)=μ j • b j) (hm : Antitone μ) (i : Fin n) :
    hA.eigenvalues hn i=μ i := by
  apply le_antisymm
  · obtain ⟨v,hv,hav,hbv⟩ := paired_basis_slice (hA.eigenvectorBasis hn) b i
    have h1 := quadratic_lower_spectral_slice hA hn i v hav
    have h2 : inner ℝ (A v) v≤μ i*‖v‖^2 := by
      rw [diagonal_quadratic_expansion hA b μ hμ,eigenbasis_norm_expansion b,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i≤j
      · exact mul_le_mul_of_nonneg_right (hm hij) (sq_nonneg _)
      · rw [hbv j (lt_of_not_ge hij)]; simp
    exact (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).mp (h1.trans h2)
  · obtain ⟨v,hv,hbv,hav⟩ := paired_basis_slice b (hA.eigenvectorBasis hn) i
    have h1 : μ i*‖v‖^2≤ inner ℝ (A v) v := by
      rw [diagonal_quadratic_expansion hA b μ hμ,eigenbasis_norm_expansion b,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hji : j ≤ i
      · exact mul_le_mul_of_nonneg_right (hm hji) (sq_nonneg _)
      · rw [hbv j (lt_of_not_ge hji)]; simp
    have h2 := quadratic_upper_spectral_slice hA hn i v hav
    exact (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).mp (h1.trans h2)

lemma positive_eigenvalues_of_injective {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    (hi : Function.Injective A) {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    0<hA.isSymmetric.eigenvalues hn i := by
  apply lt_of_le_of_ne (hA.nonneg_eigenvalues hn i)
  intro h
  have H := hA.isSymmetric.apply_eigenvectorBasis hn i
  rw [←h] at H
  simp only [RCLike.ofReal_real_eq_id,id_eq,zero_smul] at H
  have H0 := hi (H.trans (map_zero A).symm)
  have H1 := (hA.isSymmetric.eigenvectorBasis hn).norm_eq_one i
  rw [H0,norm_zero] at H1
  norm_num at H1

lemma ordered_eigenvalues_inverse {A K : E →ₗ[ℝ] E}
    (hA : A.IsPositive) (hK : K.IsSymmetric)
    (hi : Function.Injective A) (hAK : ∀ v, A (K v)=v)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    hK.eigenvalues hn i=(hA.isSymmetric.eigenvalues hn i.rev)⁻¹ := by
  let b := (hA.isSymmetric.eigenvectorBasis hn).reindex Fin.revPerm
  let μ : Fin n → ℝ := fun j => (hA.isSymmetric.eigenvalues hn j.rev)⁻¹
  have hμ (j : Fin n) : K (b j)=μ j • b j := by
    apply hi
    rw [hAK,map_smul]
    have he : A (b j)=hA.isSymmetric.eigenvalues hn j.rev • b j := by
      simpa only [b,OrthonormalBasis.reindex_apply,Fin.revPerm_symm,Fin.revPerm_apply,
        RCLike.ofReal_real_eq_id,id_eq]
        using hA.isSymmetric.apply_eigenvectorBasis hn j.rev
    rw [he,smul_smul]
    dsimp only [μ]
    rw [inv_mul_cancel₀ (positive_eigenvalues_of_injective hA hi hn j.rev).ne',one_smul]
  apply ordered_eigenvalues_of_diagonal_basis hK hn b μ hμ _ i
  intro j k hjk
  exact inv_le_inv₀ (positive_eigenvalues_of_injective hA hi hn k.rev)
    (positive_eigenvalues_of_injective hA hi hn j.rev) |>.mpr
      (hA.isSymmetric.eigenvalues_antitone hn (Fin.rev_le_rev.mpr hjk))

end InverseSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ScaledSpectrum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport
section ScaledSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ordered_eigenvalues_nonneg_smul {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    (hA.smul (show starRingEnd ℝ c=c by simp)).eigenvalues hn i=
      c*hA.eigenvalues hn i := by
  apply ordered_eigenvalues_of_diagonal_basis _ hn (hA.eigenvectorBasis hn)
    (fun j => c*hA.eigenvalues hn j)
  · intro j
    simp only [LinearMap.smul_apply,hA.apply_eigenvectorBasis hn,
      RCLike.ofReal_real_eq_id,id_eq,smul_smul]
  · intro j k hjk
    exact mul_le_mul_of_nonneg_left (hA.eigenvalues_antitone hn hjk) hc

lemma reciprocal_spectrum_bounds {a b c C δ S L : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0 < c) (hC : 0<C) (hδ : 0 ≤ δ)
    (hS : 0<S) (hL : 0<L) (hlo : a*S ≤ c*L) (hup : L ≤ C*b*S) :
    (1/(C*b))*δ/S ≤ δ*L⁻¹ ∧ δ*L⁻¹ ≤ (c/a)*δ/S := by
  constructor
  · have he : (1/(C*b))*δ/S=δ/(C*b*S) := by ring
    rw [he,←div_eq_mul_inv]
    exact (div_le_div_iff₀ (mul_pos (mul_pos hC hb) hS) hL).2
      (mul_le_mul_of_nonneg_left hup hδ)
  · have hden : (a/c)*S ≤ L := by
      rw [div_mul_eq_mul_div,div_le_iff₀ hc]
      simpa only [mul_comm c L] using hlo
    have H := div_le_div_of_nonneg_left hδ (mul_pos (div_pos ha hc) hS) hden
    have he : δ/((a/c)*S)=(c/a)*δ/S := by
      field_simp
    rw [he,div_eq_mul_inv] at H
    exact H

end ScaledSpectrum
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section RadialSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_9
lemma uniform_radial_inverse_profile :
    ∃ l u B : ℝ, 0<l ∧ 0<u ∧ 0<B ∧
      ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ δ∈Ioc (0:ℝ) (1/2),
      ∃ (K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
        (hK : K.toLinearMap.IsPositive), Function.Bijective K ∧
        (∀ v, |radialHessianDefectBilinear x p δ v v-δ*inner ℝ (K v) v|≤B*δ*‖v‖^2) ∧
        ∀ i : Fin (Module.finrank ℝ (Model n)),
          l*δ/((endpointExpDifferential x p).toLinearMap.singularValues i.rev+δ) ≤
            δ*hK.isSymmetric.eigenvalues rfl i ∧
          δ*hK.isSymmetric.eigenvalues rfl i ≤
            u*δ/((endpointExpDifferential x p).toLinearMap.singularValues i.rev+δ) := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_radial_singular_shortening (n := n) (M := M)
  obtain ⟨c,C,hc,hC,J⟩ := uniform_join_exp_ordered_comparison (n := n) (M := M)
  obtain ⟨B,hB,BG⟩ := uniform_radial_Schur_background (n := n) (M := M)
  refine ⟨1/(C*b),c/a,B,div_pos (by norm_num) (mul_pos hC hb),div_pos hc ha,hB,?_⟩
  intro x p hp δ hd
  obtain ⟨K,hKb,hK,hInv,hEq,hBg⟩ := BG x p hp δ hd
  refine ⟨K,hK,hKb,hBg,?_⟩
  intro i
  let A := splitJoinHessianOperator x (1/2) ((1-δ) • p)
  have hmin := minimizingVectors_smul hp
    (show 0 ≤ 1-δ by linarith [hd.2]) (show 1-δ ≤ 1 by linarith [hd.1])
  have hA : A.toLinearMap.IsPositive := splitJoinHessianOperator_positive hmin
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  have hAi : Function.Injective A := (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mpr
    (fun v => ⟨K v,hInv v⟩)
  have heig := ordered_eigenvalues_inverse hA hK.isSymmetric hAi hInv rfl i
  rw [heig]
  have hR := H x p hp δ ⟨hd.1.le,hd.2⟩ i.rev
  have hJ := J x ((1-δ) • p) hmin (1/2) (by constructor <;> norm_num) i.rev
  let S := (endpointExpDifferential x p).toLinearMap.singularValues i.rev+δ
  let R := (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i.rev
  let L := hA.isSymmetric.eigenvalues rfl i.rev
  change a*S ≤ R ∧ R ≤ b*S at hR
  change L ≤ C*R ∧ R ≤ c*L at hJ
  have hS : 0<S := add_pos_of_nonneg_of_pos
    ((endpointExpDifferential x p).toLinearMap.singularValues_nonneg i.rev) hd.1
  have hL : 0<L := positive_eigenvalues_of_injective hA hAi rfl i.rev
  have hlo : a*S ≤ c*L := hR.1.trans hJ.2
  have hup : L ≤ C*b*S := by
    simpa only [mul_assoc] using hJ.1.trans (mul_le_mul_of_nonneg_left hR.2 hC.le)
  exact reciprocal_spectrum_bounds ha hb hc hC hd.1.le hS hL hlo hup

end RadialSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ShearBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set ContinuousLinearMap

namespace WeakMTWTransport
section ShearBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma rankOne_perturbation_bounds (q : E) {r U : ℝ}
    (hlo : -(1/2:ℝ) ≤ r*‖q‖^2) (hup : |r| *‖q‖^2 ≤ U) (v : E) :
    (1/2:ℝ)*‖v‖ ≤ ‖v+(r*inner ℝ v q) • q‖ ∧
    ‖v+(r*inner ℝ v q) • q‖ ≤ (1+U)*‖v‖ := by
  have hcs : |inner ℝ v q| ≤ ‖v‖*‖q‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v q
  have hcs2 : (inner ℝ v q)^2 ≤ ‖q‖^2*‖v‖^2 := by
    have H := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
    simpa only [sq_abs,mul_pow,mul_comm] using H
  have hinner : inner ℝ (v+(r*inner ℝ v q) • q) v=
      ‖v‖^2+r*(inner ℝ v q)^2 := by
    rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,real_inner_comm q v]
    ring
  have hcoer : (1/2:ℝ)*‖v‖^2 ≤ inner ℝ (v+(r*inner ℝ v q) • q) v := by
    rw [hinner]
    by_cases hr : 0 ≤ r
    · nlinarith [mul_nonneg hr (sq_nonneg (inner ℝ v q))]
    · have H := mul_le_mul_of_nonpos_left hcs2 (le_of_not_ge hr)
      have H2 := mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖v‖)
      nlinarith only [H,H2]
  constructor
  · by_cases hv : v=0
    · simp [hv]
    · have H := hcoer.trans (real_inner_le_norm _ _)
      have hn : 0<‖v‖ := norm_pos_iff.mpr hv
      nlinarith only [H,hn]
  · calc
      _ ≤ ‖v‖+‖(r*inner ℝ v q) • q‖ := norm_add_le _ _
      _ = ‖v‖+|r| *|inner ℝ v q| *‖q‖ := by rw [norm_smul,Real.norm_eq_abs,abs_mul]
      _ ≤ ‖v‖+|r| *(‖v‖*‖q‖)*‖q‖ := by gcongr
      _ = ‖v‖+(|r| *‖q‖^2)*‖v‖ := by ring
      _ ≤ ‖v‖+U*‖v‖ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hup (norm_nonneg v))
      _ = _ := by ring

lemma spectralShear_uniform_bounds (p q : E) {a B t : ℝ}
    (ha : 0<a) (hB : 0<B) (haB : a*B ≤ 1/2)
    (hpq : 0< inner ℝ p q) (hβ : ‖q‖^2/inner ℝ p q ≤ B)
    (ht : t∈Icc (-a) 1) (v : E) :
    (1/2:ℝ)*‖v‖ ≤ ‖spectralShear p q t v‖ ∧
    ‖spectralShear p q t v‖ ≤ (2+B)*‖v‖ := by
  let β := ‖q‖^2/inner ℝ p q
  have hβ0 : 0 ≤ β := div_nonneg (sq_nonneg _) hpq.le
  have htlo : -(1/2:ℝ) ≤ t*β := by
    have H := mul_le_mul_of_nonneg_right ht.1 hβ0
    have H2 := mul_le_mul_of_nonneg_left hβ ha.le
    change a*β ≤ a*B at H2
    nlinarith only [H,H2,haB]
  have htu : |t| *β ≤ 1+B := by
    have hupper := mul_le_mul_of_nonneg_right ht.2 hβ0
    change β ≤ B at hβ
    calc
      |t| *β = |t*β| := by rw [abs_mul,abs_of_nonneg hβ0]
      _ ≤ 1+B := abs_le.mpr
        ⟨by linarith only [htlo,hB],by linarith only [hupper,hβ]⟩
  have hlo : -(1/2:ℝ) ≤ (t/inner ℝ p q)*‖q‖^2 := by
    simpa only [β,div_mul_eq_mul_div,mul_div_assoc,mul_comm t] using htlo
  have hup : |t/inner ℝ p q| *‖q‖^2 ≤ 1+B := by
    rw [abs_div,abs_of_pos hpq]
    simpa only [β,div_mul_eq_mul_div,mul_div_assoc] using htu
  have H := rankOne_perturbation_bounds q hlo hup v
  rw [spectralShear_apply]
  have he : t*(inner ℝ v q/inner ℝ p q)=(t/inner ℝ p q)*inner ℝ v q := by ring
  rw [he]
  simpa only [show (1:ℝ)+(1+B)=2+B by ring] using H

lemma spectralShear_bijective [FiniteDimensional ℝ E] (p q : E) {a B t : ℝ}
    (ha : 0<a) (hB : 0<B) (haB : a*B ≤ 1/2)
    (hpq : 0< inner ℝ p q) (hβ : ‖q‖^2/inner ℝ p q ≤ B) (ht : t∈Icc (-a) 1) :
    Function.Bijective (spectralShear p q t) := by
  have hinj : Function.Injective (spectralShear p q t) := by
    change Function.Injective (spectralShear p q t).toLinearMap
    rw [← LinearMap.ker_eq_bot (f := (spectralShear p q t).toLinearMap),LinearMap.ker_eq_bot']
    intro v hv
    have H := (spectralShear_uniform_bounds p q ha hB haB hpq hβ ht v).1
    change spectralShear p q t v=0 at hv
    rw [hv,norm_zero] at H
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  exact ⟨hinj,(LinearMap.injective_iff_surjective (f := (spectralShear p q t).toLinearMap)).mp hinj⟩
end ShearBounds
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ShearedOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearedOperator
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_11
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_shearedRadialOperator (x : M) (p q : TangentSpace 𝓘(ℝ,Model n) x) (δ t : ℝ)
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (shearedRadialOperator x p q δ t v) w =
      radialHessianDefectBilinear x (p+t • q) δ (spectralShear p q t v) (spectralShear p q t w) :=
  InnerProductSpace.toDual_symm_apply

lemma shearedRadialOperator_symmetric {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x}
    {δ t : ℝ} (hp : (1-δ) • (p+t • q)∈injectivityDomain x) :
    (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (shearedRadialOperator x p q δ t v) w =
    inner ℝ v (shearedRadialOperator x p q δ t w)
  rw [real_inner_comm (shearedRadialOperator x p q δ t w) v,inner_shearedRadialOperator,inner_shearedRadialOperator]
  exact radialHessianDefect_symm hp _ _

end ShearedOperator
end WeakMTWTransport

end

end

section

noncomputable section
namespace WeakMTWTransport
section BackgroundSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ordered_sheared_background_spectrum {F K : E →ₗ[ℝ] E}
    (hF : F.IsSymmetric) (hK : K.IsPositive) (L : E →ₗ[ℝ] E)
    (hL : Function.Bijective L) {l u δ b : ℝ} (hl : 0<l) (hu : 0≤u) (hd : 0≤δ)
    (hLn : ∀ v, l*‖v‖≤‖L v‖ ∧ ‖L v‖≤u*‖v‖)
    (hbg : ∀ v, |inner ℝ (F v) v-δ*inner ℝ (K (L v)) (L v)|≤b*‖v‖^2)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    l^2*(δ*hK.isSymmetric.eigenvalues hn i)-b ≤ hF.eigenvalues hn i ∧
    hF.eigenvalues hn i ≤ u^2*(δ*hK.isSymmetric.eigenvalues hn i)+b := by
  let W := L.adjoint ∘ₗ K ∘ₗ L
  have hW : W.IsPositive := hK.adjoint_conj L
  have hw (v : E) : inner ℝ (W v) v=inner ℝ (K (L v)) (L v) := by
    simp only [W,LinearMap.comp_apply,LinearMap.adjoint_inner_left]
  have hcong := ordered_eigenvalues_bounded_congruence hW hK L hL hl hu hLn hw hn hn i
  have hup := ordered_eigenvalue_quadratic_comparison hF hW.isSymmetric hd
    (fun v => by have H := (abs_le.mp (hbg v)).2; rw [←hw] at H; linarith) hn i
  have hδW := hW.isSymmetric.smul (show starRingEnd ℝ δ=δ by simp)
  have hlo := ordered_eigenvalue_quadratic_comparison hδW hF (a := 1) (b := b)
    (by norm_num) (fun v => by
      have H := (abs_le.mp (hbg v)).1
      change inner ℝ (δ • W v) v ≤ 1*inner ℝ (F v) v+b*‖v‖^2
      rw [real_inner_smul_left,hw]
      linarith) hn i
  rw [ordered_eigenvalues_nonneg_smul hW.isSymmetric hd hn i] at hlo
  have hcl : l^2*hK.isSymmetric.eigenvalues hn i ≤ hW.isSymmetric.eigenvalues hn i := by
    have H := mul_le_mul_of_nonneg_left hcong.2 (sq_nonneg l)
    have he : l^2*(1/l)^2=1 := by field_simp
    rw [←mul_assoc,he,one_mul] at H
    exact H
  constructor
  · have H := mul_le_mul_of_nonneg_left hcl hd
    nlinarith only [H,hlo]
  · have H := mul_le_mul_of_nonneg_left hcong.1 hd
    nlinarith only [H,hup]
end BackgroundSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ShearedSpectrum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearedSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_12
lemma uniform_sheared_radial_spectrum_oai {a B : ℝ} (ha : 0<a) (hB : 0<B)
    (haB : a*B≤1/2) :
    ∃ l u b : ℝ, 0<l ∧ 0<u ∧ 0<b ∧
      ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q≤B →
      (∀ t∈Icc (-a) 1, p+t • q∈minimizingVectors x) →
      ∀ δ∈Ioc (0:ℝ) (1/2), ∀ t∈Icc (-a) 1,
      ∃ hF : (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric,
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      l*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)-b*δ ≤
        hF.eigenvalues rfl i ∧
      hF.eigenvalues rfl i ≤
        u*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)+b*δ := by
  obtain ⟨l,u,b,hl,hu,hb,H⟩ := uniform_radial_inverse_profile (n := n) (M := M)
  refine ⟨l/4,(2+B)^2*u,b*(2+B)^2,by positivity,by positivity,by positivity,?_⟩
  intro x p q hpq hβ hline δ hd t ht
  have hPt := hline t ht
  have hPi := contracted_minimizer_mem_injectivityDomain hPt
    (show 0<1-δ by linarith [hd.2]) (show 1-δ<1 by linarith [hd.1])
  have hF := shearedRadialOperator_symmetric hPi
  refine ⟨hF,?_⟩
  intro i
  obtain ⟨K,hK,hKb,hBg,hSp⟩ := H x (p+t • q) hPt δ hd
  let L := spectralShear p q t
  have hLn := spectralShear_uniform_bounds p q ha hB haB hpq hβ ht
  have hLb := spectralShear_bijective p q ha hB haB hpq hβ ht
  have hbg : ∀ v, |inner ℝ (shearedRadialOperator x p q δ t v) v-
      δ*inner ℝ (K (L v)) (L v)|≤(b*(2+B)^2*δ)*‖v‖^2 := by
    intro v
    rw [inner_shearedRadialOperator]
    have hs2 : ‖L v‖^2≤(2+B)^2*‖v‖^2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hLn v).2
    have HH := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hb.le hd.1.le)
    have HH2 := (hBg (L v)).trans HH
    convert HH2 using 1 <;> first | rfl | ring
  have HG := ordered_sheared_background_spectrum hF hK L.toLinearMap hLb
    (show (0:ℝ)<1/2 by norm_num) (show 0≤2+B by positivity) hd.1.le hLn hbg rfl i
  have Hlo := mul_le_mul_of_nonneg_left (hSp i).1 (sq_nonneg (1/2:ℝ))
  have Hup := mul_le_mul_of_nonneg_left (hSp i).2 (sq_nonneg (2+B))
  constructor
  · have HH := le_trans (sub_le_sub_right Hlo (b*(2+B)^2*δ)) HG.1
    convert HH using 1 <;> first | rfl | ring
  · have HH := HG.2.trans (add_le_add Hup le_rfl)
    convert HH using 1 <;> first | rfl | ring
end ShearedSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.uniform_sheared_radial_spectrum_oai.{u_1} := @OAI.WeakMTWTransport.uniform_sheared_radial_spectrum_oai.{u_1}
