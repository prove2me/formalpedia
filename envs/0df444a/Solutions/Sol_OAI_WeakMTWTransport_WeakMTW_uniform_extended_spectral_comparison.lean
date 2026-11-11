-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.uniform_extended_spectral_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:02.010729+00:00
-- url     : https://prove2.me/submissions/fbdfbb1a-e644-46ba-a669-ac4cc085e25b

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
import Theorems.Thm_OAI_WeakMTWTransport_uniform_sheared_radial_quadratic_bounds
import Theorems.Thm_OAI_WeakMTWTransport_uniform_sheared_radial_spectrum

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_BoundedConvexSecant
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

namespace WeakMTWTransport

lemma bounded_convex_secant {f : ℝ → ℝ} {a b C d x y : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f) (hC : 0 ≤ C) (hd : 0<d)
    (hb : ∀ t∈Icc a b, |f t| ≤ C)
    (hx : x∈Icc (a+d) (b-d)) (hy : y∈Icc (a+d) (b-d)) :
    |f y-f x| ≤ (2*C/d)*|y-x| := by
  wlog hxy : x ≤ y generalizing x y
  · have H := this hy hx (le_of_not_ge hxy)
    simpa only [abs_sub_comm] using H
  obtain rfl | hxy := hxy.eq_or_lt
  · simp
  have hax : a<x := by linarith [hx.1]
  have hyb : y<b := by linarith [hy.2]
  have hxab : x∈Icc a b := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hyab : y∈Icc a b := ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hab : a ≤ b := by linarith
  have haab : a∈Icc a b := ⟨le_rfl,hab⟩
  have hbab : b∈Icc a b := ⟨hab,le_rfl⟩
  have hfa := abs_le.mp (hb a haab)
  have hfb := abs_le.mp (hb b hbab)
  have hfx := abs_le.mp (hb x hxab)
  have hfy := abs_le.mp (hb y hyab)
  have Hlo := hf.slope_mono_adjacent haab hyab hax hxy
  have Hup := hf.slope_mono_adjacent hxab hbab hxy hyb
  have hlo : -(2*C/d) ≤ (f x-f a)/(x-a) := by
    rw [←neg_div,div_le_div_iff₀ hd (sub_pos.mpr hax)]
    have H := mul_le_mul_of_nonneg_right (show -2*C ≤ f x-f a by linarith) hd.le
    have H2 := mul_le_mul_of_nonneg_left (show d ≤ x-a by linarith [hx.1]) (by positivity : 0 ≤ 2*C)
    nlinarith only [H,H2]
  have hup : (f b-f y)/(b-y) ≤ 2*C/d := by
    rw [div_le_div_iff₀ (sub_pos.mpr hyb) hd]
    have H := mul_le_mul_of_nonneg_right (show f b-f y ≤ 2*C by linarith) hd.le
    have H2 := mul_le_mul_of_nonneg_left (show d ≤ b-y by linarith [hy.2]) (by positivity : 0 ≤ 2*C)
    nlinarith only [H,H2]
  have H1 := hlo.trans Hlo
  have H2 := Hup.trans hup
  rw [le_div_iff₀ (sub_pos.mpr hxy)] at H1
  rw [div_le_iff₀ (sub_pos.mpr hxy)] at H2
  rw [abs_of_pos (sub_pos.mpr hxy)]
  exact abs_le.mpr ⟨by nlinarith only [H1],H2⟩

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FactorNorm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section UniformPieces
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_split_exp_bounds :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ t∈Icc (1/4:ℝ) (3/4),
      (∀ v, l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) (t • z.2) v‖ ∧
        ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) (t • z.2) v‖≤u*‖v‖) ∧
      (∀ v, let r := reverseRay (tangentScale (1-t) (sprayFlow t z));
        l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
          (riemannianExp r.1) r.2 v‖ ∧
        ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
          (riemannianExp r.1) r.2 v‖≤u*‖v‖) := by
  let G := {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1}
  let S := Icc (1/4:ℝ) (3/4) ×ˢ G
  let P : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale q.1 q.2
  let R : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => reverseRay (tangentScale (1-q.1) (sprayFlow q.1 q.2))
  have hP : Continuous P := contMDiff_tangentScale.continuous
  have hR : Continuous R := continuous_reverseRay.comp (contMDiff_tangentScale.continuous.comp
    ((continuous_const.sub continuous_fst).prodMk contMDiff_sprayFlow.continuous))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_total_minimizingVectors (n := n) (M := M))
  have hK : IsCompact (P '' S ∪ R '' S) := (hS.image hP).union (hS.image hR)
  have hI : ∀ w∈P '' S ∪ R '' S, w.2∈injectivityDomain w.1 := by
    intro w hw
    rcases hw with hw | hw
    · rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
      exact contracted_minimizer_mem_injectivityDomain htz.2 (by linarith [htz.1.1])
        (by linarith [htz.1.2])
    · rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
      exact reverseRay_injectivityDomain (proper_suffix_in_injectivityDomain htz.2
        (by linarith [htz.1.1]) (by linarith [htz.1.2]) le_rfl)
  obtain ⟨l,u,hl,hu,H⟩ := compact_exp_differential_bounds hK hI
  refine ⟨l,u,hl,hu,?_⟩
  intro z hz t ht
  exact ⟨H (P (t,z)) (Or.inl (mem_image_of_mem _ ⟨ht,hz⟩)),
    H (R (t,z)) (Or.inr (mem_image_of_mem _ ⟨ht,hz⟩))⟩

end UniformPieces
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiniteLogScaleAvoidance
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

namespace WeakMTWTransport

lemma finite_log_scale_avoidance (S : Finset ℝ) {lo hi L : ℝ} (hL : 0≤L)
    (hwide : lo+((S.card:ℝ)+2)*(2*L+1)<hi) :
    ∃ u∈Ioo lo hi, ∀ s∈S, L < |u-s| := by
  classical
  let u : Fin (S.card+1) → ℝ := fun i => lo+((i.val:ℝ)+1)*(2*L+1)
  have hu (i : Fin (S.card+1)) : u i∈Ioo lo hi := by
    have hv0 : (0:ℝ)≤ i.val := Nat.cast_nonneg _
    have hv1 : (i.val:ℝ)<(S.card:ℝ)+1 := by exact_mod_cast i.isLt
    dsimp [u]
    constructor <;> nlinarith [mul_nonneg (show 0≤(S.card:ℝ)+1-i.val by linarith) (show 0≤2*L+1 by linarith)]
  by_contra h
  have hex (i : Fin (S.card+1)) : ∃ s : {s // s∈S}, |u i-s.val|≤L := by
    by_contra H
    apply h
    refine ⟨u i,hu i,?_⟩
    intro s hs
    by_contra hh
    exact H ⟨⟨s,hs⟩,le_of_not_gt hh⟩
  let g : Fin (S.card+1) → {s // s∈S} := fun i => (hex i).choose
  have hg (i : Fin (S.card+1)) : |u i-(g i).val|≤L := (hex i).choose_spec
  have hsep (i j : Fin (S.card+1)) (hij : i.val<j.val) : g i≠g j := by
    intro H
    have H1 := abs_le.mp (hg i)
    have H2 := abs_le.mp (hg j)
    rw [←H] at H2
    have hv : (i.val:ℝ)+1≤j.val := by exact_mod_cast Nat.succ_le_of_lt hij
    dsimp [u] at H1 H2
    have HH := mul_nonneg (show 0≤(j.val:ℝ)-i.val-1 by linarith) (show 0≤2*L+1 by linarith)
    nlinarith only [H1.1,H2.2,HH,hL]
  have hinj : Function.Injective g := by
    intro i j H
    rcases lt_trichotomy i.val j.val with hij|hij|hij
    · exact False.elim (hsep i j hij H)
    · exact Fin.ext hij
    · exact False.elim (hsep j i hij H.symm)
  have HH := Fintype.card_le_of_injective g hinj
  simp only [Fintype.card_fin,Fintype.card_coe] at HH
  omega

lemma finite_spectral_gap_propagation {f : ℕ → ℝ} {N : ℕ} {c ε : ℝ}
    (hgap : 2*ε < c)
    (hbin : ∀ k≤N, f k≤ε ∨ c≤f k)
    (hstep : ∀ k<N, |f (k+1)-f k|≤ε)
    (hzero : c≤f 0) : c≤f N := by
  have H : ∀ k≤N, c≤f k := by
    intro k hk
    induction k with
    | zero => exact hzero
    | succ k ih =>
      have hc := ih (by omega)
      rcases hbin (k+1) hk with hsmall|hlarge
      · have hs := (abs_le.mp (hstep k (by omega))).1
        linarith
      · exact hlarge
  exact H N le_rfl
end WeakMTWTransport

end

end

end

end OAI
end

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

local instance localInst_rd2b4ac_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
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
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_UniformFiniteRadialScale
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

namespace WeakMTWTransport

lemma uniform_finite_radial_scale {N : ℕ} {D η L : ℝ}
    (hD : 0 < D) (hη : 0<η) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : Finset ℝ), S.card ≤ N → ∀ s₀ s₁ : ℝ,
      0 < s₁ → s₁ ≤ D → s₀ < c*s₁ →
      ∃ δ : ℝ, 0<δ ∧ δ ≤ η ∧ Real.exp L*s₀ ≤ δ ∧ δ*Real.exp L ≤ s₁ ∧
        ∀ s∈S, Real.exp L*s ≤ δ ∨ δ*Real.exp L ≤ s := by
  classical
  let T := min (η/D) (Real.exp (-L))
  let W := ((N:ℝ)+3)*(2*L+1)
  have hT : 0 < T := lt_min (div_pos hη hD) (Real.exp_pos _)
  have hTe : T ≤ Real.exp (-L) := min_le_right _ _
  have hTη : T*D ≤ η := by
    have HH := min_le_left (η/D) (Real.exp (-L))
    change T ≤ η/D at HH
    exact (le_div_iff₀ hD).mp HH
  refine ⟨T*Real.exp (-W-L),mul_pos hT (Real.exp_pos _),?_⟩
  intro S hNS s₀ s₁ hs₁ hsD hs₀
  let Q := (S.filter (fun s => 0 < s)).image Real.log
  have hQc : Q.card ≤ N := (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans hNS
  have hlog : Real.exp (Real.log (s₁*T))=s₁*T := Real.exp_log (mul_pos hs₁ hT)
  have hwide : (Real.log (s₁*T)-W)+((Q.card:ℝ)+2)*(2*L+1) < Real.log (s₁*T) := by
    have hc : (Q.card:ℝ) ≤ N := by exact_mod_cast hQc
    dsimp [W]
    have HH := mul_nonneg (show 0 ≤ (N:ℝ)-Q.card by linarith) (show 0 ≤ 2*L+1 by linarith)
    nlinarith only [HH,hL]
  obtain ⟨u,hu,hsep⟩ := finite_log_scale_avoidance Q hL.le hwide
  let δ := Real.exp u
  have hδhi : δ ≤ s₁*T := by
    have HH := (Real.exp_lt_exp.mpr hu.2).le
    simpa only [hlog] using HH
  have hδlo : s₁*T*Real.exp (-W) ≤ δ := by
    have HH := (Real.exp_lt_exp.mpr hu.1).le
    rw [sub_eq_add_neg,Real.exp_add,hlog] at HH
    exact HH
  have hexp : Real.exp (-L)*Real.exp L=1 := by rw [←Real.exp_add]; simp
  have hexpW : Real.exp (-W-L)*Real.exp L=Real.exp (-W) := by
    rw [←Real.exp_add]
    congr 1
    ring
  refine ⟨δ,Real.exp_pos _,?_,?_,?_,?_⟩
  · have HH := mul_le_mul_of_nonneg_right hsD hT.le
    exact hδhi.trans (HH.trans (by simpa only [mul_comm T] using hTη))
  · have HH := mul_lt_mul_of_pos_right hs₀ (Real.exp_pos L)
    have he : T*Real.exp (-W-L)*s₁*Real.exp L=s₁*T*Real.exp (-W) := by
      calc
        _ = (s₁*T)*(Real.exp (-W-L)*Real.exp L) := by ring
        _ = _ := by rw [hexpW]
    rw [he] at HH
    have Hcenter : Real.exp L*s₀ ≤ s₁*T*Real.exp (-W) := by
      simpa only [mul_comm (Real.exp L) s₀] using HH.le
    exact Hcenter.trans hδlo
  · have HH := mul_le_mul_of_nonneg_right hδhi (Real.exp_pos L).le
    have H2 := mul_le_mul_of_nonneg_left hTe hs₁.le
    have H3 := mul_le_mul_of_nonneg_right H2 (Real.exp_pos L).le
    have he : s₁*Real.exp (-L)*Real.exp L=s₁ := by rw [mul_assoc,hexp,mul_one]
    rw [he] at H3
    exact HH.trans H3
  · intro s hs
    by_cases hspos : 0 < s
    · have hlogs : Real.log s∈Q := Finset.mem_image.mpr
        ⟨s,Finset.mem_filter.mpr ⟨hs,hspos⟩,rfl⟩
      rcases lt_abs.mp (hsep (Real.log s) hlogs) with HH|HH
      · left
        have Hexp := (Real.exp_lt_exp.mpr (show Real.log s+L < u by linarith)).le
        rw [Real.exp_add,Real.exp_log hspos] at Hexp
        simpa only [mul_comm s] using Hexp
      · right
        have Hexp := (Real.exp_lt_exp.mpr (show u+L < Real.log s by linarith)).le
        rw [Real.exp_add,Real.exp_log hspos] at Hexp
        exact Hexp
    · exact Or.inl ((mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos L).le (le_of_not_gt hspos)).trans
        (Real.exp_pos u).le)
end WeakMTWTransport

end

end

section

noncomputable section
namespace WeakMTWTransport

lemma radial_profile_small {s δ l b f R ε : ℝ}
    (hs : 0 ≤ s) (hd : 0 < δ) (hl : 0 ≤ l) (hR : 1 ≤ R)
    (hsmall : R*s ≤ δ) (hbg : b*δ ≤ ε)
    (hf : l*δ/(s+δ)-b*δ ≤ f) : l/2-ε ≤ f := by
  have hsδ : s ≤ δ := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hR)]
  have HH : l/2 ≤ l*δ/(s+δ) := by
    rw [le_div_iff₀ (add_pos_of_nonneg_of_pos hs hd)]
    nlinarith [mul_nonneg hl (sub_nonneg.mpr hsδ)]
  linarith

lemma radial_profile_large {s δ u b f R ε : ℝ}
    (hs : 0 ≤ s) (hd : 0 < δ) (hu : 0 ≤ u) (hR : 0 < R)
    (hlarge : δ*R ≤ s) (hbg : b*δ ≤ ε)
    (hf : f ≤ u*δ/(s+δ)+b*δ) : f ≤ u/R+ε := by
  have HH : u*δ/(s+δ) ≤ u/R := by
    rw [div_le_div_iff₀ (add_pos_of_nonneg_of_pos hs hd) hR]
    nlinarith [mul_nonneg hu (show 0 ≤ s+δ-δ*R by linarith)]
  linarith
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ConvexSpectrum
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

namespace WeakMTWTransport
section ConvexSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bounded_matrix_convex_eigen_secant {A : ℝ → E →ₗ[ℝ] E} {a b C d x y : ℝ}
    (hA : ∀ t∈Icc a b, (A t).IsSymmetric)
    (hc : ∀ v, ConvexOn ℝ (Icc a b) (fun t => inner ℝ (A t v) v))
    (hC : 0≤C) (hd : 0<d)
    (hb : ∀ t∈Icc a b, ∀ v, |inner ℝ (A t v) v|≤C*‖v‖^2)
    (hx : x∈Icc (a+d) (b-d)) (hy : y∈Icc (a+d) (b-d))
    (hxi : x∈Icc a b) (hyi : y∈Icc a b)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    |(hA y hyi).eigenvalues hn i-(hA x hxi).eigenvalues hn i|≤(2*C/d)*|y-x| := by
  have H (v : E) := bounded_convex_secant (hc v) (mul_nonneg hC (sq_nonneg ‖v‖))
    hd (fun t ht => hb t ht v) hx hy
  have H' (v : E) : |inner ℝ (A y v) v-inner ℝ (A x v) v|≤
      ((2*C/d)*|y-x|)*‖v‖^2 := by
    convert H v using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hup := ordered_eigenvalue_quadratic_comparison (hA y hyi) (hA x hxi)
    (a := 1) (b := (2*C/d)*|y-x|) (by norm_num)
    (fun v => by have := (abs_le.mp (H' v)).2; linarith) hn i
  have hlo := ordered_eigenvalue_quadratic_comparison (hA x hxi) (hA y hyi)
    (a := 1) (b := (2*C/d)*|y-x|) (by norm_num)
    (fun v => by have := (abs_le.mp (H' v)).1; linarith) hn i
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma matrix_convex_eigen_endpoint {A : ℝ → E →ₗ[ℝ] E} {a C e : ℝ}
    (ha : 0≤a) (he : e∈Icc (0:ℝ) 1)
    (hA : ∀ t∈Icc (-a) 1, (A t).IsSymmetric)
    (hc : ∀ v, ConvexOn ℝ (Icc (-a) 1) (fun t => inner ℝ (A t v) v))
    (hb : ∀ v, inner ℝ (A 0 v) v≤C*‖v‖^2)
    (hm : 1-e∈Icc (-a) 1) (h1 : (1:ℝ)∈Icc (-a) 1)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    (hA (1-e) hm).eigenvalues hn i ≤
      (1-e)*(hA 1 h1).eigenvalues hn i+e*C := by
  refine ordered_eigenvalue_quadratic_comparison (hA (1-e) hm) (hA 1 h1)
    (show 0≤1-e by linarith [he.2]) ?_ hn i
  intro v
  have H := (hc v).2 (show (0:ℝ)∈Icc (-a) 1 by constructor <;> linarith) h1
    he.1 (show 0≤1-e by linarith [he.2]) (show e+(1-e)=1 by ring)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add] at H
  have H2 := mul_le_mul_of_nonneg_left (hb v) he.1
  nlinarith only [H,H2]
end ConvexSpectrum
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

lemma radialHessianDefect_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {δ : ℝ}
    (hδ : δ≠1) (hp : (1-δ) • p∈injectivityDomain x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) : radialHessianDefectBilinear x p δ p v=0 := by
  rw [radialHessianDefect_apply,normalHessian_contracted_radial (sub_ne_zero.mpr hδ.symm) hp]
  ring

lemma radialHessianDefect_add_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {δ : ℝ}
    (hδ : δ≠1) (hp : (1-δ) • p∈injectivityDomain x)
    (z : TangentSpace 𝓘(ℝ,Model n) x) (a : ℝ) :
    radialHessianDefectBilinear x p δ (z+a • p) (z+a • p)=radialHessianDefectBilinear x p δ z z := by
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,radialHessianDefect_radial hδ hp]
  rw [radialHessianDefect_symm hp z p,radialHessianDefect_radial hδ hp]
  ring

lemma spectralShear_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q z : E) (t : ℝ) : spectralShear p q t z=z+(t*(inner ℝ z q/inner ℝ p q)) • q := by
  simp only [spectralShear,add_apply,ContinuousLinearMap.id_apply,
    smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    smul_smul,real_inner_comm q z]
  congr 2
  ring

lemma spectralShear_transverse_representative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p q z : E) (t : ℝ) :
    z-(inner ℝ z q/inner ℝ p q) • p=
      spectralShear p q t z+(-(inner ℝ z q/inner ℝ p q)) • (p+t • q) := by
  rw [spectralShear_apply,smul_add,smul_smul]
  module

lemma spectralShear_transverse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q z : E) (hpq : inner ℝ p q≠0) :
    inner ℝ (z-(inner ℝ z q/inner ℝ p q) • p) q=0 := by
  simp only [inner_sub_left,real_inner_smul_left,div_mul_cancel₀ _ hpq,sub_self]

lemma radialHessianDefect_shear {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x} {δ t : ℝ}
    (hδ : δ≠1) (hp : (1-δ) • (p+t • q)∈injectivityDomain x)
    (z : TangentSpace 𝓘(ℝ,Model n) x) :
    radialHessianDefectBilinear x (p+t • q) δ (spectralShear p q t z) (spectralShear p q t z)=
    radialHessianDefectBilinear x (p+t • q) δ
      (z-(inner ℝ z q/inner ℝ p q) • p) (z-(inner ℝ z q/inner ℝ p q) • p) := by
  rw [spectralShear_transverse_representative p q z t]
  exact (radialHessianDefect_add_radial hδ hp _ _).symm

lemma WeakMTW.spectralShear_convexOn (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p q : TangentSpace 𝓘(ℝ,Model n) x) (hpq : inner ℝ p q≠0)
    {δ : ℝ} (hδ0 : 0≤δ) (hδ1 : δ≠1) {D : Set ℝ} (hD : Convex ℝ D)
    (hline : ∀ t∈D, (1-δ) • (p+t • q)∈injectivityDomain x)
    (z : TangentSpace 𝓘(ℝ,Model n) x) :
    ConvexOn ℝ D (fun t => radialHessianDefectBilinear x (p+t • q) δ
      (spectralShear p q t z) (spectralShear p q t z)) := by
  let ξ := z-(inner ℝ z q/inner ℝ p q) • p
  have hξ : inner ℝ ξ ((1-δ) • q)=0 := by
    rw [real_inner_smul_right,spectralShear_transverse p q z hpq,mul_zero]
  have hlin : ∀ t∈D, (1-δ) • p+t • ((1-δ) • q)∈injectivityDomain x := by
    intro t ht
    convert hline t ht using 1
    all_goals try with_reducible_and_instances rfl
    module
  have H := hmtw.transverse_concaveOn_injectivityDomain x ((1-δ) • p) ξ
    ((1-δ) • q) hD hlin hξ
  refine ⟨hD,?_⟩
  intro a ha b hb u v hu hv huv
  have hc := hD ha hb hu hv huv
  have HA := H.2 ha hb hu hv huv
  simp only [smul_eq_mul] at HA
  have heq (t : ℝ) (ht : t∈D) :
      radialHessianDefectBilinear x (p+t • q) δ (spectralShear p q t z) (spectralShear p q t z)=
      -δ*(hessianValue x ((1-δ) • p+t • ((1-δ) • q)) ξ-inner ℝ ξ ξ) := by
    rw [radialHessianDefect_shear hδ1 (hline t ht),radialHessianDefect_apply]
    rw [hessianValue_eq_normalHessian (hlin t ht)]
    have hr : (1-δ) • (p+t • q)=(1-δ) • p+t • ((1-δ) • q) := by module
    rw [hr]
  dsimp only
  rw [heq _ hc,heq a ha,heq b hb]
  simp only [smul_eq_mul]
  have hcst := congrArg (fun r : ℝ => r*(δ*inner ℝ ξ ξ)) huv
  nlinarith [mul_le_mul_of_nonneg_left HA hδ0]

end ShearConvexity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ShearedOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma WeakMTW.shearedRadialOperator_convexOn (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p q : TangentSpace 𝓘(ℝ,Model n) x) (hpq : inner ℝ p q≠0)
    {a δ : ℝ} (hd : δ∈Ioc (0:ℝ) (1/2))
    (hline : ∀ t∈Icc (-a) 1, p+t • q∈minimizingVectors x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ConvexOn ℝ (Icc (-a) 1) (fun t => inner ℝ (shearedRadialOperator x p q δ t v) v) := by
  simpa only [inner_shearedRadialOperator] using hmtw.spectralShear_convexOn x p q hpq hd.1.le
    (show δ≠1 by linarith [hd.2]) (convex_Icc _ _)
    (fun t ht => contracted_minimizer_mem_injectivityDomain (hline t ht)
      (show 0<1-δ by linarith [hd.2]) (show 1-δ<1 by linarith [hd.1])) v
end ShearedOperator
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FiniteIntervalMesh
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

namespace WeakMTWTransport

lemma finite_interval_mesh {K ε e : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (he : e∈Ioo (0:ℝ) 1) :
    ∃ N : ℕ, 0<N ∧ ∃ t : ℕ → ℝ, t 0=0 ∧ t N=1-e ∧
      (∀ k≤N, t k∈Icc (0:ℝ) (1-e)) ∧
      ∀ k<N, K*|t (k+1)-t k| ≤ ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (K/ε+1)
  have hn0 : (0:ℝ)<N := by
    have := div_nonneg hK hε.le
    linarith
  have hNnat : 0<N := by exact_mod_cast hn0
  let t : ℕ → ℝ := fun k => (k:ℝ)/N*(1-e)
  refine ⟨N,hNnat,t,by simp [t],by simp [t,ne_of_gt hn0],?_,?_⟩
  · intro k hk
    have hr : (k:ℝ)/N ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hk)
    have hr0 : 0 ≤ (k:ℝ)/N := div_nonneg (Nat.cast_nonneg _) hn0.le
    dsimp [t]
    constructor
    · exact mul_nonneg hr0 (by linarith [he.2])
    · have HH := mul_le_mul_of_nonneg_right hr (show 0 ≤ 1-e by linarith [he.2])
      simpa only [one_mul] using HH
  · intro k hk
    have hstep : t (k+1)-t k=(1-e)/N := by
      dsimp [t]
      rw [Nat.cast_add,Nat.cast_one]
      ring
    rw [hstep,abs_of_nonneg (div_nonneg (by linarith [he.2]) hn0.le)]
    have hKN : K/N ≤ ε := by
      rw [div_le_iff₀ hn0]
      have HH := (div_lt_iff₀ hε).mp (show K/ε<(N:ℝ) by linarith [hN])
      linarith
    have HH := mul_le_mul_of_nonneg_left (show (1-e)/N ≤ 1/N by
      exact div_le_div_of_nonneg_right (by linarith [he.1]) hn0.le) hK
    rw [mul_one_div] at HH
    exact HH.trans hKN
end WeakMTWTransport

end

end

section

noncomputable section
open Set

namespace WeakMTWTransport

lemma uniform_finite_profile_comparison {C l u b D e K : ℝ}
    (hC : 0<C) (hl : 0<l) (hu : 0<u) (hb : 0<b) (hD : 0<D)
    (he : e∈Ioo (0:ℝ) 1) (heC : e*C ≤ l/32) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℝ → ℝ) (f : ℝ → ℝ → ℝ),
      (∀ t∈Icc (0:ℝ) 1, 0 ≤ s t) → s 1 ≤ D →
      (∀ δ∈Ioc (0:ℝ) (1/2), ∀ t∈Icc (0:ℝ) 1,
        l*δ/(s t+δ)-b*δ ≤ f δ t ∧ f δ t ≤ u*δ/(s t+δ)+b*δ) →
      (∀ δ∈Ioc (0:ℝ) (1/2), ∀ x∈Icc (0:ℝ) (1-e), ∀ y∈Icc (0:ℝ) (1-e),
        |f δ y-f δ x| ≤ K*|y-x|) →
      (∀ δ∈Ioc (0:ℝ) (1/2), f δ (1-e) ≤ (1-e)*f δ 1+e*C) →
      c*s 1 ≤ s 0 := by
  classical
  let ε := l/16
  have hε : 0<ε := by
    dsimp [ε]
    linarith only [heC, mul_pos he.1 hC]
  obtain ⟨N,hN,t,ht0,htN,ht,hstep⟩ := finite_interval_mesh hK hε he
  let L := 32*u/l+1
  have hL : 0<L := by dsimp [L] <;> positivity
  have hR : 1 ≤ Real.exp L := (show 1 ≤ L+1 by linarith).trans (Real.add_one_le_exp L)
  have hRu : u/Real.exp L ≤ l/32 := by
    rw [div_le_iff₀ (Real.exp_pos L)]
    have HH := Real.add_one_le_exp L
    have HH2 := mul_le_mul_of_nonneg_left HH hl.le
    have hcancel : l*(32*u/l)=32*u := by field_simp
    dsimp [L] at HH2
    nlinarith only [HH2,hcancel,hl]
  let η := min (1/2:ℝ) (l/(32*b))
  have hη : 0<η := lt_min (by norm_num) (div_pos hl (by positivity))
  obtain ⟨c,hc,HC⟩ := uniform_finite_radial_scale (N := N+1) hD hη hL
  refine ⟨c,hc,?_⟩
  intro s f hs hsD hprof hlip hend
  by_contra H
  have hfail : s 0 < c*s 1 := lt_of_not_ge H
  have hs₀ := hs 0 (by constructor <;> norm_num)
  have hs₁ : 0 < s 1 := by nlinarith only [hfail,hs₀,hc]
  let S := (Finset.range (N+1)).image (fun k => s (t k))
  have hSc : S.card ≤ N+1 := Finset.card_image_le.trans (by simp)
  obtain ⟨δ,hd0,hdη,hdsmall,hdlarge,hdsep⟩ := HC S hSc (s 0) (s 1) hs₁ hsD hfail
  have hd : δ∈Ioc (0:ℝ) (1/2) := ⟨hd0,hdη.trans (min_le_left _ _)⟩
  have hbg : b*δ ≤ l/32 := by
    have HH := hdη.trans (min_le_right _ _)
    have HH2 := (le_div_iff₀ (show 0<32*b by positivity)).mp HH
    nlinarith only [HH2]
  have hti (k : ℕ) (hk : k≤N) : t k∈Icc (0:ℝ) 1 :=
    ⟨(ht k hk).1,le_trans (ht k hk).2 (by linarith [he.1])⟩
  have hlarge_case (r : ℝ) (hr : r∈Icc (0:ℝ) 1) (hh : Real.exp L*s r ≤ δ) :
      l/4 ≤ f δ r := by
    have HH := radial_profile_small (hs r hr) hd0 hl.le hR hh hbg (hprof δ hd r hr).1
    linarith
  have hsmall_case (r : ℝ) (hr : r∈Icc (0:ℝ) 1) (hh : δ*Real.exp L ≤ s r) :
      f δ r ≤ ε := by
    have HH := radial_profile_large (hs r hr) hd0 hu.le (Real.exp_pos L) hh hbg
      (hprof δ hd r hr).2
    dsimp [ε]
    linarith
  have hfzero : l/4 ≤ f δ (t 0) := by
    rw [ht0]
    exact hlarge_case 0 (by constructor <;> norm_num) hdsmall
  have hfend : f δ 1 ≤ ε := hsmall_case 1 (by constructor <;> norm_num) hdlarge
  have hfbin (k : ℕ) (hk : k≤N) : f δ (t k) ≤ ε ∨ l/4 ≤ f δ (t k) := by
    have hmem : s (t k)∈S := Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),rfl⟩
    rcases hdsep _ hmem with Hs|Hs
    · exact Or.inr (hlarge_case (t k) (hti k hk) Hs)
    · exact Or.inl (hsmall_case (t k) (hti k hk) Hs)
  have hfstep (k : ℕ) (hk : k<N) : |f δ (t (k+1))-f δ (t k)| ≤ ε :=
    (hlip δ hd (t k) (ht k (by omega)) (t (k+1)) (ht (k+1) (by omega))).trans (hstep k hk)
  have Hlarge := finite_spectral_gap_propagation (f := fun k => f δ (t k))
    (show 2*ε<l/4 by dsimp [ε] <;> linarith) hfbin hfstep hfzero
  rw [htN] at Hlarge
  have Hup := hend δ hd
  have HH := mul_le_mul_of_nonneg_left hfend (show 0 ≤ 1-e by linarith [he.2])
  have HH2 := mul_nonneg hε.le he.1.le
  dsimp [ε] at HH HH2
  nlinarith only [Hlarge,Hup,HH,HH2,heC,hl]
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SingularValuesBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma singularValues_le_of_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →ₗ[ℝ] F) {u : ℝ} (hu : 0 ≤ u)
    (h : ∀ v, ‖A v‖ ≤ u*‖v‖) {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    A.singularValues i ≤ u := by
  let hS := A.isSymmetric_adjoint_comp_self
  let v := hS.eigenvectorBasis hn i
  have hv : ‖v‖=1 := (hS.eigenvectorBasis hn).orthonormal.norm_eq_one i
  have he := congrArg (fun w => inner ℝ w v) (hS.apply_eigenvectorBasis hn i)
  simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
    real_inner_smul_left,RCLike.ofReal_real_eq_id,id_eq] at he
  change inner ℝ (A v) (A v)=hS.eigenvalues hn i*inner ℝ v v at he
  simp only [real_inner_self_eq_norm_sq] at he
  rw [←A.sq_singularValues_fin hn, hv] at he
  have HH := h v
  rw [hv,mul_one] at HH
  have hs := A.singularValues_nonneg i
  nlinarith [norm_nonneg (A v)]

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EndpointSpectrumBound
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
section EndpointSpectrumBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_13
lemma uniform_endpoint_singular_bound :
    ∃ D : ℝ, 0<D ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ D := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_radial_singular_shortening (n := n) (M := M)
  obtain ⟨l,u,hl,hu,J⟩ := uniform_split_exp_bounds (n := n) (M := M)
  refine ⟨u/a,div_pos hu ha,?_⟩
  intro x p hp i
  have hj := (J (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp (1/2)
    (by constructor <;> norm_num)).1
  have hj' : ∀ v : TangentSpace 𝓘(ℝ,Model n) x,
      ‖endpointExpDifferential x ((1/2:ℝ) • p) v‖ ≤ u*‖v‖ := fun v => by
    exact (hj v).2
  have hS := singularValues_le_of_bound (E := TangentSpace 𝓘(ℝ,Model n) x)
    (F := TangentSpace 𝓘(ℝ,Model n) (riemannianExp x ((1/2:ℝ) • p))) (endpointExpDifferential x ((1/2:ℝ) • p)).toLinearMap
    hu.le hj' rfl i
  have hR := (H x p hp (1/2) (by constructor <;> norm_num) i).1
  rw [show (1:ℝ)-1/2=1/2 by norm_num] at hR
  have HH := hR.trans hS
  rw [le_div_iff₀ ha]
  nlinarith only [HH,ha]
end EndpointSpectrumBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section AffineSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_14
lemma WeakMTW.uniform_extended_spectral_comparison_oai
    (hmtw : WeakMTW (n := n) (M := M)) {a₀ B : ℝ} (ha₀ : 0<a₀) (hB : 0<B) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q ≤ B →
      (∀ t∈Icc (-a₀) 1, p+t • q∈minimizingVectors x) →
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      c*(endpointExpDifferential x (p+q)).toLinearMap.singularValues i ≤
        (endpointExpDifferential x p).toLinearMap.singularValues i := by
  let a := min a₀ (1/(2*B))
  have ha : 0<a := lt_min ha₀ (div_pos (by norm_num) (by positivity))
  have haB : a*B ≤ 1/2 := by
    have HH := min_le_right a₀ (1/(2*B))
    have HH2 := (le_div_iff₀ (show 0<2*B by positivity)).mp HH
    nlinarith only [HH2]
  obtain ⟨l,u,b,hl,hu,hb,HSp⟩ := uniform_sheared_radial_spectrum (n := n) (M := M) ha hB haB
  obtain ⟨C,hC,HB⟩ := uniform_sheared_radial_quadratic_bounds (n := n) (M := M) ha hB haB
  obtain ⟨D,hD,HD⟩ := uniform_endpoint_singular_bound (n := n) (M := M)
  let e := min (1/2:ℝ) (l/(64*C))
  have he0 : 0<e := lt_min (by norm_num) (div_pos hl (by positivity))
  have he1 : e<1 := (min_le_left _ _).trans_lt (by norm_num)
  have heC : e*C ≤ l/32 := by
    have HH := (le_div_iff₀ (show 0<64*C by positivity)).mp
      (min_le_right (1/2:ℝ) (l/(64*C)))
    change e*(64*C) ≤ l at HH
    nlinarith only [HH,hl]
  let d := min a e
  have hdpos : 0<d := lt_min ha he0
  let K := 2*C/d
  have hK : 0 ≤ K := div_nonneg (by positivity) hdpos.le
  obtain ⟨c,hc,HC⟩ := uniform_finite_profile_comparison hC hl hu hb hD ⟨he0,he1⟩ heC hK
  refine ⟨c,hc,?_⟩
  intro x p q hpq hβ hline₀ j
  have hline (t : ℝ) (ht : t∈Icc (-a) 1) : p+t • q∈minimizingVectors x :=
    hline₀ t ⟨by have := min_le_left a₀ (1/(2*B)); change a ≤ a₀ at this; linarith [ht.1],ht.2⟩
  let i := j.rev
  let s : ℝ → ℝ := fun t => (endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev
  have hSym (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Icc (-a) 1) :
      (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric :=
    shearedRadialOperator_symmetric (contracted_minimizer_mem_injectivityDomain (hline t ht)
      (by linarith [hd.2]) (by linarith [hd.1]))
  let f : ℝ → ℝ → ℝ := fun δ t =>
    if H : δ∈Ioc (0:ℝ) (1/2) ∧ t∈Icc (-a) 1 then (hSym δ H.1 t H.2).eigenvalues rfl i else 0
  have hf (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Icc (-a) 1) :
      f δ t=(hSym δ hd t ht).eigenvalues rfl i := by
    dsimp only [f]
    rw [dite_eq_left (show δ∈Ioc (0:ℝ) (1/2) ∧ t∈Icc (-a) 1 from ⟨hd,ht⟩)]
  have hI (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : t∈Icc (-a) 1 := ⟨by linarith [ht.1],ht.2⟩
  have hSmall (t : ℝ) (ht : t∈Icc (0:ℝ) (1-e)) : t∈Icc (0:ℝ) 1 :=
    ⟨ht.1,by linarith [ht.2]⟩
  have hInt (t : ℝ) (ht : t∈Icc (0:ℝ) (1-e)) : t∈Icc (-a+d) (1-d) := by
    have hda : d ≤ a := min_le_left _ _
    have hde : d ≤ e := min_le_right _ _
    constructor <;> linarith [ht.1,ht.2]
  have h0 : (0:ℝ)∈Icc (-a) 1 := ⟨by linarith,by norm_num⟩
  have h1 : (1:ℝ)∈Icc (-a) 1 := ⟨by linarith,le_rfl⟩
  have hm : 1-e∈Icc (-a) 1 := ⟨by linarith,by linarith⟩
  have HS (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : 0 ≤ s t :=
    (endpointExpDifferential x (p+t • q)).toLinearMap.singularValues_nonneg i.rev
  have HD' : s 1 ≤ D := HD x (p+1 • q) (hline 1 h1) i.rev
  have HP (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      l*δ/(s t+δ)-b*δ ≤ f δ t ∧ f δ t ≤ u*δ/(s t+δ)+b*δ := by
    obtain ⟨hF,H⟩ := HSp x p q hpq hβ hline δ hd t (hI t ht)
    rw [hf δ hd t (hI t ht)]
    exact H i
  have HL (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (r : ℝ) (hr : r∈Icc (0:ℝ) (1-e))
      (t : ℝ) (ht : t∈Icc (0:ℝ) (1-e)) : |f δ t-f δ r| ≤ K*|t-r| := by
    rw [hf δ hd t (hI t (hSmall t ht)),hf δ hd r (hI r (hSmall r hr))]
    exact bounded_matrix_convex_eigen_secant (hSym δ hd)
      (hmtw.shearedRadialOperator_convexOn x p q hpq.ne' hd hline) hC.le hdpos
      (fun t ht v => (HB x p q hpq hβ hline δ hd t ht v).2)
      (hInt r hr) (hInt t ht) (hI r (hSmall r hr)) (hI t (hSmall t ht)) rfl i
  have HE (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) : f δ (1-e) ≤ (1-e)*f δ 1+e*C := by
    rw [hf δ hd (1-e) hm,hf δ hd 1 h1]
    exact matrix_convex_eigen_endpoint ha.le ⟨he0.le,he1.le⟩ (hSym δ hd)
      (hmtw.shearedRadialOperator_convexOn x p q hpq.ne' hd hline)
      (fun v => (le_abs_self _).trans (HB x p q hpq hβ hline δ hd 0 h0 v).2) hm h1 rfl i
  have result := HC s f HS HD' HP HL HE
  have hz : p+(0:ℝ) • q=p := by simp
  have ho : p+(1:ℝ) • q=p+q := by simp
  have hsz : s 0=(endpointExpDifferential x p).toLinearMap.singularValues j := by
    change (endpointExpDifferential x (p+(0:ℝ) • q)).toLinearMap.singularValues i.rev=_
    rw [hz,show i.rev=j from Fin.rev_rev j]
  have hso : s 1=(endpointExpDifferential x (p+q)).toLinearMap.singularValues j := by
    change (endpointExpDifferential x (p+(1:ℝ) • q)).toLinearMap.singularValues i.rev=_
    rw [ho,show i.rev=j from Fin.rev_rev j]
  rwa [hsz,hso] at result
end AffineSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.uniform_extended_spectral_comparison_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.uniform_extended_spectral_comparison_oai.{u_1}
