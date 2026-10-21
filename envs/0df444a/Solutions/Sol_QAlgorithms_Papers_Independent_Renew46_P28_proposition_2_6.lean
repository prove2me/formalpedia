-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.proposition_2_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:21:28.584412+00:00
-- url     : https://prove2.me/submissions/7f8e3f13-c1c1-4c3d-906f-33058dcee0a3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28
open QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w


open Matrix

theorem g66q_cia {K : Type u} [Field K] [TopologicalSpace K] [T2Space K] [IsTopologicalDivisionRing K]
    {A : Type v} [Ring A] [Algebra K A] [FiniteDimensional K A] [TopologicalSpace A]
    {n : ℕ} (b : Module.Basis (Fin n) K A) (hb : Topology.IsInducing b.equivFun) :
    continuousInverseAlgebra K A := by
  classical
  obtain ⟨e, he_def⟩ : ∃ e, e = b.equivFun := ⟨_, rfl⟩
  rw [← he_def] at hb
  have he : Continuous e := hb.continuous
  have hcont : ∀ {X : Type v} [TopologicalSpace X] (f : X → A),
      Continuous (fun x => e (f x)) → Continuous f := fun f h => hb.continuous_iff.2 h
  have hexp : ∀ x : A, x = ∑ i, e x i • b i := fun x => by rw [he_def]; exact (b.sum_equivFun x).symm
  have hci : ∀ i, Continuous fun x : A => e x i := fun i => (continuous_apply i).comp he
  let L := Algebra.leftMulMatrix b
  have hLe : ∀ a, L a = ∑ i, e a i • L (b i) := by
    intro a
    calc L a = L (∑ i, e a i • b i) := congrArg L (hexp a)
      _ = ∑ i, e a i • L (b i) := by rw [map_sum]; simp_rw [map_smul]
  have hL : Continuous (fun a : A => L a) := by
    have : (fun a => L a) = fun a => ∑ i, e a i • L (b i) := funext hLe
    rw [this]
    fun_prop
  have hmul : ∀ x y : A, e (x * y) = ∑ i, ∑ j, (e x i * e y j) • e (b i * b j) := by
    intro x y
    conv_lhs => rw [hexp x, hexp y]
    rw [Finset.sum_mul_sum]
    simp only [map_sum, map_smul, smul_mul_smul_comm]
  have hmulv : ∀ a x : A, L a *ᵥ e x = e (a * x) := by
    intro a x
    simp only [L, Algebra.leftMulMatrix_apply, he_def, Module.Basis.equivFun_apply]
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  have hunit : ∀ a : A, IsUnit a ↔ (L a).det ≠ 0 := by
    intro a
    constructor
    · intro h
      exact (Matrix.isUnit_iff_isUnit_det _).1 (h.map L) |>.ne_zero
    · intro h
      have hdet : LinearMap.det (Algebra.lmul K A a) ≠ 0 := by
        rw [← LinearMap.det_toMatrix b]
        simpa [L, Algebra.leftMulMatrix_apply] using h
      have hu : IsUnit (Algebra.lmul K A a) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
      have hac : a * c = 1 := hc
      have hca : c * a = 1 := by
        apply Algebra.leftMulMatrix_injective b
        rw [map_mul, map_one]
        apply mul_eq_one_comm.1
        rw [← map_mul, hac, map_one]
      exact ⟨⟨a, c, hac, hca⟩, rfl⟩
  have hT2 : T2Space A := (Topology.IsEmbedding.mk hb e.injective).t2Space
  have hadd : ContinuousAdd A := ⟨(hb.continuous_iff (f := fun p : A × A => p.1 + p.2)).2
    (by simp only [Function.comp_def, map_add]; fun_prop)⟩
  have hneg : ContinuousNeg A := ⟨(hb.continuous_iff (f := fun p : A => -p)).2
    (by simp only [Function.comp_def, map_neg]; fun_prop)⟩
  have hmulc : ContinuousMul A := ⟨(hb.continuous_iff (f := fun p : A × A => p.1 * p.2)).2 (by
    have : (fun p : A × A => e (p.1 * p.2)) =
        fun p => ∑ i, ∑ j, (e p.1 i * e p.2 j) • e (b i * b j) := funext fun p => hmul p.1 p.2
    simp only [Function.comp_def]
    rw [this]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (((hci i).comp continuous_fst).mul ((hci j).comp continuous_snd)).smul continuous_const)⟩
  have hring : IsTopologicalRing A := {}
  have hsmul : ContinuousSMul K A := ⟨(hb.continuous_iff (f := fun p : K × A => p.1 • p.2)).2
    (by simp only [Function.comp_def, map_smul]; fun_prop)⟩
  refine ⟨hT2, hring, hsmul, ?_, ?_⟩
  · have : {a : A | IsUnit a} = (fun a => (L a).det) ⁻¹' {0}ᶜ := by
      ext a; simp [hunit]
    rw [this]
    exact isOpen_compl_singleton.preimage (hL.matrix_det)
  · apply hb.continuous_iff.2
    simp only [Function.comp_def]
    have key : ∀ a : {a : A // IsUnit a}, e (Ring.inverse a.val) =
        (L a.val)⁻¹ *ᵥ e 1 := by
      intro a
      have hd : IsUnit (L a.val).det := isUnit_iff_ne_zero.2 ((hunit _).1 a.2)
      have h1 : a.val * Ring.inverse a.val = 1 := Ring.mul_inverse_cancel _ a.2
      conv_rhs => rw [← h1, ← hmulv]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
    simp_rw [key, Matrix.inv_def, Ring.inverse_eq_inv']
    have hd : ∀ a : {a : A // IsUnit a}, (L a.val).det ≠ 0 := fun a => (hunit _).1 a.2
    have h1 : Continuous fun a : {a : A // IsUnit a} => L a.val := hL.comp continuous_subtype_val
    exact ((h1.matrix_det.inv₀ hd).smul h1.matrix_adjugate).matrix_mulVec continuous_const

/-- Proposition 2.6, PDF p.18: the constructed canonical vector topology
makes every finite-dimensional unital associative algebra a CIA. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : TopologicalSpace A := canonicalFiniteVectorTopology K A
    continuousInverseAlgebra K A := by
  letI : TopologicalSpace A := canonicalFiniteVectorTopology K A
  exact g66q_cia (Module.finBasis K A) ⟨rfl⟩

