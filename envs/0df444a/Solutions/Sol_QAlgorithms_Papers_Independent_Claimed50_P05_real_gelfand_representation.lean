-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.real_gelfand_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:58:07.666469+00:00
-- url     : https://prove2.me/submissions/032bad85-312d-4ffb-96fb-691829bebced

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

open Set Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P05

namespace X7Z10R

universe u

variable {B : Type u} [CStarAlgebra B]

/-- The complexification `A + iA` of a real star subalgebra. -/
def X7_cplx (A : StarSubalgebra ℝ B) (hself : ∀ a : A, star (a : B) = (a : B)) :
    StarSubalgebra ℂ B where
  carrier := {c | ∃ a ∈ A, ∃ b ∈ A, c = a + Complex.I • b}
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a' - b * b', A.sub_mem (A.mul_mem ha ha') (A.mul_mem hb hb'),
      a * b' + b * a', A.add_mem (A.mul_mem ha hb') (A.mul_mem hb ha'), ?_⟩
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
      neg_smul, one_smul, smul_add, smul_sub]
    abel
  add_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a + a', A.add_mem ha ha', b + b', A.add_mem hb hb', ?_⟩
    rw [smul_add]; abel
  algebraMap_mem' := by
    intro z
    refine ⟨z.re • (1 : B), A.smul_mem A.one_mem z.re, z.im • (1 : B),
      A.smul_mem A.one_mem z.im, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul,
      ← add_smul]
    congr 1
    rw [mul_comm]
    exact (Complex.re_add_im z).symm
  star_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, -b, A.neg_mem hb, ?_⟩
    rw [star_add, star_smul, hself ⟨a, ha⟩, hself ⟨b, hb⟩]
    simp

theorem X7_mem_cplx (A : StarSubalgebra ℝ B) (hself : ∀ a : A, star (a : B) = (a : B))
    (c : B) : c ∈ X7_cplx A hself ↔ ∃ a ∈ A, ∃ b ∈ A, c = a + Complex.I • b := Iff.rfl

theorem X7_A_le (A : StarSubalgebra ℝ B) (hself : ∀ a : A, star (a : B) = (a : B))
    (a : B) (ha : a ∈ A) : a ∈ X7_cplx A hself :=
  ⟨a, ha, 0, A.zero_mem, by simp⟩

/-- Self-adjoint elements of the complexification lie in `A`. -/
theorem X7_sa_mem (A : StarSubalgebra ℝ B) (hself : ∀ a : A, star (a : B) = (a : B))
    (c : B) (hc : c ∈ X7_cplx A hself) (hs : star c = c) : c ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hc
  have hsI : star Complex.I = -Complex.I := by simp
  rw [star_add, star_smul, hself ⟨a, ha⟩, hself ⟨b, hb⟩, hsI] at hs
  replace hs := add_left_cancel hs
  have h2 : (2 * Complex.I) • b = 0 := by
    rw [mul_smul, two_smul]
    have : (-Complex.I) • b = -(Complex.I • b) := neg_smul _ _
    rw [this] at hs
    nth_rw 1 [← hs]
    exact neg_add_cancel _
  have hb0 : b = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (by simp)
    · exact h
  rw [hb0, smul_zero, add_zero]
  exact ha

theorem X7_cplx_closed (A : StarSubalgebra ℝ B) (hclosed : IsClosed (A : Set B))
    (hself : ∀ a : A, star (a : B) = (a : B)) :
    IsClosed ((X7_cplx A hself : StarSubalgebra ℂ B) : Set B) := by
  have hset : ((X7_cplx A hself : StarSubalgebra ℂ B) : Set B) =
      (fun c : B => (2⁻¹ : ℝ) • (c + star c)) ⁻¹' (A : Set B) ∩
        (fun c : B => (2⁻¹ : ℝ) • ((-Complex.I) • (c - star c))) ⁻¹' (A : Set B) := by
    ext c
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      have hs : star (a + Complex.I • b) = a + (-Complex.I) • b := by
        rw [star_add, star_smul, hself ⟨a, ha⟩, hself ⟨b, hb⟩]
        simp
      simp only [Set.mem_inter_iff, Set.mem_preimage, hs]
      constructor
      · have : (2⁻¹ : ℝ) • (a + Complex.I • b + (a + (-Complex.I) • b)) = a := by
          rw [neg_smul]
          have : a + Complex.I • b + (a + -(Complex.I • b)) = (2 : ℝ) • a := by
            rw [two_smul]; abel
          rw [this, smul_smul]; norm_num
        rw [this]; exact ha
      · have : (2⁻¹ : ℝ) • ((-Complex.I) • (a + Complex.I • b - (a + (-Complex.I) • b))) = b := by
          have e : a + Complex.I • b - (a + (-Complex.I) • b) = (2 * Complex.I) • b := by
            rw [neg_smul, mul_smul, two_smul]; abel
          rw [e, smul_smul, ← Complex.coe_smul, smul_smul,
            show ((2⁻¹ : ℝ) : ℂ) * (-Complex.I * (2 * Complex.I)) = 1 by
              push_cast; linear_combination (-1 : ℂ) * Complex.I_sq, one_smul]
        rw [this]; exact hb
    · rintro ⟨h1, h2⟩
      refine ⟨_, h1, _, h2, ?_⟩
      show c = (2⁻¹ : ℝ) • (c + star c) +
        Complex.I • ((2⁻¹ : ℝ) • ((-Complex.I) • (c - star c)))
      rw [smul_comm Complex.I (2⁻¹ : ℝ), smul_smul Complex.I (-Complex.I)]
      simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
      rw [← smul_add, show c + star c + (c - star c) = (2 : ℝ) • c by rw [two_smul]; abel, smul_smul]
      norm_num
  rw [hset]
  apply IsClosed.inter
  · exact hclosed.preimage (continuous_const.smul (continuous_id.add continuous_star))
  · exact hclosed.preimage (continuous_const.smul (continuous_const.smul
      (continuous_id.sub continuous_star)))

theorem X7_cplx_comm (A : StarSubalgebra ℝ B)
    (hcomm : ∀ a b : A, (a : B) * (b : B) = (b : B) * (a : B))
    (hself : ∀ a : A, star (a : B) = (a : B)) (x y : B) (hx : x ∈ X7_cplx A hself)
    (hy : y ∈ X7_cplx A hself) : x * y = y * x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨a', ha', b', hb', rfl⟩ := hy
  have c1 := hcomm ⟨a, ha⟩ ⟨a', ha'⟩
  have c2 := hcomm ⟨a, ha⟩ ⟨b', hb'⟩
  have c3 := hcomm ⟨b, hb⟩ ⟨a', ha'⟩
  have c4 := hcomm ⟨b, hb⟩ ⟨b', hb'⟩
  simp only at c1 c2 c3 c4
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, c1, c2, c3, c4, smul_add]
  abel

end X7Z10R

end QAlgorithms.Papers.Independent.Claimed50.P05

end

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

universe u_1

open QAlgorithms.Papers.Independent.Claimed50.P05.X7Z10R in
theorem solution {B : Type u_1} [CStarAlgebra B]
    (A : StarSubalgebra ℝ B) (hclosed : IsClosed (A : Set B))
    (hcomm : ∀ a b : A, (a : B) * (b : B) = (b : B) * (a : B))
    (hself : ∀ a : A, star (a : B) = (a : B)) :
    ∃ (Z : Type u_1) (t : TopologicalSpace Z),
      letI := t
      ∃ (hc : CompactSpace Z) (ht : T2Space Z),
        letI := hc
        letI := ht
        ∃ e : C(Z, ℝ) ≃⋆ₐ[ℝ] A, Isometry e := by
  set C := X7_cplx A hself with hCdef
  haveI hCc : IsClosed (C : Set B) := X7_cplx_closed A hclosed hself
  letI inst : CommCStarAlgebra C :=
    { StarSubalgebra.cstarAlgebra C with
      mul_comm := fun x y => Subtype.ext (X7_cplx_comm A hcomm hself x y x.2 y.2) }
  let Γ := gelfandStarTransform C
  have hΓiso : ∀ c : C, ‖Γ c‖ = ‖c‖ := fun c =>
    (AddMonoidHomClass.isometry_iff_norm _).mp (gelfandTransform_isometry C) c
  refine ⟨WeakDual.characterSpace ℂ C, inferInstance, inferInstance, inferInstance, ?_⟩
  -- real-valued functions to complex-valued
  let toC : C(WeakDual.characterSpace ℂ C, ℝ) → C(WeakDual.characterSpace ℂ C, ℂ) :=
    fun f => ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hmem : ∀ f, ((Γ.symm (toC f) : C) : B) ∈ A := by
    intro f
    apply X7_sa_mem A hself _ (Γ.symm (toC f)).2
    have : star (Γ.symm (toC f)) = Γ.symm (toC f) := by
      rw [← map_star]
      congr 1
      ext z
      simp [toC, Complex.conj_ofReal]
    exact congrArg Subtype.val this
  have hreal : ∀ a : A, ∀ z, ((Γ ⟨(a : B), X7_A_le A hself _ a.2⟩ z).re : ℂ) =
      Γ ⟨(a : B), X7_A_le A hself _ a.2⟩ z := by
    intro a z
    have hs : star (⟨(a : B), X7_A_le A hself _ a.2⟩ : C) = ⟨(a : B), X7_A_le A hself _ a.2⟩ :=
      Subtype.ext (hself a)
    have h := congrArg (fun g => g z) (map_star Γ (⟨(a : B), X7_A_le A hself _ a.2⟩ : C))
    simp only [hs] at h
    have h' : star (Γ ⟨(a : B), X7_A_le A hself _ a.2⟩ z) =
        Γ ⟨(a : B), X7_A_le A hself _ a.2⟩ z := by
      rw [← ContinuousMap.star_apply, ← h]
    exact Complex.conj_eq_iff_re.mp (by rw [starRingEnd_apply]; exact h')
  let fwd : C(WeakDual.characterSpace ℂ C, ℝ) → A := fun f => ⟨_, hmem f⟩
  let bwd : A → C(WeakDual.characterSpace ℂ C, ℝ) := fun a =>
    ⟨fun z => (Γ ⟨(a : B), X7_A_le A hself _ a.2⟩ z).re,
      Complex.continuous_re.comp (Γ ⟨(a : B), X7_A_le A hself _ a.2⟩).continuous⟩
  have hleft : ∀ f, bwd (fwd f) = f := by
    intro f
    ext z
    have : (⟨((fwd f : A) : B), X7_A_le A hself _ (fwd f).2⟩ : C) = Γ.symm (toC f) :=
      Subtype.ext rfl
    simp only [bwd, ContinuousMap.coe_mk]
    rw [this, StarAlgEquiv.apply_symm_apply]
    simp [toC]
  have hright : ∀ a, fwd (bwd a) = a := by
    intro a
    have h1 : toC (bwd a) = Γ ⟨(a : B), X7_A_le A hself _ a.2⟩ := by
      ext z
      simp only [toC, bwd, ContinuousMap.coe_mk]
      exact hreal a z
    apply Subtype.ext
    simp only [fwd]
    rw [h1, StarAlgEquiv.symm_apply_apply]
  have htoC_mul : ∀ f g, toC (f * g) = toC f * toC g := by
    intro f g; ext z; simp [toC]
  have htoC_add : ∀ f g, toC (f + g) = toC f + toC g := by
    intro f g; ext z; simp [toC]
  have htoC_smul : ∀ (r : ℝ) f, toC (r • f) = (r : ℂ) • toC f := by
    intro r f; ext z; simp [toC]
  let e : C(WeakDual.characterSpace ℂ C, ℝ) ≃⋆ₐ[ℝ] A :=
    { toFun := fwd
      invFun := bwd
      left_inv := hleft
      right_inv := hright
      map_mul' := by
        intro f g
        apply Subtype.ext
        simp only [fwd, htoC_mul, map_mul]
        rfl
      map_add' := by
        intro f g
        apply Subtype.ext
        simp only [fwd, htoC_add, map_add]
        rfl
      map_star' := by
        intro f
        apply Subtype.ext
        have : star f = f := by ext z; simp
        rw [this]
        exact (hself (fwd f)).symm
      map_smul' := by
        intro r f
        apply Subtype.ext
        simp only [fwd, htoC_smul, map_smul]
        change ((r : ℂ) • ((Γ.symm (toC f) : C) : B)) = r • ((Γ.symm (toC f) : C) : B)
        exact Complex.coe_smul r _ }
  refine ⟨e, ?_⟩
  apply AddMonoidHomClass.isometry_of_norm
  intro f
  change ‖((Γ.symm (toC f) : C) : B)‖ = ‖f‖
  have h1 : ‖((Γ.symm (toC f) : C) : B)‖ = ‖toC f‖ := by
    have := hΓiso (Γ.symm (toC f))
    rw [StarAlgEquiv.apply_symm_apply] at this
    exact this.symm
  rw [h1]
  apply le_antisymm
  · refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun z => ?_)
    simp only [toC, ContinuousMap.coe_mk, Complex.norm_real]
    exact f.norm_coe_le_norm z
  · refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun z => ?_)
    have := (toC f).norm_coe_le_norm z
    simpa [toC, Complex.norm_real] using this
