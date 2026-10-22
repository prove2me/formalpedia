-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.finite_projective_dual
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:34:24.062729+00:00
-- url     : https://prove2.me/submissions/d6fb8d0c-e941-4188-9d0d-b438893a55c7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

/-- canonical map (A → R) ⊗ M → (A → M). -/
def g74b_phi (R A M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    (A → R) ⊗[R] M →ₗ[R] (A → M) :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (g : A → R) (m : M) => fun x => g x • m)
    (fun g g' m => by funext x; simp [add_smul])
    (fun r g m => by funext x; simp [mul_smul])
    (fun g m m' => by funext x; simp [smul_add])
    (fun r g m => by funext x; simp [smul_comm r (g x) m]))

theorem g74b_dualDistrib_eq (R A : Type u) [CommRing R] [AddCommGroup A] [Module R A] :
    TensorProduct.dualDistrib R A A =
      (TensorProduct.lift.equiv (RingHom.id R) A A R).toLinearMap ∘ₗ dualTensorHom R A (Module.Dual R A) := by
  apply TensorProduct.ext'
  intro f g
  apply TensorProduct.ext'
  intro m n
  simp [TensorProduct.dualDistrib_apply, dualTensorHom_apply]

theorem g74b_phi_dth {R A P X : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X]
    (b : P →ₗ[R] A →ₗ[R] R) (z : P ⊗[R] X) :
    g74b_phi R A X (TensorProduct.map (evaluationEmbedding b) LinearMap.id z) =
      ⇑(dualTensorHom R A X (LinearMap.rTensor X b z)) := by
  induction z using TensorProduct.induction_on with
  | zero => funext a; simp
  | tmul f x => funext a; rfl
  | add z z' hz hz' =>
    rw [map_add, map_add, hz, hz', map_add, map_add]
    rfl

theorem g74b_rTensor_inj_of_leftInv {R P P' X : Type u} [CommSemiring R]
    [AddCommMonoid P] [Module R P] [AddCommMonoid P'] [Module R P'] [AddCommMonoid X] [Module R X]
    (f : P →ₗ[R] P') (g : P' →ₗ[R] P) (hgf : g ∘ₗ f = LinearMap.id) :
    Function.Injective (LinearMap.rTensor X f) := by
  apply Function.LeftInverse.injective (g := LinearMap.rTensor X g)
  intro z
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hgf, LinearMap.rTensor_id,
    LinearMap.id_apply]

theorem g74b_pure_of_leftInv {R A P X : Type u} [CommRing R] [Ring A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X]
    (b : P →ₗ[R] A →ₗ[R] R) (g : Module.Dual R A →ₗ[R] P) (hgb : g ∘ₗ b = LinearMap.id) :
    Function.Injective (TensorProduct.map (evaluationEmbedding b) (LinearMap.id : X →ₗ[R] X)) := by
  intro y y' hyy
  apply g74b_rTensor_inj_of_leftInv b g hgb
  apply (dualTensorHom_bijective (R := R) (M := A) (N := X)).1
  apply DFunLike.coe_injective
  rw [← g74b_phi_dth, ← g74b_phi_dth, hyy]

theorem g74b_pure_of_bij {R A P X : Type u} [CommRing R] [Ring A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X]
    (b : P →ₗ[R] A →ₗ[R] R) (hb : Function.Bijective b) :
    IsTensorInjective (evaluationEmbedding b) X := by
  unfold IsTensorInjective
  let e : P ≃ₗ[R] Module.Dual R A := LinearEquiv.ofBijective b hb
  apply g74b_pure_of_leftInv b e.symm.toLinearMap
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
  exact e.symm_apply_apply f

/-- Remark 2.12, PDF p.7: equality of duals, purity in all functions, and canonical tensor duality. -/
theorem solution [IsNoetherianRing R] [Module.Finite R A]
    [Module.Projective R A] :
    finiteDual R A = ⊤ ∧
    IsPureMap (R := R) (N := finiteDual R A) (L := A → R)
      (evaluationEmbedding (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A)) ∧
    Function.Bijective (TensorProduct.dualDistrib R A A) := by
  have htop : finiteDual R A = ⊤ := by
    rw [eq_top_iff]
    intro f _
    apply Submodule.subset_span
    refine ⟨⊥, ?_, fun a ha => ?_⟩
    · unfold IsCofiniteLeft LeftQuotient
      infer_instance
    · have : a = 0 := (Submodule.mem_bot A).1 ha
      rw [this, map_zero]
  refine ⟨htop, ⟨?_, ?_⟩, ?_⟩
  · intro f g hfg
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact congrFun hfg a
  · intro X _ _
    unfold finiteDualPairing
    generalize finiteDual R A = S at htop ⊢
    subst htop
    apply g74b_pure_of_bij
    refine ⟨?_, ?_⟩
    · exact Subtype.val_injective
    · intro φ
      exact ⟨⟨φ, Submodule.mem_top⟩, rfl⟩
  · rw [g74b_dualDistrib_eq, LinearMap.coe_comp]
    exact (LinearEquiv.bijective _).comp dualTensorHom_bijective


end Cofinite



end
