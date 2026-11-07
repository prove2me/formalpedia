-- Prove2me | solution 1 for StrongConv.norm_toFull_eq_fullNorm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T09:34:13.759202+00:00
-- url     : https://prove2.me/submissions/058984bd-6f40-4f83-a30d-88c3d3e7c3b9

import Definitions.Def_StrongConv
import Definitions.Def_FullGroupCStar
import Definitions.Def_StrongConvFull
import Theorems.Thm_StrongConv_isLUB_fullNorm_and_norm_eval_le_fullNorm
import Mathlib

section
section
/-!
# CGTvH p. 12: `‖P(u, u*)‖` in `M_D(C*(F_d))` is `P.fullNorm`

`StrongConv.norm_toFull_eq_fullNorm`, from the published
`StrongConv.isLUB_fullNorm_and_norm_eval_le_fullNorm`.

* `blockHom f`: a *-homomorphism `f : A → B(H)` applied entrywise, then read as a block operator on
  `D` copies of `H`; a *-homomorphism `M_D(A) → B(H^D)`.
* `blockHom (lift π) P.toFull = P.eval (π ∘ of)`.
* `≥`: each tuple of unitary matrices is a representation on `EuclideanSpace`; *-homomorphisms of
  C*-algebras are contractive.
* `≤`: the representations of `C*(F_d)` separate points, so the product of all `blockHom (lift π)`
  into `ℓ^∞` is an injective, hence isometric, *-homomorphism.
-/

noncomputable section

open UniformSpace

namespace StrongConv.FullAux

/-! ## Block operators -/

section Block

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {D : ℕ}

/-- The operator on `D` copies of `H` with blocks `M a b`. -/
def blockOp (M : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) :
    PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H) :=
  ∑ a : Fin D, ∑ b : Fin D,
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => H)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.single ℂ (fun _ : Fin D => H) a).comp
        ((M a b).comp (PiLp.proj 2 (fun _ : Fin D => H) b))))

lemma blockOp_apply (M : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) (x : PiLp 2 (fun _ : Fin D => H))
    (a : Fin D) : blockOp M x a = ∑ b, M a b (x b) := by
  simp [blockOp, ContinuousLinearMap.sum_apply, Pi.single_apply]

lemma tensorOp_apply (A : Matrix (Fin D) (Fin D) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin D => H)) (a : Fin D) : tensorOp A T x a = ∑ b, A a b • T (x b) := by
  simp [tensorOp, ContinuousLinearMap.sum_apply, Pi.single_apply]

lemma blockOp_ext {T S : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)}
    (h : ∀ x a, T x a = S x a) : T = S :=
  ContinuousLinearMap.ext fun x => PiLp.ext fun a => h x a

lemma blockOp_add (M N : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) :
    blockOp (M + N) = blockOp M + blockOp N :=
  blockOp_ext fun x a => by
    simp [blockOp_apply, Finset.sum_add_distrib]

lemma blockOp_smul (c : ℂ) (M : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) :
    blockOp (c • M) = c • blockOp M :=
  blockOp_ext fun x a => by
    simp [blockOp_apply, Finset.smul_sum]

lemma blockOp_zero : blockOp (0 : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) = 0 :=
  blockOp_ext fun x a => by simp [blockOp_apply]

lemma blockOp_one : blockOp (1 : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) = 1 :=
  blockOp_ext fun x a => by
    rw [blockOp_apply, Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq]; rfl
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), ContinuousLinearMap.zero_apply]
    · intro h; exact absurd (Finset.mem_univ a) h

lemma blockOp_mul (M N : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) :
    blockOp (M * N) = blockOp M * blockOp N :=
  blockOp_ext fun x a => by
    simp only [blockOp_apply, ContinuousLinearMap.mul_apply, Matrix.mul_apply,
      ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.mul_apply]
    rw [Finset.sum_comm]

lemma blockOp_conjTranspose (M : Matrix (Fin D) (Fin D) (H →L[ℂ] H)) :
    blockOp M.conjTranspose = star (blockOp M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, blockOp_apply, Matrix.conjTranspose_apply, sum_inner, inner_sum,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [Finset.sum_comm]

lemma blockOp_eq_zero {M : Matrix (Fin D) (Fin D) (H →L[ℂ] H)} (h : blockOp M = 0) (a b : Fin D) :
    M a b = 0 := by
  ext v
  have := congrArg (fun T => T (WithLp.toLp 2 (Pi.single b v)) a) h
  simpa [blockOp_apply, Pi.single_apply, apply_ite] using this

end Block

/-! ## Entrywise *-homomorphisms into block operators -/

section BlockHom

variable {A : Type*} [CStarAlgebra A] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {D : ℕ}

/-- `f` applied entrywise, read as a block operator. -/
def blockHom (f : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    CStarMatrix (Fin D) (Fin D) A →⋆ₐ[ℂ]
      (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) where
  toFun X := blockOp (fun a b => f (X a b))
  map_one' := by
    refine (congrArg blockOp ?_).trans blockOp_one
    funext a b
    rw [CStarMatrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  map_mul' X Y := by
    refine (congrArg blockOp ?_).trans (blockOp_mul _ _)
    funext a b
    rw [CStarMatrix.mul_apply]
    show f (∑ j, X a j * Y j b) = ∑ j, f (X a j) * f (Y j b)
    simp only [map_sum, map_mul]
  map_zero' := by
    refine (congrArg blockOp ?_).trans blockOp_zero
    funext a b
    rw [CStarMatrix.zero_apply, map_zero]; rfl
  map_add' X Y := by
    refine (congrArg blockOp ?_).trans (blockOp_add _ _)
    funext a b
    rw [CStarMatrix.add_apply, map_add]; rfl
  commutes' r := by
    have h : algebraMap ℂ (CStarMatrix (Fin D) (Fin D) A) r = r • 1 :=
      Algebra.algebraMap_eq_smul_one r
    show blockOp (fun a b => f ((algebraMap ℂ (CStarMatrix (Fin D) (Fin D) A) r) a b)) = _
    simp only [h]
    rw [Algebra.algebraMap_eq_smul_one, ← blockOp_one, ← blockOp_smul]
    congr 1
    funext a b
    simp only [CStarMatrix.smul_apply, CStarMatrix.one_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  map_star' X := by
    refine (congrArg blockOp ?_).trans (blockOp_conjTranspose _)
    funext a b
    rw [CStarMatrix.star_apply]
    show f (star (X b a)) = star (f (X b a))
    exact map_star f _

lemma blockHom_apply (f : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (X : CStarMatrix (Fin D) (Fin D) A) :
    blockHom f X = blockOp (fun a b => f (X a b)) := rfl

end BlockHom

/-! ## The bridge: `blockHom (lift π) P.toFull = P.eval (π ∘ of)` -/

section Bridge

variable {D d : ℕ}

open FullGroupCStar

/-- The unitaries `π(gᵢ)` of a representation of the free group. -/
def repU (π : Rep (FreeGroup (Fin d))) : Fin d → π.H →L[ℂ] π.H :=
  fun i => (π.ρ (FreeGroup.of i) : π.H →L[ℂ] π.H)

lemma lift_letterElt (π : Rep (FreeGroup (Fin d))) (l : Fin d ⊕ Fin d) :
    lift π (NCPoly.letterElt l) = letterOp (repU π) l := by
  cases l with
  | inl i =>
    show lift π (of (FreeGroup.of i) : FullGroupCStar _) = _
    exact lift_of π _
  | inr i =>
    show lift π (star (of (FreeGroup.of i) : FullGroupCStar _)) = star _
    rw [map_star, lift_of]; rfl

lemma lift_wordElt (π : Rep (FreeGroup (Fin d))) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    lift π (NCPoly.wordElt w) = wordOp (repU π) w := by
  rw [NCPoly.wordElt, wordOp, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => lift_letterElt π l

lemma blockHom_toFull (π : Rep (FreeGroup (Fin d))) (P : NCPoly D d) :
    blockHom (lift π) P.toFull = P.eval (repU π) := by
  have hM : (fun a b => lift π (P.toFull a b) : Matrix (Fin D) (Fin D) (π.H →L[ℂ] π.H)) =
      fun a b => ∑ w ∈ P.support, P w a b • wordOp (repU π) w := by
    funext a b
    show lift π (∑ w ∈ P.support, P w a b • NCPoly.wordElt w) = _
    simp only [map_sum, map_smul, lift_wordElt]
  rw [blockHom_apply, hM]
  refine blockOp_ext fun x a => ?_
  refine (blockOp_apply _ x a).trans ?_
  simp only [NCPoly.eval, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    tensorOp_apply, ContinuousLinearMap.smul_apply]
  exact Finset.sum_comm

end Bridge

/-! ## The representations separate the points of `C*(G)` -/

section Separate

open FullGroupCStar

variable {G : Type*} [Group G]

lemma eq_zero_of_forall_lift_eq_zero (a : FullGroupCStar G) (h : ∀ π : Rep G, lift π a = 0) :
    a = 0 := by
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, hx⟩ : ∃ x : PreAlg G, dist a (x : FullGroupCStar G) < ε / 2 :=
    Completion.denseRange_coe.exists_dist_lt a (half_pos hε)
  rw [dist_eq_norm] at hx
  have hxn : ‖(x : FullGroupCStar G)‖ ≤ ‖a - x‖ := by
    rw [Completion.norm_coe, PreAlg.norm_def]
    refine maxNorm_le (norm_nonneg _) fun π => ?_
    rw [← lift_coe π x]
    calc ‖lift π (x : FullGroupCStar G)‖ = ‖lift π ((x : FullGroupCStar G) - a)‖ := by
          rw [map_sub, h π, sub_zero]
      _ ≤ ‖(x : FullGroupCStar G) - a‖ := NonUnitalStarAlgHom.norm_apply_le _ _
      _ = ‖a - x‖ := norm_sub_rev _ _
  calc ‖a‖ = ‖(a - x) + (x : FullGroupCStar G)‖ := by rw [sub_add_cancel]
    _ ≤ ‖a - x‖ + ‖(x : FullGroupCStar G)‖ := norm_add_le _ _
    _ ≤ 0 + ε := by linarith

end Separate

/-! ## The product of all block representations into `ℓ^∞` -/

section Product

open FullGroupCStar

variable {G : Type} [Group G] {D : ℕ}

/-- The C*-algebra `B(H_π^D)` of block operators of a representation `π`. -/
def BlockFam (G : Type) [Group G] (D : ℕ) (π : Rep G) : Type :=
  PiLp 2 (fun _ : Fin D => π.H) →L[ℂ] PiLp 2 (fun _ : Fin D => π.H)

instance (π : Rep G) : CStarAlgebra (BlockFam G D π) :=
  inferInstanceAs (CStarAlgebra (PiLp 2 (fun _ : Fin D => π.H) →L[ℂ] PiLp 2 (fun _ : Fin D => π.H)))

instance (π : Rep G) : NonUnitalCStarAlgebra (BlockFam G D π) := inferInstance

instance (π : Rep G) : NonUnitalNormedRing (BlockFam G D π) := inferInstance

/-- `X ↦ (blockHom (lift π) X)_π`, a *-homomorphism into `ℓ^∞`. -/
def prodHom : CStarMatrix (Fin D) (Fin D) (FullGroupCStar G) →⋆ₙₐ[ℂ]
    lp (BlockFam G D) ⊤ where
  toFun X := ⟨fun π => (blockHom (lift π) X : BlockFam G D π), memℓp_infty ⟨‖X‖, by
    rintro _ ⟨π, rfl⟩; exact NonUnitalStarAlgHom.norm_apply_le (blockHom (lift π)) X⟩⟩
  map_smul' c X := by ext π; exact map_smul (blockHom (lift π)) c X
  map_zero' := by ext π; exact map_zero (blockHom (lift π))
  map_add' X Y := by ext π; exact map_add (blockHom (lift π)) X Y
  map_mul' X Y := by ext π; exact map_mul (blockHom (lift π)) X Y
  map_star' X := by ext π; exact map_star (blockHom (lift π)) X

lemma prodHom_apply (X : CStarMatrix (Fin D) (Fin D) (FullGroupCStar G)) (π : Rep G) :
    (prodHom X π : BlockFam G D π) = blockHom (lift π) X := rfl

lemma prodHom_injective : Function.Injective (prodHom (G := G) (D := D)) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  refine CStarMatrix.ext fun a b => eq_zero_of_forall_lift_eq_zero _ fun π => ?_
  have h1 : blockHom (lift π) X = 0 := by
    rw [← prodHom_apply, hX]; rfl
  exact blockOp_eq_zero h1 a b

end Product

end StrongConv.FullAux

namespace StrongConv

open FullGroupCStar FullAux

theorem norm_toFull_eq_fullNorm_dev {D d : ℕ} (P : NCPoly D d) : ‖P.toFull‖ = P.fullNorm := by
  obtain ⟨hlub, hle⟩ := isLUB_fullNorm_and_norm_eval_le_fullNorm.{0} P
  have hnonneg : 0 ≤ P.fullNorm :=
    (norm_nonneg _).trans (hlub.1 ⟨0, fun _ => 1, rfl⟩)
  apply le_antisymm
  · rw [← NonUnitalStarAlgHom.norm_map prodHom prodHom_injective P.toFull]
    refine lp.norm_le_of_forall_le hnonneg fun π => ?_
    rw [prodHom_apply, blockHom_toFull]
    exact hle π.H (repU π) fun i => (π.ρ (FreeGroup.of i)).2
  · refine hlub.2 ?_
    rintro _ ⟨n, U, rfl⟩
    have hU : ∀ i, Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ) ∈
        unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
      intro i
      rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, Unitary.star_mul_self_of_mem (U i).2,
        Unitary.mul_star_self_of_mem (U i).2, map_one]
      exact ⟨rfl, rfl⟩
    let π : Rep (FreeGroup (Fin d)) :=
      { H := EuclideanSpace ℂ (Fin n)
        ρ := FreeGroup.lift fun i => ⟨_, hU i⟩ }
    have hπ : repU π = fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ) := by
      funext i
      simp [repU, π]
    have := NonUnitalStarAlgHom.norm_apply_le (blockHom (lift π)) P.toFull
    rw [blockHom_toFull, hπ] at this
    exact this

end StrongConv

end
end
end

section
open StrongConv

theorem solution {D d : ℕ} (P : NCPoly D d) : ‖P.toFull‖ = P.fullNorm := by
  apply StrongConv.norm_toFull_eq_fullNorm_dev <;> assumption

end
