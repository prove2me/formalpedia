-- Prove2me | solution 1 for RandomDimReduction.Channel.lemma_5_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T19:16:06.608783+00:00
-- url     : https://prove2.me/submissions/137d1816-4d14-498d-ab7f-65d77b1aee7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RandomDimReduction_Channel_theorem_5_1
import Definitions.Def_RandomDimReduction_Channel_Tensor
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Representations
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_RandomDimReduction_Channel_Schur
import Mathlib.RepresentationTheory.Character
import Theorems.Thm_KWSpectrum_Estimator_eq_2_4_projections
import Theorems.Thm_RandomDimReduction_Channel_spechtModel_properties
import Mathlib
import Theorems.Thm_RandomDimReduction_Channel_lemma_5_4
import Theorems.Thm_RandomDimReduction_Channel_lemma_5_5
import Mathlib.LinearAlgebra.Matrix.Bilinear
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

-- TensorAlgebra
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tensor_mul {a b c : Type} [Fintype b] (n : ℕ)
    (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    tensor n (A * B) = tensor n A * tensor n B := by
  ext i j
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum fun t z => A (i t) z * B z (j t)

lemma tensor_conjTranspose {a b : Type} (n : ℕ) (A : Matrix a b ℂ) :
    tensor n Aᴴ = (tensor n A)ᴴ := by
  ext i j
  simp [tensor, Matrix.conjTranspose_apply]

lemma tensor_one {a : Type} [DecidableEq a] (n : ℕ) :
    tensor n (1 : Op a) = 1 := by
  ext i j
  simp only [tensor, Matrix.one_apply, Finset.prod_boole]
  simp [funext_iff]

lemma tensor_isometry {a b : Type} [Fintype a] [Fintype b] [DecidableEq b] (n : ℕ)
    (A : Matrix a b ℂ) (h : Aᴴ * A = 1) :
    (tensor n A)ᴴ * tensor n A = 1 := by
  rw [← tensor_conjTranspose, ← tensor_mul, h, tensor_one]

end RandomDimReduction.Channel

-- ProjectorAlgebra
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma toEuclideanLin_subspaceProjector {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Matrix.toEuclideanLin (subspaceProjector S) = S.starProjection.toLinearMap := by
  apply (EuclideanSpace.basisFun ι ℂ).toBasis.ext
  intro i
  ext j
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, subspaceProjector,
    EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]

lemma subspaceProjector_isHermitian {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) : (subspaceProjector S).IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, toEuclideanLin_subspaceProjector]
  exact S.starProjection_isSymmetric

lemma subspaceProjector_idempotent {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    subspaceProjector S * subspaceProjector S = subspaceProjector S := by
  apply Matrix.toEuclideanLin.injective
  change Matrix.toLpLin 2 2 (_ * _) = _
  rw [Matrix.toLpLin_mul 2 2 2]
  change Matrix.toEuclideanLin (subspaceProjector S) ∘ₗ
    Matrix.toEuclideanLin (subspaceProjector S) = _
  rw [toEuclideanLin_subspaceProjector]
  exact congrArg ContinuousLinearMap.toLinearMap S.isIdempotentElem_starProjection

lemma subspaceProjector_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) : (subspaceProjector S).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (subspaceProjector S)
  rwa [subspaceProjector_isHermitian S, subspaceProjector_idempotent] at h

end RandomDimReduction.Channel

-- RepresentationSchur
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def matrixRepresentation {G : Type} [Group G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) :
    Representation ℂ G (EuclideanSpace ℂ (Fin d)) where
  toFun g := Matrix.toEuclideanLin (r g : Op (Fin d))
  map_one' := by
    change Matrix.toEuclideanLin ((r 1 : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin d)) = 1
    simp [Matrix.toEuclideanLin]
    rfl
  map_mul' g h := by
    change Matrix.toEuclideanLin ((r (g*h) : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin d)) =
      Matrix.toEuclideanLin (r g : Op (Fin d)) * Matrix.toEuclideanLin (r h : Op (Fin d))
    simp [Matrix.toEuclideanLin, map_mul, Matrix.toLpLin_mul_same]
    rfl

lemma matrixRepresentation_irreducible {G : Type} [Group G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) (hr : Irreducible r) :
    (matrixRepresentation r).IsIrreducible := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hr.1⟩
  haveI : Nontrivial (Subrepresentation (matrixRepresentation r)) :=
    ⟨⟨⊥, ⊤, by
      intro h
      have he : (0 : EuclideanSpace ℂ (Fin d)) = EuclideanSpace.basisFun (Fin d) ℂ 0 := by
        have hmem : EuclideanSpace.basisFun (Fin d) ℂ 0 ∈ (⊤ : Subrepresentation (matrixRepresentation r)) := trivial
        rw [← h] at hmem
        exact hmem.symm
      exact (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.ne_zero 0 he.symm⟩⟩
  refine ⟨?_⟩
  intro S
  have h := hr.2 S.toSubmodule (fun g x hx => S.apply_mem_toSubmodule g hx)
  rcases h with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact h

lemma matrix_schur_scalar {G : Type} [Group G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) (hr : Irreducible r)
    (M : Op (Fin d)) (hM : ∀ g, M * (r g : Op (Fin d)) = (r g : Op (Fin d)) * M) :
    ∃ c : ℂ, M = c • 1 := by
  let rho := matrixRepresentation r
  haveI : rho.IsIrreducible := matrixRepresentation_irreducible r hr
  let f : Representation.IntertwiningMap rho rho :=
    { toLinearMap := Matrix.toEuclideanLin M
      isIntertwining' g := by
        change Matrix.toLpLin 2 2 M ∘ₗ Matrix.toLpLin 2 2 (r g : Op (Fin d)) =
          Matrix.toLpLin 2 2 (r g : Op (Fin d)) ∘ₗ Matrix.toLpLin 2 2 M
        rw [← Matrix.toLpLin_mul 2 2 2, ← Matrix.toLpLin_mul 2 2 2, hM g] }
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := rho)).surjective f
  refine ⟨c, ?_⟩
  apply Matrix.toEuclideanLin.injective
  have h := congrArg Representation.IntertwiningMap.toLinearMap hc
  change c • LinearMap.id = Matrix.toEuclideanLin M at h
  simpa [Matrix.toEuclideanLin] using h.symm

def matrixIntertwiner {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (hM : ∀ g, (M * (rA g : Op (Fin a)) : Matrix (Fin b) (Fin a) ℂ) = (rB g : Op (Fin b)) * M) :
    Representation.IntertwiningMap (matrixRepresentation rA) (matrixRepresentation rB) where
  toLinearMap := Matrix.toEuclideanLin M
  isIntertwining' g := by
    change Matrix.toLpLin 2 2 M ∘ₗ Matrix.toLpLin 2 2 (rA g : Op (Fin a)) =
      Matrix.toLpLin 2 2 (rB g : Op (Fin b)) ∘ₗ Matrix.toLpLin 2 2 M
    rw [← Matrix.toLpLin_mul 2 2 2, ← Matrix.toLpLin_mul 2 2 2]
    exact congrArg (Matrix.toLpLin 2 2) (hM g)

lemma intertwiner_nonzero_dims {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (hrA : Irreducible rA) (hrB : Irreducible rB)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (hM : ∀ g, (M * (rA g : Op (Fin a)) : Matrix (Fin b) (Fin a) ℂ) = (rB g : Op (Fin b)) * M) (hne : M ≠ 0) : a = b := by
  haveI := matrixRepresentation_irreducible rA hrA
  haveI := matrixRepresentation_irreducible rB hrB
  let f := matrixIntertwiner rA rB M hM
  have hf : f ≠ 0 := by
    intro h
    apply hne
    apply Matrix.toEuclideanLin.injective
    have he := congrArg Representation.IntertwiningMap.toLinearMap h
    simpa [f, matrixIntertwiner] using he
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf
  have hd := (LinearEquiv.ofBijective f.toLinearMap hb).finrank_eq
  simpa using hd

lemma adjoint_intertwiner {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (hM : ∀ g, (M * (rA g : Op (Fin a)) : Matrix (Fin b) (Fin a) ℂ) = (rB g : Op (Fin b)) * M) (g : G) :
    (Mᴴ * (rB g : Op (Fin b)) : Matrix (Fin a) (Fin b) ℂ) = (rA g : Op (Fin a)) * Mᴴ := by
  have hinv {e : ℕ} (r : G →* Matrix.unitaryGroup (Fin e) ℂ) :
      (r g⁻¹ : Op (Fin e))ᴴ = (r g : Op (Fin e)) := by
    change star (((r g⁻¹) : Matrix.unitaryGroup (Fin e) ℂ) : Op (Fin e)) = _
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star, star_star]
  have h := congrArg (fun X : Matrix (Fin b) (Fin a) ℂ => Xᴴ) (hM g⁻¹)
  simp only [Matrix.conjTranspose_mul] at h
  rw [hinv rA, hinv rB] at h
  exact h.symm

lemma nonzero_intertwiner_unitary {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (hrA : Irreducible rA) (hrB : Irreducible rB)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (hM : ∀ g, (M * (rA g : Op (Fin a)) : Matrix (Fin b) (Fin a) ℂ) = (rB g : Op (Fin b)) * M) (hne : M ≠ 0) :
    ∃ T : Matrix (Fin b) (Fin a) ℂ,
      Tᴴ * T = 1 ∧ T * Tᴴ = 1 ∧ ∀ g, (T * (rA g : Op (Fin a)) : Matrix (Fin b) (Fin a) ℂ) = (rB g : Op (Fin b)) * T := by
  have hd := intertwiner_nonzero_dims rA rB hrA hrB M hM hne
  subst b
  haveI : NeZero a := ⟨Nat.ne_of_gt hrA.1⟩
  have hcomm (g : G) : ((Mᴴ * M) * (rA g : Op (Fin a)) : Op (Fin a)) = (rA g : Op (Fin a)) * (Mᴴ * M) := by
    rw [Matrix.mul_assoc, hM g, ← Matrix.mul_assoc, adjoint_intertwiner rA rB M hM g, Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := matrix_schur_scalar rA hrA (Mᴴ * M) hcomm
  have hcnonneg : 0 ≤ c := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self M).diag_nonneg (i := (0 : Fin a))
    simpa [hc] using h
  have hcne : c ≠ 0 := by
    intro he
    apply hne
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simp [hc, he]
  have hcim : 0 = c.im := (Complex.nonneg_iff.mp hcnonneg).2
  have hcre : 0 < c.re := by
    have hle := (Complex.nonneg_iff.mp hcnonneg).1
    refine lt_of_le_of_ne hle ?_
    intro he
    apply hcne
    apply Complex.ext
    · exact he.symm
    · exact hcim.symm
  have hreal : (c.re : ℂ) = c := Complex.ext rfl hcim
  let s : ℂ := ((Real.sqrt c.re)⁻¹ : ℝ)
  have hs : star s = s := by simp [s]
  have hsc : s * s * c = 1 := by
    have hs0 : Real.sqrt c.re ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcre)
    have he : (Real.sqrt c.re)⁻¹ * (Real.sqrt c.re)⁻¹ * c.re = 1 := by
      field_simp
      nlinarith [Real.sq_sqrt hcre.le]
    rw [← hreal]
    dsimp [s]
    exact_mod_cast he
  let T := s • M
  have hT : Tᴴ * T = 1 := by
    simp only [T, Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul,
      hc, smul_smul]
    rw [← mul_assoc, hsc, one_smul]
  refine ⟨T, hT, (mul_eq_one_comm).mp hT, ?_⟩
  intro g
  simp only [T, Matrix.smul_mul, Matrix.mul_smul, hM g]

lemma intertwiner_zero_of_inequivalent {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (hrA : Irreducible rA) (hrB : Irreducible rB) (hne : Inequivalent rA rB)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (hM : ∀ g, (M * (rA g : Op (Fin a)) : Matrix (Fin b) (Fin a) ℂ) = (rB g : Op (Fin b)) * M) : M = 0 := by
  by_contra h
  exact hne (nonzero_intertwiner_unitary rA rB hrA hrB M hM h)

end RandomDimReduction.Channel

-- SpechtTrace
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma spechtProjection_eq {n : ℕ} (lam : Shape n) :
    QAlgorithms.Schur.spechtProjection lam = subspaceProjector (QAlgorithms.Schur.spechtSpace lam) := by
  ext i j
  simp [QAlgorithms.Schur.spechtProjection, subspaceProjector, QAlgorithms.ket,
    EuclideanSpace.inner_single_left, EuclideanSpace.basisFun_apply]

lemma standardSpecht_trace {n : ℕ} (lam : Shape n) (π : Equiv.Perm (Fin n)) :
    (standardSpecht lam π).trace = QAlgorithms.Schur.spechtCharacter lam π := by
  let E := QAlgorithms.Schur.spechtSpace lam
  let b := stdOrthonormalBasis ℂ E
  have hm : standardSpecht lam π = LinearMap.toMatrix b.toBasis b.toBasis
      (QAlgorithms.Schur.spechtRepresentation lam π) := by
    ext i j
    simp only [standardSpecht, LinearMap.toMatrix_apply]
    simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    rfl
  have htr : (standardSpecht lam π).trace =
      LinearMap.trace ℂ E (QAlgorithms.Schur.spechtRepresentation lam π) := by
    calc
      _ = ((LinearMap.toMatrix b.toBasis b.toBasis) (QAlgorithms.Schur.spechtRepresentation lam π)).trace :=
        congrArg Matrix.trace hm
      _ = _ := (LinearMap.trace_eq_matrix_trace ℂ b.toBasis _).symm
  rw [htr]
  unfold QAlgorithms.Schur.spechtCharacter
  rw [spechtProjection_eq]
  rw [← Matrix.trace_toLin_eq _ (EuclideanSpace.basisFun (Equiv.Perm (Fin n)) ℂ).toBasis]
  change LinearMap.trace ℂ E (E.orthogonalProjectionOnto.toLinearMap.comp
    ((Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular π)).comp E.subtype)) =
    LinearMap.trace ℂ (EuclideanSpace ℂ (Equiv.Perm (Fin n)))
      (Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular π * subspaceProjector E))
  rw [show Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular π * subspaceProjector E) =
    (Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular π)).comp E.starProjection.toLinearMap by
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, toEuclideanLin_subspaceProjector]]
  exact LinearMap.trace_comp_comm' _ _

lemma SpechtModel_trace {n : ℕ} (κ : SpechtModel n) (lam : Shape n) (π : Equiv.Perm (Fin n)) :
    (κ.action lam π : Op (Fin (spechtDim lam))).trace = QAlgorithms.Schur.spechtCharacter lam π := by
  obtain ⟨U, hU⟩ := κ.labelled lam
  rw [← standardSpecht_trace lam π, ← hU π]
  have hu : (U : Op (Fin (spechtDim lam)))ᴴ * (U : Op (Fin (spechtDim lam))) = 1 :=
    Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul]

end RandomDimReduction.Channel

-- PermutationCharacters
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma perm_entry_reversed (d n : ℕ) (g : Equiv.Perm (Fin n)) (y x : Word n d) :
    QAlgorithms.Schur.tensorPermutation d n g y x = if x = y ∘ g then 1 else 0 := by
  simp only [QAlgorithms.Schur.tensorPermutation, Matrix.of_apply]
  have h : (y = x ∘ g.symm) ↔ (x = y ∘ g) := by
    constructor <;> rintro rfl <;> funext i <;> simp
  by_cases hx : x = y ∘ g
  · rw [if_pos (h.mpr hx), if_pos hx]
  · rw [if_neg (fun h' => hx (h.mp h')), if_neg hx]

lemma tensorPermutation_mul (d n : ℕ) (g h : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.tensorPermutation d n g * QAlgorithms.Schur.tensorPermutation d n h =
      QAlgorithms.Schur.tensorPermutation d n (g * h) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (y ∘ g)]
  · rw [perm_entry_reversed, perm_entry_reversed, perm_entry_reversed, if_pos rfl,
      one_mul, Equiv.Perm.coe_mul]
    rfl
  · intro b _ hb
    rw [perm_entry_reversed, if_neg (fun e => hb e), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma perm_entry_identity (n : ℕ) (g : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.tensorPermutation n n g id id = if g = 1 then 1 else 0 := by
  rw [perm_entry_reversed]
  have he : ((id : Fin n → Fin n) = id ∘ g) ↔ g = 1 := by
    constructor
    · intro h
      apply Equiv.ext
      intro i
      exact (congrFun h i).symm
    · rintro rfl
      rfl
  simp only [he]

lemma isotypic_identity_entry (n : ℕ) (lam : Shape n) :
    QAlgorithms.Schur.isotypicProjector lam id id =
      ((spechtDim lam : ℂ) / (n.factorial : ℂ)) * QAlgorithms.Schur.spechtCharacter lam 1 := by
  simp [QAlgorithms.Schur.isotypicProjector, Matrix.smul_apply, Matrix.sum_apply,
    perm_entry_identity, mul_ite, spechtDim]

lemma isotypic_product_identity_entry (n : ℕ) (lam mu : Shape n) :
    (QAlgorithms.Schur.isotypicProjector lam * QAlgorithms.Schur.isotypicProjector mu) id id =
      (((spechtDim lam : ℂ) / (n.factorial : ℂ)) * ((spechtDim mu : ℂ) / (n.factorial : ℂ))) *
        ∑ g : Equiv.Perm (Fin n),
          QAlgorithms.Schur.spechtCharacter lam g * QAlgorithms.Schur.spechtCharacter mu g⁻¹ := by
  simp only [QAlgorithms.Schur.isotypicProjector, smul_mul_smul_comm,
    Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    tensorPermutation_mul, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    perm_entry_identity]
  rw [Finset.sum_comm]
  simp_rw [mul_eq_one_iff_eq_inv, mul_ite, mul_zero, mul_one]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_inv]
  simp only [← Finset.mul_sum, spechtDim]

end RandomDimReduction.Channel

-- SchurPermutations
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tensorPermutation_one (n d : ℕ) : QAlgorithms.Schur.tensorPermutation d n 1 = 1 := by
  ext i j
  rfl

lemma tensorPermutation_adjoint (n d : ℕ) (π : Equiv.Perm (Fin n)) :
    (QAlgorithms.Schur.tensorPermutation d n π)ᴴ = QAlgorithms.Schur.tensorPermutation d n π⁻¹ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, perm_entry_reversed]
  have he : (i = j ∘ π) ↔ j = i ∘ (π⁻¹ : Equiv.Perm (Fin n)) := by
    constructor <;> rintro rfl <;> funext t <;> simp
  simp [he]

def tensorPermutation_rep (n d : ℕ) :
    Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Word n d) ℂ where
  toFun π := ⟨QAlgorithms.Schur.tensorPermutation d n π, by
    constructor
    · change (QAlgorithms.Schur.tensorPermutation d n π)ᴴ * QAlgorithms.Schur.tensorPermutation d n π = 1
      rw [tensorPermutation_adjoint, tensorPermutation_mul, inv_mul_cancel, tensorPermutation_one]
    · change QAlgorithms.Schur.tensorPermutation d n π * (QAlgorithms.Schur.tensorPermutation d n π)ᴴ = 1
      rw [tensorPermutation_adjoint, tensorPermutation_mul, mul_inv_cancel, tensorPermutation_one]⟩
  map_one' := by apply Subtype.ext; exact tensorPermutation_one n d
  map_mul' π σ := by apply Subtype.ext; exact (tensorPermutation_mul d n π σ).symm

lemma tensor_perm_natural (n k d : ℕ) (W : Matrix (Fin d) (Fin k) ℂ)
    (π : Equiv.Perm (Fin n)) :
    tensor n W * QAlgorithms.Schur.tensorPermutation k n π =
      QAlgorithms.Schur.tensorPermutation d n π * tensor n W := by
  have he (i j : Word n d) : i = j ∘ π.symm ↔ j = i ∘ π := by
    constructor <;> intro h <;> subst_vars <;> funext t <;> simp
  ext i j
  simp only [Matrix.mul_apply, QAlgorithms.Schur.tensorPermutation, Matrix.of_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [he]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [tensor, Function.comp_apply]
  simpa using (Equiv.prod_comp π (fun t => W (i t) (j (π.symm t)))).symm

lemma schur_nu_one {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (hsp : ∀ lam : Shape n, 0 < spechtDim lam) (lam : Shape n) : S.nu lam 1 = 1 := by
  haveI : NeZero (spechtDim lam) := ⟨Nat.ne_of_gt (hsp lam)⟩
  have h := S.intertwines 1 1
  rw [tensorPermutation_one, tensor_one, Matrix.mul_one, Matrix.mul_one, S.left_unitary] at h
  ext i j
  have he := congrArg (fun A : Op (SchurIndex n d) => A ⟨lam, (0,i)⟩ ⟨lam, (0,j)⟩) h
  simpa [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply] using he.symm

lemma schur_intertwines_permutation {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (hsp : ∀ lam : Shape n, 0 < spechtDim lam) (π : Equiv.Perm (Fin n)) :
    S.U * QAlgorithms.Schur.tensorPermutation d n π * S.Uᴴ =
      Matrix.blockDiagonal' (fun lam => Matrix.kronecker (κ.action lam π : Op (Fin (spechtDim lam)))
        (1 : Op (Fin (weylDim d lam)))) := by
  have h := S.intertwines π 1
  simpa only [tensor_one, Matrix.mul_one, schur_nu_one S hsp] using h

end RandomDimReduction.Channel

-- CharacterProjectors
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma trace_action_conjugate {G : Type} [Group G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) (g h : G) :
    (r (h*g*h⁻¹) : Op (Fin d)).trace = (r g : Op (Fin d)).trace := by
  simp only [map_mul, Submonoid.coe_mul]
  rw [Matrix.trace_mul_cycle, ← Submonoid.coe_mul, ← map_mul, inv_mul_cancel,
    map_one, Submonoid.coe_one, Matrix.one_mul]

lemma weightedGroupSum_commutes {G : Type} [Group G] [Fintype G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) (f : G → ℂ)
    (hf : ∀ g h, f (h*g*h⁻¹) = f g) (h : G) :
    (∑ g, f g • (r g : Op (Fin d))) * (r h : Op (Fin d)) =
      (r h : Op (Fin d)) * ∑ g, f g • (r g : Op (Fin d)) := by
  simp only [Finset.sum_mul, Matrix.smul_mul, Finset.mul_sum, Matrix.mul_smul]
  have he := (MulAut.conj h).toEquiv.sum_comp
    (fun g => f g • ((r g : Op (Fin d)) * (r h : Op (Fin d))))
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  change f (h*g*h⁻¹) • ((r (h*g*h⁻¹) : Op (Fin d)) * (r h : Op (Fin d))) = _
  rw [hf]
  congr 1
  rw [← Submonoid.coe_mul, ← map_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one, map_mul, Submonoid.coe_mul]

lemma spechtDim_pos_of_model {n : ℕ} (hn : 0 < n) (κ : SpechtModel n) (lam : Shape n) :
    0 < spechtDim lam := ((spechtModel_properties n hn κ).1 lam).1

lemma specht_char_one' {n : ℕ} (κ : SpechtModel n) (lam : Shape n) :
    QAlgorithms.Schur.spechtCharacter lam 1 = (spechtDim lam : ℂ) := by
  rw [← SpechtModel_trace κ lam 1, map_one]
  simp

lemma specht_char_inner' {n : ℕ} (hn : 0 < n) (κ : SpechtModel n) (lam mu : Shape n) :
    (n.factorial : ℂ)⁻¹ * ∑ g : Equiv.Perm (Fin n),
      QAlgorithms.Schur.spechtCharacter lam g * QAlgorithms.Schur.spechtCharacter mu g⁻¹ =
      if lam = mu then 1 else 0 := by
  have hN : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hl : (spechtDim lam : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (spechtDim_pos_of_model hn κ lam))
  have hm : (spechtDim mu : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (spechtDim_pos_of_model hn κ mu))
  by_cases h : lam = mu
  · subst mu
    rw [if_pos rfl]
    have hp := (KWSpectrum.Estimator.eq_2_4_projections lam).2.2.1
    have he := congrArg (fun A : Op (Word n n) => A id id) hp
    rw [isotypic_product_identity_entry, isotypic_identity_entry, specht_char_one' κ] at he
    have hs : (∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter lam g *
        QAlgorithms.Schur.spechtCharacter lam g⁻¹) = (n.factorial : ℂ) := by
      apply mul_left_cancel₀ (mul_ne_zero (div_ne_zero hl hN) (div_ne_zero hl hN))
      rw [he]
      field_simp
    rw [hs, inv_mul_cancel₀ hN]
  · rw [if_neg h]
    have hp := (KWSpectrum.Estimator.eq_2_4_projections lam).2.2.2.1 mu (Ne.symm h)
    have he := congrArg (fun A : Op (Word n n) => A id id) hp
    rw [isotypic_product_identity_entry, Matrix.zero_apply] at he
    have hs := (mul_eq_zero.mp he).resolve_left
      (mul_ne_zero (div_ne_zero hl hN) (div_ne_zero hm hN))
    rw [hs, mul_zero]

lemma specht_central_character_action {n : ℕ} (hn : 0 < n) (κ : SpechtModel n)
    (lam mu : Shape n) :
    ((spechtDim lam : ℂ) / (n.factorial : ℂ)) •
      (∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter lam g⁻¹ •
        (κ.action mu g : Op (Fin (spechtDim mu)))) =
      if lam = mu then 1 else 0 := by
  let B : Op (Fin (spechtDim mu)) := ∑ g : Equiv.Perm (Fin n),
    QAlgorithms.Schur.spechtCharacter lam g⁻¹ • (κ.action mu g : Op (Fin (spechtDim mu)))
  have hclass (g h : Equiv.Perm (Fin n)) :
      QAlgorithms.Schur.spechtCharacter lam (h*g*h⁻¹)⁻¹ =
        QAlgorithms.Schur.spechtCharacter lam g⁻¹ := by
    rw [← SpechtModel_trace κ, ← SpechtModel_trace κ]
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using trace_action_conjugate (κ.action lam) g⁻¹ h
  obtain ⟨c,hc⟩ := matrix_schur_scalar (κ.action mu) ((spechtModel_properties n hn κ).1 mu)
    B (weightedGroupSum_commutes (κ.action mu) _ hclass)
  have ht := congrArg Matrix.trace hc
  simp only [B, Matrix.trace_sum, Matrix.trace_smul, SpechtModel_trace,
    smul_eq_mul, Matrix.trace_one, Fintype.card_fin] at ht
  have hi := specht_char_inner' hn κ mu lam
  have hs : ∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter lam g⁻¹ *
      QAlgorithms.Schur.spechtCharacter mu g = c * (spechtDim mu : ℂ) := by
    simpa only [mul_comm] using ht
  simp_rw [mul_comm (QAlgorithms.Schur.spechtCharacter mu _) _] at hi
  rw [hs] at hi
  have hN : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hmu : (spechtDim mu : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (spechtDim_pos_of_model hn κ mu))
  change ((spechtDim lam : ℂ) / (n.factorial : ℂ)) • B = _
  rw [hc, smul_smul]
  by_cases h : lam = mu
  · subst mu
    rw [if_pos rfl] at hi ⊢
    have hscale : (spechtDim lam : ℂ) / (n.factorial : ℂ) * c = 1 := by
      linear_combination hi
    rw [hscale, one_smul]
  · rw [if_neg h]
    rw [if_neg (Ne.symm h)] at hi
    have hc0 : c = 0 := by
      apply (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (inv_ne_zero hN))).resolve_right hmu
    rw [hc0, mul_zero, zero_smul]

end RandomDimReduction.Channel

-- SchurProjectors
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def schurSector {n : ℕ} (d : ℕ) (lam : Shape n) : Op (SchurIndex n d) :=
  Matrix.blockDiagonal' fun mu => if mu = lam then 1 else 0

lemma block_character_linear {L G : Type} [Fintype G] [DecidableEq L]
    (p q : L → ℕ) (R : ∀ l, G → Op (Fin (p l))) (c : ℂ) (f : G → ℂ) :
    Matrix.blockDiagonal' (fun l => Matrix.kronecker (c • ∑ g, f g • R l g)
      (1 : Op (Fin (q l)))) =
      c • ∑ g, f g • Matrix.blockDiagonal' (fun l => Matrix.kronecker (R l g)
        (1 : Op (Fin (q l)))) := by
  ext ⟨l,i⟩ ⟨m,j⟩
  by_cases hlm : l = m
  · subst m
    simp [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.smul_apply,
      Matrix.sum_apply, Finset.sum_mul, mul_assoc]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hlm, Matrix.smul_apply, Matrix.sum_apply]

lemma schur_character_projector {n d : ℕ} (hn : 0 < n) {κ : SpechtModel n}
    (S : SchurTransform κ d) (lam : Shape n) :
    S.U * (((spechtDim lam : ℂ) / (n.factorial : ℂ)) •
      ∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter lam g⁻¹ •
        QAlgorithms.Schur.tensorPermutation d n g) * S.Uᴴ = schurSector d lam := by
  have hsp := spechtDim_pos_of_model hn κ
  calc
    _ = ((spechtDim lam : ℂ) / (n.factorial : ℂ)) •
        ∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter lam g⁻¹ •
          (S.U * QAlgorithms.Schur.tensorPermutation d n g * S.Uᴴ) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    _ = Matrix.blockDiagonal' (fun mu => Matrix.kronecker
        (((spechtDim lam : ℂ) / (n.factorial : ℂ)) •
          ∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter lam g⁻¹ •
            (κ.action mu g : Op (Fin (spechtDim mu))))
        (1 : Op (Fin (weylDim d mu)))) := by
      simp_rw [schur_intertwines_permutation S hsp]
      exact (block_character_linear (fun mu : Shape n => spechtDim mu)
        (fun mu : Shape n => weylDim d mu) (fun mu g => (κ.action mu g : Op (Fin (spechtDim mu)))) _ _).symm
    _ = schurSector d lam := by
      congr 1
      funext mu
      rw [specht_central_character_action hn κ]
      by_cases h : lam = mu
      · subst mu
        simp [Matrix.kronecker, Matrix.one_kronecker_one]
      · simp [h, Ne.symm h, Matrix.kronecker]

lemma schurSector_zero_of_absent {n d : ℕ} (lam : Shape n) (h : ¬height lam ≤ d) :
    schurSector d lam = 0 := by
  ext ⟨mu,i⟩ ⟨nu,j⟩
  by_cases hmn : mu = nu
  · subst nu
    simp only [schurSector, Matrix.blockDiagonal'_apply_eq]
    by_cases hml : mu = lam
    · subst mu
      have hi : (0 : ℕ) < weylDim d lam := Nat.zero_lt_of_lt i.2.isLt
      simp [weylDim,h] at hi
    · simp [hml]
  · simp [schurSector, Matrix.blockDiagonal'_apply_ne _ _ _ hmn]

lemma schur_isotypic {n d : ℕ} (hn : 0 < n) {κ : SpechtModel n}
    (S : SchurTransform κ d) (lam : Shape n) :
    S.U * isotypic d lam * S.Uᴴ = schurSector d lam := by
  by_cases h : height lam ≤ d
  · rw [isotypic, dif_pos h]
    have he : QAlgorithms.Schur.isotypicProjector (shapeAt lam h) =
        ((spechtDim lam : ℂ) / (n.factorial : ℂ)) •
          ∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter lam g⁻¹ •
            QAlgorithms.Schur.tensorPermutation d n g := rfl
    rw [he]
    exact schur_character_projector hn S lam
  · rw [isotypic, dif_neg h, Matrix.mul_zero, Matrix.zero_mul, schurSector_zero_of_absent lam h]

end RandomDimReduction.Channel

-- RawBlocks
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def rawBlock {L : Type} {a b : L → Type}
    (D : Matrix (Sigma a) (Sigma b) ℂ) (l m : L) : Matrix (a l) (b m) ℂ :=
  fun i j => D ⟨l,i⟩ ⟨m,j⟩

lemma rawBlock_mul_right {L : Type} [Fintype L] [DecidableEq L]
    {a b c : L → Type} [∀ l, Fintype (b l)]
    (D : Matrix (Sigma a) (Sigma b) ℂ) (R : ∀ l, Matrix (b l) (c l) ℂ) (l m : L) :
    rawBlock (D * Matrix.blockDiagonal' R) l m = rawBlock D l m * R m := by
  ext i j
  simp only [rawBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single m]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro t _ htm
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htm]
  · simp

lemma rawBlock_mul_left {L : Type} [Fintype L] [DecidableEq L]
    {a b c : L → Type} [∀ l, Fintype (b l)]
    (R : ∀ l, Matrix (a l) (b l) ℂ) (D : Matrix (Sigma b) (Sigma c) ℂ) (l m : L) :
    rawBlock (Matrix.blockDiagonal' R * D) l m = R l * rawBlock D l m := by
  ext i j
  simp only [rawBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single l]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro t _ htl
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htl.symm]
  · simp

end RandomDimReduction.Channel

-- MomentBlocks
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma baseEmbedding_isometry {k d : ℕ} (hkd : k ≤ d) :
    (baseEmbedding k d)ᴴ * baseEmbedding k d = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hkd i)]
  · simp [Matrix.conjTranspose_apply, baseEmbedding, Matrix.one_apply, Fin.ext_iff]
  · intro x _ hx
    have hne : x.val ≠ i.val := by
      intro he
      exact hx (Fin.ext he)
    simp [Matrix.conjTranspose_apply, baseEmbedding, hne]
  · simp

lemma moment_eq_twirl (n k d : ℕ) :
    moment n k d = twirl n d (tensor n (baseEmbedding k d) * (tensor n (baseEmbedding k d))ᴴ) := by
  unfold moment twirl
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro V
  simp only [randomEmbedding, Matrix.conjTranspose_mul, tensor_mul,
    tensor_conjTranspose, Matrix.mul_assoc]

lemma partialTraceRight_kronecker {a b : Type} [Fintype b]
    (A : Op a) (B : Op b) :
    WildeQIT.partialTraceRight (Matrix.kronecker A B) = B.trace • A := by
  ext i j
  simp [WildeQIT.partialTraceRight, Matrix.kronecker_apply, Matrix.trace,
    Finset.mul_sum, Matrix.smul_apply, mul_comm]

lemma sum_schurSector {n d : ℕ} (c : Shape n → ℂ) :
    (∑ lam : Shape n, c lam • schurSector d lam) =
      Matrix.blockDiagonal' (fun lam => c lam • (1 : Op (Fin (spechtDim lam) × Fin (weylDim d lam)))) := by
  ext ⟨l,i⟩ ⟨m,j⟩
  by_cases hlm : l = m
  · subst m
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single l]
    · simp only [schurSector, Matrix.blockDiagonal'_apply_eq, if_pos rfl, ite_true]
    · intro v _ hv
      simp only [schurSector, Matrix.blockDiagonal'_apply_eq, if_neg (Ne.symm hv),
        Matrix.zero_apply, mul_zero]
    · simp
  · simp [schurSector, Matrix.blockDiagonal'_apply_ne _ _ _ hlm, Matrix.sum_apply, Matrix.smul_apply]

lemma schur_moment_blocks (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (κ : SpechtModel n) (Sd : SchurTransform κ d) (Sk : SchurTransform κ k) :
    Sd.U * moment n k d * Sd.Uᴴ = Matrix.blockDiagonal' (fun lam : Shape n =>
      (((weylDim k lam : ℂ) / (weylDim d lam : ℂ))) •
        (1 : Op (Fin (spechtDim lam) × Fin (weylDim d lam)))) := by
  let T := tensor n (baseEmbedding k d)
  obtain ⟨eta,heta,hiso⟩ := lemma_5_5 n k d hn hk hkd κ Sd Sk (baseEmbedding k d) (baseEmbedding_isometry hkd)
  let D : Matrix (SchurIndex n d) (SchurIndex n k) ℂ := Sd.U * T * Sk.Uᴴ
  have hD : D = Matrix.blockDiagonal' (fun lam =>
      Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam)) := heta
  have hXX : Sd.U * (T * Tᴴ) * Sd.Uᴴ = D * Dᴴ := by
    symm
    dsimp [D]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Sd.U * T * (Sk.Uᴴ * Sk.U) * Tᴴ * Sd.Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Sk.right_unitary]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hblock (lam : Shape n) : schurBlock Sd (T * Tᴴ) lam lam =
      Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam * (eta lam)ᴴ) := by
    change rawBlock (Sd.U * (T * Tᴴ) * Sd.Uᴴ) lam lam = _
    rw [hXX, hD, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    ext i j
    simp only [rawBlock, Matrix.blockDiagonal'_apply_eq]
  rw [moment_eq_twirl, lemma_5_4 n d hn (hk.trans hkd) κ Sd]
  unfold twirlBlocks
  congr 1
  funext lam
  rw [hblock, partialTraceRight_kronecker, Matrix.trace_mul_comm, hiso,
    Matrix.trace_one, Fintype.card_fin]
  ext i j
  simp [Matrix.kronecker_apply, Matrix.one_apply, Matrix.smul_apply, div_eq_mul_inv,
    mul_assoc, Prod.ext_iff, ite_and, and_comm]
  <;> split_ifs <;> rfl

lemma moment_expansion (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (κ : SpechtModel n) (Sd : SchurTransform κ d) (Sk : SchurTransform κ k) :
    moment n k d = ∑ lam : Shape n, if height lam ≤ k then
      ((weylDim k lam : ℂ) / (weylDim d lam : ℂ)) • isotypic d lam else 0 := by
  have hinj : Function.Injective (fun X : Op (Word n d) => Sd.U * X * Sd.Uᴴ) := by
    have hc (Z : Op (Word n d)) : Sd.Uᴴ * (Sd.U * Z * Sd.Uᴴ) * Sd.U = Z := by
      calc
        _ = (Sd.Uᴴ * Sd.U) * Z * (Sd.Uᴴ * Sd.U) := by simp only [Matrix.mul_assoc]
        _ = Z := by rw [Sd.right_unitary]; simp only [Matrix.one_mul, Matrix.mul_one]
    intro X Y h
    have he := congrArg (fun Z : Op (SchurIndex n d) => Sd.Uᴴ * Z * Sd.U) h
    rwa [hc, hc] at he
  apply hinj
  change Sd.U * moment n k d * Sd.Uᴴ = Sd.U * (∑ lam : Shape n, if height lam ≤ k then
    ((weylDim k lam : ℂ) / (weylDim d lam : ℂ)) • isotypic d lam else 0) * Sd.Uᴴ
  rw [schur_moment_blocks n k d hn hk hkd κ Sd Sk]
  have he : (∑ lam : Shape n, if height lam ≤ k then
      ((weylDim k lam : ℂ) / (weylDim d lam : ℂ)) • isotypic d lam else 0) =
      ∑ lam : Shape n, ((weylDim k lam : ℂ) / (weylDim d lam : ℂ)) • isotypic d lam := by
    apply Finset.sum_congr rfl
    intro lam _
    by_cases h : height lam ≤ k
    · rw [if_pos h]
    · simp [h, weylDim]
  rw [he]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    schur_isotypic hn Sd]
  exact (sum_schurSector _).symm

end RandomDimReduction.Channel

-- MatrixConjugation
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma conjugation_cancel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (U : Matrix b a ℂ) (hU : Uᴴ * U = 1) (X : Op a) :
    Uᴴ * (U * X * Uᴴ) * U = X := by
  calc
    _ = (Uᴴ * U) * X * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hU]; simp only [Matrix.one_mul, Matrix.mul_one]

def rectangularConjugation {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (U : Matrix b a ℂ) (hL : U * Uᴴ = 1) (hR : Uᴴ * U = 1) : Op a ≃⋆ₐ[ℂ] Op b where
  toFun X := U * X * Uᴴ
  invFun Y := Uᴴ * Y * U
  left_inv := conjugation_cancel U hR
  right_inv Y := by
    have h := conjugation_cancel Uᴴ (by simpa using hL) Y
    simpa only [Matrix.conjTranspose_conjTranspose] using h
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc
      _ = U * X * (Uᴴ * U) * Y * Uᴴ := by
        rw [hR]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul]
  map_star' X := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

def schurConjugation {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d) :
    Op (Word n d) ≃⋆ₐ[ℂ] Op (SchurIndex n d) :=
  rectangularConjugation S.U S.left_unitary S.right_unitary

lemma schurConjugation_apply {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (X : Op (Word n d)) : schurConjugation S X = S.U * X * S.Uᴴ := rfl

lemma schurConjugation_symm_apply {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (Y : Op (SchurIndex n d)) : (schurConjugation S).symm Y = S.Uᴴ * Y * S.U := rfl

end RandomDimReduction.Channel

-- SupportProjector
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma subspaceProjector_range_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Op ι) (hP : P.IsHermitian) (hP2 : P * P = P) :
    subspaceProjector (LinearMap.range (Matrix.toEuclideanLin P)) = P := by
  let L := Matrix.toEuclideanLin P
  have hi : IsIdempotentElem L := by
    change Matrix.toEuclideanLin P ∘ₗ Matrix.toEuclideanLin P = Matrix.toEuclideanLin P
    have h := congrArg Matrix.toEuclideanLin hP2
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h
  have hs : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP
  have hp : L.IsSymmetricProjection := ⟨hi, hs⟩
  have he := (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hp).2
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_subspaceProjector]
  exact he.symm

lemma subspaceProjector_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    subspaceProjector Sᗮ = 1 - subspaceProjector S := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_subspaceProjector]
  simp only [Matrix.toEuclideanLin, map_sub, Matrix.toLpLin_one]
  change Sᗮ.starProjection.toLinearMap = LinearMap.id -
    Matrix.toEuclideanLin (subspaceProjector S)
  rw [toEuclideanLin_subspaceProjector, Submodule.starProjection_orthogonal]
  rfl

lemma matrix_range_eq_of_support {ι : Type} [Fintype ι] [DecidableEq ι]
    (M P N : Op ι) (hPM : P * M = M) (hMN : M * N = P) :
    LinearMap.range (Matrix.toEuclideanLin M) = LinearMap.range (Matrix.toEuclideanLin P) := by
  apply le_antisymm
  · rintro x ⟨v,rfl⟩
    refine ⟨Matrix.toEuclideanLin M v, ?_⟩
    have h := congrArg (fun A : Op ι => Matrix.toEuclideanLin A v) hPM
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h
  · rintro x ⟨v,rfl⟩
    refine ⟨Matrix.toEuclideanLin N v, ?_⟩
    have h := congrArg (fun A : Op ι => Matrix.toEuclideanLin A v) hMN
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h

lemma matrix_projectors_of_support {ι : Type} [Fintype ι] [DecidableEq ι]
    (M P N : Op ι) (hM : M.IsHermitian) (hP : P.IsHermitian) (hP2 : P * P = P)
    (hPM : P * M = M) (hMN : M * N = P) :
    subspaceProjector (LinearMap.range (Matrix.toEuclideanLin M)) = P ∧
      subspaceProjector (LinearMap.ker (Matrix.toEuclideanLin M)) = 1-P := by
  have hr := matrix_range_eq_of_support M P N hPM hMN
  have hproj : subspaceProjector (LinearMap.range (Matrix.toEuclideanLin M)) = P := by
    rw [hr]
    exact subspaceProjector_range_eq P hP hP2
  refine ⟨hproj, ?_⟩
  have hs : (Matrix.toEuclideanLin M).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  rw [← hs.orthogonal_range, subspaceProjector_orthogonal, hproj]

end RandomDimReduction.Channel

-- PositiveIntegral
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma convex_posSemidef (ι : Type) [Fintype ι] :
    Convex ℝ {A : Op ι | A.PosSemidef} := by
  intro A hA B hB r s hr hs _
  exact (hA.smul hr).add (hB.smul hs)

lemma isClosed_posSemidef (ι : Type) [Fintype ι] :
    IsClosed {A : Op ι | A.PosSemidef} := by
  have hh : IsClosed {A : Op ι | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hq : IsClosed (⋂ v : ι → ℂ, {A : Op ι | 0 ≤ star v ⬝ᵥ (A *ᵥ v)}) := by
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    fun_prop
  convert hh.inter hq using 1
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  exact Matrix.posSemidef_iff_dotProduct_mulVec

lemma integral_posSemidef {ι G : Type} [Fintype ι]
    [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (f : G → Op ι)
    (hf : Continuous f) (hp : ∀ g, (f g).PosSemidef) :
    (∫ g, f g ∂μ).PosSemidef := by
  exact (convex_posSemidef ι).integral_mem (isClosed_posSemidef ι)
    (Filter.Eventually.of_forall hp)
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))

end RandomDimReduction.Channel

-- MomentPositivity
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma continuous_tensor_all {a b : Type} (n : ℕ) : Continuous (tensor (a := a) (b := b) n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_finsetProd _ fun t _ => (continuous_apply (j t)).comp (continuous_apply (i t))

lemma moment_posSemidef (n k d : ℕ) : (moment n k d).PosSemidef := by
  unfold moment
  simp_rw [tensor_mul, tensor_conjTranspose]
  apply integral_posSemidef
  · exact ((continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)).matrix_mul
      ((continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)).matrix_conjTranspose
  · intro V
    exact Matrix.posSemidef_self_mul_conjTranspose _

lemma inverseRootMoment_isHermitian (n k d : ℕ) : (inverseRootMoment n k d).IsHermitian := by
  exact cfc_predicate _ _

end RandomDimReduction.Channel

-- MomentSupport
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def schurScalars {n : ℕ} (d : ℕ) (c : Shape n → ℂ) : Op (SchurIndex n d) :=
  Matrix.blockDiagonal' fun lam => c lam • (1 : Op (Fin (spechtDim lam) × Fin (weylDim d lam)))

lemma schurScalars_mul {n d : ℕ} (c e : Shape n → ℂ) :
    schurScalars d c * schurScalars d e = schurScalars d (fun lam => c lam * e lam) := by
  unfold schurScalars
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext lam
  rw [smul_mul_smul_comm, Matrix.one_mul]

lemma schurScalars_hermitian {n d : ℕ} (c : Shape n → ℂ) (hc : ∀ lam, star (c lam) = c lam) :
    (schurScalars d c).IsHermitian := by
  change (schurScalars d c)ᴴ = schurScalars d c
  unfold schurScalars
  rw [Matrix.blockDiagonal'_conjTranspose]
  congr 1
  funext lam
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hc]

lemma schurScalars_one {n d : ℕ} : schurScalars (n := n) d (fun _ => 1) = 1 := by
  simp only [schurScalars, one_smul]
  exact Matrix.blockDiagonal'_one

lemma schurScalars_sub {n d : ℕ} (c e : Shape n → ℂ) :
    schurScalars d (fun lam => c lam - e lam) = schurScalars d c - schurScalars d e := by
  simp only [schurScalars, sub_smul]
  exact Matrix.blockDiagonal'_sub _ _

lemma schur_weighted_isotypic {n d : ℕ} (hn : 0 < n) {κ : SpechtModel n}
    (S : SchurTransform κ d) (c : Shape n → ℂ) :
    schurConjugation S (∑ lam : Shape n, c lam • isotypic d lam) = schurScalars d c := by
  change S.U * (∑ lam : Shape n, c lam • isotypic d lam) * S.Uᴴ = _
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    schur_isotypic hn S]
  exact sum_schurSector c

lemma schur_lowProjector {n k d : ℕ} (hn : 0 < n) {κ : SpechtModel n}
    (S : SchurTransform κ d) : schurConjugation S (lowProjector n k d) =
      schurScalars d (fun lam : Shape n => if height lam ≤ k then 1 else 0) := by
  have he : lowProjector n k d = ∑ lam : Shape n,
      (if height lam ≤ k then (1 : ℂ) else 0) • isotypic d lam := by
    apply Finset.sum_congr rfl
    intro lam _
    split_ifs <;> simp
  rw [he, schur_weighted_isotypic hn S]

lemma schur_highProjector {n k d : ℕ} (hn : 0 < n) {κ : SpechtModel n}
    (S : SchurTransform κ d) : schurConjugation S (highProjector n k d) =
      schurScalars d (fun lam : Shape n => if k < height lam then 1 else 0) := by
  have he : highProjector n k d = ∑ lam : Shape n,
      (if k < height lam then (1 : ℂ) else 0) • isotypic d lam := by
    apply Finset.sum_congr rfl
    intro lam _
    split_ifs <;> simp
  rw [he, schur_weighted_isotypic hn S]

lemma schurSector_zero_of_weyl_zero {n d : ℕ} (lam : Shape n) (h : weylDim d lam = 0) :
    schurSector d lam = 0 := by
  ext ⟨mu,i⟩ ⟨nu,j⟩
  by_cases hmn : mu = nu
  · subst nu
    simp only [schurSector, Matrix.blockDiagonal'_apply_eq]
    by_cases hml : mu = lam
    · subst mu
      have hi := i.2.isLt
      exact (Nat.not_lt_zero _ (hi.trans_eq h)).elim
    · simp [hml]
  · simp [schurSector, Matrix.blockDiagonal'_apply_ne _ _ _ hmn]

lemma weylDim_pos_of_height {n d : ℕ} (hn : 0 < n) {κ : SpechtModel n}
    (S : SchurTransform κ d) (lam : Shape n) (h : height lam ≤ d) : 0 < weylDim d lam := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hp : isotypic d lam ≠ 0 := by
    simpa only [isotypic, dif_pos h] using (KWSpectrum.Estimator.eq_2_4_projections (shapeAt lam h)).1
  apply hp
  apply (schurConjugation S).injective
  rw [map_zero]
  change S.U * isotypic d lam * S.Uᴴ = 0
  rw [schur_isotypic hn S, schurSector_zero_of_weyl_zero lam hz]

lemma moment_support_projectors (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (κ : SpechtModel n) (Sd : SchurTransform κ d) (Sk : SchurTransform κ k) :
    imageProjector n k d = lowProjector n k d ∧
      kernelProjector n k d = highProjector n k d := by
  let F := schurConjugation Sd
  let a : Shape n → ℂ := fun lam => (weylDim k lam : ℂ) / (weylDim d lam : ℂ)
  let ell : Shape n → ℂ := fun lam => if height lam ≤ k then 1 else 0
  let N : Op (Word n d) := F.symm (schurScalars d (fun lam => (a lam)⁻¹))
  have hM : F (moment n k d) = schurScalars d a := schur_moment_blocks n k d hn hk hkd κ Sd Sk
  have hP : F (lowProjector n k d) = schurScalars d ell := schur_lowProjector hn Sd
  have hellsq : (fun lam => ell lam * ell lam) = ell := by
    funext lam
    dsimp [ell]
    split_ifs <;> simp
  have hellM : (fun lam => ell lam * a lam) = a := by
    funext lam
    dsimp [ell,a]
    by_cases h : height lam ≤ k
    · simp [h]
    · simp [h,weylDim]
  have haInv : (fun lam => a lam * (a lam)⁻¹) = ell := by
    funext lam
    dsimp [ell,a]
    by_cases h : height lam ≤ k
    · have hk' : (weylDim k lam : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (weylDim_pos_of_height hn Sk lam h))
      have hd' : (weylDim d lam : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (weylDim_pos_of_height hn Sd lam (h.trans hkd)))
      rw [if_pos h]
      exact mul_inv_cancel₀ (div_ne_zero hk' hd')
    · simp [h,weylDim]
  have hPH : (lowProjector n k d).IsHermitian := by
    apply F.injective
    change F (star (lowProjector n k d)) = F (lowProjector n k d)
    rw [map_star,hP]
    exact schurScalars_hermitian ell (by intro lam; dsimp [ell]; split_ifs <;> simp)
  have hP2 : lowProjector n k d * lowProjector n k d = lowProjector n k d := by
    apply F.injective
    calc
      F (lowProjector n k d * lowProjector n k d) =
          F (lowProjector n k d) * F (lowProjector n k d) := map_mul F _ _
      _ = F (lowProjector n k d) := by rw [hP,schurScalars_mul,hellsq]
  have hPM : lowProjector n k d * moment n k d = moment n k d := by
    apply F.injective
    calc
      F (lowProjector n k d * moment n k d) =
          F (lowProjector n k d) * F (moment n k d) := map_mul F _ _
      _ = F (moment n k d) := by rw [hP,hM,schurScalars_mul,hellM]
  have hMN : moment n k d * N = lowProjector n k d := by
    apply F.injective
    rw [map_mul]
    change F (moment n k d) * F N = F (lowProjector n k d)
    rw [hP,hM]
    change schurScalars d a * F (F.symm (schurScalars d (fun lam => (a lam)⁻¹))) = _
    rw [F.apply_symm_apply,schurScalars_mul,haInv]
  have hhigh : highProjector n k d = 1-lowProjector n k d := by
    apply F.injective
    rw [map_sub,map_one]
    change schurConjugation Sd (highProjector n k d) = 1 - F (lowProjector n k d)
    rw [hP]
    rw [schur_highProjector hn Sd, ← schurScalars_one, ← schurScalars_sub]
    congr 1
    funext lam
    dsimp [ell]
    by_cases h : height lam ≤ k
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]
  have hp := matrix_projectors_of_support (moment n k d) (lowProjector n k d) N
    (moment_posSemidef n k d).isHermitian hPH hP2 hPM hMN
  exact ⟨hp.1, hp.2.trans hhigh.symm⟩

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d) :
    moment n k d = (∑ lam : Shape n, if height lam ≤ k then
        ((weylDim k lam : ℂ) / (weylDim d lam : ℂ)) • isotypic d lam else 0) ∧
    imageProjector n k d = lowProjector n k d ∧
    kernelProjector n k d = highProjector n k d := by
  obtain ⟨c,K,hc,κ,S,hS⟩ := RandomDimReduction.Channel.theorem_5_1
  exact ⟨moment_expansion n k d hn hk hkd (κ n) (S n d) (S n k),
    moment_support_projectors n k d hn hk hkd (κ n) (S n d) (S n k)⟩
