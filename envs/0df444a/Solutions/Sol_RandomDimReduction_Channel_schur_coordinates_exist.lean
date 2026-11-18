-- Prove2me | solution 1 for RandomDimReduction.Channel.schur_coordinates_exist
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T19:51:41.293388+00:00
-- url     : https://prove2.me/submissions/87368a0a-4b8f-4d0f-b6fa-40f42c9fef53

import Definitions.Def_RandomDimReduction_Channel_Tensor
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Representations
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_RandomDimReduction_Channel_Schur
import Mathlib.RepresentationTheory.Character
import Theorems.Thm_KWSpectrum_Estimator_eq_2_4_projections
import Theorems.Thm_RandomDimReduction_Channel_spechtModel_properties
import Mathlib.RepresentationTheory.Maschke
import Theorems.Thm_RandomDimReduction_Channel_lemma_B_2
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise MonoidAlgebra

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

-- CharacterIrreducible
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma matrix_character_trace {G : Type} [Group G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) (g : G) :
    (matrixRepresentation r).character g = (r g : Op (Fin d)).trace := by
  exact Matrix.trace_toLin_eq _ (EuclideanSpace.basisFun (Fin d) ℂ).toBasis

lemma matrix_irreducible_of_end_finrank {G : Type} [Group G] [Fintype G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) (hd : 0 < d)
    (he : Module.finrank ℂ (Representation.IntertwiningMap (matrixRepresentation r) (matrixRepresentation r)) = 1) :
    Irreducible r := by
  let rho := matrixRepresentation r
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  haveI : NeZero (Nat.card G : ℂ) := ⟨by simp [Nat.card_eq_fintype_card]⟩
  haveI : Nontrivial rho.asModule := by
    change Nontrivial (EuclideanSpace ℂ (Fin d))
    infer_instance
  haveI : Nontrivial (Submodule ℂ[G] rho.asModule) := by
    let x : rho.asModule := EuclideanSpace.basisFun (Fin d) ℂ 0
    have hx : x ≠ 0 := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.ne_zero 0
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have hmem : x ∈ (⊥ : Submodule ℂ[G] rho.asModule) := by rw [h]; trivial
    exact hx hmem
  have hid : (1 : Module.End ℂ[G] rho.asModule) ≠ 0 := by
    intro h
    have := congrArg (fun f : Module.End ℂ[G] rho.asModule => f (EuclideanSpace.basisFun (Fin d) ℂ 0)) h
    exact (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.ne_zero 0 this
  have hEnd : Module.finrank ℂ (Module.End ℂ[G] rho.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd (ρ := rho)).toLinearEquiv.finrank_eq]
    exact he
  haveI : IsSimpleModule ℂ[G] rho.asModule := by
    apply (isSimpleModule_iff ℂ[G] rho.asModule).mpr
    refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
    intro S
    obtain ⟨T, hST⟩ := exists_isCompl S
    let P := S.projection T hST
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (1 : Module.End ℂ[G] rho.asModule) hid).mp hEnd P
    by_cases hcz : c = 0
    · left
      have hp : P = 0 := by simpa [hcz] using hc.symm
      have hh := S.range_projection hST
      rw [show S.projection T hST = 0 from hp, LinearMap.range_zero] at hh
      exact hh.symm
    · right
      rw [← S.range_projection hST]
      apply LinearMap.range_eq_top.mpr
      intro x
      refine ⟨c⁻¹ • x, ?_⟩
      change P (c⁻¹ • x) = x
      rw [← hc]
      simp [smul_smul, hcz]
  haveI : rho.IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mpr inferInstance
  refine ⟨hd, ?_⟩
  intro S hS
  let S' : Subrepresentation rho := ⟨S, fun g x hx => hS g x hx⟩
  rcases eq_bot_or_eq_top S' with hb | ht
  · left
    exact congrArg Subrepresentation.toSubmodule hb
  · right
    exact congrArg Subrepresentation.toSubmodule ht

end RandomDimReduction.Channel

-- SpechtModelExistence
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma leftRegular_one (n : ℕ) : QAlgorithms.Schur.leftRegular (1 : Equiv.Perm (Fin n)) = 1 := by
  ext g h
  simp [QAlgorithms.Schur.leftRegular,Matrix.one_apply]

lemma leftRegular_mul {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.leftRegular (p*q) = QAlgorithms.Schur.leftRegular p * QAlgorithms.Schur.leftRegular q := by
  ext g h
  simp only [QAlgorithms.Schur.leftRegular,Matrix.mul_apply,Matrix.of_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_assoc]

lemma leftRegular_mul_matrix {n : ℕ} (p : Equiv.Perm (Fin n))
    (B : Op (Equiv.Perm (Fin n))) (g h : Equiv.Perm (Fin n)) :
    (QAlgorithms.Schur.leftRegular p * B) g h = B (p⁻¹*g) h := by
  have he (t : Equiv.Perm (Fin n)) : (g = p*t) ↔ t = p⁻¹*g := by
    constructor
    · intro hg
      rw [hg,inv_mul_cancel_left]
    · rintro rfl
      simp
  simp only [Matrix.mul_apply,QAlgorithms.Schur.leftRegular,Matrix.of_apply,he,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

lemma matrix_mul_leftRegular {n : ℕ} (p : Equiv.Perm (Fin n))
    (B : Op (Equiv.Perm (Fin n))) (g h : Equiv.Perm (Fin n)) :
    (B * QAlgorithms.Schur.leftRegular p) g h = B g (p*h) := by
  simp only [Matrix.mul_apply,QAlgorithms.Schur.leftRegular,Matrix.of_apply,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]

lemma leftRegular_youngRight_commute {n : ℕ} (lam : Shape n) (p : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.leftRegular p * QAlgorithms.Schur.youngRightOperator lam =
      QAlgorithms.Schur.youngRightOperator lam * QAlgorithms.Schur.leftRegular p := by
  ext g h
  rw [leftRegular_mul_matrix,matrix_mul_leftRegular]
  simp only [QAlgorithms.Schur.youngRightOperator,Matrix.of_apply,inv_mul_eq_iff_eq_mul,mul_assoc]

lemma leftRegular_preserves_specht {n : ℕ} (lam : Shape n) (p : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℂ (Equiv.Perm (Fin n))) (hx : x ∈ QAlgorithms.Schur.spechtSpace lam) :
    Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular p) x ∈ QAlgorithms.Schur.spechtSpace lam := by
  obtain ⟨y,rfl⟩ := hx
  refine ⟨Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular p) y, ?_⟩
  have h := congrArg (fun A : Op (Equiv.Perm (Fin n)) => Matrix.toEuclideanLin A y)
    (leftRegular_youngRight_commute lam p)
  simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,LinearMap.comp_apply] using h.symm

lemma spechtRepresentation_coe {n : ℕ} (lam : Shape n) (p : Equiv.Perm (Fin n))
    (x : QAlgorithms.Schur.spechtSpace lam) :
    (QAlgorithms.Schur.spechtRepresentation lam p x).val =
      Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular p) x.val := by
  change (QAlgorithms.Schur.spechtSpace lam).starProjection
    (Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular p) x.val) = _
  exact (QAlgorithms.Schur.spechtSpace lam).starProjection_eq_self_iff.mpr
    (leftRegular_preserves_specht lam p x.val x.property)

lemma leftRegular_toEuclideanLin {n : ℕ} (p : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℂ (Equiv.Perm (Fin n))) :
    Matrix.toEuclideanLin (QAlgorithms.Schur.leftRegular p) x =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft p) x := by
  ext g
  have he (t : Equiv.Perm (Fin n)) : (g = p*t) ↔ t = p⁻¹*g := by
    constructor
    · intro hg
      rw [hg,inv_mul_cancel_left]
    · rintro rfl
      simp
  simp [Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,
    QAlgorithms.Schur.leftRegular,he,LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

lemma spechtRepresentation_one {n : ℕ} (lam : Shape n) :
    QAlgorithms.Schur.spechtRepresentation lam 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [spechtRepresentation_coe,leftRegular_one]
  simp [Matrix.toEuclideanLin]

lemma spechtRepresentation_mul {n : ℕ} (lam : Shape n) (p q : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.spechtRepresentation lam (p*q) =
      (QAlgorithms.Schur.spechtRepresentation lam p).comp (QAlgorithms.Schur.spechtRepresentation lam q) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply,spechtRepresentation_coe,leftRegular_mul,
    Matrix.toEuclideanLin,Matrix.toLpLin_mul_same]

noncomputable def spechtIsometry {n : ℕ} (lam : Shape n) (p : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.spechtSpace lam ≃ₗᵢ[ℂ] QAlgorithms.Schur.spechtSpace lam where
  toLinearEquiv :=
    { toLinearMap := QAlgorithms.Schur.spechtRepresentation lam p
      invFun := QAlgorithms.Schur.spechtRepresentation lam p⁻¹
      left_inv x := by
        change QAlgorithms.Schur.spechtRepresentation lam p⁻¹ (QAlgorithms.Schur.spechtRepresentation lam p x) = x
        have h := congrArg (fun L => L x) (spechtRepresentation_mul lam p⁻¹ p)
        simpa only [inv_mul_cancel,spechtRepresentation_one,LinearMap.id_apply,LinearMap.comp_apply] using h.symm
      right_inv x := by
        change QAlgorithms.Schur.spechtRepresentation lam p (QAlgorithms.Schur.spechtRepresentation lam p⁻¹ x) = x
        have h := congrArg (fun L => L x) (spechtRepresentation_mul lam p p⁻¹)
        simpa only [mul_inv_cancel,spechtRepresentation_one,LinearMap.id_apply,LinearMap.comp_apply] using h.symm }
  norm_map' x := by
    change ‖(QAlgorithms.Schur.spechtRepresentation lam p x).val‖ = ‖x.val‖
    rw [spechtRepresentation_coe,leftRegular_toEuclideanLin]
    exact LinearIsometryEquiv.norm_map _ _

lemma standardSpecht_toMatrix {n : ℕ} (lam : Shape n) (p : Equiv.Perm (Fin n)) :
    standardSpecht lam p = LinearMap.toMatrix (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam)).toBasis
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam)).toBasis
      (QAlgorithms.Schur.spechtRepresentation lam p) := by
  ext i j
  simp only [standardSpecht,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]

noncomputable def standardSpechtHom {n : ℕ} (lam : Shape n) :
    Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin (spechtDim lam)) ℂ where
  toFun p := ⟨standardSpecht lam p, by
    have h := (spechtIsometry lam p).toMatrix_mem_unitaryGroup
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam))
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam))
    change LinearMap.toMatrix
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam)).toBasis
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam)).toBasis
      (QAlgorithms.Schur.spechtRepresentation lam p) ∈ _ at h
    rw [← standardSpecht_toMatrix] at h
    exact h⟩
  map_one' := by
    apply Subtype.ext
    change standardSpecht lam 1 = 1
    simp only [standardSpecht_toMatrix,spechtRepresentation_one,LinearMap.toMatrix_id]
    rfl
  map_mul' p q := by
    apply Subtype.ext
    change standardSpecht lam (p*q) = standardSpecht lam p * standardSpecht lam q
    simp only [standardSpecht_toMatrix,spechtRepresentation_mul]
    exact LinearMap.toMatrix_comp
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam)).toBasis
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam)).toBasis
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam)).toBasis _ _

noncomputable def canonicalSpechtModel (n : ℕ) : SpechtModel n where
  action lam := standardSpechtHom lam
  labelled lam := ⟨1,by
    intro p
    change (1 : Op (Fin (spechtDim lam))) * standardSpecht lam p *
      (1 : Op (Fin (spechtDim lam)))ᴴ = standardSpecht lam p
    simp⟩

end RandomDimReduction.Channel

-- IntertwinerHilbertSpace
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def vectorMatrixEquiv (a b : ℕ) : EuclideanSpace ℂ (Fin b × Fin a) ≃ₗ[ℂ] Matrix (Fin b) (Fin a) ℂ where
  toFun x i j := x (i,j)
  invFun T := WithLp.toLp 2 (fun ij => T ij.1 ij.2)
  left_inv x := by ext ⟨i,j⟩; rfl
  right_inv T := by ext i j; rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def intertwinerVectors {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin b × Fin a)) where
  carrier x := ∀ g, vectorMatrixEquiv a b x * (rA g : Op (Fin a)) =
    (rB g : Op (Fin b)) * vectorMatrixEquiv a b x
  zero_mem' := by intro g; simp
  add_mem' hx hy := by intro g; simp only [map_add,Matrix.add_mul,Matrix.mul_add,hx g,hy g]
  smul_mem' c x hx := by intro g; simp only [map_smul,Matrix.smul_mul,Matrix.mul_smul,hx g]

def intertwinerVectorsToMap {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ) :
    intertwinerVectors rA rB →ₗ[ℂ] Representation.IntertwiningMap (matrixRepresentation rA) (matrixRepresentation rB) where
  toFun x := matrixIntertwiner rA rB (vectorMatrixEquiv a b x.val) x.property
  map_add' x y := by
    apply Representation.IntertwiningMap.toLinearMap_injective
    change Matrix.toEuclideanLin (vectorMatrixEquiv a b (x.val+y.val)) =
      Matrix.toEuclideanLin (vectorMatrixEquiv a b x.val) + Matrix.toEuclideanLin (vectorMatrixEquiv a b y.val)
    rw [map_add,map_add]
  map_smul' c x := by
    apply Representation.IntertwiningMap.toLinearMap_injective
    change Matrix.toEuclideanLin (vectorMatrixEquiv a b (c • x.val)) =
      c • Matrix.toEuclideanLin (vectorMatrixEquiv a b x.val)
    rw [map_smul,map_smul]

def intertwinerVectorsEquiv {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ) :
    intertwinerVectors rA rB ≃ₗ[ℂ] Representation.IntertwiningMap (matrixRepresentation rA) (matrixRepresentation rB) :=
  LinearEquiv.ofBijective (intertwinerVectorsToMap rA rB) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply (vectorMatrixEquiv a b).injective
      apply Matrix.toEuclideanLin.injective
      exact congrArg Representation.IntertwiningMap.toLinearMap hxy
    · intro T
      let M : Matrix (Fin b) (Fin a) ℂ := Matrix.toEuclideanLin.symm T.toLinearMap
      have hM (g : G) : M * (rA g : Op (Fin a)) = (rB g : Op (Fin b)) * M := by
        apply Matrix.toEuclideanLin.injective
        have hT := T.isIntertwining' g
        change T.toLinearMap ∘ₗ Matrix.toEuclideanLin (rA g : Op (Fin a)) =
          Matrix.toEuclideanLin (rB g : Op (Fin b)) ∘ₗ T.toLinearMap at hT
        simp only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same]
        change Matrix.toEuclideanLin M ∘ₗ Matrix.toEuclideanLin (rA g : Op (Fin a)) =
          Matrix.toEuclideanLin (rB g : Op (Fin b)) ∘ₗ Matrix.toEuclideanLin M
        simpa only [M,LinearEquiv.apply_symm_apply] using hT
      let x : intertwinerVectors rA rB := ⟨(vectorMatrixEquiv a b).symm M,by
        intro g
        rw [LinearEquiv.apply_symm_apply]
        exact hM g⟩
      refine ⟨x,?_⟩
      apply Representation.IntertwiningMap.toLinearMap_injective
      change Matrix.toEuclideanLin (vectorMatrixEquiv a b ((vectorMatrixEquiv a b).symm M)) = T.toLinearMap
      rw [LinearEquiv.apply_symm_apply]
      exact Matrix.toEuclideanLin.apply_symm_apply T.toLinearMap)

lemma frobenius_inner_trace {a b : ℕ} (x y : EuclideanSpace ℂ (Fin b × Fin a)) :
    ((vectorMatrixEquiv a b x)ᴴ * vectorMatrixEquiv a b y).trace = inner ℂ x y := by
  change (∑ i : Fin a, ∑ j : Fin b, star (x (j,i)) * y (j,i)) = inner ℂ x y
  rw [Finset.sum_comm]
  simp only [PiLp.inner_apply,RCLike.inner_apply',Fintype.sum_prod_type]
  rfl

lemma intertwiner_gram_scalar {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (hA : Irreducible rA) (x y : intertwinerVectors rA rB) :
    (vectorMatrixEquiv a b x.val)ᴴ * vectorMatrixEquiv a b y.val =
      (inner ℂ x y / (a : ℂ)) • (1 : Op (Fin a)) := by
  let X := vectorMatrixEquiv a b x.val
  let Y := vectorMatrixEquiv a b y.val
  have hc (g : G) : Xᴴ * Y * (rA g : Op (Fin a)) = (rA g : Op (Fin a)) * (Xᴴ * Y) := by
    rw [Matrix.mul_assoc,y.property g,← Matrix.mul_assoc,
      adjoint_intertwiner rA rB X x.property g,Matrix.mul_assoc]
  obtain ⟨c,hc⟩ := matrix_schur_scalar rA hA (Xᴴ*Y) hc
  have ht := congrArg Matrix.trace hc
  rw [Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin] at ht
  rw [show (Xᴴ * Y).trace = inner ℂ x y from frobenius_inner_trace x.val y.val] at ht
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA.1)
  have hceq : c = inner ℂ x y / (a : ℂ) := by
    rw [ht]
    exact (mul_div_cancel_right₀ c ha).symm
  rw [hc,hceq]

end RandomDimReduction.Channel

-- IntertwinerBasis
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev intertwinerMultiplicity {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ) :=
  Module.finrank ℂ (intertwinerVectors rA rB)

def intertwinerBasisMatrix {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (j : Fin (intertwinerMultiplicity rA rB)) : Matrix (Fin b) (Fin a) ℂ :=
  (Real.sqrt (a : ℝ) : ℂ) • vectorMatrixEquiv a b
    (stdOrthonormalBasis ℂ (intertwinerVectors rA rB) j).val

lemma intertwinerBasisMatrix_intertwines {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (j : Fin (intertwinerMultiplicity rA rB)) (g : G) :
    intertwinerBasisMatrix rA rB j * (rA g : Op (Fin a)) =
      (rB g : Op (Fin b)) * intertwinerBasisMatrix rA rB j := by
  unfold intertwinerBasisMatrix
  rw [Matrix.smul_mul,Matrix.mul_smul]
  congr 1
  exact (stdOrthonormalBasis ℂ (intertwinerVectors rA rB) j).property g

lemma sqrt_cast_gram (a : ℕ) :
    star (Real.sqrt (a : ℝ) : ℂ) * (Real.sqrt (a : ℝ) : ℂ) = (a : ℂ) := by
  rw [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg a),Complex.ofReal_natCast]

lemma intertwinerBasisMatrix_gram {G : Type} [Group G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (hA : Irreducible rA) (i j : Fin (intertwinerMultiplicity rA rB)) :
    (intertwinerBasisMatrix rA rB i)ᴴ * intertwinerBasisMatrix rA rB j =
      if i = j then 1 else 0 := by
  let b := stdOrthonormalBasis ℂ (intertwinerVectors rA rB)
  have h := intertwiner_gram_scalar rA rB hA (b i) (b j)
  unfold intertwinerBasisMatrix
  rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,sqrt_cast_gram,h,smul_smul]
  have hi := (orthonormal_iff_ite.mp b.orthonormal) i j
  rw [hi]
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA.1)
  by_cases hij : i = j
  · simp [hij,ha]
  · simp [hij]

lemma intertwinerBasisMatrix_cross {G L : Type} [Group G] {dim : L → ℕ} {b : ℕ}
    (r : ∀ l, G →* Matrix.unitaryGroup (Fin (dim l)) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (hirr : ∀ l, Irreducible (r l))
    (hneq : ∀ l m, l ≠ m → Inequivalent (r l) (r m))
    (l m : L) (hlm : l ≠ m)
    (i : Fin (intertwinerMultiplicity (r l) rB)) (j : Fin (intertwinerMultiplicity (r m) rB)) :
    (intertwinerBasisMatrix (r l) rB i)ᴴ * intertwinerBasisMatrix (r m) rB j = 0 := by
  let X := intertwinerBasisMatrix (r l) rB i
  let Y := intertwinerBasisMatrix (r m) rB j
  apply intertwiner_zero_of_inequivalent (r m) (r l) (hirr m) (hirr l) (hneq m l (Ne.symm hlm))
  intro g
  rw [Matrix.mul_assoc,intertwinerBasisMatrix_intertwines,
    ← Matrix.mul_assoc,adjoint_intertwiner (r l) rB X (intertwinerBasisMatrix_intertwines (r l) rB i) g,
    Matrix.mul_assoc]

end RandomDimReduction.Channel

-- SchurMultiplicityDimensions
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def oneRowDiagram (n : ℕ) : YoungDiagram where
  cells := (Finset.range n).image (fun j => (0,j))
  isLowerSet := by
    rintro a b hab hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨b.2,Finset.mem_range.mpr (hab.2.trans_lt (Finset.mem_range.mp hj)),?_⟩
    exact Prod.ext (Nat.eq_zero_of_le_zero hab.1).symm rfl

lemma oneRow_colLen_le_one (n : ℕ) : (oneRowDiagram n).colLen 0 ≤ 1 := by
  rw [YoungDiagram.colLen_eq_card]
  have hs : (oneRowDiagram n).col 0 ⊆ {(0,0)} := by
    intro p hp
    have hh := YoungDiagram.mem_col_iff.mp hp
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hh.1
    subst p
    have hj0 : j = 0 := hh.2
    simp [hj0]
  simpa using Finset.card_le_card hs

lemma diagram_colLen_le_card (D : YoungDiagram) (j : ℕ) : D.colLen j ≤ D.card := by
  rw [YoungDiagram.colLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

def oneRowShape (n : ℕ) : Shape n :=
  ⟨oneRowDiagram n,by
    have hc : (oneRowDiagram n).card = n := by
      simp only [YoungDiagram.card,oneRowDiagram]
      rw [Finset.card_image_of_injective _ (by intro a b h; exact (Prod.mk.inj h).2),Finset.card_range]
    exact ⟨hc,(diagram_colLen_le_card _ _).trans_eq hc⟩⟩

lemma specht_regular_character {n : ℕ} (g : Equiv.Perm (Fin n)) :
    (∑ lam : Shape n, ((spechtDim lam : ℂ) / (n.factorial : ℂ)) *
      QAlgorithms.Schur.spechtCharacter lam g⁻¹) = if g = 1 then 1 else 0 := by
  have hp := (KWSpectrum.Estimator.eq_2_4_projections (oneRowShape n)).2.2.2.2.1
  have he := congrArg (fun A : Op (Word n n) => A id (fun t => g t)) hp
  have hentry (lam : Shape n) : QAlgorithms.Schur.isotypicProjector lam id (fun t => g t) =
      ((spechtDim lam : ℂ) / (n.factorial : ℂ)) * QAlgorithms.Schur.spechtCharacter lam g⁻¹ := by
    simp [QAlgorithms.Schur.isotypicProjector,Matrix.smul_apply,Matrix.sum_apply,perm_entry_reversed,spechtDim]
  have hig : ((id : Fin n → Fin n) = fun t => g t) ↔ g = 1 := by
    constructor
    · intro h
      apply Equiv.ext
      intro t
      exact (congrFun h t).symm
    · rintro rfl
      rfl
  simpa only [Matrix.sum_apply,hentry,Matrix.one_apply,hig] using he

lemma intertwinerMultiplicity_character {G : Type} [Group G] [Fintype G] {a b : ℕ}
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ) (rB : G →* Matrix.unitaryGroup (Fin b) ℂ) :
    (intertwinerMultiplicity rA rB : ℂ) = (Fintype.card G : ℂ)⁻¹ *
      ∑ g : G, (rB g : Op (Fin b)).trace * (rA g⁻¹ : Op (Fin a)).trace := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by simp [Nat.card_eq_fintype_card])
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (matrixRepresentation rA) (matrixRepresentation rB)
  rw [← (intertwinerVectorsEquiv rA rB).finrank_eq] at h
  simpa only [Nat.card_eq_fintype_card,matrix_character_trace] using h.symm

lemma sum_specht_intertwiner_dimensions {n b : ℕ} (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) :
    (∑ lam : Shape n, spechtDim lam * intertwinerMultiplicity (κ.action lam) rB) = b := by
  suffices hc : (∑ lam : Shape n, (spechtDim lam : ℂ) *
      (intertwinerMultiplicity (κ.action lam) rB : ℂ)) = (b : ℂ) by exact_mod_cast hc
  simp_rw [intertwinerMultiplicity_character,Fintype.card_perm,Fintype.card_fin,SpechtModel_trace]
  calc
    _ = ∑ g : Equiv.Perm (Fin n), (rB g : Op (Fin b)).trace *
        ∑ lam : Shape n, ((spechtDim lam : ℂ) / (n.factorial : ℂ)) *
          QAlgorithms.Schur.spechtCharacter lam g⁻¹ := by
      simp only [Finset.mul_sum,Finset.sum_mul,div_eq_mul_inv]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro lam _
      ring
    _ = (b : ℂ) := by
      simp only [specht_regular_character,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_eq',Finset.mem_univ,if_true,map_one,Submonoid.coe_one,
        Matrix.trace_one,Fintype.card_fin]

end RandomDimReduction.Channel

-- RepresentationReindex
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma reindex_mul {a b c a' b' c' : Type} [Fintype b] [Fintype b']
    (ea : a ≃ a') (eb : b ≃ b') (ec : c ≃ c') (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    (Matrix.reindex ea eb A * Matrix.reindex eb ec B : Matrix a' c' ℂ) = Matrix.reindex ea ec (A * B) :=
  Matrix.reindexLinearEquiv_mul ℂ ℂ ea eb ec A B

lemma reindex_one {a b : Type} [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Matrix.reindex e e (1 : Op a) = 1 := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply]

def reindexStarAlgEquiv {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) : Op a ≃⋆ₐ[ℂ] Op b :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro M; rfl
    map_smul' := by intro c M; rfl }

def reindexUnitaryHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) : Matrix.unitaryGroup a ℂ →* Matrix.unitaryGroup b ℂ where
  toFun U := ⟨Matrix.reindex e e (U : Op a), Unitary.map_mem (reindexStarAlgEquiv e) U.property⟩
  map_one' := by apply Subtype.ext; exact reindex_one e
  map_mul' U V := by apply Subtype.ext; exact (reindex_mul e e e _ _).symm

lemma reindexUnitaryHom_coe {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (U : Matrix.unitaryGroup a ℂ) :
    (reindexUnitaryHom e U : Op b) = Matrix.reindex e e (U : Op a) := rfl

def finiteRepDecomposition {G L a : Type} [Group G] [Fintype L] [DecidableEq L]
    [Fintype a] [DecidableEq a] (m dim : L → ℕ)
    (r : G →* Matrix.unitaryGroup a ℂ)
    (rho : ∀ l, G →* Matrix.unitaryGroup (Fin (dim l)) ℂ)
    (T : Matrix (RepIndex m dim) a ℂ) (hL : T * Tᴴ = 1) (hR : Tᴴ * T = 1)
    (hI : ∀ g, T * (r g : Op a) * Tᴴ = Matrix.blockDiagonal'
      (fun l => Matrix.kronecker (1 : Op (Fin (m l))) (rho l g : Op (Fin (dim l))))) :
    RepDecomposition m dim ((reindexUnitaryHom (Fintype.equivFin a)).comp r) rho where
  T := Matrix.reindex (Equiv.refl _) (Fintype.equivFin a) T
  left_unitary := by
    rw [show Classical.decEq L = (inferInstance : DecidableEq L) from Subsingleton.elim _ _]
    rw [Matrix.conjTranspose_reindex, reindex_mul, hL]
    exact reindex_one _
  right_unitary := by
    rw [Matrix.conjTranspose_reindex, reindex_mul, hR]
    exact reindex_one _
  intertwines g := by
    rw [show Classical.decEq L = (inferInstance : DecidableEq L) from Subsingleton.elim _ _]
    change Matrix.reindex (Equiv.refl _) (Fintype.equivFin a) T *
      Matrix.reindex (Fintype.equivFin a) (Fintype.equivFin a) (r g : Op a) *
      (Matrix.reindex (Equiv.refl _) (Fintype.equivFin a) T)ᴴ = _
    rw [Matrix.conjTranspose_reindex, reindex_mul, reindex_mul, hI g]
    rfl

end RandomDimReduction.Channel

-- SchurSynthesis
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev MultiplicityIndex {n b : ℕ} (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) :=
  (lam : Shape n) × (Fin (spechtDim lam) × Fin (intertwinerMultiplicity (κ.action lam) rB))

def schurSynthesis {n b : ℕ} (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) :
    Matrix (Fin b) (MultiplicityIndex κ rB) ℂ :=
  fun h i => intertwinerBasisMatrix (κ.action i.1) rB i.2.2 h i.2.1

lemma schurSynthesis_isometry {n b : ℕ} (hn : 0 < n) (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) :
    (schurSynthesis κ rB)ᴴ * schurSynthesis κ rB = 1 := by
  have hirr := (spechtModel_properties n hn κ).1
  have hneq := (spechtModel_properties n hn κ).2
  ext ⟨l,⟨s,i⟩⟩ ⟨m,⟨t,j⟩⟩
  have he : ((schurSynthesis κ rB)ᴴ * schurSynthesis κ rB) ⟨l,(s,i)⟩ ⟨m,(t,j)⟩ =
      ((intertwinerBasisMatrix (κ.action l) rB i)ᴴ * intertwinerBasisMatrix (κ.action m) rB j) s t := rfl
  rw [he]
  by_cases hlm : l = m
  · subst m
    rw [intertwinerBasisMatrix_gram _ _ (hirr l)]
    by_cases hij : i = j
    · subst j
      simp [Matrix.one_apply]
    · simp [hij,Matrix.one_apply,Prod.ext_iff]
  · rw [intertwinerBasisMatrix_cross κ.action rB hirr hneq l m hlm]
    simp [Matrix.one_apply,show (⟨l,(s,i)⟩ : MultiplicityIndex κ rB) ≠ ⟨m,(t,j)⟩ from
      fun h => hlm (congrArg Sigma.fst h)]

lemma rectangular_coisometry_of_card_eq {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (T : Matrix b a ℂ) (hT : Tᴴ*T=1) (hc : Fintype.card a = Fintype.card b) : T*Tᴴ=1 := by
  let e : a ≃ b := Fintype.equivOfCardEq hc
  let R : Op b := Matrix.reindex (Equiv.refl b) e T
  have hR : Rᴴ*R=1 := by
    change (Matrix.reindex (Equiv.refl b) e T)ᴴ * Matrix.reindex (Equiv.refl b) e T = 1
    rw [Matrix.conjTranspose_reindex,reindex_mul,hT,reindex_one]
  have hR' : R*Rᴴ=1 := (mul_eq_one_comm).mp hR
  change Matrix.reindex (Equiv.refl b) e T * (Matrix.reindex (Equiv.refl b) e T)ᴴ = 1 at hR'
  rw [Matrix.conjTranspose_reindex,reindex_mul] at hR'
  exact hR'

lemma schurSynthesis_coisometry {n b : ℕ} (hn : 0 < n) (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) :
    schurSynthesis κ rB * (schurSynthesis κ rB)ᴴ = 1 := by
  apply rectangular_coisometry_of_card_eq _ (schurSynthesis_isometry hn κ rB)
  simpa only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin] using
    sum_specht_intertwiner_dimensions κ rB

lemma schurSynthesis_intertwines {n b : ℕ} (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) (g : Equiv.Perm (Fin n)) :
    (rB g : Op (Fin b)) * schurSynthesis κ rB = schurSynthesis κ rB *
      Matrix.blockDiagonal' (fun lam : Shape n => Matrix.kronecker
        (κ.action lam g : Op (Fin (spechtDim lam)))
        (1 : Op (Fin (intertwinerMultiplicity (κ.action lam) rB)))) := by
  ext h ⟨lam,⟨s,j⟩⟩
  have hh := congrArg (fun M : Matrix (Fin b) (Fin (spechtDim lam)) ℂ => M h s)
    (intertwinerBasisMatrix_intertwines (κ.action lam) rB j g)
  simp only [Matrix.mul_apply] at hh
  simp only [Matrix.mul_apply,Fintype.sum_sigma]
  rw [Finset.sum_eq_single lam]
  · simp only [Matrix.blockDiagonal'_apply_eq,Fintype.sum_prod_type,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,mul_assoc,mul_ite,mul_zero,mul_one,
      Finset.sum_ite_eq',Finset.mem_univ,if_true,schurSynthesis]
    exact hh.symm
  · intro mu _ hmu
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ hmu]
  · simp

lemma schurSynthesis_conjugates {n b : ℕ} (hn : 0 < n) (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) (g : Equiv.Perm (Fin n)) :
    (schurSynthesis κ rB)ᴴ * (rB g : Op (Fin b)) * schurSynthesis κ rB =
      Matrix.blockDiagonal' (fun lam : Shape n => Matrix.kronecker
        (κ.action lam g : Op (Fin (spechtDim lam)))
        (1 : Op (Fin (intertwinerMultiplicity (κ.action lam) rB)))) := by
  rw [Matrix.mul_assoc,schurSynthesis_intertwines,← Matrix.mul_assoc,
    schurSynthesis_isometry hn κ rB,Matrix.one_mul]

end RandomDimReduction.Channel

-- TensorMultiplicity
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev tensorWordDimension (n d : ℕ) := Fintype.card (Word n d)

def finiteTensorPermutationRep (n d : ℕ) :
    Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin (tensorWordDimension n d)) ℂ :=
  (reindexUnitaryHom (Fintype.equivFin (Word n d))).comp (tensorPermutation_rep n d)

lemma finiteTensorPermutationRep_apply (n d : ℕ) (g : Equiv.Perm (Fin n)) :
    (finiteTensorPermutationRep n d g : Op (Fin (tensorWordDimension n d))) =
      Matrix.reindex (Fintype.equivFin (Word n d)) (Fintype.equivFin (Word n d))
        (QAlgorithms.Schur.tensorPermutation d n g) := rfl

lemma reindex_trace {a b : Type} [Fintype a] [Fintype b] (e : a ≃ b) (A : Op a) :
    (Matrix.reindex e e A).trace = A.trace := by
  change (∑ i : b, A (e.symm i) (e.symm i)) = ∑ i : a, A i i
  exact e.symm.sum_comp (fun i => A i i)

lemma finiteTensor_trace (n d : ℕ) (g : Equiv.Perm (Fin n)) :
    (finiteTensorPermutationRep n d g : Op (Fin (tensorWordDimension n d))).trace =
      (QAlgorithms.Schur.tensorPermutation d n g).trace := by
  rw [finiteTensorPermutationRep_apply,reindex_trace]

lemma tensorMultiplicity_present {n d : ℕ} (hn : 0 < n) (κ : SpechtModel n)
    (lam : Shape n) (hlam : height lam ≤ d) :
    intertwinerMultiplicity (κ.action lam) (finiteTensorPermutationRep n d) = weylDim d lam := by
  have hdim := intertwinerMultiplicity_character (κ.action lam) (finiteTensorPermutationRep n d)
  simp only [Fintype.card_perm,Fintype.card_fin,finiteTensor_trace,SpechtModel_trace] at hdim
  have htr := (KWSpectrum.Estimator.eq_2_4_projections (shapeAt lam hlam)).2.2.2.2.2.2.2 1
  rw [tensorPermutation_one,Matrix.one_mul] at htr
  have he : QAlgorithms.Schur.spechtCharacter (shapeAt lam hlam) 1 =
      QAlgorithms.Schur.spechtCharacter lam 1 := rfl
  rw [he,specht_char_one' κ] at htr
  have htr' : (QAlgorithms.Schur.isotypicProjector (shapeAt lam hlam)).trace =
      (weylDim d lam : ℂ) * (spechtDim lam : ℂ) := by
    simpa only [weylDim,dif_pos hlam] using htr
  have hraw : (QAlgorithms.Schur.isotypicProjector (shapeAt lam hlam)).trace =
      (spechtDim lam : ℂ) * (intertwinerMultiplicity (κ.action lam) (finiteTensorPermutationRep n d) : ℂ) := by
    rw [hdim]
    simp only [QAlgorithms.Schur.isotypicProjector,Matrix.trace_smul,Matrix.trace_sum,smul_eq_mul]
    have hcast : Module.finrank ℂ (QAlgorithms.Schur.spechtSpace (shapeAt lam hlam)) = spechtDim lam := rfl
    rw [hcast]
    simp only [div_eq_mul_inv,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    have hg : QAlgorithms.Schur.spechtCharacter (shapeAt lam hlam) g⁻¹ =
        QAlgorithms.Schur.spechtCharacter lam g⁻¹ := rfl
    rw [hg]
    ring
  have hsp : (spechtDim lam : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (spechtDim_pos_of_model hn κ lam))
  have h := hraw.symm.trans htr'
  rw [mul_comm (weylDim d lam : ℂ)] at h
  exact_mod_cast mul_left_cancel₀ hsp h

lemma shapeOfPartition {n d : ℕ} (lam : QAlgorithms.Schur.Partition d n) :
    ∃ mu : Shape n, mu.val = lam.val := by
  exact ⟨⟨lam.val,lam.property.1,(diagram_colLen_le_card lam.val 0).trans_eq lam.property.1⟩,rfl⟩

lemma finite_projector_intertwiner {n d : ℕ} (hn : 0 < n) (κ : SpechtModel n)
    (lam mu : Shape n) (hmu : height mu ≤ d)
    (T : Matrix (Fin (tensorWordDimension n d)) (Fin (spechtDim lam)) ℂ)
    (hT : ∀ g, T * (κ.action lam g : Op (Fin (spechtDim lam))) =
      (finiteTensorPermutationRep n d g : Op (Fin (tensorWordDimension n d))) * T) :
    Matrix.reindex (Fintype.equivFin (Word n d)) (Fintype.equivFin (Word n d))
      (QAlgorithms.Schur.isotypicProjector (shapeAt mu hmu)) * T = if mu = lam then T else 0 := by
  let e := Fintype.equivFin (Word n d)
  have he : Matrix.reindex e e (QAlgorithms.Schur.isotypicProjector (shapeAt mu hmu)) =
      ((spechtDim mu : ℂ) / (n.factorial : ℂ)) • ∑ g : Equiv.Perm (Fin n),
        QAlgorithms.Schur.spechtCharacter mu g⁻¹ •
          (finiteTensorPermutationRep n d g : Op (Fin (tensorWordDimension n d))) := by
    change reindexStarAlgEquiv e (QAlgorithms.Schur.isotypicProjector (shapeAt mu hmu)) = _
    change reindexStarAlgEquiv e (((spechtDim mu : ℂ) / (n.factorial : ℂ)) •
      ∑ g : Equiv.Perm (Fin n), QAlgorithms.Schur.spechtCharacter mu g⁻¹ •
        QAlgorithms.Schur.tensorPermutation d n g) = _
    simp only [map_smul,map_sum]
    rfl
  rw [he]
  have hh : (((spechtDim mu : ℂ) / (n.factorial : ℂ)) • ∑ g : Equiv.Perm (Fin n),
      QAlgorithms.Schur.spechtCharacter mu g⁻¹ •
        (finiteTensorPermutationRep n d g : Op (Fin (tensorWordDimension n d)))) * T =
      T * (((spechtDim mu : ℂ) / (n.factorial : ℂ)) • ∑ g : Equiv.Perm (Fin n),
        QAlgorithms.Schur.spechtCharacter mu g⁻¹ • (κ.action lam g : Op (Fin (spechtDim lam)))) := by
    simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.sum_mul,Matrix.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [hT]
  rw [hh,specht_central_character_action hn κ mu lam]
  split_ifs <;> simp

lemma tensorMultiplicity_absent {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) (κ : SpechtModel n)
    (lam : Shape n) (hlam : ¬height lam ≤ d) :
    intertwinerMultiplicity (κ.action lam) (finiteTensorPermutationRep n d) = 0 := by
  have hzero : ∀ x : intertwinerVectors (κ.action lam) (finiteTensorPermutationRep n d), x = 0 := by
    intro x
    let T := vectorMatrixEquiv (spechtDim lam) (tensorWordDimension n d) x.val
    have hT := x.property
    haveI : Nonempty (QAlgorithms.Schur.Partition d n) :=
      ⟨⟨oneRowDiagram n,(oneRowShape n).property.1,(oneRow_colLen_le_one n).trans hd⟩⟩
    let mu0 := Classical.choice (inferInstance : Nonempty (QAlgorithms.Schur.Partition d n))
    have hp := (KWSpectrum.Estimator.eq_2_4_projections mu0).2.2.2.2.1
    have he := congrArg (reindexStarAlgEquiv (Fintype.equivFin (Word n d))) hp
    simp only [map_sum,map_one] at he
    have hproj (mu : QAlgorithms.Schur.Partition d n) :
        reindexStarAlgEquiv (Fintype.equivFin (Word n d)) (QAlgorithms.Schur.isotypicProjector mu) * T = 0 := by
      obtain ⟨s,hs⟩ := shapeOfPartition mu
      have hheight : height s ≤ d := by simpa only [height,hs] using mu.property.2
      have hsm : shapeAt s hheight = mu := Subtype.ext hs
      have hne : s ≠ lam := by intro h; subst s; exact hlam hheight
      have h := finite_projector_intertwiner hn κ lam s hheight T hT
      rw [hsm,if_neg hne] at h
      exact h
    have hmul := congrArg (fun P : Op (Fin (tensorWordDimension n d)) => P*T) he
    simp only [Matrix.sum_mul,hproj,Finset.sum_const_zero,Matrix.one_mul] at hmul
    apply Subtype.ext
    apply (vectorMatrixEquiv (spechtDim lam) (tensorWordDimension n d)).injective
    simpa only [Submodule.coe_zero,map_zero] using hmul.symm
  haveI : Subsingleton (intertwinerVectors (κ.action lam) (finiteTensorPermutationRep n d)) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  exact Module.finrank_zero_of_subsingleton

lemma tensorMultiplicity_eq_weylDim {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) (κ : SpechtModel n)
    (lam : Shape n) :
    intertwinerMultiplicity (κ.action lam) (finiteTensorPermutationRep n d) = weylDim d lam := by
  by_cases h : height lam ≤ d
  · exact tensorMultiplicity_present hn κ lam h
  · rw [tensorMultiplicity_absent hn hd κ lam h]
    simp [weylDim,h]

end RandomDimReduction.Channel

-- PermutationCoordinates
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma exists_multiplicity_coordinates {n b : ℕ} (hn : 0 < n) (κ : SpechtModel n)
    (rB : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin b) ℂ) (q : Shape n → ℕ)
    (hq : ∀ lam, q lam = intertwinerMultiplicity (κ.action lam) rB) :
    ∃ U : Matrix ((lam : Shape n) × (Fin (spechtDim lam) × Fin (q lam))) (Fin b) ℂ,
      U*Uᴴ=1 ∧ Uᴴ*U=1 ∧ ∀ g, U * (rB g : Op (Fin b)) * Uᴴ =
        Matrix.blockDiagonal' (fun lam : Shape n => Matrix.kronecker
          (κ.action lam g : Op (Fin (spechtDim lam))) (1 : Op (Fin (q lam)))) := by
  have he : q = fun lam => intertwinerMultiplicity (κ.action lam) rB := funext hq
  subst q
  refine ⟨(schurSynthesis κ rB)ᴴ,?_,?_,?_⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using schurSynthesis_isometry hn κ rB
  · simpa only [Matrix.conjTranspose_conjTranspose] using schurSynthesis_coisometry hn κ rB
  · intro g
    simpa only [Matrix.conjTranspose_conjTranspose] using schurSynthesis_conjugates hn κ rB g

lemma exists_permutation_coordinates {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) (κ : SpechtModel n) :
    ∃ U : Matrix (SchurIndex n d) (Word n d) ℂ,
      U*Uᴴ=1 ∧ Uᴴ*U=1 ∧ ∀ g, U * QAlgorithms.Schur.tensorPermutation d n g * Uᴴ =
        Matrix.blockDiagonal' (fun lam : Shape n => Matrix.kronecker
          (κ.action lam g : Op (Fin (spechtDim lam))) (1 : Op (Fin (weylDim d lam)))) := by
  obtain ⟨U,hL,hR,hP⟩ := exists_multiplicity_coordinates hn κ (finiteTensorPermutationRep n d)
    (fun lam : Shape n => weylDim d lam) (fun lam => (tensorMultiplicity_eq_weylDim hn hd κ lam).symm)
  let e := Fintype.equivFin (Word n d)
  let V : Matrix (SchurIndex n d) (Word n d) ℂ := Matrix.reindex (Equiv.refl _) e.symm U
  refine ⟨V,?_,?_,?_⟩
  · change Matrix.reindex (Equiv.refl _) e.symm U * (Matrix.reindex (Equiv.refl _) e.symm U)ᴴ = 1
    rw [Matrix.conjTranspose_reindex,reindex_mul,hL,reindex_one]
  · change (Matrix.reindex (Equiv.refl _) e.symm U)ᴴ * Matrix.reindex (Equiv.refl _) e.symm U = 1
    rw [Matrix.conjTranspose_reindex,reindex_mul,hR,reindex_one]
  · intro g
    have hperm : QAlgorithms.Schur.tensorPermutation d n g =
        Matrix.reindex e.symm e.symm (finiteTensorPermutationRep n d g : Op (Fin (tensorWordDimension n d))) := by
      rw [finiteTensorPermutationRep_apply]
      ext i j
      simp [Matrix.reindex_apply,e]
    change Matrix.reindex (Equiv.refl _) e.symm U * QAlgorithms.Schur.tensorPermutation d n g *
      (Matrix.reindex (Equiv.refl _) e.symm U)ᴴ = _
    rw [hperm,Matrix.conjTranspose_reindex,reindex_mul,reindex_mul,hP]
    rfl

end RandomDimReduction.Channel

-- FiniteIntertwiner
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma finite_intertwiner_decomposition {G L a b : Type} [Group G] [Fintype L] [DecidableEq L]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (mA mB dim : L → ℕ)
    (rA : G →* Matrix.unitaryGroup a ℂ) (rB : G →* Matrix.unitaryGroup b ℂ)
    (rho : ∀ l, G →* Matrix.unitaryGroup (Fin (dim l)) ℂ)
    (hirr : ∀ l, Irreducible (rho l))
    (hneq : ∀ l l', l ≠ l' → Inequivalent (rho l) (rho l'))
    (TA : Matrix (RepIndex mA dim) a ℂ) (TB : Matrix (RepIndex mB dim) b ℂ)
    (hLA : TA * TAᴴ = 1) (hRA : TAᴴ * TA = 1)
    (hLB : TB * TBᴴ = 1) (hRB : TBᴴ * TB = 1)
    (hIA : ∀ g, TA * (rA g : Op a) * TAᴴ = Matrix.blockDiagonal'
      (fun l => Matrix.kronecker (1 : Op (Fin (mA l))) (rho l g : Op (Fin (dim l)))))
    (hIB : ∀ g, TB * (rB g : Op b) * TBᴴ = Matrix.blockDiagonal'
      (fun l => Matrix.kronecker (1 : Op (Fin (mB l))) (rho l g : Op (Fin (dim l)))))
    (M : Matrix b a ℂ) (hM : ∀ g, (M * (rA g : Op a) : Matrix b a ℂ) = (rB g : Op b) * M) :
    ∃ B : ∀ l, Matrix (Fin (mB l)) (Fin (mA l)) ℂ,
      TB * M * TAᴴ = Matrix.blockDiagonal' (fun l => Matrix.kronecker (B l) (1 : Op (Fin (dim l)))) := by
  let eA := Fintype.equivFin a
  let eB := Fintype.equivFin b
  let rA' := (reindexUnitaryHom eA).comp rA
  let rB' := (reindexUnitaryHom eB).comp rB
  let DA := finiteRepDecomposition mA dim rA rho TA hLA hRA hIA
  let DB := finiteRepDecomposition mB dim rB rho TB hLB hRB hIB
  let M' := Matrix.reindex eB eA M
  have hM' (g : G) : (M' * (rA' g : Op (Fin (Fintype.card a))) :
      Matrix (Fin (Fintype.card b)) (Fin (Fintype.card a)) ℂ) = (rB' g : Op (Fin (Fintype.card b))) * M' := by
    change Matrix.reindex eB eA M * Matrix.reindex eA eA (rA g : Op a) =
      Matrix.reindex eB eB (rB g : Op b) * Matrix.reindex eB eA M
    rw [reindex_mul, reindex_mul, hM g]
  obtain ⟨B, hB⟩ := lemma_B_2 (Fintype.card a) (Fintype.card b) mA mB dim rA' rB' rho hirr hneq DA DB M' hM'
  refine ⟨B, ?_⟩
  have hh : DB.T * M' * DA.Tᴴ = TB * M * TAᴴ := by
    change Matrix.reindex (Equiv.refl _) eB TB * Matrix.reindex eB eA M *
      (Matrix.reindex (Equiv.refl _) eA TA)ᴴ = _
    rw [Matrix.conjTranspose_reindex, reindex_mul, reindex_mul]
    rfl
  rw [hh] at hB
  exact hB

end RandomDimReduction.Channel

-- SchurSwap
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

def sigmaSwap {L : Type} (a b : L → Type) : (Σ l, a l × b l) ≃ (Σ l, b l × a l) where
  toFun x := ⟨x.1, (x.2.2,x.2.1)⟩
  invFun x := ⟨x.1, (x.2.2,x.2.1)⟩
  left_inv := by rintro ⟨l,x,y⟩; rfl
  right_inv := by rintro ⟨l,x,y⟩; rfl

lemma sigmaSwap_kronecker {L : Type} [DecidableEq L] {a b c d : L → Type}
    (A : ∀ l, Matrix (a l) (c l) ℂ) (B : ∀ l, Matrix (b l) (d l) ℂ) :
    Matrix.reindex (sigmaSwap a b) (sigmaSwap c d)
      (Matrix.blockDiagonal' (fun l => Matrix.kronecker (A l) (B l))) =
      Matrix.blockDiagonal' (fun l => Matrix.kronecker (B l) (A l)) := by
  ext ⟨l,x,y⟩ ⟨m,u,v⟩
  by_cases hlm : l = m
  · subst m
    simp [Matrix.reindex_apply, sigmaSwap, Matrix.blockDiagonal'_apply, Matrix.kronecker, mul_comm]
  · simp [Matrix.reindex_apply, sigmaSwap, Matrix.blockDiagonal'_apply, hlm]

abbrev schurSwap (n d : ℕ) : SchurIndex n d ≃
    RepIndex (fun lam : Shape n => weylDim d lam) (fun lam => spechtDim lam) :=
  sigmaSwap (fun lam => Fin (spechtDim lam)) (fun lam => Fin (weylDim d lam))

def schurAsRepMatrix {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d) :
    Matrix (RepIndex (fun lam : Shape n => weylDim d lam) (fun lam => spechtDim lam)) (Word n d) ℂ :=
  Matrix.reindex (schurSwap n d) (Equiv.refl _) S.U

lemma schurAsRep_left {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d) :
    schurAsRepMatrix S * (schurAsRepMatrix S)ᴴ = 1 := by
  unfold schurAsRepMatrix
  rw [Matrix.conjTranspose_reindex, reindex_mul, S.left_unitary]
  exact reindex_one _

lemma schurAsRep_right {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d) :
    (schurAsRepMatrix S)ᴴ * schurAsRepMatrix S = 1 := by
  unfold schurAsRepMatrix
  rw [Matrix.conjTranspose_reindex, reindex_mul, S.right_unitary]
  exact reindex_one _

lemma schurAsRep_intertwines {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (hsp : ∀ lam : Shape n, 0 < spechtDim lam) (π : Equiv.Perm (Fin n)) :
    schurAsRepMatrix S * (tensorPermutation_rep n d π : Op (Word n d)) * (schurAsRepMatrix S)ᴴ =
      Matrix.blockDiagonal' (fun lam => Matrix.kronecker (1 : Op (Fin (weylDim d lam)))
        (κ.action lam π : Op (Fin (spechtDim lam)))) := by
  change Matrix.reindex (schurSwap n d) (Equiv.refl _) S.U *
    Matrix.reindex (Equiv.refl _) (Equiv.refl _) (QAlgorithms.Schur.tensorPermutation d n π) *
      (Matrix.reindex (schurSwap n d) (Equiv.refl _) S.U)ᴴ = _
  rw [Matrix.conjTranspose_reindex, reindex_mul, reindex_mul,
    schur_intertwines_permutation S hsp]
  exact sigmaSwap_kronecker _ _

end RandomDimReduction.Channel

-- SchurCoordinatesExist
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma schurTransform_of_permutation_coordinates {n d : ℕ} (hn : 0 < n)
    (κ : SpechtModel n) (U : Matrix (SchurIndex n d) (Word n d) ℂ)
    (hL : U*Uᴴ=1) (hR : Uᴴ*U=1)
    (hP : ∀ g, U * QAlgorithms.Schur.tensorPermutation d n g * Uᴴ =
      Matrix.blockDiagonal' (fun lam : Shape n => Matrix.kronecker
        (κ.action lam g : Op (Fin (spechtDim lam))) (1 : Op (Fin (weylDim d lam))))) :
    Nonempty (SchurTransform κ d) := by
  obtain ⟨hirr,hneq⟩ := spechtModel_properties n hn κ
  let T : Matrix (RepIndex (fun lam : Shape n => weylDim d lam) (fun lam : Shape n => spechtDim lam))
      (Word n d) ℂ := Matrix.reindex (schurSwap n d) (Equiv.refl _) U
  have hTL : T*Tᴴ=1 := by
    change Matrix.reindex (schurSwap n d) (Equiv.refl _) U *
      (Matrix.reindex (schurSwap n d) (Equiv.refl _) U)ᴴ = 1
    rw [Matrix.conjTranspose_reindex,reindex_mul,hL,reindex_one]
  have hTR : Tᴴ*T=1 := by
    change (Matrix.reindex (schurSwap n d) (Equiv.refl _) U)ᴴ *
      Matrix.reindex (schurSwap n d) (Equiv.refl _) U = 1
    rw [Matrix.conjTranspose_reindex,reindex_mul,hR,reindex_one]
  have hTI (g : Equiv.Perm (Fin n)) : T * (tensorPermutation_rep n d g : Op (Word n d)) * Tᴴ =
      Matrix.blockDiagonal' (fun lam : Shape n => Matrix.kronecker
        (1 : Op (Fin (weylDim d lam))) (κ.action lam g : Op (Fin (spechtDim lam)))) := by
    change Matrix.reindex (schurSwap n d) (Equiv.refl _) U *
      Matrix.reindex (Equiv.refl _) (Equiv.refl _) (QAlgorithms.Schur.tensorPermutation d n g) *
      (Matrix.reindex (schurSwap n d) (Equiv.refl _) U)ᴴ = _
    rw [Matrix.conjTranspose_reindex,reindex_mul,reindex_mul,hP]
    exact sigmaSwap_kronecker (fun lam : Shape n => (κ.action lam g : Op (Fin (spechtDim lam))))
      (fun lam : Shape n => (1 : Op (Fin (weylDim d lam))))
  have hA (A : Op (Fin d)) : ∃ B : ∀ lam : Shape n, Op (Fin (weylDim d lam)),
      U * tensor n A * Uᴴ = Matrix.blockDiagonal' (fun lam =>
        Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (B lam)) := by
    obtain ⟨B,hB⟩ := finite_intertwiner_decomposition
      (fun lam : Shape n => weylDim d lam) (fun lam : Shape n => weylDim d lam) (fun lam : Shape n => spechtDim lam)
      (tensorPermutation_rep n d) (tensorPermutation_rep n d) κ.action hirr hneq
      T T hTL hTR hTL hTR hTI hTI (tensor n A) (fun g => tensor_perm_natural n d d A g)
    refine ⟨B,?_⟩
    apply (Matrix.reindex (schurSwap n d) (schurSwap n d)).injective
    change Matrix.reindex (schurSwap n d) (Equiv.refl _) U *
      Matrix.reindex (Equiv.refl _) (Equiv.refl _) (tensor n A) *
      (Matrix.reindex (schurSwap n d) (Equiv.refl _) U)ᴴ = _ at hB
    rw [Matrix.conjTranspose_reindex,reindex_mul,reindex_mul] at hB
    rw [hB]
    exact (sigmaSwap_kronecker (fun lam : Shape n => (1 : Op (Fin (spechtDim lam)))) B).symm
  choose B hB using hA
  refine ⟨{ U := U
            left_unitary := hL
            right_unitary := hR
            nu := fun lam A => B A lam
            intertwines := ?_ }⟩
  intro g A
  calc
    _ = (U * QAlgorithms.Schur.tensorPermutation d n g * Uᴴ) * (U * tensor n A * Uᴴ) := by
      symm
      calc
        _ = U * QAlgorithms.Schur.tensorPermutation d n g * (Uᴴ*U) * tensor n A * Uᴴ := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR];simp only [Matrix.mul_one,Matrix.mul_assoc]
    _ = _ := by
      rw [hP,hB,← Matrix.blockDiagonal'_mul]
      congr 1
      funext lam
      simp only [Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]

lemma schurTransform_exists {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) (κ : SpechtModel n) :
    Nonempty (SchurTransform κ d) := by
  obtain ⟨U,hL,hR,hP⟩ := exists_permutation_coordinates hn hd κ
  exact schurTransform_of_permutation_coordinates hn κ U hL hR hP

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ κ : SpechtModel n, ∀ d : ℕ, 1 ≤ d → Nonempty (SchurTransform κ d) := by
  exact ⟨canonicalSpechtModel n,fun d hd => schurTransform_exists hn hd _⟩
