-- Prove2me | solution 1 for RandomDimReduction.Channel.spechtModel_properties
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:37:37.384031+00:00
-- url     : https://prove2.me/submissions/d15cf400-1652-427d-8759-ff4e12d9c5ee

import Definitions.Def_RandomDimReduction_Channel_Schur
import Definitions.Def_RandomDimReduction_Channel_Representations
import Theorems.Thm_KWSpectrum_Estimator_eq_2_4_projections
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise MonoidAlgebra

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

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma spechtDim_pos {n : ℕ} (lam : Shape n) : 0 < spechtDim lam := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hp := (KWSpectrum.Estimator.eq_2_4_projections lam).1
  apply hp
  have hz' : Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lam) = 0 := hz
  simp [QAlgorithms.Schur.isotypicProjector, hz']

lemma specht_char_one {n : ℕ} (κ : SpechtModel n) (lam : Shape n) :
    QAlgorithms.Schur.spechtCharacter lam 1 = (spechtDim lam : ℂ) := by
  rw [← SpechtModel_trace κ lam 1, map_one]
  simp

lemma specht_char_inner {n : ℕ} (κ : SpechtModel n) (lam mu : Shape n) :
    (n.factorial : ℂ)⁻¹ * ∑ g : Equiv.Perm (Fin n),
      QAlgorithms.Schur.spechtCharacter lam g * QAlgorithms.Schur.spechtCharacter mu g⁻¹ =
      if lam = mu then 1 else 0 := by
  have hN : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hl : (spechtDim lam : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (spechtDim_pos lam))
  have hm : (spechtDim mu : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (spechtDim_pos mu))
  by_cases h : lam = mu
  · subst mu
    rw [if_pos rfl]
    have hp := (KWSpectrum.Estimator.eq_2_4_projections lam).2.2.1
    have he := congrArg (fun A : Op (Word n n) => A id id) hp
    rw [isotypic_product_identity_entry, isotypic_identity_entry, specht_char_one κ] at he
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

lemma SpechtModel_irreducible {n : ℕ} (κ : SpechtModel n) (lam : Shape n) :
    Irreducible (κ.action lam) := by
  apply matrix_irreducible_of_end_finrank _ (spechtDim_pos lam)
  haveI : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (by simp [Nat.card_eq_fintype_card])
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (matrixRepresentation (κ.action lam)) (matrixRepresentation (κ.action lam))
  simp only [matrix_character_trace, SpechtModel_trace, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin] at h
  rw [specht_char_inner κ lam lam, if_pos rfl] at h
  exact_mod_cast h.symm

lemma SpechtModel_inequivalent {n : ℕ} (κ : SpechtModel n) (lam mu : Shape n) (hne : lam ≠ mu) :
    Inequivalent (κ.action lam) (κ.action mu) := by
  rintro ⟨T, hT, hT', hcom⟩
  have hchar (g : Equiv.Perm (Fin n)) :
      QAlgorithms.Schur.spechtCharacter lam g = QAlgorithms.Schur.spechtCharacter mu g := by
    rw [← SpechtModel_trace κ lam g, ← SpechtModel_trace κ mu g]
    calc
      _ = (Tᴴ * T * (κ.action lam g : Op (Fin (spechtDim lam)))).trace := by
        rw [hT, Matrix.one_mul]
      _ = (T * (κ.action lam g : Op (Fin (spechtDim lam))) * Tᴴ).trace :=
        (Matrix.trace_mul_cycle _ _ _).symm
      _ = ((κ.action mu g : Op (Fin (spechtDim mu))) * T * Tᴴ).trace := by
        have hc : (T * (κ.action lam g : Op (Fin (spechtDim lam))) :
            Matrix (Fin (spechtDim mu)) (Fin (spechtDim lam)) ℂ) =
            (κ.action mu g : Op (Fin (spechtDim mu))) * T := hcom g
        rw [hc]
      _ = _ := by rw [Matrix.mul_assoc, hT', Matrix.mul_one]
  have he := specht_char_inner κ lam mu
  simp_rw [hchar] at he
  rw [specht_char_inner κ mu mu, if_pos rfl, if_neg hne] at he
  exact one_ne_zero he

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n : ℕ) (hn : 0 < n) (κ : SpechtModel n) :
    (∀ lam : Shape n, Irreducible (κ.action lam)) ∧
    (∀ lam mu : Shape n, lam ≠ mu → Inequivalent (κ.action lam) (κ.action mu)) := by
  exact ⟨SpechtModel_irreducible κ, SpechtModel_inequivalent κ⟩
