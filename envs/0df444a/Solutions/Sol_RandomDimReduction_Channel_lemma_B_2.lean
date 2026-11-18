-- Prove2me | solution 1 for RandomDimReduction.Channel.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:14:00.476825+00:00
-- url     : https://prove2.me/submissions/fa4feb3d-0032-4ad1-bdad-3914adfe3239

import Definitions.Def_RandomDimReduction_Channel_Representations
import Mathlib.RepresentationTheory.Irreducible

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise ENNReal

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

def repBlock {L : Type} {mA mB dim : L → ℕ}
    (D : Matrix (RepIndex mB dim) (RepIndex mA dim) ℂ) (l m : L)
    (u : Fin (mB l)) (v : Fin (mA m)) : Matrix (Fin (dim l)) (Fin (dim m)) ℂ :=
  fun i j => D ⟨l, (u,i)⟩ ⟨m, (v,j)⟩

lemma repBlock_mul_right {L : Type} [Fintype L] [DecidableEq L]
    (mA mB dim : L → ℕ) (R : ∀ l, Op (Fin (dim l)))
    (D : Matrix (RepIndex mB dim) (RepIndex mA dim) ℂ) (l m : L)
    (u : Fin (mB l)) (v : Fin (mA m)) :
    repBlock (D * Matrix.blockDiagonal' (fun t =>
      Matrix.kronecker (1 : Op (Fin (mA t))) (R t))) l m u v = repBlock D l m u v * R m := by
  ext i j
  simp only [repBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single m]
  · simp [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply,
      Fintype.sum_prod_type, ite_mul, mul_ite]
  · intro t _ htm
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htm]
  · simp

lemma repBlock_mul_left {L : Type} [Fintype L] [DecidableEq L]
    (mA mB dim : L → ℕ) (R : ∀ l, Op (Fin (dim l)))
    (D : Matrix (RepIndex mB dim) (RepIndex mA dim) ℂ) (l m : L)
    (u : Fin (mB l)) (v : Fin (mA m)) :
    repBlock (Matrix.blockDiagonal' (fun t =>
      Matrix.kronecker (1 : Op (Fin (mB t))) (R t)) * D) l m u v = R l * repBlock D l m u v := by
  ext i j
  simp only [repBlock, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single l]
  · simp [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply,
      Fintype.sum_prod_type, ite_mul, mul_ite]
  · intro t _ htl
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ htl.symm]
  · simp

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {G L : Type} [Group G] [Fintype L] [DecidableEq L]
    (a b : ℕ) (mA mB dim : L → ℕ)
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (rho : ∀ l, G →* Matrix.unitaryGroup (Fin (dim l)) ℂ)
    (hirr : ∀ l, Irreducible (rho l))
    (hneq : ∀ l l', l ≠ l' → Inequivalent (rho l) (rho l'))
    (TA : RepDecomposition mA dim rA rho) (TB : RepDecomposition mB dim rB rho)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (hM : ∀ g, M * (rA g : Op _) = (rB g : Op _) * M) :
    ∃ B : ∀ l, Matrix (Fin (mB l)) (Fin (mA l)) ℂ,
      TB.T * M * TA.Tᴴ =
        Matrix.blockDiagonal' (fun l => Matrix.kronecker (B l) (1 : Op (Fin (dim l)))) := by
  have hMc (g : G) : (M * (rA g : Op (Fin a)) : Matrix (Fin b) (Fin a) ℂ) = (rB g : Op (Fin b)) * M := hM g
  let D : Matrix (RepIndex mB dim) (RepIndex mA dim) ℂ := TB.T * M * TA.Tᴴ
  have hdiag (g : G) :
      D * Matrix.blockDiagonal' (fun l => Matrix.kronecker (1 : Op (Fin (mA l))) (rho l g : Op (Fin (dim l)))) =
      Matrix.blockDiagonal' (fun l => Matrix.kronecker (1 : Op (Fin (mB l))) (rho l g : Op (Fin (dim l)))) * D := by
    have hTA := TA.intertwines g
    have hTB := TB.intertwines g
    have heq : Classical.decEq L = (inferInstance : DecidableEq L) := Subsingleton.elim _ _
    rw [heq] at hTA hTB
    rw [← hTA, ← hTB]
    calc
      _ = TB.T * M * (TA.Tᴴ * TA.T) * (rA g : Op (Fin a)) * TA.Tᴴ := by
        dsimp [D]
        simp only [Matrix.mul_assoc]
      _ = TB.T * M * (rA g : Op (Fin a)) * TA.Tᴴ := by rw [TA.right_unitary, Matrix.mul_one]
      _ = TB.T * (rB g : Op (Fin b)) * M * TA.Tᴴ := by
        have h := congrArg (fun N : Matrix (Fin b) (Fin a) ℂ => TB.T * N * TA.Tᴴ) (hMc g)
        simpa only [Matrix.mul_assoc] using h
      _ = TB.T * (rB g : Op (Fin b)) * (TB.Tᴴ * TB.T) * M * TA.Tᴴ := by
        rw [TB.right_unitary, Matrix.mul_one]
      _ = _ := by dsimp [D]; simp only [Matrix.mul_assoc]
  have hblock (l m : L) (u : Fin (mB l)) (v : Fin (mA m)) (g : G) :
      (repBlock D l m u v * (rho m g : Op (Fin (dim m))) : Matrix (Fin (dim l)) (Fin (dim m)) ℂ) =
      (rho l g : Op (Fin (dim l))) * repBlock D l m u v := by
    have h := congrArg (fun N : Matrix (RepIndex mB dim) (RepIndex mA dim) ℂ => repBlock N l m u v) (hdiag g)
    simpa only [repBlock_mul_left, repBlock_mul_right] using h
  have hscalar (l : L) (u : Fin (mB l)) (v : Fin (mA l)) :
      ∃ c : ℂ, repBlock D l l u v = c • 1 :=
    matrix_schur_scalar (rho l) (hirr l) (repBlock D l l u v) (hblock l l u v)
  let B : ∀ l, Matrix (Fin (mB l)) (Fin (mA l)) ℂ :=
    fun l u v => Classical.choose (hscalar l u v)
  have hB (l : L) (u : Fin (mB l)) (v : Fin (mA l)) :
      repBlock D l l u v = B l u v • 1 := Classical.choose_spec (hscalar l u v)
  refine ⟨B, ?_⟩
  change D = _
  ext ⟨l, u, i⟩ ⟨m, v, j⟩
  by_cases hlm : l = m
  · subst m
    change repBlock D l l u v i j = _
    rw [hB]
    simp [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.smul_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hlm]
    have hz := intertwiner_zero_of_inequivalent (rho m) (rho l) (hirr m) (hirr l)
      (hneq m l (Ne.symm hlm)) (repBlock D l m u v) (hblock l m u v)
    exact congrArg (fun N : Matrix (Fin (dim l)) (Fin (dim m)) ℂ => N i j) hz
