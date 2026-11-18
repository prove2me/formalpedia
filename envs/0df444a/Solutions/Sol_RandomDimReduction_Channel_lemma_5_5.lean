-- Prove2me | solution 1 for RandomDimReduction.Channel.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:46:49.789214+00:00
-- url     : https://prove2.me/submissions/9cbf7c4c-51da-44a7-aa57-c7dcc24debd2

import Definitions.Def_RandomDimReduction_Channel_Schur
import Theorems.Thm_RandomDimReduction_Channel_lemma_B_2
import Theorems.Thm_RandomDimReduction_Channel_spechtModel_properties

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

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


end RandomDimReduction.Channel

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

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (κ : SpechtModel n) (Sd : SchurTransform κ d) (Sk : SchurTransform κ k)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) :
    ∃ eta : ∀ lam : Shape n, Matrix (Fin (weylDim d lam)) (Fin (weylDim k lam)) ℂ,
      Sd.U * tensor n W * Sk.Uᴴ =
        Matrix.blockDiagonal' (fun lam => Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam)) ∧
      ∀ lam, (eta lam)ᴴ * eta lam = 1 := by
  obtain ⟨hirr, hneq⟩ := RandomDimReduction.Channel.spechtModel_properties n hn κ
  have hsp (lam : Shape n) : 0 < spechtDim lam := (hirr lam).1
  obtain ⟨eta, heta⟩ := finite_intertwiner_decomposition
    (fun lam : Shape n => weylDim k lam) (fun lam : Shape n => weylDim d lam) (fun lam : Shape n => spechtDim lam)
    (tensorPermutation_rep n k) (tensorPermutation_rep n d) κ.action hirr hneq
    (schurAsRepMatrix Sk) (schurAsRepMatrix Sd)
    (schurAsRep_left Sk) (schurAsRep_right Sk) (schurAsRep_left Sd) (schurAsRep_right Sd)
    (schurAsRep_intertwines Sk hsp) (schurAsRep_intertwines Sd hsp)
    (tensor n W) (fun π => tensor_perm_natural n k d W π)
  have hcore : Sd.U * tensor n W * Sk.Uᴴ =
      Matrix.blockDiagonal' (fun lam => Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam)) := by
    apply (Matrix.reindex (schurSwap n d) (schurSwap n k)).injective
    change Matrix.reindex (schurSwap n d) (Equiv.refl _) Sd.U *
      Matrix.reindex (Equiv.refl _) (Equiv.refl _) (tensor n W) *
      (Matrix.reindex (schurSwap n k) (Equiv.refl _) Sk.U)ᴴ = _ at heta
    rw [Matrix.conjTranspose_reindex, reindex_mul, reindex_mul] at heta
    rw [heta]
    exact (sigmaSwap_kronecker (fun lam : Shape n => (1 : Op (Fin (spechtDim lam)))) eta).symm
  refine ⟨eta, hcore, ?_⟩
  have hdiso : (Sd.U * tensor n W * Sk.Uᴴ)ᴴ * (Sd.U * tensor n W * Sk.Uᴴ) = 1 := by
    calc
      _ = Sk.U * (tensor n W)ᴴ * (Sd.Uᴴ * Sd.U) * tensor n W * Sk.Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Sk.U * ((tensor n W)ᴴ * tensor n W) * Sk.Uᴴ := by
        rw [Sd.right_unitary]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [tensor_isometry n W hW, Matrix.mul_one, Sk.left_unitary]
  rw [hcore, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul] at hdiso
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul] at hdiso
  intro lam
  haveI : NeZero (spechtDim lam) := ⟨Nat.ne_of_gt (hsp lam)⟩
  ext i j
  have he := congrArg (fun A : Op (SchurIndex n k) => A ⟨lam,(0,i)⟩ ⟨lam,(0,j)⟩) hdiso
  simpa [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply] using he
