-- Prove2me | solution 1 for WatrousTQI.extreme_unital_qubit_is_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T15:28:33.250856+00:00
-- url     : https://prove2.me/submissions/4c774393-41a7-4620-8560-5af0873059fd

import Definitions.Def_WatrousTQI_UnitalChannels
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Theorems.Thm_WatrousTQI_two_kraus_biunitary_diagonalization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.FinCases
import Theorems.Thm_WatrousTQI_unital_extreme_kraus_criterion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ComplexConjugate ComplexOrder
namespace OwnChoi
open QAlgorithms
abbrev C (dx dy : ℕ) := Matrix (Fin dy × Fin dx) (Fin dy × Fin dx) ℂ
noncomputable def F (dx dy : ℕ) : C dx dy →ₗ[ℝ] Superop (Fin dx) (Fin dy) where
  toFun J X o p := ∑ i, ∑ j, X i j * J (o,i) (p,j)
  map_add' A B := by
    ext X o p
    simp [mul_add,Finset.sum_add_distrib]
  map_smul' a A := by
    ext X o p
    change (∑ i, ∑ j, X i j * (a • A (o,i) (p,j))) = a • (∑ i, ∑ j, X i j * A (o,i) (p,j))
    simp_rw [mul_smul_comm,Finset.smul_sum]
noncomputable def CJ {dx dy m : ℕ} (E : Fin m → Matrix (Fin dy) (Fin dx) ℂ) : C dx dy :=
  ∑ j, Matrix.vecMulVec (fun p => E j p.1 p.2) (star (fun p => E j p.1 p.2))
def TL {dx dy : ℕ} : C dx dy →ₗ[ℝ] Matrix (Fin dx) (Fin dx) ℂ where
  toFun J i j := ∑ o, J (o,i) (o,j)
  map_add' A B := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' a A := by ext i j; simp [Finset.smul_sum]
lemma CJ_pos {dx dy m : ℕ} (E : Fin m → Matrix (Fin dy) (Fin dx) ℂ) : (CJ E).PosSemidef := by
  unfold CJ
  exact Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _)
lemma F_CJ {dx dy m : ℕ} (E : Fin m → Matrix (Fin dy) (Fin dx) ℂ) : F dx dy (CJ E) = krausApply E := by
  ext o p q
  change (∑ i, ∑ j, o i j * (CJ E) (p,i) (q,j)) = _
  simp only [ LinearMap.coe_mk, AddHom.coe_mk, CJ, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, krausApply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
lemma TL_CJ {dx dy m : ℕ} (E : Fin m → Matrix (Fin dy) (Fin dx) ℂ) :
    TL (CJ E) = (∑ l, (E l)ᴴ * E l)ᵀ := by
  ext i j
  simp only [TL, LinearMap.coe_mk, AddHom.coe_mk, CJ, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun o _ => ?_
  ring
lemma CJ_exists {dx dy : ℕ} (J : C dx dy) (hJ : J.PosSemidef) :
    ∃ (m : ℕ) (E : Fin m → Matrix (Fin dy) (Fin dx) ℂ), J = CJ E := by
  obtain ⟨m,v,hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hJ
  refine ⟨m, fun j o i => v j (o,i), ?_⟩
  simpa [CJ] using hv

lemma F_injective (dx dy : ℕ) : Function.Injective (F dx dy) := by
  intro J K h
  ext ⟨o,i⟩ ⟨p,j⟩
  have hh := congrArg (fun f : Superop (Fin dx) (Fin dy) => f (Matrix.single i j 1) o p) h
  simpa [F,Matrix.single_apply,ite_and,eq_comm] using hh
lemma image_channels (dx dy : ℕ) :
    F dx dy '' {J : C dx dy | J.PosSemidef ∧ TL J = 1} = {Φ | IsChannel Φ} := by
  classical
  ext Φ
  constructor
  · rintro ⟨J,⟨hp,ht⟩,rfl⟩
    obtain ⟨m,E,rfl⟩ := CJ_exists J hp
    refine ⟨m,E,?_,?_⟩
    · have h := congrArg Matrix.transpose ht
      simpa [TL_CJ,IsKrausFamily] using h
    · intro X;exact congrFun (F_CJ E) X
  · rintro ⟨m,E,hE,hΦ⟩
    refine ⟨CJ E,⟨CJ_pos E,?_⟩,?_⟩
    · rw [TL_CJ,hE,Matrix.transpose_one]
    · rw [F_CJ];exact (funext hΦ).symm
lemma injective_image_extreme {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (S : Set V) (x : V) : f x ∈ (f '' S).extremePoints ℝ ↔ x ∈ S.extremePoints ℝ := by
  constructor
  · intro h
    have hx : x ∈ S := by
      obtain ⟨y,hy,hxy⟩ := h.1
      exact hf hxy ▸ hy
    refine ⟨hx,?_⟩
    intro y hy z hz hseg
    apply hf
    apply h.2 ⟨y,hy,rfl⟩ ⟨z,hz,rfl⟩
    obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
    exact ⟨a,b,ha,hb,hab,by rw [← map_smul,← map_smul,← map_add,heq]⟩
  · intro h
    refine ⟨⟨x,h.1,rfl⟩,?_⟩
    rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩ hseg
    apply congrArg f
    apply h.2 hy hz
    obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
    exact ⟨a,b,ha,hb,hab,hf (by rw [map_add,map_smul,map_smul];exact heq)⟩
lemma channel_F_iff {dx dy : ℕ} (J : C dx dy) :
    IsChannel (F dx dy J) ↔ J.PosSemidef ∧ TL J = 1 := by
  change F dx dy J ∈ {Φ | IsChannel Φ} ↔ _
  rw [← image_channels]
  constructor
  · rintro ⟨K,hK,hKJ⟩
    exact (F_injective dx dy hKJ) ▸ hK
  · intro h;exact ⟨J,h,rfl⟩
end OwnChoi

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
set_option backward.isDefEq.respectTransparency false
namespace OwnMinimal
lemma psd_independent_vectors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (hJ : J.PosSemidef) :
    ∃ m : ℕ, ∃ v : Fin m → (ι → ℂ),
      LinearIndependent ℂ v ∧ J = ∑ a, Matrix.vecMulVec (v a) (star (v a)) := by
  classical
  let U := hJ.isHermitian.eigenvectorUnitary
  let s : ι → ℝ := fun a => Real.sqrt (hJ.isHermitian.eigenvalues a)
  let W : ι → (ι → ℂ) := fun a => (s a : ℂ) • (U : Matrix ι ι ℂ).col a
  let S := {a : ι // s a ≠ 0}
  have hcols : LinearIndependent ℂ (fun a : S => (U : Matrix ι ι ℂ).col a.1) :=
    (Matrix.linearIndependent_cols_of_isUnit (Unitary.isUnit_coe (U := U))).comp _ Subtype.val_injective
  let w : S → ℂˣ := fun a => Units.mk0 (s a.1 : ℂ) (by exact_mod_cast a.2)
  have hW : LinearIndependent ℂ (fun a : S => W a.1) := by
    convert hcols.units_smul w using 1
    rfl
  have hspectral : J = ∑ a : ι, Matrix.vecMulVec (W a) (star (W a)) := by
    rw [hJ.isHermitian.spectral_theorem]
    ext i j
    change ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun a => (hJ.isHermitian.eigenvalues a : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ) i j = _
    simp only [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.conjTranspose_apply,
      mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
      Matrix.sum_apply,Matrix.vecMulVec_apply,W,Pi.smul_apply,Matrix.col_apply,
      Pi.star_apply,smul_eq_mul,Complex.star_def,map_mul,Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro a _
    have hs : (s a : ℂ) * (s a : ℂ) = (hJ.isHermitian.eigenvalues a : ℂ) := by
      rw [← Complex.ofReal_mul,Real.mul_self_sqrt (hJ.eigenvalues_nonneg a)]
    linear_combination -(U : Matrix ι ι ℂ) i a * (starRingEnd ℂ) ((U : Matrix ι ι ℂ) j a) * hs
  have hsum : ∑ a : ι, Matrix.vecMulVec (W a) (star (W a)) =
      ∑ a : S, Matrix.vecMulVec (W a.1) (star (W a.1)) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun a => s a ≠ 0)]
    have hz : ∑ a : {a : ι // ¬ s a ≠ 0}, Matrix.vecMulVec (W a.1) (star (W a.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have ha : s a.1 = 0 := not_not.mp a.2
      simp [W,ha]
    rw [hz,add_zero]
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S,fun a => W (e a).1,hW.comp e e.injective,?_⟩
  rw [hspectral,hsum]
  exact (Fintype.sum_equiv e _ _ (fun a => rfl)).symm

lemma independent_kraus {dx dy : ℕ} (Φ : QAlgorithms.Superop (Fin dx) (Fin dy))
    (hΦ : QAlgorithms.IsChannel Φ) :
    ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin dy) (Fin dx) ℂ,
      QAlgorithms.IsKrausFamily A ∧ LinearIndependent ℂ A ∧
        ∀ X, Φ X = QAlgorithms.krausApply A X := by
  classical
  obtain ⟨k,E,hE,hrepE⟩ := hΦ
  obtain ⟨m,v,hv,hJ⟩ := psd_independent_vectors (OwnChoi.CJ E) (OwnChoi.CJ_pos E)
  let A : Fin m → Matrix (Fin dy) (Fin dx) ℂ := fun a o i => v a (o,i)
  let vec : Matrix (Fin dy) (Fin dx) ℂ →ₗ[ℂ] (Fin dy × Fin dx → ℂ) :=
    { toFun := fun B p => B p.1 p.2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hA : LinearIndependent ℂ A := LinearIndependent.of_comp vec hv
  have hCJ : OwnChoi.CJ A = OwnChoi.CJ E := by
    rw [hJ]
    rfl
  have hF : OwnChoi.F dx dy (OwnChoi.CJ A) = Φ := by
    rw [hCJ,OwnChoi.F_CJ];exact (funext hrepE).symm
  refine ⟨m,A,?_,hA,?_⟩
  · have ht : OwnChoi.TL (OwnChoi.CJ A) = 1 := by
      rw [hCJ,OwnChoi.TL_CJ,hE,Matrix.transpose_one]
    have h := congrArg Matrix.transpose ht
    simpa only [QAlgorithms.IsKrausFamily,OwnChoi.TL_CJ,Matrix.transpose_transpose,Matrix.transpose_one] using h
  · intro X
    have h := congrFun hF X
    rw [OwnChoi.F_CJ] at h
    exact h.symm
end OwnMinimal

noncomputable section
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace OwnQubit
lemma ul (U : Matrix.unitaryGroup (Fin 2) ℂ) : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * U = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using U.property.1
lemma ur (U : Matrix.unitaryGroup (Fin 2) ℂ) : (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using U.property.2

lemma undo (U V : Matrix.unitaryGroup (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (D : Matrix (Fin 2) (Fin 2) ℂ)
    (h : (V : Matrix (Fin 2) (Fin 2) ℂ) * A * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = D) :
    A = (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * D * (U : Matrix (Fin 2) (Fin 2) ℂ) := by
  have he := congrArg (fun X => (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X * (U : Matrix (Fin 2) (Fin 2) ℂ)) h
  have hl : (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
      ((V : Matrix (Fin 2) (Fin 2) ℂ) * A * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = A := by
    calc
      _ = ((V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * V) * A * ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [ul V,ul U,Matrix.one_mul,Matrix.mul_one]
  exact hl.symm.trans he
lemma products (U V : Matrix.unitaryGroup (Fin 2) ℂ) (x y : Fin 2 → ℂ) :
    let A := (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal x * (U : Matrix (Fin 2) (Fin 2) ℂ)
    let B := (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal y * (U : Matrix (Fin 2) (Fin 2) ℂ)
    (Bᴴ*A,A*Bᴴ) =
      ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal (fun i => x i * star (y i)) * U,
       (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal (fun i => x i * star (y i)) * V) := by
  dsimp only
  have hd1 : (Matrix.diagonal y)ᴴ * Matrix.diagonal x = Matrix.diagonal (fun i => x i * star (y i)) := by
    rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hd2 : Matrix.diagonal x * (Matrix.diagonal y)ᴴ = Matrix.diagonal (fun i => x i * star (y i)) := by
    simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Pi.star_apply]
  apply Prod.ext
  · simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (Matrix.diagonal y)ᴴ *
          ((V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) * Matrix.diagonal x * U := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [ur V,Matrix.mul_one]
        calc
          _ = (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * ((Matrix.diagonal y)ᴴ * Matrix.diagonal x) * U := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hd1]
  · simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal x *
          ((U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) * (Matrix.diagonal y)ᴴ * V := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [ur U,Matrix.mul_one]
        calc
          _ = (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (Matrix.diagonal x * (Matrix.diagonal y)ᴴ) * V := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hd2]
lemma two_dependent (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hTP : (A 0)ᴴ * A 0 + (A 1)ᴴ * A 1 = 1)
    (hU : A 0 * (A 0)ᴴ + A 1 * (A 1)ᴴ = 1) :
    ¬ LinearIndependent ℂ (fun ab : Fin 2 × Fin 2 => ((A ab.2)ᴴ * A ab.1,A ab.1 * (A ab.2)ᴴ)) := by
  classical
  obtain ⟨U,V,x,y,hx,hy⟩ := WatrousTQI.two_kraus_biunitary_diagonalization 2 (by decide) (A 0) (A 1) hTP hU
  let z : Fin 2 → Fin 2 → ℂ := ![x,y]
  have hA (a : Fin 2) : A a = (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal (z a) * U := by
    fin_cases a
    · exact undo U V _ _ hx
    · exact undo U V _ _ hy
  let L : (Fin 2 → ℂ) →ₗ[ℂ] (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :=
    { toFun := fun w => ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal w * U,
        (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Matrix.diagonal w * V)
      map_add' := by
        intro w v
        change (_,_) = (_,_)
        apply Prod.ext <;>
          change _ * Matrix.diagonal (fun i => w i + v i) * _ = _ + _
        all_goals rw [← Matrix.diagonal_add];simp only [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intro c w; simp [Matrix.diagonal_smul,Matrix.mul_smul,Matrix.smul_mul] }
  let c : Fin 2 × Fin 2 → (Fin 2 → ℂ) := fun ab i => z ab.1 i * star (z ab.2 i)
  have he : (fun ab : Fin 2 × Fin 2 => ((A ab.2)ᴴ * A ab.1,A ab.1 * (A ab.2)ᴴ)) = L ∘ c := by
    funext ab
    rw [hA ab.1,hA ab.2]
    exact products U V (z ab.1) (z ab.2)
  intro hLI
  rw [he] at hLI
  have hc := (LinearIndependent.of_comp L hLI).fintype_card_le_finrank
  norm_num at hc
end OwnQubit

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
set_option backward.isDefEq.respectTransparency false
open QAlgorithms

open WatrousTQI

set_option autoImplicit false



theorem solution
    (Φ : QAlgorithms.Superop (Fin 2) (Fin 2))
    (h : Φ ∈ (unitalChannels 2).extremePoints ℝ) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        Φ X = (U : Matrix (Fin 2) (Fin 2) ℂ) * X *
          (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
  classical
  have hΦ : IsChannel Φ := h.1.1
  have hu : Φ (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := h.1.2
  obtain ⟨m,A,hTP,hLI,hrep⟩ := OwnMinimal.independent_kraus Φ hΦ
  have hU : ∑ a, A a * (A a)ᴴ = 1 := by
    have hh := (hrep 1).symm.trans hu
    simpa only [krausApply,Matrix.mul_one] using hh
  have hm : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    subst m
    have he : (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      simpa only [IsKrausFamily,Finset.univ_eq_empty,Finset.sum_empty] using hTP
    exact zero_ne_one he
  have hPair := (WatrousTQI.unital_extreme_kraus_criterion 2 m (by decide) hm Φ hΦ hu A hLI hrep).mp h
  have hcard : m*m ≤ 8 := by
    simpa [Module.finrank_matrix] using hPair.fintype_card_le_finrank
  have hm12 : m = 1 ∨ m = 2 := by
    have hm2 : m ≤ 2 := by nlinarith
    omega
  rcases hm12 with rfl | rfl
  · have hA : (A 0)ᴴ * A 0 = 1 := by simpa [IsKrausFamily] using hTP
    let U : Matrix.unitaryGroup (Fin 2) ℂ :=
      ⟨A 0,(Matrix.mem_unitaryGroup_iff').mpr hA⟩
    refine ⟨U,?_⟩
    intro X
    rw [hrep]
    simp [krausApply,U]
  · have hTP2 : (A 0)ᴴ * A 0 + (A 1)ᴴ * A 1 = 1 := by simpa [IsKrausFamily,Fin.sum_univ_two] using hTP
    have hU2 : A 0 * (A 0)ᴴ + A 1 * (A 1)ᴴ = 1 := by simpa [Fin.sum_univ_two] using hU
    exact (OwnQubit.two_dependent A hTP2 hU2 hPair).elim
