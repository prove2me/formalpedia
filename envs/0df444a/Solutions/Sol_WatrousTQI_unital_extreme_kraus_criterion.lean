-- Prove2me | solution 1 for WatrousTQI.unital_extreme_kraus_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T15:21:37.07891+00:00
-- url     : https://prove2.me/submissions/4cf7a47a-1f79-42bb-8def-4350389213ab

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_WatrousTQI_UnitalChannels
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Positivity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
namespace OwnPSD
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma supported_factor (A : Matrix (ι) (κ) ℂ) (P : Matrix (ι) (ι) ℂ) :
    (P.PosSemidef ∧ LinearMap.range P.mulVecLin ≤ LinearMap.range A.mulVecLin) ↔
      ∃ Q : Matrix (κ) (κ) ℂ, Q.PosSemidef ∧ P = A * Q * Aᴴ := by
  classical
  constructor
  · rintro ⟨hP,hr⟩
    let f := A.mulVecLin
    obtain ⟨g,hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr f.surjective_rangeRestrict)
    obtain ⟨b,hb⟩ := g.exists_extend
    let B : Matrix (κ) (ι) ℂ := Matrix.toLin'.symm b
    have hB : B.mulVecLin = b := Matrix.toLin'.apply_symm_apply b
    have hs (v : ι → ℂ) (hv : v ∈ LinearMap.range A.mulVecLin) : A.mulVec (B.mulVec v) = v := by
      have he := congrArg (fun h : LinearMap.range f →ₗ[ℂ] LinearMap.range f => h ⟨v,hv⟩) hg
      have he' := congrArg Subtype.val he
      have hb' := congrArg (fun h : LinearMap.range f →ₗ[ℂ] (κ → ℂ) => h ⟨v,hv⟩) hb
      change A.mulVec (g ⟨v,hv⟩) = v at he'
      change b v = g ⟨v,hv⟩ at hb'
      have hBv := congrArg (fun h : (ι → ℂ) →ₗ[ℂ] (κ → ℂ) => h v) hB
      change B.mulVec v = b v at hBv
      rw [hBv,hb']
      exact he'
    have hAP : A * B * P = P := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      change (A * B * P).mulVec v = P.mulVec v
      rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
      exact hs _ (hr ⟨v,rfl⟩)
    have hPA : P * (A * B)ᴴ = P := by
      have h := congrArg Matrix.conjTranspose hAP
      simpa only [Matrix.conjTranspose_mul,hP.isHermitian.eq] using h
    refine ⟨B * P * Bᴴ,hP.mul_mul_conjTranspose_same B,?_⟩
    symm
    calc
      A * (B * P * Bᴴ) * Aᴴ = (A * B * P) * (A * B)ᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = P * (A * B)ᴴ := by rw [hAP]
      _ = P := hPA
  · rintro ⟨Q,hQ,rfl⟩
    refine ⟨hQ.mul_mul_conjTranspose_same A,?_⟩
    rintro v ⟨x,rfl⟩
    refine ⟨(Q * Aᴴ).mulVec x,?_⟩
    change A.mulVec ((Q * Aᴴ).mulVec x) = (A * Q * Aᴴ).mulVec x
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc]

lemma hermitian_range_of_ker (P Q : Matrix (ι) (ι) ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hk : ∀ x, P.mulVec x = 0 → Q.mulVec x = 0) :
    LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin := by
  have he : LinearMap.range Q.toEuclideanLin ≤ LinearMap.range P.toEuclideanLin := by
    rw [← Submodule.orthogonal_le_orthogonal_iff,
      LinearMap.orthogonal_range,LinearMap.orthogonal_range,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hP.eq,hQ.eq]
    intro x hx
    change P.toEuclideanLin x = 0 at hx
    change Q.toEuclideanLin x = 0
    have hx' : P.mulVec (WithLp.ofLp x) = 0 := by
      have := congrArg WithLp.ofLp hx
      simpa using this
    simpa only [Matrix.toEuclideanLin_apply,← WithLp.toLp_zero] using
      congrArg (WithLp.toLp 2) (hk _ hx')
  rintro y ⟨x,rfl⟩
  obtain ⟨z,hz⟩ := he ⟨WithLp.toLp 2 x,rfl⟩
  refine ⟨WithLp.ofLp z,?_⟩
  have h := congrArg WithLp.ofLp hz
  simpa using h
lemma summand_range (P Q₀ Q₁ : Matrix (ι) (ι) ℂ)
    (h₀ : Q₀.PosSemidef) (h₁ : Q₁.PosSemidef)
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hP : P = t • Q₀ + (1-t) • Q₁) :
    LinearMap.range Q₀.mulVecLin ≤ LinearMap.range P.mulVecLin ∧
    LinearMap.range Q₁.mulVecLin ≤ LinearMap.range P.mulVecLin := by
  have hp : P.PosSemidef := hP ▸ (h₀.smul ht₀.le).add (h₁.smul (sub_pos.mpr ht₁).le)
  have hk (x : ι → ℂ) (hx : P.mulVec x = 0) :
      Q₀.mulVec x = 0 ∧ Q₁.mulVec x = 0 := by
    have hz : t • (star x ⬝ᵥ Q₀.mulVec x) + (1-t) • (star x ⬝ᵥ Q₁.mulVec x) = 0 := by
      have := congrArg (fun v => star x ⬝ᵥ v) hx
      rw [hP,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec,
        dotProduct_add,dotProduct_smul,dotProduct_smul,
        dotProduct_zero] at this
      exact this
    have hz₀ : t • (star x ⬝ᵥ Q₀.mulVec x) = 0 := by
      apply le_antisymm _ (smul_nonneg ht₀.le (h₀.dotProduct_mulVec_nonneg x))
      calc
        _ ≤ t • (star x ⬝ᵥ Q₀.mulVec x) + (1-t) • (star x ⬝ᵥ Q₁.mulVec x) :=
          le_add_of_nonneg_right (smul_nonneg (sub_pos.mpr ht₁).le (h₁.dotProduct_mulVec_nonneg x))
        _ = 0 := hz
    have hz₁ : (1-t) • (star x ⬝ᵥ Q₁.mulVec x) = 0 := by
      simpa only [hz₀,zero_add] using hz
    exact ⟨(h₀.dotProduct_mulVec_zero_iff x).mp ((smul_eq_zero.mp hz₀).resolve_left ht₀.ne'),
      (h₁.dotProduct_mulVec_zero_iff x).mp ((smul_eq_zero.mp hz₁).resolve_left (sub_pos.mpr ht₁).ne')⟩
  exact ⟨hermitian_range_of_ker P Q₀ hp.isHermitian h₀.isHermitian (fun x hx => (hk x hx).1),
    hermitian_range_of_ker P Q₁ hp.isHermitian h₁.isHermitian (fun x hx => (hk x hx).2)⟩

lemma positive_perturb (H : Matrix κ κ ℂ) (hH : H.IsHermitian) :
    ∃ e : ℝ, 0 < e ∧ (1 + e • H).PosSemidef ∧ (1 - e • H).PosSemidef := by
  let c : ℝ := ‖H‖ + 1
  have hc : 0 < c := by dsimp [c]; linarith [norm_nonneg H]
  have hself : IsSelfAdjoint H := hH
  have hp : (c • (1 : Matrix κ κ ℂ) + H).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    have h := hself.neg_algebraMap_norm_le_self
    have h' : 0 ≤ (‖H‖ : ℝ) • (1 : Matrix κ κ ℂ) + H := by
      simpa only [Algebra.algebraMap_eq_smul_one,neg_le_iff_add_nonneg'] using h
    have h1 := Matrix.PosSemidef.one (n := κ) (R := ℂ)
    convert add_nonneg h' h1.nonneg using 1 <;> simp [c,add_smul] <;> abel
  have hm : (c • (1 : Matrix κ κ ℂ) - H).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    have h := hself.le_algebraMap_norm_self
    have h' : 0 ≤ (‖H‖ : ℝ) • (1 : Matrix κ κ ℂ) - H := by
      simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mpr h
    have h1 := Matrix.PosSemidef.one (n := κ) (R := ℂ)
    convert add_nonneg h' h1.nonneg using 1 <;> simp [c,add_smul] <;> abel
  refine ⟨c⁻¹,inv_pos.mpr hc,?_,?_⟩
  · have h := hp.smul (inv_pos.mpr hc).le
    simpa only [smul_add,smul_smul,inv_mul_cancel₀ hc.ne',one_smul] using h
  · have h := hm.smul (inv_pos.mpr hc).le
    simpa only [smul_sub,smul_smul,inv_mul_cancel₀ hc.ne',one_smul] using h
def congLin (M : Matrix ι κ ℂ) : Matrix κ κ ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun H := M * H * Mᴴ
  map_add' H K := by simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' a H := by simp [Matrix.mul_smul,Matrix.smul_mul]
lemma cong_injective (M : Matrix ι κ ℂ) (hM : Function.Injective M.mulVecLin) :
    Function.Injective (congLin M) := by
  obtain ⟨b,hb⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hM)
  let B : Matrix κ ι ℂ := Matrix.toLin'.symm b
  have hBM : B * M = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_one]
    exact (congrArg (fun f => f.comp M.mulVecLin) (Matrix.toLin'.apply_symm_apply b)).trans hb
  have hinv (H : Matrix κ κ ℂ) : B * congLin M H * Bᴴ = H := by
    change B * (M * H * Mᴴ) * Bᴴ = H
    calc
      _ = (B*M) * H * (B*M)ᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = H := by rw [hBM,Matrix.one_mul,Matrix.conjTranspose_one,Matrix.mul_one]
  intro H K h
  rw [← hinv H,← hinv K,h]
lemma extreme_criterion {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : Matrix ι κ ℂ) (hM : Function.Injective M.mulVecLin)
    (L : Matrix ι ι ℂ →ₗ[ℝ] V) (b : V) (hb : L (M*Mᴴ) = b) :
    M*Mᴴ ∈ ({P : Matrix ι ι ℂ | P.PosSemidef ∧ L P = b}).extremePoints ℝ ↔
      ∀ H : Matrix κ κ ℂ, H.IsHermitian → L (congLin M H) = 0 → H = 0 := by
  classical
  constructor
  · intro he H hH hLH
    obtain ⟨e,hepos,hp,hm⟩ := positive_perturb H hH
    let P := M*Mᴴ
    let D := e • congLin M H
    have hplus : (P+D).PosSemidef := by
      convert hp.mul_mul_conjTranspose_same M using 1
      simp [P,D,congLin,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]
    have hminus : (P-D).PosSemidef := by
      convert hm.mul_mul_conjTranspose_same M using 1
      simp [P,D,congLin,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
    have heq : P + D = P := he.2 ⟨hplus,by simp [P,D,map_add,map_smul,hLH,hb]⟩
      ⟨hminus,by simp [P,D,map_sub,map_smul,hLH,hb]⟩ (mem_openSegment_add_sub (𝕜 := ℝ) P D)
    have hD : D = 0 := add_left_cancel (heq.trans (add_zero P).symm)
    have hzero : congLin M H = 0 := (smul_eq_zero.mp hD).resolve_left hepos.ne'
    exact cong_injective M hM (hzero.trans (map_zero (congLin M)).symm)
  · intro h
    refine ⟨⟨Matrix.posSemidef_self_mul_conjTranspose M,hb⟩,?_⟩
    intro P hP Q hQ hseg
    obtain ⟨a,c,ha,hc,hac,heq⟩ := hseg
    have hac' : c = 1-a := by linarith
    have ha1 : a < 1 := by linarith
    have hMM : LinearMap.range (M*Mᴴ).mulVecLin ≤ LinearMap.range M.mulVecLin := by
      rintro v ⟨x,rfl⟩
      exact ⟨Mᴴ.mulVec x,Matrix.mulVec_mulVec ..⟩
    have hr := summand_range (M*Mᴴ) P Q hP.1 hQ.1 a ha ha1 (by rw [← hac'];exact heq.symm)
    obtain ⟨R,hR,hPR⟩ := (supported_factor M P).mp ⟨hP.1,hr.1.trans hMM⟩
    have hR0 : R-1 = 0 := by
      apply h (R-1) (hR.isHermitian.sub Matrix.isHermitian_one)
      rw [map_sub,map_sub]
      have hcR : congLin M R = P := hPR.symm
      have hc1 : congLin M 1 = M*Mᴴ := by simp [congLin]
      rw [hcR,hc1,hP.2,hb,sub_self]
    have hR1 : R = 1 := sub_eq_zero.mp hR0
    rw [hPR,hR1,Matrix.mul_one]
end OwnPSD

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

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace OwnCoeff
lemma hermitian_kernel_vector (m : ℕ)
    (S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ))
    (hs : ∀ C ∈ S, Cᴴ ∈ S) (C : Matrix (Fin m) (Fin m) ℂ) (hC : C ∈ S) (hn : C ≠ 0) :
    ∃ H : Matrix (Fin m) (Fin m) ℂ, H.IsHermitian ∧ H ≠ 0 ∧ H ∈ S := by
  have hr : (realPart C : Matrix (Fin m) (Fin m) ℂ) ∈ S := by
    rw [realPart_apply_coe]
    exact S.smul_of_tower_mem _ (S.add_mem hC (hs C hC))
  have hi : (imaginaryPart C : Matrix (Fin m) (Fin m) ℂ) ∈ S := by
    rw [imaginaryPart_apply_coe]
    exact S.smul_mem _ (S.smul_of_tower_mem _ (S.sub_mem hC (hs C hC)))
  by_cases hR : (realPart C : Matrix (Fin m) (Fin m) ℂ) = 0
  · refine ⟨imaginaryPart C,(imaginaryPart C).property,?_,hi⟩
    intro hI
    apply hn
    have hh := realPart_add_I_smul_imaginaryPart C
    rw [hR,hI,smul_zero,add_zero] at hh
    exact hh.symm
  · exact ⟨realPart C,(realPart C).property,hR,hr⟩


variable {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [StarAddMonoid V] [StarModule ℂ V]
def coeffLin (v : Fin m × Fin m → V) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] V where
  toFun H := ∑ a, ∑ b, H a b • v (a,b)
  map_add' C D := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c C := by simp [Finset.smul_sum,smul_smul]
lemma hermitian_criterion (v : Fin m × Fin m → V)
    (hv : ∀ a b, star (v (a,b)) = v (b,a)) :
    LinearIndependent ℂ v ↔
      ∀ H : Matrix (Fin m) (Fin m) ℂ, H.IsHermitian → coeffLin v H = 0 → H = 0 := by
  classical
  constructor
  · intro h H _ hH
    rw [Fintype.linearIndependent_iff] at h
    have hz : ∑ ab, H ab.1 ab.2 • v ab = 0 := by
      simpa only [coeffLin,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_prod_type] using hH
    ext a b
    exact h _ hz (a,b)
  · intro h
    by_contra hn
    rw [Fintype.linearIndependent_iff] at hn
    push_neg at hn
    obtain ⟨c,hc,i,hi⟩ := hn
    let C : Matrix (Fin m) (Fin m) ℂ := fun a b => c (a,b)
    have hC : C ∈ LinearMap.ker (coeffLin v) := by
      change (∑ a, ∑ b, c (a,b) • v (a,b)) = 0
      simpa only [Fintype.sum_prod_type] using hc
    have hs : ∀ D ∈ LinearMap.ker (coeffLin v), Dᴴ ∈ LinearMap.ker (coeffLin v) := by
      intro D hD
      have he := congrArg star (show coeffLin v D = 0 from hD)
      change star (∑ a, ∑ b, D a b • v (a,b)) = star (0 : V) at he
      simp only [star_sum,star_smul,hv,star_zero] at he
      rw [Finset.sum_comm] at he
      change (∑ a, ∑ b, Dᴴ a b • v (a,b)) = 0
      simpa only [Matrix.conjTranspose_apply,Complex.star_def] using he
    have hCn : C ≠ 0 := by
      intro he;apply hi;exact congrFun (congrFun he i.1) i.2
    obtain ⟨H,hH,hHn,hHz⟩ := hermitian_kernel_vector m (LinearMap.ker (coeffLin v)) hs C hC hCn
    exact hHn (h H hH hHz)
end OwnCoeff

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
namespace OwnKraus
open OwnChoi QAlgorithms
variable {dx dy m : ℕ}
def M (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ) : Matrix (Fin dy × Fin dx) (Fin m) ℂ :=
  fun p a => A a p.1 p.2
lemma M_choi (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ) : M A * (M A)ᴴ = CJ A := by
  ext ⟨o,i⟩ ⟨p,j⟩
  simp [M,CJ,Matrix.mul_apply,Matrix.sum_apply,Matrix.vecMulVec_apply,Complex.star_def]
lemma M_injective (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ) (hLI : LinearIndependent ℂ A) :
    Function.Injective (M A).mulVecLin := by
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  change (M A).mulVec x = 0 at hx
  have hs : ∑ a, x a • A a = 0 := by
    ext o i
    have h := congrFun hx (o,i)
    simpa [M,Matrix.mulVec,dotProduct,Matrix.sum_apply,mul_comm] using h
  funext a
  exact (Fintype.linearIndependent_iff.mp hLI) x hs a
lemma TL_cong (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ) (H : Matrix (Fin m) (Fin m) ℂ) :
    TL (OwnPSD.congLin (M A) H) =
      (OwnCoeff.coeffLin (fun ab : Fin m × Fin m => (A ab.2)ᴴ * A ab.1) H)ᵀ := by
  ext i j
  change (∑ o, (M A * H * (M A)ᴴ) (o,i) (o,j)) = _
  simp only [Matrix.mul_apply,M,Matrix.conjTranspose_apply,Complex.star_def,
    OwnCoeff.coeffLin,LinearMap.coe_mk,AddHom.coe_mk,Matrix.transpose_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2,b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun o _ => ?_
  ring
lemma F_cong_one (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ) (H : Matrix (Fin m) (Fin m) ℂ) :
    F dx dy (OwnPSD.congLin (M A) H) 1 =
      OwnCoeff.coeffLin (fun ab : Fin m × Fin m => A ab.1 * (A ab.2)ᴴ) H := by
  ext o p
  change (∑ i, ∑ j, (1 : Matrix (Fin dx) (Fin dx) ℂ) i j *
    (M A * H * (M A)ᴴ) (o,i) (p,j)) = _
  simp only [Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [Matrix.mul_apply,M,Matrix.conjTranspose_apply,Complex.star_def,
    OwnCoeff.coeffLin,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2,b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end OwnKraus

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
open OwnChoi OwnKraus QAlgorithms
namespace OwnUnital
noncomputable def UL (d : ℕ) : C d d →ₗ[ℝ] (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) where
  toFun J := (TL J,F d d J 1)
  map_add' J K := by ext <;> simp [map_add]
  map_smul' a J := by ext <;> simp [map_smul]
lemma image_unital (d : ℕ) :
    F d d '' {J : C d d | J.PosSemidef ∧ UL d J = (1,1)} = WatrousTQI.unitalChannels d := by
  classical
  ext Φ
  constructor
  · rintro ⟨J,⟨hp,hu⟩,rfl⟩
    have he : TL J = 1 ∧ F d d J 1 = 1 := ⟨congrArg Prod.fst hu,congrArg Prod.snd hu⟩
    exact ⟨(channel_F_iff J).mpr ⟨hp,he.1⟩,he.2⟩
  · intro h
    have hc : Φ ∈ {Ψ | IsChannel Ψ} := h.1
    rw [← image_channels] at hc
    obtain ⟨J,hJ,rfl⟩ := hc
    exact ⟨J,⟨hJ.1,Prod.ext hJ.2 h.2⟩,rfl⟩
lemma UL_cong_zero {d m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin m) (Fin m) ℂ) :
    UL d (OwnPSD.congLin (M A) H) = 0 ↔
      OwnCoeff.coeffLin (fun ab : Fin m × Fin m => ((A ab.2)ᴴ * A ab.1,A ab.1 * (A ab.2)ᴴ)) H = 0 := by
  have hp : OwnCoeff.coeffLin (fun ab : Fin m × Fin m => ((A ab.2)ᴴ * A ab.1,A ab.1 * (A ab.2)ᴴ)) H =
      (OwnCoeff.coeffLin (fun ab : Fin m × Fin m => (A ab.2)ᴴ * A ab.1) H,
        OwnCoeff.coeffLin (fun ab : Fin m × Fin m => A ab.1 * (A ab.2)ᴴ) H) := by
    simp only [OwnCoeff.coeffLin,LinearMap.coe_mk,AddHom.coe_mk,Prod.smul_mk,← prod_mk_sum]
  change (TL (OwnPSD.congLin (M A) H),F d d (OwnPSD.congLin (M A) H) 1) = (0,0) ↔ _
  rw [hp]
  change (TL (OwnPSD.congLin (M A) H),F d d (OwnPSD.congLin (M A) H) 1) = (0,0) ↔ (_,_) = (0,0)
  simp only [Prod.mk.injEq,TL_cong,F_cong_one,Matrix.transpose_eq_zero]
end OwnUnital

open WatrousTQI

set_option autoImplicit false



theorem solution (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (Φ : QAlgorithms.Superop (Fin d) (Fin d))
    (hΦ : QAlgorithms.IsChannel Φ)
    (hu : Φ (1 : Matrix (Fin d) (Fin d) ℂ) = 1)
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hLI : LinearIndependent ℂ A)
    (hrep : ∀ X, Φ X = QAlgorithms.krausApply A X) :
    Φ ∈ (unitalChannels d).extremePoints ℝ ↔
      LinearIndependent ℂ (fun ab : Fin m × Fin m =>
        ((A ab.2)ᴴ * A ab.1, A ab.1 * (A ab.2)ᴴ)) := by
  have hFP : F d d (M A * (M A)ᴴ) = Φ := by
    rw [M_choi,F_CJ];exact (funext hrep).symm
  have hfeas : (M A * (M A)ᴴ).PosSemidef ∧ TL (M A * (M A)ᴴ) = 1 :=
    channel_F_iff _ |>.mp (hFP.symm ▸ hΦ)
  have hUL : OwnUnital.UL d (M A * (M A)ᴴ) = (1,1) :=
    Prod.ext hfeas.2 (by change F d d (M A * (M A)ᴴ) 1 = 1;rw [hFP];exact hu)
  rw [← hFP,← OwnUnital.image_unital,injective_image_extreme (F d d) (F_injective d d)]
  rw [OwnPSD.extreme_criterion (M A) (M_injective A hLI) (OwnUnital.UL d) (1,1) hUL]
  rw [OwnCoeff.hermitian_criterion _ (by
    intro a b
    apply Prod.ext <;> change (_ * _)ᴴ = _
    · simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    · simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose])]
  exact ⟨fun h H hH h0 => h H hH ((OwnUnital.UL_cong_zero A H).mpr h0),
    fun h H hH h0 => h H hH ((OwnUnital.UL_cong_zero A H).mp h0)⟩
