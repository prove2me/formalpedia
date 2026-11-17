-- Prove2me | solution 1 for ZigZagStrong.ZigZag.random_model_strong_convergence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T07:07:40.837597+00:00
-- url     : https://prove2.me/submissions/33e0faa6-ec81-40b7-a908-78b499b580f0

import Mathlib
import Definitions.Def_DerandSq_NCPoly_eval
import Definitions.Def_StrongConv
import Definitions.Def_DerandSq_leftReg
import Definitions.Def_DerandSq_permOp
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_perpCompress
import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_DerandSq_PM
import Theorems.Thm_DerandSq_theorem_2_14
import Theorems.Thm_ZigZagStrong_ZigZag_involution_strong_convergence

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace ZigZagStrong.ZigZag.Bridge

open scoped InnerProductSpace

section Cj
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Conjugation by a unitary. -/
def cj (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : F →L[ℂ] F :=
  (W : E →L[ℂ] F).comp (T.comp (W.symm : F →L[ℂ] E))

theorem cj_apply (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (x : F) : cj W T x = W (T (W.symm x)) := rfl

theorem cj_mul (W : E ≃ₗᵢ[ℂ] F) (S T : E →L[ℂ] E) : cj W (S * T) = cj W S * cj W T := by
  ext x; simp [cj_apply]

theorem cj_one (W : E ≃ₗᵢ[ℂ] F) : cj W 1 = 1 := by
  ext x; simp [cj_apply]

theorem cj_add (W : E ≃ₗᵢ[ℂ] F) (S T : E →L[ℂ] E) : cj W (S + T) = cj W S + cj W T := by
  ext x; simp [cj_apply]

theorem cj_smul (W : E ≃ₗᵢ[ℂ] F) (c : ℂ) (T : E →L[ℂ] E) : cj W (c • T) = c • cj W T := by
  ext x; simp [cj_apply]

theorem cj_sum {α : Type*} (W : E ≃ₗᵢ[ℂ] F) (s : Finset α) (T : α → E →L[ℂ] E) :
    cj W (∑ a ∈ s, T a) = ∑ a ∈ s, cj W (T a) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext x; simp [cj_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cj_add, ih]

theorem cj_star (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : cj W (star T) = star (cj W T) := by
  simp only [cj, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  rfl

theorem cj_list_prod (W : E ≃ₗᵢ[ℂ] F) (l : List (E →L[ℂ] E)) :
    cj W l.prod = (l.map (cj W)).prod := by
  induction l with
  | nil => exact cj_one W
  | cons a l ih => rw [List.prod_cons, cj_mul, ih, List.map_cons, List.prod_cons]

theorem norm_cj (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : ‖cj W T‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [cj_apply, LinearIsometryEquiv.norm_map]
    calc ‖T (W.symm x)‖ ≤ ‖T‖ * ‖W.symm x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have : T x = W.symm (cj W T (W x)) := by simp [cj_apply]
    rw [this, LinearIsometryEquiv.norm_map]
    calc ‖cj W T (W x)‖ ≤ ‖cj W T‖ * ‖W x‖ := (cj W T).le_opNorm _
      _ = ‖cj W T‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

end Cj

section One
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One copy of `H`. -/
def e1 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    H ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Fin 1 => H) where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => H)).symm.toLinearEquiv
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2]
    simp [PiLp.equivOfUnique]

theorem e1_symm_apply (x : PiLp 2 (fun _ : Fin 1 => H)) : (e1 H).symm x = x 0 := rfl

theorem e1_apply (x : H) (i : Fin 1) : e1 H x i = x := by
  fin_cases i; rfl

theorem tensorOp_one (A : Matrix (Fin 1) (Fin 1) ℂ) (T : H →L[ℂ] H) :
    AccessibleMaps.tensorOp A T = cj (e1 H) (A 0 0 • T) := by
  ext x i
  fin_cases i
  simp [AccessibleMaps.tensorOp, AccessibleMaps.inject, cj_apply, e1_apply, e1_symm_apply]

theorem tensorOp_one' (A : Matrix (Fin 1) (Fin 1) ℂ) (T : H →L[ℂ] H) :
    StrongConv.tensorOp A T = cj (e1 H) (A 0 0 • T) := by
  ext x i
  fin_cases i
  simp [StrongConv.tensorOp, cj_apply, e1_apply, e1_symm_apply]

end One


section Scal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A scalar polynomial (the `(0,0)` entries) evaluated at a tuple. -/
def scal {ι : Type*} (P : DerandSq.NCPoly 1 ι) (u : ι → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ w ∈ P.support, (P w 0 0) • DerandSq.wordOp u w

theorem wordOp_eq {r : ℕ} (u : Fin r → H →L[ℂ] H) (w : FreeMonoid (Fin r ⊕ Fin r)) :
    StrongConv.wordOp u w = DerandSq.wordOp u w := by
  unfold StrongConv.wordOp DerandSq.wordOp
  congr 2
  funext l
  cases l <;> rfl

theorem eval_eq {ι : Type*} (P : DerandSq.NCPoly 1 ι) (u : ι → H →L[ℂ] H) :
    DerandSq.NCPoly.eval P u = cj (e1 H) (scal P u) := by
  rw [DerandSq.NCPoly.eval, scal, cj_sum]
  exact Finset.sum_congr rfl fun w _ => tensorOp_one _ _

theorem seval_eq {r : ℕ} (P : StrongConv.NCPoly 1 r) (u : Fin r → H →L[ℂ] H) :
    StrongConv.NCPoly.eval P u = cj (e1 H) (scal P u) := by
  rw [StrongConv.NCPoly.eval, scal, cj_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [tensorOp_one', wordOp_eq]

theorem norm_seval {r : ℕ} (P : StrongConv.NCPoly 1 r) (u : Fin r → H →L[ℂ] H) :
    ‖StrongConv.NCPoly.eval P u‖ = ‖scal P u‖ := by
  rw [seval_eq, norm_cj]

theorem norm_eval {ι : Type*} (P : DerandSq.NCPoly 1 ι) (u : ι → H →L[ℂ] H) :
    ‖DerandSq.NCPoly.eval P u‖ = ‖scal P u‖ := by
  rw [eval_eq, norm_cj]

theorem wordOp_intertwine {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {ι : Type*} (u : ι → H →L[ℂ] H) (v : ι → F →L[ℂ] F) (K : F →L[ℂ] H)
    (h1 : ∀ i, (u i).comp K = K.comp (v i))
    (h2 : ∀ i, (star (u i)).comp K = K.comp (star (v i))) (w : FreeMonoid (ι ⊕ ι)) :
    (DerandSq.wordOp u w).comp K = K.comp (DerandSq.wordOp v w) := by
  unfold DerandSq.wordOp
  induction w.toList with
  | nil => ext x; simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha : (DerandSq.letterOp u a).comp K = K.comp (DerandSq.letterOp v a) := by
      cases a with
      | inl i => exact h1 i
      | inr i => exact h2 i
    change (DerandSq.letterOp u a).comp ((List.map (DerandSq.letterOp u) l).prod.comp K) =
      K.comp ((DerandSq.letterOp v a).comp (List.map (DerandSq.letterOp v) l).prod)
    rw [ih, ← ContinuousLinearMap.comp_assoc, ha, ContinuousLinearMap.comp_assoc]

theorem scal_intertwine {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {ι : Type*} (P : DerandSq.NCPoly 1 ι) (u : ι → H →L[ℂ] H)
    (v : ι → F →L[ℂ] F) (K : F →L[ℂ] H)
    (h1 : ∀ i, (u i).comp K = K.comp (v i))
    (h2 : ∀ i, (star (u i)).comp K = K.comp (star (v i))) :
    (scal P u).comp K = K.comp (scal P v) := by
  ext x
  simp only [scal, ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  exact congrArg (fun T : F →L[ℂ] H => T x) (wordOp_intertwine u v K h1 h2 w)

theorem scal_cj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {ι : Type*} (P : DerandSq.NCPoly 1 ι) (v : ι → H →L[ℂ] H)
    (W : H ≃ₗᵢ[ℂ] F) : scal P (fun i => cj W (v i)) = cj W (scal P v) := by
  rw [scal, scal, cj_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cj_smul, DerandSq.wordOp, DerandSq.wordOp, cj_list_prod, List.map_map]
  congr 3
  funext l
  cases l with
  | inl i => rfl
  | inr i => exact (cj_star W (v i)).symm

theorem wordOp_map {ι κ : Type*} (e : ι → κ) (u : κ → H →L[ℂ] H) (w : FreeMonoid (ι ⊕ ι)) :
    DerandSq.wordOp u (FreeMonoid.map (Sum.map e e) w) = DerandSq.wordOp (fun i => u (e i)) w := by
  unfold DerandSq.wordOp
  rw [FreeMonoid.toList_map, List.map_map]
  congr 2
  funext l
  cases l <;> rfl

theorem scal_mapDomain {ι κ : Type*} (e : ι → κ) (P : DerandSq.NCPoly 1 ι)
    (u : κ → H →L[ℂ] H) :
    scal (Finsupp.mapDomain (FreeMonoid.map (Sum.map e e)) P) u = scal P (fun i => u (e i)) := by
  have key : ∀ Q : DerandSq.NCPoly 1 κ,
      scal Q u = Q.sum (fun w A => A 0 0 • DerandSq.wordOp u w) := fun Q => rfl
  have key' : ∀ Q : DerandSq.NCPoly 1 ι,
      scal Q (fun i => u (e i)) = Q.sum (fun w A => A 0 0 • DerandSq.wordOp (fun i => u (e i)) w) :=
    fun Q => rfl
  rw [key, key', Finsupp.sum_mapDomain_index]
  · exact Finsupp.sum_congr fun w _ => by rw [wordOp_map]
  · intro w; simp
  · intro w A B; simp [add_smul]

end Scal

section Perp

/-- `1 - J` on `ℂ^N`. -/
def Qn (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ)))

theorem Qn_apply {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    Qn N x i = x i - (N : ℂ)⁻¹ * ∑ j, x j := by
  show (Matrix.toEuclideanCLM (𝕜 := ℂ)
    (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ))) x).ofLp i = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    Matrix.one_apply]

theorem inner_ones {N : ℕ} (y : EuclideanSpace ℂ (Fin N)) :
    ⟪StrongConv.onesVec N, y⟫_ℂ = ∑ j, y j := by
  simp [StrongConv.onesVec, PiLp.inner_apply]

theorem sum_Qn {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : ∑ j, Qn N x j = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Qn_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem Qn_mem {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : Qn N x ∈ StrongConv.OnesPerp N := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_ones, sum_Qn]

theorem Qn_of_mem {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) (hx : x ∈ StrongConv.OnesPerp N) :
    Qn N x = x := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_ones] at hx
  ext i
  rw [Qn_apply, hx, mul_zero, sub_zero]

theorem sub_Qn {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) :
    x - Qn N x = ((N : ℂ)⁻¹ * ∑ j, x j) • StrongConv.onesVec N := by
  ext i
  simp [Qn_apply, StrongConv.onesVec]

theorem norm_Qn_le {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : ‖Qn N x‖ ≤ ‖x‖ := by
  have horth : ⟪Qn N x, x - Qn N x⟫_ℂ = 0 := by
    rw [sub_Qn, inner_smul_right, ← inner_conj_symm, inner_ones, sum_Qn]
    simp
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [add_sub_cancel] at h
  have : ‖Qn N x‖ * ‖Qn N x‖ ≤ ‖x‖ * ‖x‖ := by
    rw [h]; nlinarith [mul_self_nonneg ‖x - Qn N x‖]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this

/-- The projection onto `1^⊥`, as a map into the subspace. -/
def proj (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] StrongConv.OnesPerp N :=
  (Qn N).codRestrict _ Qn_mem

theorem incl_proj (N : ℕ) : (StrongConv.OnesPerp N).subtypeL.comp (proj N) = Qn N := by
  ext x; rfl

theorem proj_incl (N : ℕ) :
    (proj N).comp (StrongConv.OnesPerp N).subtypeL = ContinuousLinearMap.id ℂ _ := by
  ext x : 1
  exact Subtype.ext (Qn_of_mem x.1 x.2)

theorem norm_proj_le (N : ℕ) : ‖proj N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_Qn_le x

theorem norm_incl_le (N : ℕ) : ‖(StrongConv.OnesPerp N).subtypeL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp

theorem permOp_incl {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (DerandSq.permOp σ).comp (StrongConv.OnesPerp N).subtypeL =
      (StrongConv.OnesPerp N).subtypeL.comp (StrongConv.permOpPerp σ) := by
  ext x; rfl

theorem star_permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    star (DerandSq.permOp σ) = DerandSq.permOp σ⁻¹ := by
  have : DerandSq.permOp σ =
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ : _) :
        EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) := rfl
  rw [this, LinearIsometryEquiv.star_eq_symm]
  ext x i
  simp [DerandSq.permOp, LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

theorem star_permOpPerp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    star (StrongConv.permOpPerp σ) = StrongConv.permOpPerp σ⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change ⟪DerandSq.permOp σ⁻¹ x, (y : EuclideanSpace ℂ (Fin N))⟫_ℂ =
    ⟪(x : EuclideanSpace ℂ (Fin N)), DerandSq.permOp σ y⟫_ℂ
  rw [← star_permOp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem norm_perpCompress {ι : Type*} {N : ℕ} (P : DerandSq.NCPoly 1 ι)
    (σ : ι → Equiv.Perm (Fin N)) :
    ‖DerandSq.perpCompress 1 N (DerandSq.NCPoly.eval P (fun i => DerandSq.permOp (σ i)))‖ =
      ‖scal P (fun i => StrongConv.permOpPerp (σ i))‖ := by
  set K := (StrongConv.OnesPerp N).subtypeL
  set S := scal P (fun i => DerandSq.permOp (σ i))
  set S' := scal P (fun i => StrongConv.permOpPerp (σ i))
  have hS : S.comp K = K.comp S' := scal_intertwine P _ _ K (fun i => permOp_incl (σ i))
    (fun i => by rw [star_permOp, star_permOpPerp]; exact permOp_incl _)
  have hpc : DerandSq.perpCompress 1 N (DerandSq.NCPoly.eval P (fun i => DerandSq.permOp (σ i)))
      = cj (e1 _) (K.comp (S'.comp (proj N))) := by
    rw [DerandSq.perpCompress, eval_eq]
    simp only [tensorOp_one, Matrix.one_apply_eq, one_smul]
    change cj _ (Qn N) * (cj _ S * cj _ (Qn N)) = _
    rw [← cj_mul, ← cj_mul]
    congr 1
    rw [← incl_proj]
    ext x : 1
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    have h1 := congrArg (fun T => T (proj N x)) hS
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun T => T (S' (proj N x))) (proj_incl N)
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [h2]
    rfl
  rw [hpc, norm_cj]
  apply le_antisymm
  · calc ‖K.comp (S'.comp (proj N))‖ ≤ ‖K‖ * (‖S'‖ * ‖proj N‖) :=
          (K.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (S'.opNorm_comp_le _)
            (norm_nonneg _))
      _ ≤ 1 * (‖S'‖ * 1) := by
          gcongr
          · exact norm_incl_le N
          · exact norm_proj_le N
      _ = ‖S'‖ := by ring
  · have : S' = (proj N).comp ((K.comp (S'.comp (proj N))).comp K) := by
      ext x : 1
      simp only [ContinuousLinearMap.comp_apply]
      have h2 := congrArg (fun T => T (S' (proj N (K x)))) (proj_incl N)
      have h3 := congrArg (fun T => T x) (proj_incl N)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h2 h3
      rw [h2, h3]
    calc ‖S'‖ = ‖(proj N).comp ((K.comp (S'.comp (proj N))).comp K)‖ := by rw [← this]
      _ ≤ ‖proj N‖ * (‖K.comp (S'.comp (proj N))‖ * ‖K‖) :=
          ((proj N).opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖K.comp (S'.comp (proj N))‖ * 1) := by
          gcongr
          · exact norm_proj_le N
          · exact norm_incl_le N
      _ = _ := by ring

end Perp

section Limit

/-- Transport of `ℓ²` along a bijection. -/
def lpMap {A B : Type*} (e : A ≃ B) : L2 A →ₗ[ℂ] L2 B where
  toFun f := ⟨fun y => f (e.symm y), by
    have hf := lp.memℓp f
    rw [memℓp_gen_iff (by norm_num)] at hf
    change Memℓp (fun y : B => f (e.symm y)) 2
    rw [memℓp_gen_iff (by norm_num)]
    exact e.symm.summable_iff.mpr hf⟩
  map_add' f g := by ext y; rfl
  map_smul' c f := by ext y; rfl

theorem lpMap_apply {A B : Type*} (e : A ≃ B) (f : L2 A) (y : B) : lpMap e f y = f (e.symm y) :=
  rfl

/-- The unitary `ℓ²(A) ≃ ℓ²(B)` induced by a bijection. -/
def lpCongr {A B : Type*} (e : A ≃ B) : L2 A ≃ₗᵢ[ℂ] L2 B where
  toLinearEquiv :=
    { lpMap e with
      invFun := lpMap e.symm
      left_inv := fun f => by ext x; simp [lpMap_apply]
      right_inv := fun f => by ext x; simp [lpMap_apply] }
  norm_map' f := by
    change ‖lpMap e f‖ = ‖f‖
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun x => ‖f x‖ ^ (2 : ENNReal).toReal)

theorem lpCongr_apply {A B : Type*} (e : A ≃ B) (f : L2 A) (y : B) :
    lpCongr e f y = f (e.symm y) := rfl

theorem lpCongr_symm_apply {A B : Type*} (e : A ≃ B) (f : L2 B) (x : A) :
    (lpCongr e).symm f x = f (e x) := by
  change f (e.symm.symm x) = _
  rfl

variable {G : Type*} [Group G]

/-- `F_0 ∗ G → G`. -/
def collapse (G : Type*) [Group G] : Monoid.Coprod (FreeGroup (Fin 0)) G →* G :=
  Monoid.Coprod.lift 1 (MonoidHom.id G)

theorem inr_collapse (x : Monoid.Coprod (FreeGroup (Fin 0)) G) :
    Monoid.Coprod.inr (collapse G x) = x := by
  have h : (Monoid.Coprod.inr : G →* Monoid.Coprod (FreeGroup (Fin 0)) G).comp (collapse G) =
      MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · apply FreeGroup.ext_hom
      intro a
      exact a.elim0
    · ext g
      simp [collapse]
  exact congrArg (fun f => f x) h

theorem collapse_inr (g : G) : collapse G (Monoid.Coprod.inr g) = g := by
  simp [collapse]

/-- `F_0 ∗ G ≃ G` as types. -/
def collapseEquiv (G : Type*) [Group G] : Monoid.Coprod (FreeGroup (Fin 0)) G ≃ G where
  toFun := collapse G
  invFun := Monoid.Coprod.inr
  left_inv := inr_collapse
  right_inv := collapse_inr

theorem cj_leftReg (g : G) :
    cj (lpCongr (collapseEquiv G)) (DerandSq.leftReg (Monoid.Coprod.inr g)) = regularL2 g := by
  ext f y
  rw [cj_apply, lpCongr_apply]
  change ((lpCongr (collapseEquiv G)).symm f) ((Monoid.Coprod.inr g)⁻¹ *
    (collapseEquiv G).symm y) = f ((Equiv.mulLeft g).symm y)
  rw [lpCongr_symm_apply]
  change f (collapse G ((Monoid.Coprod.inr g)⁻¹ * Monoid.Coprod.inr y)) = f (g⁻¹ * y)
  rw [map_mul, map_inv, collapse_inr, collapse_inr]

theorem norm_scal_limit {r : ℕ} (P : DerandSq.NCPoly 1 (Fin r)) :
    ‖scal P (fun j => DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) :
        Monoid.Coprod (FreeGroup (Fin 0)) (DerandSq.Gam r)))‖ =
      ‖scal P (fun j => regularL2 (involutionGenerator j))‖ := by
  rw [← norm_cj (lpCongr (collapseEquiv (DerandSq.Gam r))), ← scal_cj]
  have h : (fun j => cj (lpCongr (collapseEquiv (DerandSq.Gam r)))
      (DerandSq.leftReg (Monoid.Coprod.inr (DerandSq.mGen j) :
        Monoid.Coprod (FreeGroup (Fin 0)) (DerandSq.Gam r)))) =
      fun j => regularL2 (involutionGenerator j) := funext fun j => cj_leftReg _
  rw [h]

end Limit

section Prob

theorem uniformProb_nonneg {Ω : Type*} [Fintype Ω] (A : Ω → Prop) :
    0 ≤ StrongConv.uniformProb A := by
  unfold StrongConv.uniformProb
  positivity

theorem uniformProb_le_coinProb {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω')
    (A : Ω → Prop) (B : Ω' → Prop) (h : ∀ ω, A ω → B (e ω)) :
    StrongConv.uniformProb A ≤ PunctSketch.coinProb B := by
  classical
  unfold StrongConv.uniformProb PunctSketch.coinProb
  rw [Fintype.card_congr e]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card_of_injOn e
    (fun ω hω => by simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hω ⊢; exact h ω hω)
    (fun x _ y _ hxy => e.injective hxy)

/-- Matchings as a pair (no permutations, `r` perfect matchings). -/
def matchEquiv (m r : ℕ) :
    (Fin r → Matching m) ≃ (Fin 0 → Equiv.Perm (Fin m)) × (Fin r → DerandSq.PM m) where
  toFun τ := (fun i => i.elim0, fun j => ⟨(τ j).1, fun x => ⟨(τ j).2.1 x, (τ j).2.2 x⟩⟩)
  invFun p j := ⟨(p.2 j).1, fun x => ((p.2 j).2 x).1, fun x => ((p.2 j).2 x).2⟩
  left_inv τ := rfl
  right_inv p := by
    ext
    · exact (Fin.elim0 ‹_›)
    · rfl

end Prob

end ZigZagStrong.ZigZag.Bridge

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem random_model_strong_convergence_dev (r : ℕ) :
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Equiv.Perm (Fin (n+2))))
    (fun _ σ => StrongConv.sModel σ) (StrongConv.sLimit r) ∧
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Matching (2*(n+1))))
    (fun _ τ i => StrongConv.permOpPerp (τ i).val)
    (fun i => regularL2 (involutionGenerator i)) ∧
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Involution (n+2)))
    (fun _ τ i => StrongConv.permOpPerp (τ i).val)
    (fun i => regularL2 (involutionGenerator i)) := by
  open Bridge in
  refine ⟨?_, ?_, involution_strong_convergence r⟩
  · intro P ε hε
    have h := ((DerandSq.theorem_2_14 1 r 0 ε hε).1 P).comp (tendsto_add_atTop_nat 2)
    refine squeeze_zero (fun n => uniformProb_nonneg _) (fun n => ?_) h
    simp only [Function.comp_apply]
    apply uniformProb_le_coinProb (Equiv.refl _)
    intro σ hσ
    simp only [Set.mem_ofPred_eq] at hσ
    rw [norm_seval, norm_seval] at hσ
    rw [norm_perpCompress, norm_eval]
    exact hσ.le
  · intro P ε hε
    have h := ((DerandSq.theorem_2_14 1 0 r ε hε).2
      (Finsupp.mapDomain (FreeMonoid.map (Sum.map Sum.inr Sum.inr)) P)).comp
      (tendsto_add_atTop_nat 1)
    refine squeeze_zero (fun n => uniformProb_nonneg _) (fun n => ?_) h
    simp only [Function.comp_apply]
    apply uniformProb_le_coinProb (matchEquiv _ r)
    intro τ hτ
    simp only [Set.mem_ofPred_eq] at hτ
    rw [norm_seval, norm_seval] at hτ
    have hu : (Sum.elim (fun i => DerandSq.permOp ((matchEquiv _ r τ).1 i))
        (fun j => DerandSq.permOp ((matchEquiv _ r τ).2 j).1)) =
        fun k => DerandSq.permOp (Sum.elim (matchEquiv (2 * (n + 1)) r τ).1
          (fun j => ((matchEquiv _ r τ).2 j).1) k) := by
      funext k; cases k <;> rfl
    rw [hu, norm_perpCompress, scal_mapDomain, norm_eval, scal_mapDomain]
    simp only [Sum.elim_inr]
    rw [norm_scal_limit]
    exact hτ.le

end ZigZagStrong.ZigZag

open ZigZagStrong.ZigZag in
open Filter MeasureTheory in
open scoped BigOperators Topology in
theorem solution (r : ℕ) :
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Equiv.Perm (Fin (n+2))))
    (fun _ σ => StrongConv.sModel σ) (StrongConv.sLimit r) ∧
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Matching (2*(n+1))))
    (fun _ τ i => StrongConv.permOpPerp (τ i).val)
    (fun i => regularL2 (involutionGenerator i)) ∧
  StrongConvergence (fun n => finiteLaw (Ω := Fin r → Involution (n+2)))
    (fun _ τ i => StrongConv.permOpPerp (τ i).val)
    (fun i => regularL2 (involutionGenerator i)) :=
  ZigZagStrong.ZigZag.random_model_strong_convergence_dev r
