-- Prove2me | solution 1 for SNumbers.approximationNumber_mul_detNumber_le_detNumber_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:40:11.809622+00:00
-- url     : https://prove2.me/submissions/87f7510b-3211-4fb7-8aa0-0a59a53b8ceb

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_detSet_nonempty
public import Theorems.Thm_SNumbers_norm_det_le_detNumber
public import Theorems.Thm_SNumbers_detNumber_nonneg
public import Theorems.Thm_SNumbers_rank_comp_le_of_euclidean
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_Matrix_det_eq_corner_mul_det_submatrix
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_padFin_castLE
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL


section
@[expose] public section
universe u
open ContinuousLinearMap
open scoped Pointwise
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma pow_self_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) ^ n := by
  cases n with
  | zero => norm_num
  | succ m => exact pow_pos (by exact_mod_cast Nat.succ_pos m) _
private lemma growth_ratio_pos (k : ℕ) :
    (0 : ℝ) < (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) :=
  div_pos (pow_self_pos k) (pow_pos (by positivity) _)
private lemma lam_mul_add_mu_mul_le {lam mu a b c : ℝ}
    (hlm : lam ^ 2 + mu ^ 2 = 1) (hc : 0 ≤ c) (hsq : a ^ 2 + b ^ 2 = c ^ 2) :
    lam * a + mu * b ≤ c := by
  have h1 : (lam * a + mu * b) ^ 2 ≤ c ^ 2 := by
    nlinarith [sq_nonneg (lam * b - mu * a)]
  exact le_of_sq_le_sq h1 hc
private lemma clm_apply_eq_sum {k : ℕ} {Z : Type u} [NormedAddCommGroup Z]
    [NormedSpace 𝕜 Z] (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Z)
    (z : EuclideanSpace 𝕜 (Fin k)) :
    F z = ∑ j, z j • F (EuclideanSpace.single j (1 : 𝕜)) := by
  classical
  have hz : ∑ j, z j • EuclideanSpace.single j (1 : 𝕜) = z := by
    simpa using (EuclideanSpace.basisFun (Fin k) 𝕜).sum_repr z
  calc F z = F (∑ j, z j • EuclideanSpace.single j (1 : 𝕜)) := by rw [hz]
    _ = ∑ j, z j • F (EuclideanSpace.single j (1 : 𝕜)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => map_smul F _ _
private lemma coord_apply_eq_sum {k m : ℕ}
    (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin m))
    (z : EuclideanSpace 𝕜 (Fin k)) (i : Fin m) :
    F z i = ∑ j, z j * (F (EuclideanSpace.single j (1 : 𝕜))) i := by
  have h := clm_apply_eq_sum ((innerSL 𝕜 (EuclideanSpace.single i (1 : 𝕜))).comp F) z
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, smul_eq_mul] at h
  exact h
section Border
variable {k : ℕ}
private lemma castLE_succ_eq_castSucc (i : Fin k) :
    Fin.castLE (Nat.le_succ k) i = Fin.castSucc i := rfl
variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)
private lemma borderDom_apply (v : EuclideanSpace 𝕜 (Fin (k + 1))) :
    borderDom A x lam mu v = (lam : 𝕜) • A (projFin (p := 2) (Nat.le_succ k) v) +
      ((mu : 𝕜) * v (Fin.last k)) • x := by
  rw [borderDom, add_apply, smul_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, smul_smul]
private lemma borderDom_single_castSucc (j : Fin k) :
    borderDom A x lam mu (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
      = (lam : 𝕜) • A (EuclideanSpace.single j (1 : 𝕜)) := by
  have hproj : projFin (p := 2) (Nat.le_succ k)
      (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, castLE_succ_eq_castSucc i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  rw [borderDom_apply, hproj, PiLp.single_apply,
    if_neg (Fin.castSucc_lt_last j).ne', mul_zero, zero_smul, add_zero]
private lemma borderDom_single_last :
    borderDom A x lam mu (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = (mu : 𝕜) • x := by
  have hproj : projFin (p := 2) (Nat.le_succ k)
      (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = 0 := by
    ext i
    rw [projFin_apply, PiLp.single_apply, castLE_succ_eq_castSucc i, PiLp.zero_apply,
      if_neg (Fin.castSucc_lt_last i).ne]
  rw [borderDom_apply, hproj, map_zero, smul_zero, zero_add, PiLp.single_apply,
    if_pos rfl, mul_one]
private lemma borderCod_castSucc (y : Y) (i : Fin k) :
    (borderCod B b lam mu y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := by
  rw [borderCod, add_apply, PiLp.add_apply, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply,
    ← castLE_succ_eq_castSucc i, padFin_castLE, PiLp.single_apply,
    if_neg ((Fin.castSucc_lt_last i).ne ∘ (castLE_succ_eq_castSucc i ▸ ·)),
    smul_zero, smul_zero, add_zero, smul_eq_mul]
private lemma borderCod_last (y : Y) :
    (borderCod B b lam mu y) (Fin.last k) = (mu : 𝕜) * b y := by
  rw [borderCod, add_apply, PiLp.add_apply, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply, padFin_apply,
    dif_neg (by simp), smul_zero, zero_add, PiLp.single_apply, if_pos rfl,
    smul_eq_mul, smul_eq_mul, mul_one]
private lemma norm_sq_projFin_add_last (v : EuclideanSpace 𝕜 (Fin (k + 1))) :
    ‖projFin (p := 2) (Nat.le_succ k) v‖ ^ 2 + ‖v (Fin.last k)‖ ^ 2 = ‖v‖ ^ 2 := by
  have h1 : ‖v‖ ^ 2 = ∑ i : Fin (k + 1), ‖v i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have h2 : ‖projFin (p := 2) (Nat.le_succ k) v‖ ^ 2
      = ∑ i : Fin k, ‖v (Fin.castSucc i)‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [projFin_apply, castLE_succ_eq_castSucc i]
  rw [h1, h2, Fin.sum_univ_castSucc]
private lemma norm_borderDom_le (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1) :
    ‖borderDom A x lam mu‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, borderDom_apply]
  have h1 : ‖(lam : 𝕜) • A (projFin (p := 2) (Nat.le_succ k) v)‖
      ≤ lam * ‖projFin (p := 2) (Nat.le_succ k) v‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hlam]
    have := (A.le_opNorm (projFin (p := 2) (Nat.le_succ k) v)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hA)
    exact mul_le_mul_of_nonneg_left this hlam
  have h2 : ‖((mu : 𝕜) * v (Fin.last k)) • x‖ ≤ mu * ‖v (Fin.last k)‖ := by
    rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hmu, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hx) hmu
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  exact lam_mul_add_mu_mul_le hlm (norm_nonneg v) (norm_sq_projFin_add_last v)
private lemma norm_borderCod_le (hB : ‖B‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1) :
    ‖borderCod B b lam mu‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  have hsq : ‖borderCod B b lam mu y‖ ^ 2
      = lam ^ 2 * ‖B y‖ ^ 2 + mu ^ 2 * ‖b y‖ ^ 2 := by
    have h1 : ‖borderCod B b lam mu y‖ ^ 2
        = ∑ i : Fin (k + 1), ‖(borderCod B b lam mu y) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have h2 : ‖B y‖ ^ 2 = ∑ i : Fin k, ‖(B y) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [h1, Fin.sum_univ_castSucc, borderCod_last B b lam mu y]
    have h3 : ∀ i : Fin k, ‖(borderCod B b lam mu y) (Fin.castSucc i)‖ ^ 2
        = lam ^ 2 * ‖(B y) i‖ ^ 2 := by
      intro i
      rw [borderCod_castSucc B b lam mu y i, norm_mul, RCLike.norm_ofReal,
        abs_of_nonneg hlam, mul_pow]
    rw [Finset.sum_congr rfl fun i _ => h3 i, ← Finset.mul_sum, ← h2, norm_mul,
      RCLike.norm_ofReal, abs_of_nonneg hmu, mul_pow]
  have hBy : ‖B y‖ ≤ ‖y‖ :=
    (B.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
  have hby : ‖b y‖ ≤ ‖y‖ :=
    (b.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hb)
  have hsq2 : ‖borderCod B b lam mu y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [hsq]
    have e1 : lam ^ 2 * ‖B y‖ ^ 2 ≤ lam ^ 2 * ‖y‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (B y)) hBy
      nlinarith [sq_nonneg lam]
    have e2 : mu ^ 2 * ‖b y‖ ^ 2 ≤ mu ^ 2 * ‖y‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (b y)) hby
      nlinarith [sq_nonneg mu]
    nlinarith [e1, e2]
  exact le_of_sq_le_sq hsq2 (norm_nonneg _)
end Border
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (k : ℕ) :
    (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) * approximationNumber S k * detNumber S k
      ≤ detNumber S (k + 1) := by
  classical
  set cst : ℝ := (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) with hcst
  have hcst0 : 0 ≤ cst := (growth_ratio_pos k).le
  -- Every admissible value `r` for `Δₖ(S)` satisfies `cst · aₖ(S) · r ≤ Δₖ₊₁(S)`.
  have hkey : ∀ r ∈ detSet S k, cst * approximationNumber S k * r
      ≤ detNumber S (k + 1) := by
    rintro r ⟨A, B, hA, hB, rfl⟩
    set T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
      B.comp (S.comp A) with hTdef
    have hTapp : ∀ z, T z = B (S (A z)) := fun z => by
      rw [hTdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    set rT : ℝ :=
      ‖LinearMap.det (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ with hrT
    -- A singular compression contributes nothing.
    by_cases hdet0 : LinearMap.det
        (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0
    · rw [hrT, hdet0, norm_zero, mul_zero]
      exact detNumber_nonneg S (k + 1)
    -- The rank-`k` approximant `L = S∘A∘T⁻¹∘B∘S`.
    set E := T.toContinuousLinearEquivOfDetNeZero hdet0 with hEdef
    have hEapp : ∀ z, E z = T z := fun z => by
      rw [hEdef]
      exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply T hdet0 z
    set L : X →L[𝕜] Y := (S.comp A).comp
      ((E.symm : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)).comp
        (B.comp S)) with hLdef
    have hLrank : L.rank ≤ (k : Cardinal) := by
      rw [hLdef]
      exact rank_comp_le_of_euclidean _ _
    have hSL : approximationNumber S k ≤ ‖S - L‖ :=
      approximationNumber_le_norm_sub hLrank
    -- The main estimate, for every `η` strictly below `‖S - L‖`.
    have hinner : ∀ η : ℝ, 0 ≤ η → η < ‖S - L‖ →
        cst * η * rT ≤ detNumber S (k + 1) := by
      intro η hη0 hηlt
      obtain ⟨x, hx1, hxη⟩ := (S - L).exists_lt_apply_of_lt_opNorm hηlt
      obtain ⟨b, hb1, hbval⟩ := exists_dual_vector'' 𝕜 ((S - L) x)
      have hbη : η < ‖b ((S - L) x)‖ := by
        rw [hbval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
        exact hxη
      -- The optimal weights.
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      set lam : ℝ := Real.sqrt ((k : ℝ) / ((k : ℝ) + 1)) with hlamdef
      set mu : ℝ := Real.sqrt (1 / ((k : ℝ) + 1)) with hmudef
      have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
      have hmu0 : 0 ≤ mu := Real.sqrt_nonneg _
      have hlam2 : lam ^ 2 = (k : ℝ) / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
      have hmu2 : mu ^ 2 = 1 / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
      have hlm : lam ^ 2 + mu ^ 2 = 1 := by rw [hlam2, hmu2]; field_simp
      have hcval : lam ^ (2 * k) * mu ^ 2 = cst := by
        rw [pow_mul, hlam2, hmu2, div_pow, div_mul_div_comm, mul_one, hcst, pow_succ]
      -- `lam` is positive as soon as `k ≥ 1`.
      have hlampos : 0 < k → (lam : 𝕜) ≠ 0 := by
        intro hkpos
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hpos : 0 < lam := by rw [hlamdef]; exact Real.sqrt_pos.mpr (by positivity)
        simpa only [ne_eq, RCLike.ofReal_eq_zero] using hpos.ne'
      -- The bordered pair and the facts about it proved above.
      set A' := borderDom A x lam mu with hA'def
      set B' := borderCod B b lam mu with hB'def
      have hA'cs : ∀ j : Fin k, A' (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
          = (lam : 𝕜) • A (EuclideanSpace.single j (1 : 𝕜)) := fun j => by
        rw [hA'def]; exact borderDom_single_castSucc A x lam mu j
      have hA'last : A' (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = (mu : 𝕜) • x := by
        rw [hA'def]; exact borderDom_single_last A x lam mu
      have hB'cs : ∀ (y : Y) (i : Fin k),
          (B' y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := fun y i => by
        rw [hB'def]; exact borderCod_castSucc B b lam mu y i
      have hB'last : ∀ y : Y, (B' y) (Fin.last k) = (mu : 𝕜) * b y := fun y => by
        rw [hB'def]; exact borderCod_last B b lam mu y
      have hA'norm : ‖A'‖ ≤ 1 := by
        rw [hA'def]; exact norm_borderDom_le A x lam mu hA hx1.le hlam0 hmu0 hlm
      have hB'norm : ‖B'‖ ≤ 1 := by
        rw [hB'def]; exact norm_borderCod_le B b lam mu hB hb1 hlam0 hmu0 hlm
      -- The matrices of the two compositions in the standard bases.
      set bk := EuclideanSpace.basisFun (Fin k) 𝕜 with hbk
      set bk1 := EuclideanSpace.basisFun (Fin (k + 1)) 𝕜 with hbk1
      set Nmat := LinearMap.toMatrix bk.toBasis bk.toBasis
        (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) with hNmat
      set Mmat := LinearMap.toMatrix bk1.toBasis bk1.toBasis
        (B'.comp (S.comp A') :
          EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))
        with hMmat
      have hMapp : ∀ i j, Mmat i j
          = (B' (S (A' (EuclideanSpace.single j (1 : 𝕜))))) i := by
        intro i j
        rw [hMmat, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, hbk1, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      have hNapp : ∀ i j, Nmat i j
          = (B (S (A (EuclideanSpace.single j (1 : 𝕜))))) i := by
        intro i j
        rw [hNmat, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, hbk, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, hTapp]
      -- The four kinds of entries of the bordered matrix.
      have hMcc : ∀ i j : Fin k, Mmat (Fin.castSucc i) (Fin.castSucc j)
          = (lam : 𝕜) ^ 2 * Nmat i j := by
        intro i j
        rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'cs, hNapp,
          smul_eq_mul]
        ring
      have hMlc : ∀ j : Fin k, Mmat (Fin.last k) (Fin.castSucc j)
          = (lam : 𝕜) * (mu : 𝕜) * b (S (A (EuclideanSpace.single j (1 : 𝕜)))) := by
        intro j
        rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
        ring
      have hMcl : ∀ i : Fin k, Mmat (Fin.castSucc i) (Fin.last k)
          = (lam : 𝕜) * (mu : 𝕜) * (B (S x)) i := by
        intro i
        rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'cs, smul_eq_mul]
        ring
      have hMll : Mmat (Fin.last k) (Fin.last k) = (mu : 𝕜) ^ 2 * b (S x) := by
        rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
        ring
      -- The coefficients realising the last column as a combination of the others.
      set ζ : EuclideanSpace 𝕜 (Fin k) := E.symm (B (S x)) with hζdef
      have hTζ : T ζ = B (S x) := by
        rw [hζdef, ← hEapp, E.apply_symm_apply]
      have hLx : L x = S (A ζ) := by
        rw [hLdef, hζdef]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      have hbdiff : b ((S - L) x) = b (S x) - b (S (A ζ)) := by
        rw [sub_apply, hLx, map_sub]
      set w : Fin k → 𝕜 := fun j => ((mu : 𝕜) / (lam : 𝕜)) * ζ j with hwdef
      -- Above the corner, the last column is the `ζ`-combination of the first `k`.
      have hwrel : ∀ i : Fin k, Mmat i.castSucc (Fin.last k)
          = ∑ j, Mmat i.castSucc j.castSucc * w j := by
        intro i
        have hlamne : (lam : 𝕜) ≠ 0 := hlampos i.pos
        have hcoord : (B (S x)) i
            = ∑ j, ζ j * (B (S (A (EuclideanSpace.single j (1 : 𝕜))))) i := by
          rw [← hTζ]
          simpa only [hTapp] using coord_apply_eq_sum T ζ i
        rw [hMcl i, hcoord, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hMcc i j, hNapp i j, hwdef]
        field_simp
      -- The minor at the corner is `λ²` times the old matrix.
      have hsub : Mmat.submatrix Fin.castSucc Fin.castSucc = ((lam : 𝕜) ^ 2) • Nmat := by
        ext i j
        rw [Matrix.submatrix_apply, hMcc i j, Matrix.smul_apply, smul_eq_mul]
      have hminor : (Mmat.submatrix Fin.castSucc Fin.castSucc).det
          = (lam : 𝕜) ^ (2 * k) * Nmat.det := by
        rw [hsub, Matrix.det_smul, Fintype.card_fin, pow_mul]
      -- The corner entry after the column operation is `μ²·b((S - L)x)`.
      have hcorner : Mmat (Fin.last k) (Fin.last k)
            - ∑ j, Mmat (Fin.last k) j.castSucc * w j
          = (mu : 𝕜) ^ 2 * b ((S - L) x) := by
        rw [hMll, hbdiff, mul_sub]
        congr 1
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · -- `ℓ₂⁰` is trivial, so `Aζ = 0` and both sides vanish.
          have hζ0 : ζ = 0 := PiLp.ext fun j => j.elim0
          simp [hζ0]
        · have hlamne : (lam : 𝕜) ≠ 0 := hlampos hkpos
          have hbSAζ : b (S (A ζ))
              = ∑ j, ζ j * b (S (A (EuclideanSpace.single j (1 : 𝕜)))) := by
            simpa only [ContinuousLinearMap.comp_apply, smul_eq_mul] using
              clm_apply_eq_sum (b.comp (S.comp A)) ζ
          rw [hbSAζ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hMlc j, hwdef]
          field_simp
      -- Hence the determinant identity (∗).
      have hdetM : Mmat.det
          = (lam : 𝕜) ^ (2 * k) * (mu : 𝕜) ^ 2 * b ((S - L) x) * Nmat.det := by
        rw [Matrix.det_eq_corner_mul_det_submatrix Mmat w hwrel, hcorner, hminor]
        ring
      have hnormdet : ‖LinearMap.det (B'.comp (S.comp A') :
            EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖
          = cst * ‖b ((S - L) x)‖ * rT := by
        rw [hrT, ← LinearMap.det_toMatrix bk1.toBasis
            (B'.comp (S.comp A') :
              EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1))),
          ← LinearMap.det_toMatrix bk.toBasis
            (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)),
          ← hMmat, ← hNmat, hdetM, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
          RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg hlam0,
          abs_of_nonneg hmu0, ← hcval]
      calc cst * η * rT
          ≤ cst * ‖b ((S - L) x)‖ * rT := by gcongr
        _ = ‖LinearMap.det (B'.comp (S.comp A') :
              EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖ :=
            hnormdet.symm
        _ ≤ detNumber S (k + 1) := norm_det_le_detNumber S hA'norm hB'norm
    -- Let `η ↗ ‖S - L‖`, which is at least `aₖ(S)`.
    have hrT0 : 0 ≤ rT := by rw [hrT]; exact norm_nonneg _
    have hfin : cst * rT * approximationNumber S k ≤ detNumber S (k + 1) := by
      refine mul_le_of_forall_lt_of_nonneg (by positivity)
        (detNumber_nonneg S (k + 1)) ?_
      intro a' ha'0 ha'lt η hη0 hηlt
      calc a' * η ≤ (cst * rT) * η := by gcongr
        _ = cst * η * rT := by ring
        _ ≤ detNumber S (k + 1) := hinner η hη0 (hηlt.trans_le hSL)
    calc cst * approximationNumber S k * rT
        = cst * rT * approximationNumber S k := by ring
      _ ≤ detNumber S (k + 1) := hfin
  -- Pass to the supremum over the admissible values.
  have hsmul : (cst * approximationNumber S k) • detNumber S k ≤ detNumber S (k + 1) := by
    rw [detNumber,
      ← Real.sSup_smul_of_nonneg (mul_nonneg hcst0 (approximationNumber_nonneg S k))]
    refine csSup_le ((detSet_nonempty S k).smul_set) ?_
    rintro y ⟨r, hr, rfl⟩
    simpa using hkey r hr
  simpa using hsmul
end SNumbers
