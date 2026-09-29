-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.levelModule_unique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d6cf9697-3091-5532-932d-d7099552593e

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelModule_unique
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace LevModUnique

section FieldPart
variable {F : Type*} [Field F]

open Matrix

def cross (v w : Fin 2 → F) : F := v 0 * w 1 - v 1 * w 0

def colMat (v w : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => ![v, w] j i

theorem det_colMat (v w : Fin 2 → F) : (colMat v w).det = cross v w := by
  simp [Matrix.det_fin_two, colMat, cross]
  ring

theorem mul_colMat (X : Matrix (Fin 2) (Fin 2) F) (v w : Fin 2 → F) :
    X * colMat v w = colMat (X *ᵥ v) (X *ᵥ w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [colMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem vecMulVec_mulVec' (u g x : Fin 2 → F) :
    Matrix.vecMulVec u g *ᵥ x = (g ⬝ᵥ x) • u := by
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_two]
  ring

theorem eq_of_mulVec_eq {v w : Fin 2 → F} (h : cross v w ≠ 0) {X Y : Matrix (Fin 2) (Fin 2) F}
    (hv : X *ᵥ v = Y *ᵥ v) (hw : X *ᵥ w = Y *ᵥ w) : X = Y := by
  have hP : IsUnit (colMat v w).det := by
    rw [det_colMat]; exact isUnit_iff_ne_zero.mpr h
  have h0 : (X - Y) * colMat v w = 0 := by
    rw [mul_colMat, Matrix.sub_mulVec, Matrix.sub_mulVec, hv, hw, sub_self, sub_self]
    ext i j
    fin_cases j <;> simp [colMat]
  have : X - Y = 0 := by
    rw [← Matrix.mul_nonsing_inv_cancel_right (colMat v w) (X - Y) hP, h0, zero_mul]
  exact sub_eq_zero.mp this

theorem exists_smul_of_cross_eq_zero {v w : Fin 2 → F} (hv : v ≠ 0) (h : cross v w = 0) :
    ∃ c : F, w = c • v := by
  simp only [cross] at h
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; ext i; fin_cases i <;> simp [h0, h1]
    have hw0 : w 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    refine ⟨w 1 / v 1, ?_⟩
    ext i; fin_cases i
    · simp [h0, hw0]
    · simp [div_mul_cancel₀ _ h1]
  · refine ⟨w 0 / v 0, ?_⟩
    ext i; fin_cases i
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
      field_simp
      linear_combination h

theorem exists_mulVec_ne_zero {A : Matrix (Fin 2) (Fin 2) F} (hA : A ≠ 0) : ∃ w : Fin 2 → F, A *ᵥ w ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hA
  have : Matrix.toLin' A = 0 := LinearMap.ext fun w => by simpa using h w
  simpa using this

theorem exists_dotProduct_eq_one {u : Fin 2 → F} (hu : u ≠ 0) : ∃ g : Fin 2 → F, g ⬝ᵥ u = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.mp hu
  exact ⟨Pi.single i (u i)⁻¹, by simp [hi]⟩

def ann (v : Fin 2 → F) : Set (Matrix (Fin 2) (Fin 2) F) := {A | A *ᵥ v = 0}

def rstab (I : Set (Matrix (Fin 2) (Fin 2) F)) : Set (Matrix (Fin 2) (Fin 2) F) :=
  {x | ∀ A ∈ I, A * x ∈ I}

theorem mem_ann {v : Fin 2 → F} {A : Matrix (Fin 2) (Fin 2) F} : A ∈ ann v ↔ A *ᵥ v = 0 := Iff.rfl

theorem vecMulVec_mem_rstab_ann (v g : Fin 2 → F) : Matrix.vecMulVec v g ∈ rstab (ann v) := by
  intro A hA
  rw [mem_ann] at hA ⊢
  rw [← Matrix.mulVec_mulVec, vecMulVec_mulVec', Matrix.mulVec_smul, hA, smul_zero]

theorem ann_subset_of_vecMulVec_mem_rstab {v w g : Fin 2 → F} (hg : g ⬝ᵥ w ≠ 0)
    (h : Matrix.vecMulVec v g ∈ rstab (ann w)) : ann w ⊆ ann v := by
  intro A hA
  have := h A hA
  rw [mem_ann] at hA this ⊢
  rw [← Matrix.mulVec_mulVec, vecMulVec_mulVec', Matrix.mulVec_smul] at this
  exact (smul_eq_zero.mp this).resolve_left hg

theorem ann_eq_of_rstab_eq {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : rstab (ann v) = rstab (ann w)) : ann v = ann w := by
  obtain ⟨gv, hgv⟩ := exists_dotProduct_eq_one hv
  obtain ⟨gw, hgw⟩ := exists_dotProduct_eq_one hw
  refine Set.Subset.antisymm ?_ ?_
  · exact ann_subset_of_vecMulVec_mem_rstab (by rw [hgv]; exact one_ne_zero) (h ▸ vecMulVec_mem_rstab_ann w gv)
  · exact ann_subset_of_vecMulVec_mem_rstab (by rw [hgw]; exact one_ne_zero) (h.symm ▸ vecMulVec_mem_rstab_ann v gw)

theorem exists_eq_ann (I : Set (Matrix (Fin 2) (Fin 2) F))
    (hadd : ∀ A B, A ∈ I → B ∈ I → A + B ∈ I) (hmul : ∀ (C A : Matrix (Fin 2) (Fin 2) F), A ∈ I → C * A ∈ I)
    (hne : ∃ A ∈ I, A ≠ 0) (hpr : ∃ B, B ∉ I) : ∃ v : Fin 2 → F, v ≠ 0 ∧ I = ann v := by
  classical
  have hdet : ∀ A ∈ I, A.det = 0 := by
    intro A hA
    by_contra hd
    obtain ⟨B, hB⟩ := hpr
    apply hB
    have e : B * A⁻¹ * A = B := Matrix.nonsing_inv_mul_cancel_right A B (isUnit_iff_ne_zero.mpr hd)
    exact e ▸ hmul (B * A⁻¹) A hA
  obtain ⟨A₀, hA₀I, hA₀⟩ := hne
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (hdet A₀ hA₀I)
  obtain ⟨w, hw⟩ := exists_mulVec_ne_zero hA₀
  have hcr : cross v w ≠ 0 := by
    intro hc
    obtain ⟨c, rfl⟩ := exists_smul_of_cross_eq_zero hv hc
    rw [Matrix.mulVec_smul, hAv, smul_zero] at hw
    exact hw rfl
  obtain ⟨g₁, hg₁⟩ := exists_dotProduct_eq_one hw
  refine ⟨v, hv, Set.Subset.antisymm ?_ ?_⟩
  · intro B hB
    rw [mem_ann]
    by_contra hBv
    obtain ⟨g₂, hg₂⟩ := exists_dotProduct_eq_one hBv
    have hE : Matrix.vecMulVec (w - (g₂ ⬝ᵥ (B *ᵥ w)) • v) g₁ * A₀ + Matrix.vecMulVec v g₂ * B ∈ I :=
      hadd _ _ (hmul _ _ hA₀I) (hmul _ _ hB)
    have hE1 : Matrix.vecMulVec (w - (g₂ ⬝ᵥ (B *ᵥ w)) • v) g₁ * A₀ + Matrix.vecMulVec v g₂ * B = 1 := by
      refine eq_of_mulVec_eq hcr ?_ ?_
      · rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero,
          zero_add, vecMulVec_mulVec', hg₂, one_smul, Matrix.one_mulVec]
      · rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec', hg₁, one_smul,
          vecMulVec_mulVec', Matrix.one_mulVec, sub_add_cancel]
    obtain ⟨B', hB'⟩ := hpr
    have hB'I := hmul B' _ hE
    rw [hE1, mul_one] at hB'I
    exact hB' hB'I
  · intro B hB
    rw [mem_ann] at hB
    have : B = Matrix.vecMulVec (B *ᵥ w) g₁ * A₀ := by
      refine eq_of_mulVec_eq hcr ?_ ?_
      · rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero, hB]
      · rw [← Matrix.mulVec_mulVec, vecMulVec_mulVec', hg₁, one_smul]
    rw [this]
    exact hmul _ _ hA₀I

theorem leftIdeal_eq_of_rstab_eq (I I' : Set (Matrix (Fin 2) (Fin 2) F))
    (hadd : ∀ A B, A ∈ I → B ∈ I → A + B ∈ I) (hmul : ∀ (C A : Matrix (Fin 2) (Fin 2) F), A ∈ I → C * A ∈ I)
    (hne : ∃ A ∈ I, A ≠ 0) (hpr : ∃ B, B ∉ I)
    (hadd' : ∀ A B, A ∈ I' → B ∈ I' → A + B ∈ I') (hmul' : ∀ (C A : Matrix (Fin 2) (Fin 2) F), A ∈ I' → C * A ∈ I')
    (hne' : ∃ A ∈ I', A ≠ 0) (hpr' : ∃ B, B ∉ I')
    (h : rstab I = rstab I') : I = I' := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_ann I hadd hmul hne hpr
  obtain ⟨w, hw, rfl⟩ := exists_eq_ann I' hadd' hmul' hne' hpr'
  exact ann_eq_of_rstab_eq hv hw h

end FieldPart

end LevModUnique

namespace LevModUnique

section Frame

open scoped Quaternion
open QuaternionAlgebra

variable {a b : ℚ}

theorem natCast_rat_smul_eq (n : ℕ) (y : ℍ[ℚ, a, b]) : (n : ℚ) • y = (n : ℤ) • y := by
  rw [← Int.cast_smul_eq_zsmul ℚ (n : ℤ) y, Int.cast_natCast]

theorem intCast_rat_smul_eq (n : ℤ) (y : ℍ[ℚ, a, b]) : (n : ℚ) • y = n • y :=
  Int.cast_smul_eq_zsmul ℚ n y

structure PhiData (Λ : Submodule ℤ ℍ[ℚ, a, b]) (p : ℕ) where
  φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p)
  one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1
  mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y
  surj : Function.Surjective φ
  ker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (p : ℚ) • (y : ℍ[ℚ, a, b])

structure IsLev (Λ R J : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) : Prop where
  le : Λ ≤ J
  left : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J
  tors : ∀ y ∈ J, ((N : ℤ) • y) ∈ Λ
  index : Λ.toAddSubgroup.relIndex J.toAddSubgroup = N ^ 2
  stab : ∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J, y * x ∈ J

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ}

def Ip (D : PhiData Λ p) (J : Submodule ℤ ℍ[ℚ, a, b]) : Set (Matrix (Fin 2) (Fin 2) (ZMod p)) :=
  {m | ∃ y ∈ J, ∃ h : ((p : ℚ) • y) ∈ Λ, D.φ ⟨(p : ℚ) • y, h⟩ = m}

theorem PhiData.sub_mem (D : PhiData Λ p) (hp : p ≠ 0) {y y' : ℍ[ℚ, a, b]}
    (h : (p : ℚ) • y ∈ Λ) (h' : (p : ℚ) • y' ∈ Λ) (he : D.φ ⟨_, h⟩ = D.φ ⟨_, h'⟩) : y - y' ∈ Λ := by
  have h0 : D.φ (⟨(p : ℚ) • y, h⟩ - ⟨(p : ℚ) • y', h'⟩) = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨z, hz⟩ := (D.ker _).mp h0
  have hz' : (p : ℚ) • (y - y') = (p : ℚ) • (z : ℍ[ℚ, a, b]) := by
    rw [← hz, Submodule.coe_sub, smul_sub]
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have := smul_right_injective ℍ[ℚ, a, b] hpq hz'
  rw [this]; exact z.2

theorem PhiData.eq_zero_of_mem (D : PhiData Λ p) {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (h : (p : ℚ) • z ∈ Λ) :
    D.φ ⟨(p : ℚ) • z, h⟩ = 0 :=
  (D.ker _).mpr ⟨⟨z, hz⟩, rfl⟩

theorem PhiData.mem_of_eq_zero (D : PhiData Λ p) (hp : p ≠ 0) {y : ℍ[ℚ, a, b]} (h : (p : ℚ) • y ∈ Λ)
    (h0 : D.φ ⟨(p : ℚ) • y, h⟩ = 0) : y ∈ Λ := by
  obtain ⟨z, hz⟩ := (D.ker _).mp h0
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have := smul_right_injective ℍ[ℚ, a, b] hpq (hz : (p : ℚ) • y = (p : ℚ) • (z : ℍ[ℚ, a, b]))
  rw [this]; exact z.2

section perPrime

variable {R J : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem natCast_smul_mem_of_mem (J : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ) {y : ℍ[ℚ, a, b]} (hy : y ∈ J) :
    (n : ℚ) • y ∈ J := by
  rw [natCast_rat_smul_eq]; exact J.smul_mem _ hy

theorem intCast_smul_mem_of_mem (J : Submodule ℤ ℍ[ℚ, a, b]) (n : ℤ) {y : ℍ[ℚ, a, b]} (hy : y ∈ J) :
    (n : ℚ) • y ∈ J := by
  rw [intCast_rat_smul_eq]; exact J.smul_mem _ hy

theorem mem_Ip_iff (D : PhiData Λ p) (hp : p ≠ 0) (hJ : IsLev Λ R J N) {y : ℍ[ℚ, a, b]}
    (h : (p : ℚ) • y ∈ Λ) : D.φ ⟨(p : ℚ) • y, h⟩ ∈ Ip D J ↔ y ∈ J := by
  constructor
  · rintro ⟨y', hy', h', he⟩
    have := D.sub_mem hp h h' he.symm
    have : y = (y - y') + y' := by abel
    rw [this]
    exact add_mem (hJ.le (D.sub_mem hp h h' he.symm)) hy'
  · intro hy; exact ⟨y, hy, h, rfl⟩

theorem Ip_add (D : PhiData Λ p) {A B : Matrix (Fin 2) (Fin 2) (ZMod p)} (hA : A ∈ Ip D J) (hB : B ∈ Ip D J) :
    A + B ∈ Ip D J := by
  obtain ⟨y, hy, h, rfl⟩ := hA
  obtain ⟨y', hy', h', rfl⟩ := hB
  refine ⟨y + y', add_mem hy hy', by rw [smul_add]; exact add_mem h h', ?_⟩
  rw [← map_add]
  congr 1
  apply Subtype.ext
  simp [smul_add]

theorem Ip_mul (hΛ : IsOrder Λ) (D : PhiData Λ p) (hJ : IsLev Λ R J N)
    (C : Matrix (Fin 2) (Fin 2) (ZMod p)) {A : Matrix (Fin 2) (Fin 2) (ZMod p)} (hA : A ∈ Ip D J) :
    C * A ∈ Ip D J := by
  obtain ⟨y, hy, h, rfl⟩ := hA
  obtain ⟨x, rfl⟩ := D.surj C
  have hm : (x : ℍ[ℚ, a, b]) * ((p : ℚ) • y) ∈ Λ := hΛ.mul_mem x.2 h
  have hm' : (p : ℚ) • ((x : ℍ[ℚ, a, b]) * y) ∈ Λ := by rwa [mul_smul_comm] at hm
  refine ⟨(x : ℍ[ℚ, a, b]) * y, hJ.left _ x.2 _ hy, hm', ?_⟩
  rw [← D.mul x ⟨_, h⟩ hm]
  congr 1
  apply Subtype.ext
  simp

theorem Ip_ne_univ (D : PhiData Λ p) (hp : p.Prime) (hN : Squarefree N)
    (hJ : IsLev Λ R J N) : ∃ B, B ∉ Ip D J := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  haveI : Fact p.Prime := ⟨hp⟩

  let K : Submodule ℤ ℍ[ℚ, a, b] :=
    { carrier := {y | (p : ℚ) • y ∈ Λ}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq, smul_add] at hx hy ⊢
        exact add_mem hx hy
      zero_mem' := by simp
      smul_mem' := by
        intro n x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [← Int.cast_smul_eq_zsmul ℚ n, smul_smul, mul_comm, ← smul_smul]
        exact intCast_smul_mem_of_mem Λ n hx }
  have hmemK : ∀ y : ℍ[ℚ, a, b], y ∈ K ↔ (p : ℚ) • y ∈ Λ := fun y => Iff.rfl
  have hΛK : Λ ≤ K := fun y hy => (hmemK y).mpr (natCast_smul_mem_of_mem Λ p hy)
  have hKJ : K ≤ J := by
    intro y hy
    rw [hmemK] at hy
    exact (mem_Ip_iff D hp.ne_zero hJ hy).mp (hall _)

  let f : ↥K →+ Matrix (Fin 2) (Fin 2) (ZMod p) :=
    { toFun := fun y => D.φ ⟨(p : ℚ) • (y : ℍ[ℚ, a, b]), y.2⟩
      map_zero' := by
        have : (⟨(p : ℚ) • ((0 : ↥K) : ℍ[ℚ, a, b]), (0 : ↥K).2⟩ : ↥Λ) = 0 := Subtype.ext (by simp)
        simp only [this, map_zero]
      map_add' := by
        intro x y
        rw [← map_add]
        congr 1
        apply Subtype.ext
        simp [smul_add] }
  have hf_surj : Function.Surjective f := by
    intro m
    obtain ⟨x, rfl⟩ := D.surj m
    have hxK : (p : ℚ)⁻¹ • (x : ℍ[ℚ, a, b]) ∈ K := by
      rw [hmemK, smul_inv_smul₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]; exact x.2
    refine ⟨⟨_, hxK⟩, ?_⟩
    show D.φ ⟨(p : ℚ) • ((p : ℚ)⁻¹ • (x : ℍ[ℚ, a, b])), _⟩ = D.φ x
    congr 1
    apply Subtype.ext
    simp [smul_inv_smul₀ (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℚ) ≠ 0)]
  have hf_ker : f.ker = Λ.toAddSubgroup.addSubgroupOf K.toAddSubgroup := by
    ext y
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h0
      exact D.mem_of_eq_zero hp.ne_zero y.2 h0
    · intro hy
      exact D.eq_zero_of_mem hy y.2
  have hidx : Λ.toAddSubgroup.relIndex K.toAddSubgroup = p ^ 4 := by
    rw [AddSubgroup.relIndex, ← hf_ker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ hf_surj,
      AddSubgroup.card_top]
    rw [show Matrix (Fin 2) (Fin 2) (ZMod p) = (Fin 2 → Fin 2 → ZMod p) from rfl, Nat.card_fun, Nat.card_fun]
    simp [Nat.card_eq_fintype_card, ZMod.card]
    ring
  have hmul := AddSubgroup.relIndex_mul_relIndex Λ.toAddSubgroup K.toAddSubgroup J.toAddSubgroup hΛK hKJ
  rw [hidx, hJ.index] at hmul
  have h4 : p ^ 4 ∣ N ^ 2 := ⟨_, hmul.symm⟩
  have h2 : p ^ 2 ∣ N := by
    rw [show p ^ 4 = (p ^ 2) ^ 2 by ring] at h4
    exact (Nat.pow_dvd_pow_iff two_ne_zero).mp h4
  have := hN p (by rw [← pow_two]; exact h2)
  rw [Nat.isUnit_iff] at this
  exact hp.one_lt.ne' this

theorem Ip_ne_zero (D : PhiData Λ p) (hp : p.Prime) (hpN : p ∣ N) [NeZero N]
    (hJ : IsLev Λ R J N) : ∃ A ∈ Ip D J, A ≠ 0 := by
  by_contra hall
  haveI : Fact p.Prime := ⟨hp⟩
  have hred : ∀ y ∈ J, (p : ℚ) • y ∈ Λ → y ∈ Λ := by
    intro y hy h
    have h0 : D.φ ⟨(p : ℚ) • y, h⟩ = 0 := by
      by_contra hne
      exact hall ⟨_, ⟨y, hy, h, rfl⟩, hne⟩
    exact D.mem_of_eq_zero hp.ne_zero h h0
  let H : AddSubgroup ↥J.toAddSubgroup := Λ.toAddSubgroup.addSubgroupOf J.toAddSubgroup
  have hcard : Nat.card (↥J.toAddSubgroup ⧸ H) = N ^ 2 := by
    rw [← AddSubgroup.index_eq_card]; exact hJ.index
  haveI : Finite (↥J.toAddSubgroup ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (NeZero.ne N))
  obtain ⟨xbar, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥J.toAddSubgroup ⧸ H) p
    (by rw [hcard]; exact dvd_pow hpN two_ne_zero)
  obtain ⟨⟨y, hyJ⟩, rfl⟩ := QuotientAddGroup.mk_surjective xbar
  have hpy : (p • (⟨y, hyJ⟩ : ↥J.toAddSubgroup) : ↥J.toAddSubgroup) ∈ H := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, ← hx, addOrderOf_nsmul_eq_zero]
  have hpy' : (p : ℚ) • y ∈ Λ := by
    rw [AddSubgroup.mem_addSubgroupOf] at hpy
    rw [Nat.cast_smul_eq_nsmul]
    exact hpy
  have hyΛ : y ∈ Λ := hred y hyJ hpy'
  have h0 : (QuotientAddGroup.mk (⟨y, hyJ⟩ : ↥J.toAddSubgroup) : ↥J.toAddSubgroup ⧸ H) = 0 := by
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]; exact hyΛ
  rw [h0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

theorem stab_iff_lattice (hΛ : IsOrder Λ) (D : PhiData Λ p) (hp : p ≠ 0) (hJ : IsLev Λ R J N) (x : ↥Λ) :
    (∀ A ∈ Ip D J, A * D.φ x ∈ Ip D J) ↔
      ∀ z ∈ J, (p : ℚ) • z ∈ Λ → z * (x : ℍ[ℚ, a, b]) ∈ J := by
  constructor
  · intro hst z hz hpz
    have hm : (p : ℚ) • z * (x : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem hpz x.2
    have hm' : (p : ℚ) • (z * (x : ℍ[ℚ, a, b])) ∈ Λ := by rwa [smul_mul_assoc] at hm
    have h1 := hst _ ⟨z, hz, hpz, rfl⟩
    rw [← D.mul ⟨_, hpz⟩ x hm] at h1
    have e : (⟨(p : ℚ) • z * (x : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨(p : ℚ) • (z * (x : ℍ[ℚ, a, b])), hm'⟩ :=
      Subtype.ext (smul_mul_assoc _ _ _)
    rw [e] at h1
    exact (mem_Ip_iff D hp hJ hm').mp h1
  · intro hst A hA
    obtain ⟨z, hz, hpz, rfl⟩ := hA
    have hm : (p : ℚ) • z * (x : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem hpz x.2
    have hm' : (p : ℚ) • (z * (x : ℍ[ℚ, a, b])) ∈ Λ := by rwa [smul_mul_assoc] at hm
    rw [← D.mul ⟨_, hpz⟩ x hm]
    have e : (⟨(p : ℚ) • z * (x : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨(p : ℚ) • (z * (x : ℍ[ℚ, a, b])), hm'⟩ :=
      Subtype.ext (smul_mul_assoc _ _ _)
    rw [e]
    exact ⟨_, hst z hz hpz, hm', rfl⟩

theorem lattice_iff_mem_R (hΛ : IsOrder Λ) (hpN : p ∣ N) (hJ : IsLev Λ R J N)
    (u v : ℤ) (huv : u * (p : ℤ) + v * ((N / p : ℕ) : ℤ) = 1) (x : ↥Λ) :
    (∀ z ∈ J, (p : ℚ) • z ∈ Λ → z * (x : ℍ[ℚ, a, b]) ∈ J) ↔
      ((v * ((N / p : ℕ) : ℤ)) • (x : ℍ[ℚ, a, b]) + (u * (p : ℤ)) • (1 : ℍ[ℚ, a, b])) ∈ R := by
  have hx'Λ : ((v * ((N / p : ℕ) : ℤ)) • (x : ℍ[ℚ, a, b]) + (u * (p : ℤ)) • (1 : ℍ[ℚ, a, b])) ∈ Λ :=
    add_mem (Λ.smul_mem _ x.2) (Λ.smul_mem _ hΛ.one_mem)
  have hNp : p * (N / p) = N := Nat.mul_div_cancel' hpN
  have h1 : (u : ℚ) * (p : ℚ) + (v : ℚ) * ((N / p : ℕ) : ℚ) = 1 := by
    have := congrArg (fun t : ℤ => (t : ℚ)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one] at this
    exact this
  have hexp : ∀ y : ℍ[ℚ, a, b],
      y * ((v * ((N / p : ℕ) : ℤ)) • (x : ℍ[ℚ, a, b]) + (u * (p : ℤ)) • (1 : ℍ[ℚ, a, b])) =
        ((v : ℚ) * ((N / p : ℕ) : ℚ)) • (y * (x : ℍ[ℚ, a, b])) + ((u : ℚ) * (p : ℚ)) • y := by
    intro y
    rw [← intCast_rat_smul_eq, ← intCast_rat_smul_eq, mul_add, mul_smul_comm, mul_smul_comm, mul_one,
      Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
  rw [hJ.stab _ hx'Λ]
  constructor
  · intro hst y hy
    have hzJ : ((N / p : ℕ) : ℚ) • y ∈ J := natCast_smul_mem_of_mem J _ hy
    have hpz : (p : ℚ) • (((N / p : ℕ) : ℚ) • y) ∈ Λ := by
      rw [smul_smul, ← Nat.cast_mul, hNp, natCast_rat_smul_eq]
      exact hJ.tors y hy
    have hzx := hst _ hzJ hpz
    rw [hexp, mul_smul, mul_smul, ← smul_mul_assoc]
    exact add_mem (intCast_smul_mem_of_mem J v hzx)
      (intCast_smul_mem_of_mem J u (natCast_smul_mem_of_mem J p hy))
  · intro hst z hz hpz
    have hw : (p : ℚ) • z * ((x : ℍ[ℚ, a, b]) - 1) ∈ Λ := hΛ.mul_mem hpz (sub_mem x.2 hΛ.one_mem)
    have e : z * (x : ℍ[ℚ, a, b]) =
        z * ((v * ((N / p : ℕ) : ℤ)) • (x : ℍ[ℚ, a, b]) + (u * (p : ℤ)) • (1 : ℍ[ℚ, a, b])) +
          (u : ℚ) • ((p : ℚ) • z * ((x : ℍ[ℚ, a, b]) - 1)) := by
      rw [hexp, smul_mul_assoc, mul_sub, mul_one, smul_sub, smul_sub]
      simp only [smul_smul]
      conv_lhs => rw [← one_smul ℚ (z * (x : ℍ[ℚ, a, b])), ← h1]
      rw [add_smul]
      abel
    rw [e]
    exact add_mem (hst z hz) (intCast_smul_mem_of_mem J u (hJ.le hw))

theorem le_of_prime [Fact p.Prime] (hΛ : IsOrder Λ) (D : PhiData Λ p) (hpN : p ∣ N) [NeZero N] (hN : Squarefree N)
    {J J' : Submodule ℤ ℍ[ℚ, a, b]} (hJ : IsLev Λ R J N) (hJ' : IsLev Λ R J' N)
    {y : ℍ[ℚ, a, b]} (hy : y ∈ J) (hpy : (p : ℚ) • y ∈ Λ) : y ∈ J' := by
  have hp : p.Prime := Fact.out
  have hNp : p * (N / p) = N := Nat.mul_div_cancel' hpN
  have hcop : Nat.Coprime p (N / p) := (Nat.squarefree_mul_iff.mp (hNp.symm ▸ hN)).1
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hst : rstab (Ip D J) = rstab (Ip D J') := by
    ext m
    obtain ⟨x, rfl⟩ := D.surj m
    show (∀ A ∈ Ip D J, A * D.φ x ∈ Ip D J) ↔ (∀ A ∈ Ip D J', A * D.φ x ∈ Ip D J')
    rw [stab_iff_lattice hΛ D hp.ne_zero hJ x, stab_iff_lattice hΛ D hp.ne_zero hJ' x,
      lattice_iff_mem_R hΛ hpN hJ u v huv x, lattice_iff_mem_R hΛ hpN hJ' u v huv x]
  have heq : Ip D J = Ip D J' :=
    leftIdeal_eq_of_rstab_eq (Ip D J) (Ip D J')
      (fun A B hA hB => Ip_add D hA hB) (fun C A hA => Ip_mul hΛ D hJ C hA)
      (Ip_ne_zero D hp hpN hJ) (Ip_ne_univ D hp hN hJ)
      (fun A B hA hB => Ip_add D hA hB) (fun C A hA => Ip_mul hΛ D hJ' C hA)
      (Ip_ne_zero D hp hpN hJ') (Ip_ne_univ D hp hN hJ')
      hst
  have : D.φ ⟨(p : ℚ) • y, hpy⟩ ∈ Ip D J' := by
    rw [← heq]; exact ⟨y, hy, hpy, rfl⟩
  exact (mem_Ip_iff D hp.ne_zero hJ' hpy).mp this

end perPrime

end Frame

end LevModUnique

theorem LevModUnique.le_main
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b])
    (J J' : Submodule ℤ ℍ[ℚ, a, b]) (hJ : LevModUnique.IsLev Λ R J N) (hJ' : LevModUnique.IsLev Λ R J' N) :
    J ≤ J' := by
  have hΛo : IsOrder Λ := hΛ.1
  suffices H : ∀ n : ℕ, n ∣ N → ∀ y ∈ J, ((n : ℚ) • y) ∈ Λ → y ∈ J' by
    intro y hy
    exact H N dvd_rfl y hy (by rw [LevModUnique.natCast_rat_smul_eq]; exact hJ.tors y hy)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnN y hy hny
    by_cases hn1 : n = 1
    · subst hn1
      rw [Nat.cast_one, one_smul] at hny
      exact hJ'.le hny
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact (NeZero.ne N) (Nat.eq_zero_of_zero_dvd hnN)
    set m := n / p with hm
    have hnpm : p * m = n := Nat.mul_div_cancel' hpn
    have hcop : Nat.Coprime p m := (Nat.squarefree_mul_iff.mp (hnpm.symm ▸ hN.squarefree_of_dvd hnN)).1
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hpN : p ∣ N := hpn.trans hnN
    have hmN : m ∣ N := (Nat.div_dvd_of_dvd hpn).trans hnN
    have hm_lt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hp.one_lt
    have hqp : ¬ q ∣ p := fun h => hqN (h.trans hpN)
    have hq'p : ¬ q' ∣ p := fun h => hq'N (h.trans hpN)
    obtain ⟨φ, h1, hmul, hsurj, hker⟩ :=
      QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd hB Λ hΛ p hqp hq'p
    let D : LevModUnique.PhiData Λ p := ⟨φ, h1, hmul, hsurj, hker⟩

    have hpy : (p : ℚ) • y ∈ J' := by
      refine ih m hm_lt hmN _ (LevModUnique.natCast_smul_mem_of_mem J p hy) ?_
      rw [smul_smul, ← Nat.cast_mul, mul_comm, hnpm]; exact hny

    have hmy : (m : ℚ) • y ∈ J' := by
      refine LevModUnique.le_of_prime hΛo D hpN hN hJ hJ' (LevModUnique.natCast_smul_mem_of_mem J m hy) ?_
      rw [smul_smul, ← Nat.cast_mul, hnpm]; exact hny
    have e : y = (u : ℚ) • ((p : ℚ) • y) + (v : ℚ) • ((m : ℚ) • y) := by
      have h1 : ((u * (p : ℤ) + v * (m : ℤ) : ℤ) : ℚ) = 1 := by rw [huv]; simp
      rw [smul_smul, smul_smul, ← add_smul]
      push_cast at h1
      rw [h1, one_smul]
    rw [e]
    exact add_mem (LevModUnique.intCast_smul_mem_of_mem J' u hpy) (LevModUnique.intCast_smul_mem_of_mem J' v hmy)

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' J'' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : (Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J')))
    (hJ'' : (Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J'', y * x ∈ J''))) :
    J' = J'' := by
  have h1 : LevModUnique.IsLev Λ R J' N := ⟨hJ'.1, hJ'.2.1, hJ'.2.2.1, hJ'.2.2.2.1, hJ'.2.2.2.2⟩
  have h2 : LevModUnique.IsLev Λ R J'' N := ⟨hJ''.1, hJ''.2.1, hJ''.2.2.1, hJ''.2.2.2.1, hJ''.2.2.2.2⟩
  exact le_antisymm (LevModUnique.le_main hqN hq'N hB Λ hΛ hN R J' J'' h1 h2)
    (LevModUnique.le_main hqN hq'N hB Λ hΛ hN R J'' J' h2 h1)

end S_QuaternionAlgebra_IsEichlerOrder_levelModule_unique
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelModule_unique (solution)
