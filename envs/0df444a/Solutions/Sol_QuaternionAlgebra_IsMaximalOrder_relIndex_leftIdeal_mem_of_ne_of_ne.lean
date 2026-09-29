-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.relIndex_leftIdeal_mem_of_ne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/638cfcf8-8b66-5276-ba82-0258902c0ad7

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

namespace M2Ideal

open Matrix

variable {F : Type} [Field F]

def rowSpace (L : AddSubgroup (Matrix (Fin 2) (Fin 2) F)) : Submodule F (Fin 2 → F) :=
  Submodule.span F {v | ∃ X ∈ L, ∃ i : Fin 2, X i = v}

def rowMat (i : Fin 2) (v : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := fun a b => if a = i then v b else 0

theorem rowMat_apply_same (i : Fin 2) (v : Fin 2 → F) : rowMat i v i = v := by
  funext b; simp [rowMat]

theorem rowMat_apply_ne {i a : Fin 2} (h : a ≠ i) (v : Fin 2 → F) : rowMat i v a = 0 := by
  funext b; simp [rowMat, h]

theorem single_mul_eq_rowMat (i j : Fin 2) (X : Matrix (Fin 2) (Fin 2) F) :
    Matrix.single i j (1 : F) * X = rowMat i (X j) := by
  ext a b
  simp only [rowMat, Matrix.mul_apply, Matrix.single, Matrix.of_apply]
  by_cases ha : a = i
  · subst ha
    simp [Finset.mem_univ]
  · have : ¬ i = a := fun h => ha h.symm
    simp [this, ha]

theorem rowMat_add (i : Fin 2) (v w : Fin 2 → F) : rowMat i (v + w) = rowMat i v + rowMat i w := by
  ext a b; simp only [rowMat, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem rowMat_smul (i : Fin 2) (c : F) (v : Fin 2 → F) : rowMat i (c • v) = (c • (1 : Matrix (Fin 2) (Fin 2) F)) * rowMat i v := by
  ext a b; simp only [rowMat, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

variable (L : AddSubgroup (Matrix (Fin 2) (Fin 2) F)) (hL : ∀ A X : Matrix (Fin 2) (Fin 2) F, X ∈ L → A * X ∈ L)

include hL in
theorem rowMat_mem_of_mem_rowSpace (i : Fin 2) {v : Fin 2 → F} (hv : v ∈ rowSpace L) : rowMat i v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨X, hX, j, rfl⟩ := hv
    rw [← single_mul_eq_rowMat]; exact hL _ _ hX
  | zero => convert L.zero_mem using 1; ext a b; simp [rowMat]
  | add v w _ _ hv hw => rw [rowMat_add]; exact L.add_mem hv hw
  | smul c v _ hv => rw [rowMat_smul]; exact hL _ _ hv

include hL in

theorem mem_iff_forall_row_mem (X : Matrix (Fin 2) (Fin 2) F) : X ∈ L ↔ ∀ i, X i ∈ rowSpace L := by
  constructor
  · intro hX i; exact Submodule.subset_span ⟨X, hX, i, rfl⟩
  · intro h
    have : X = rowMat 0 (X 0) + rowMat 1 (X 1) := by
      ext a b; fin_cases a <;> simp [rowMat]
    rw [this]
    exact L.add_mem (rowMat_mem_of_mem_rowSpace L hL 0 (h 0)) (rowMat_mem_of_mem_rowSpace L hL 1 (h 1))

include hL in

noncomputable def equivProd : ↥L ≃ ↥(rowSpace L) × ↥(rowSpace L) where
  toFun X := (⟨(X : Matrix (Fin 2) (Fin 2) F) 0, (mem_iff_forall_row_mem L hL _).1 X.2 0⟩,
              ⟨(X : Matrix (Fin 2) (Fin 2) F) 1, (mem_iff_forall_row_mem L hL _).1 X.2 1⟩)
  invFun p := ⟨rowMat 0 (p.1 : Fin 2 → F) + rowMat 1 (p.2 : Fin 2 → F),
    L.add_mem (rowMat_mem_of_mem_rowSpace L hL 0 p.1.2) (rowMat_mem_of_mem_rowSpace L hL 1 p.2.2)⟩
  left_inv X := by
    apply Subtype.ext
    ext a b; fin_cases a <;> simp [rowMat]
  right_inv p := by
    ext <;> simp [rowMat]

include hL in

theorem natCard_eq [Finite F] :
    Nat.card ↥L = 1 ∨ Nat.card ↥L = Nat.card F ^ 2 ∨ Nat.card ↥L = Nat.card F ^ 4 := by
  classical
  have hc : Nat.card ↥L = Nat.card ↥(rowSpace L) ^ 2 := by
    rw [Nat.card_congr (equivProd L hL), Nat.card_prod, pow_two]

  haveI : Fintype F := Fintype.ofFinite F
  have hW : Nat.card ↥(rowSpace L) = Nat.card F ^ Module.finrank F ↥(rowSpace L) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hd : Module.finrank F ↥(rowSpace L) ≤ 2 := by
    have := Submodule.finrank_le (rowSpace L)
    simpa using this
  rw [hc, hW, ← pow_mul]
  interval_cases (Module.finrank F ↥(rowSpace L)) <;> simp

end M2Ideal

open scoped Quaternion
open QuaternionAlgebra

set_option maxHeartbeats 3200000 in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup.relIndex J.toAddSubgroup ∈
      ({1, ℓ ^ 2, ℓ ^ 4} : Set ℕ) := by
  classical
  obtain ⟨φ, -, hmul, hsurj, hker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'

  let g : ↥J.toAddSubgroup →+ Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
    { toFun := fun x => φ ⟨(x : ℍ[ℚ, a, b]), hJΛ x.2⟩
      map_zero' := by
        have : (⟨((0 : ↥J.toAddSubgroup) : ℍ[ℚ, a, b]), hJΛ (0 : ↥J.toAddSubgroup).2⟩ : ↥Λ) = 0 := Subtype.ext rfl
        rw [this, map_zero]
      map_add' := fun x y => by
        have : (⟨((x + y : ↥J.toAddSubgroup) : ℍ[ℚ, a, b]), hJΛ (x + y).2⟩ : ↥Λ) =
            ⟨(x : ℍ[ℚ, a, b]), hJΛ x.2⟩ + ⟨(y : ℍ[ℚ, a, b]), hJΛ y.2⟩ := Subtype.ext rfl
        rw [this, map_add] }
  have hg : ∀ x : ↥J.toAddSubgroup, g x = φ ⟨(x : ℍ[ℚ, a, b]), hJΛ x.2⟩ := fun x => rfl

  have hkerg : (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup.addSubgroupOf
      J.toAddSubgroup = g.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hg, hker]
    constructor
    · intro hx

      have hle : Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) ≤
          Λ.map (DistribMulAction.toLinearMap ℤ ℍ[ℚ, a, b] (ℓ : ℤ)) := by
        rw [Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hle hx
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [← hyx]
      show ((ℓ : ℤ) • y : ℍ[ℚ, a, b]) = (ℓ : ℚ) • y
      rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    · rintro ⟨y, hy⟩
      refine Submodule.subset_span ⟨(y : ℍ[ℚ, a, b]), y.2, ?_⟩
      rw [hy]
      show ((ℓ : ℤ) • (y : ℍ[ℚ, a, b])) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])
      rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

  let L : AddSubgroup (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := g.range
  have hL : ∀ A X : Matrix (Fin 2) (Fin 2) (ZMod ℓ), X ∈ L → A * X ∈ L := by
    rintro A X ⟨x, rfl⟩
    obtain ⟨m, rfl⟩ := hsurj A
    refine ⟨⟨(m : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hleft _ m.2 _ x.2⟩, ?_⟩
    rw [hg, hg]
    exact hmul m ⟨(x : ℍ[ℚ, a, b]), hJΛ x.2⟩ (hΛ.isOrder.mul_mem m.2 (hJΛ x.2))

  have hidx : (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup.relIndex
      J.toAddSubgroup = Nat.card ↥L := by
    rw [AddSubgroup.relIndex, hkerg, AddSubgroup.index_ker]
    try rfl
  rw [hidx]
  have hF : Nat.card (ZMod ℓ) = ℓ := Nat.card_zmod ℓ
  rcases M2Ideal.natCard_eq L hL with h | h | h
  · exact Or.inl h
  · rw [hF] at h; exact Or.inr (Or.inl h)
  · rw [hF] at h; exact Or.inr (Or.inr h)

end S_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne (solution)
