-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_mul_mem_line_of_line
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/36184380-0e07-52a1-a8d7-d6cf9e7b3899

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mul_mem_line_of_line
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace LT8

section matrices

variable {F : Type} [Field F]

def rk1 (c y : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.vecMulVec c y

def N (y : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := rk1 (Pi.single 0 1) y

def colMat (c : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => if j = 0 then c i else 0

theorem colMat_mul_N (c y : Fin 2 → F) : colMat c * N y = rk1 c y := by
  ext i j
  simp [colMat, N, rk1, Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two, Pi.single_apply]

theorem mul_N (C : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) : C * N y = rk1 (fun i => C i 0) y := by
  ext i j
  simp [N, rk1, Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two, Pi.single_apply]

theorem range_mul_N (y : Fin 2 → F) : Set.range (fun C : Matrix (Fin 2) (Fin 2) F => C * N y) = Set.range (fun c => rk1 c y) := by
  ext A
  constructor
  · rintro ⟨C, rfl⟩; exact ⟨fun i => C i 0, (mul_N C y).symm⟩
  · rintro ⟨c, rfl⟩; exact ⟨colMat c, colMat_mul_N c y⟩

theorem rk1_injective {y : Fin 2 → F} (hy : y ≠ 0) : Function.Injective (fun c : Fin 2 → F => rk1 c y) := by
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h; push Not at h; exact hy (funext h)
  intro c c' h
  funext i
  have := congrFun (congrFun h i) j
  simp only [rk1, Matrix.vecMulVec_apply] at this
  exact mul_right_cancel₀ hj this

theorem natCard_range_rk1 [Fintype F] {y : Fin 2 → F} (hy : y ≠ 0) :
    Nat.card ↥(Set.range (fun c : Fin 2 → F => rk1 c y)) = Nat.card F ^ 2 := by
  rw [Nat.card_range_of_injective (rk1_injective hy), Nat.card_pi, Fin.prod_univ_two, pow_two]

theorem exists_eq_range_of_card [Fintype F] (I : Set (Matrix (Fin 2) (Fin 2) F))
    (hI : ∀ (C A : Matrix (Fin 2) (Fin 2) F), A ∈ I → C * A ∈ I) (hcard : Nat.card ↥I = Nat.card F ^ 2) :
    ∃ y : Fin 2 → F, y ≠ 0 ∧ I = Set.range (fun C : Matrix (Fin 2) (Fin 2) F => C * N y) := by
  classical
  have hF : 1 < Fintype.card F := Fintype.one_lt_card
  haveI : Finite ↥I := Nat.finite_of_card_ne_zero (by rw [hcard, Nat.card_eq_fintype_card]; exact pow_ne_zero _ (by omega))

  obtain ⟨B, hB, hB0⟩ : ∃ B ∈ I, B ≠ 0 := by
    by_contra h; push Not at h
    have : I ⊆ {0} := fun A hA => by simpa using h A hA
    have h2 := Nat.card_mono (Set.finite_singleton 0) this
    rw [hcard, Nat.card_eq_fintype_card] at h2
    simp at h2
    nlinarith
  obtain ⟨i, hi⟩ : ∃ i, B i ≠ 0 := by by_contra h; push Not at h; exact hB0 (funext h)
  refine ⟨B i, hi, ?_⟩

  have hN : N (B i) ∈ I := by
    have : N (B i) = (Matrix.of fun r s => if r = 0 ∧ s = i then (1 : F) else 0) * B := by
      ext r s
      fin_cases r <;> fin_cases i <;> simp [N, rk1, Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two, Pi.single_apply]
    rw [this]; exact hI _ _ hB
  have hsub : Set.range (fun C : Matrix (Fin 2) (Fin 2) F => C * N (B i)) ⊆ I := by
    rintro _ ⟨C, rfl⟩; exact hI _ _ hN
  symm
  apply Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard, range_mul_N, natCard_range_rk1 hi]

theorem exists_invertible_row (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) F, P * Q = 1 ∧ Q * P = 1 ∧ P 0 = v := by
  by_cases h0 : v 0 ≠ 0
  · refine ⟨Matrix.of ![![v 0, v 1], ![0, 1]], Matrix.of ![![(v 0)⁻¹, -(v 0)⁻¹ * v 1], ![0, 1]], ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0]
    · funext j; fin_cases j <;> simp
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext j; fin_cases j
      · simpa using h0
      · exact h1
    push Not at h0
    refine ⟨Matrix.of ![![v 0, v 1], ![1, 0]], Matrix.of ![![0, 1], ![(v 1)⁻¹, -(v 1)⁻¹ * v 0]], ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
    · funext j; fin_cases j <;> simp

theorem N_eq_E_mul (P : Matrix (Fin 2) (Fin 2) F) : N (P 0) = colMat (Pi.single 0 1) * P := by
  ext i j
  simp [N, rk1, colMat, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.single_apply]

theorem exists_units_transport {y₀ y : Fin 2 → F} (hy₀ : y₀ ≠ 0) (hy : y ≠ 0) :
    ∃ u u' : Matrix (Fin 2) (Fin 2) F, u * u' = 1 ∧ u' * u = 1 ∧
      (∀ C : Matrix (Fin 2) (Fin 2) F, ∃ C', C * N y₀ * u = C' * N y) ∧
      (∀ C : Matrix (Fin 2) (Fin 2) F, ∃ C', C * N y * u' = C' * N y₀) := by
  obtain ⟨P₀, Q₀, hPQ₀, hQP₀, hP₀⟩ := exists_invertible_row y₀ hy₀
  obtain ⟨P, Q, hPQ, hQP, hP⟩ := exists_invertible_row y hy
  refine ⟨Q₀ * P, Q * P₀, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPQ, Matrix.one_mul, hQP₀]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P₀, hPQ₀, Matrix.one_mul, hQP]
  · intro C
    refine ⟨C, ?_⟩
    rw [← hP₀, N_eq_E_mul, ← hP, N_eq_E_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P₀, hPQ₀, Matrix.one_mul]
  · intro C
    refine ⟨C, ?_⟩
    rw [← hP₀, N_eq_E_mul, ← hP, N_eq_E_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, hPQ, Matrix.one_mul]

end matrices

end LT8

namespace LT8

theorem natCard_matrix_zmod (ℓ : ℕ) [NeZero ℓ] : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = ℓ ^ 4 := by
  show Nat.card (Fin 2 → Fin 2 → ZMod ℓ) = ℓ ^ 4
  rw [Nat.card_pi, Fin.prod_univ_two, Nat.card_pi, Fin.prod_univ_two, Nat.card_zmod]; ring

theorem exists_image_eq {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hO : IsOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (hℓL : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L)
    (hL_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L → (y : ℍ[ℚ, a, b]) * x ∈ L)
    (hL_index : L.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ y : Fin 2 → ZMod ℓ, y ≠ 0 ∧
      {A | ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧ φ x = A} = Set.range (fun C : Matrix (Fin 2) (Fin 2) (ZMod ℓ) => C * N y) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  apply exists_eq_range_of_card
  · rintro C A ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := hφsurj C
    exact ⟨⟨(y : ℍ[ℚ, a, b]) * x, hO.mul_mem y.2 x.2⟩, hL_left y x hx, hφmul y x _⟩
  ·
    rw [Nat.card_zmod]
    let θ : ↥Λ.toAddSubgroup →+ Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
      AddMonoidHom.mk' (fun x => φ ⟨x.1, x.2⟩) (fun x y => by
        show φ ⟨x.1 + y.1, _⟩ = φ ⟨x.1, x.2⟩ + φ ⟨y.1, y.2⟩
        rw [← map_add]; rfl)
    let K : AddSubgroup ↥Λ.toAddSubgroup := L.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup
    have hK : K.index = ℓ ^ 2 := hL_index
    have hHK : θ.ker ≤ K := by
      intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      obtain ⟨y, hy⟩ := (hφker ⟨x.1, x.2⟩).1 hx
      show (x : ℍ[ℚ, a, b]) ∈ L
      rw [show (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) from hy]; exact hℓL y
    have hH : θ.ker.index = ℓ ^ 4 := by
      rw [AddSubgroup.index_eq_card, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange θ).toEquiv,
        AddMonoidHom.range_eq_top.mpr (fun A => ?_), AddSubgroup.card_top, natCard_matrix_zmod]
      obtain ⟨x, rfl⟩ := hφsurj A
      exact ⟨⟨x.1, x.2⟩, rfl⟩
    have hrel : θ.ker.relIndex K = ℓ ^ 2 := by
      have := AddSubgroup.relIndex_mul_index hHK
      rw [hK, hH, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at this
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hℓ.pos 2) this

    let θK : ↥K →+ Matrix (Fin 2) (Fin 2) (ZMod ℓ) := θ.comp K.subtype
    have hkerK : θK.ker = θ.ker.addSubgroupOf K := by
      ext x; rfl
    have hcardR : Nat.card ↥θK.range = ℓ ^ 2 := by
      rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange θK).toEquiv, ← AddSubgroup.index_eq_card, hkerK]
      exact hrel
    have hset : (θK.range : Set (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) = {A | ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧ φ x = A} := by
      ext A
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨⟨x.1.1, x.1.2⟩, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨⟨x.1, x.2⟩, hx⟩, rfl⟩
    rw [← hset]
    exact hcardR

theorem stepA {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (hℓL : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L)
    (hL_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L → (y : ℍ[ℚ, a, b]) * x ∈ L)
    (hL_index : L.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ c d : ↥Λ,
      (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L) ∧
      (∀ x : ℍ[ℚ, a, b], x ∈ L → x * (d : ℍ[ℚ, a, b]) ∈ L₀) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hO := hΛ.isOrder
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  obtain ⟨y₀, hy₀, hI₀⟩ := exists_image_eq Λ hO ℓ φ hφmul hφsurj hφker L₀ hL₀ hℓL₀ hL₀_left hL₀_index
  obtain ⟨y, hy, hI⟩ := exists_image_eq Λ hO ℓ φ hφmul hφsurj hφker L hL hℓL hL_left hL_index
  obtain ⟨u, u', huu', hu'u, hfwd, hbwd⟩ := exists_units_transport hy₀ hy
  obtain ⟨c, hc⟩ := hφsurj u
  obtain ⟨d, hd⟩ := hφsurj u'
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := hO.one_mem

  have hdiff : ∀ z z' : ↥Λ, φ z = φ z' → ∃ w : ↥Λ, (z : ℍ[ℚ, a, b]) - (z' : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (w : ℍ[ℚ, a, b]) := by
    intro z z' h
    have : φ (z - z') = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨w, hw⟩ := (hφker _).1 this
    exact ⟨w, by rw [← hw]; rfl⟩
  refine ⟨c, d, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hdiff ⟨(c : ℍ[ℚ, a, b]) * d, hO.mul_mem c.2 d.2⟩ ⟨1, h1⟩ (by rw [hφmul, hc, hd, huu', hφ1])
    exact ⟨w, hw⟩
  · obtain ⟨w, hw⟩ := hdiff ⟨(d : ℍ[ℚ, a, b]) * c, hO.mul_mem d.2 c.2⟩ ⟨1, h1⟩ (by rw [hφmul, hd, hc, hu'u, hφ1])
    exact ⟨w, hw⟩
  · intro x hx
    have hxΛ : x ∈ Λ := hL₀ hx
    have hmem : φ ⟨x, hxΛ⟩ ∈ {A | ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧ φ x = A} := ⟨⟨x, hxΛ⟩, hx, rfl⟩
    rw [hI₀] at hmem
    obtain ⟨C, hC⟩ := hmem
    obtain ⟨C', hC'⟩ := hfwd C
    have hmem' : C' * N y ∈ {A | ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧ φ x = A} := by rw [hI]; exact ⟨C', rfl⟩
    obtain ⟨z, hz, hzφ⟩ := hmem'
    have hφxc : φ ⟨x * c, hO.mul_mem hxΛ c.2⟩ = φ z := by
      rw [hφmul ⟨x, hxΛ⟩ c, ← hC, hc, hC', hzφ]
    obtain ⟨w, hw⟩ := hdiff _ _ hφxc
    have : x * (c : ℍ[ℚ, a, b]) = (z : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (w : ℍ[ℚ, a, b]) := by
      rw [← hw]; simp
    rw [this]; exact L.add_mem hz (hℓL w)
  · intro x hx
    have hxΛ : x ∈ Λ := hL hx
    have hmem : φ ⟨x, hxΛ⟩ ∈ {A | ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧ φ x = A} := ⟨⟨x, hxΛ⟩, hx, rfl⟩
    rw [hI] at hmem
    obtain ⟨C, hC⟩ := hmem
    obtain ⟨C', hC'⟩ := hbwd C
    have hmem' : C' * N y₀ ∈ {A | ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧ φ x = A} := by rw [hI₀]; exact ⟨C', rfl⟩
    obtain ⟨z, hz, hzφ⟩ := hmem'
    have hφxd : φ ⟨x * d, hO.mul_mem hxΛ d.2⟩ = φ z := by
      rw [hφmul ⟨x, hxΛ⟩ d, ← hC, hd, hC', hzφ]
    obtain ⟨w, hw⟩ := hdiff _ _ hφxd
    have : x * (d : ℍ[ℚ, a, b]) = (z : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (w : ℍ[ℚ, a, b]) := by
      rw [← hw]; simp
    rw [this]; exact L₀.add_mem hz (hℓL₀ w)

end LT8

namespace LT8

section modn
variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])

theorem smul_nat_mem (n : ℕ) {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) : (n : ℚ) • z ∈ Λ := by
  rw [show (n : ℚ) = ((n : ℤ) : ℚ) by push_cast; rfl, Int.cast_smul_eq_zsmul]; exact Λ.smul_mem _ hz

theorem smul_int_mem (n : ℤ) {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) : (n : ℚ) • z ∈ Λ := by
  rw [Int.cast_smul_eq_zsmul]; exact Λ.smul_mem _ hz

def Mod (n : ℕ) (z : ℍ[ℚ, a, b]) : Prop := ∃ y : ↥Λ, z = (n : ℚ) • (y : ℍ[ℚ, a, b])

theorem Mod.add {n : ℕ} {z z' : ℍ[ℚ, a, b]} (h : Mod Λ n z) (h' : Mod Λ n z') : Mod Λ n (z + z') := by
  obtain ⟨y, rfl⟩ := h; obtain ⟨y', rfl⟩ := h'
  exact ⟨y + y', by rw [Submodule.coe_add, smul_add]⟩

theorem Mod.neg {n : ℕ} {z : ℍ[ℚ, a, b]} (h : Mod Λ n z) : Mod Λ n (-z) := by
  obtain ⟨y, rfl⟩ := h; exact ⟨-y, by rw [Submodule.coe_neg, smul_neg]⟩

theorem Mod.mul_left (hO : IsOrder Λ) {n : ℕ} {z : ℍ[ℚ, a, b]} (t : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (h : Mod Λ n z) :
    Mod Λ n (t * z) := by
  obtain ⟨y, rfl⟩ := h; exact ⟨⟨t * y, hO.mul_mem ht y.2⟩, by rw [mul_smul_comm]⟩

theorem Mod.mul_right (hO : IsOrder Λ) {n : ℕ} {z : ℍ[ℚ, a, b]} (t : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (h : Mod Λ n z) :
    Mod Λ n (z * t) := by
  obtain ⟨y, rfl⟩ := h; exact ⟨⟨y * t, hO.mul_mem y.2 ht⟩, by rw [smul_mul_assoc]⟩

theorem Mod.of_zsmul {n : ℕ} (k : ℤ) (t : ℍ[ℚ, a, b]) (ht : t ∈ Λ) : Mod Λ n (((k * n : ℤ) : ℚ) • t) :=
  ⟨⟨(k : ℚ) • t, smul_int_mem Λ k ht⟩, by push_cast; rw [mul_comm, mul_smul]⟩

theorem Mod.crt {n₁ n₂ : ℕ} (hc : Nat.Coprime n₁ n₂) {z : ℍ[ℚ, a, b]} (h₁ : Mod Λ n₁ z) (h₂ : Mod Λ n₂ z) :
    Mod Λ (n₁ * n₂) z := by
  obtain ⟨y₁, hy₁⟩ := h₁; obtain ⟨y₂, hy₂⟩ := h₂
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * n₁ + v * n₂ = 1 := by
    refine ⟨Nat.gcdA n₁ n₂, Nat.gcdB n₁ n₂, ?_⟩
    have := Nat.gcd_eq_gcd_ab n₁ n₂
    rw [Nat.Coprime.gcd_eq_one hc] at this; push_cast at this; linarith [this]
  refine ⟨⟨(u : ℚ) • (y₂ : ℍ[ℚ, a, b]) + (v : ℚ) • (y₁ : ℍ[ℚ, a, b]),
    Λ.add_mem (smul_int_mem Λ u y₂.2) (smul_int_mem Λ v y₁.2)⟩, ?_⟩
  have e1 : z = ((u : ℚ) * n₁) • z + ((v : ℚ) * n₂) • z := by
    rw [← add_smul]
    have : (u : ℚ) * n₁ + (v : ℚ) * n₂ = 1 := by exact_mod_cast huv
    rw [this, one_smul]
  have a1 : ((u : ℚ) * n₁) • z = ((u : ℚ) * n₁ * n₂) • (y₂ : ℍ[ℚ, a, b]) := by rw [hy₂, smul_smul]
  have a2 : ((v : ℚ) * n₂) • z = ((v : ℚ) * n₂ * n₁) • (y₁ : ℍ[ℚ, a, b]) := by rw [hy₁, smul_smul]
  rw [e1, a1, a2]
  show _ = ((n₁ * n₂ : ℕ) : ℚ) • ((u : ℚ) • (y₂ : ℍ[ℚ, a, b]) + (v : ℚ) • (y₁ : ℍ[ℚ, a, b]))
  rw [smul_add, smul_smul, smul_smul]
  congr 1 <;> (congr 1; push_cast; ring)

theorem pow_mem (hO : IsOrder Λ) {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (k : ℕ) : z ^ k ∈ Λ := by
  induction k with
  | zero => rw [pow_zero]; exact hO.one_mem
  | succ k ih => rw [pow_succ]; exact hO.mul_mem ih hz

theorem geom_mem (hO : IsOrder Λ) {r : ℍ[ℚ, a, b]} (hr : r ∈ Λ) (k : ℕ) :
    (Finset.range k).sum (fun i => r ^ i) ∈ Λ :=
  Submodule.sum_mem _ (fun i _ => pow_mem Λ hO hr i)

theorem Mod.smul_pow (hO : IsOrder Λ) (ℓ : ℕ) (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ) (e : ℕ) :
    Mod Λ (ℓ ^ e) (((ℓ : ℚ) • x) ^ e) :=
  ⟨⟨x ^ e, pow_mem Λ hO hx e⟩, by rw [_root_.smul_pow, Nat.cast_pow]⟩

theorem geom_succ (r : ℍ[ℚ, a, b]) (e : ℕ) :
    (Finset.range (e + 1)).sum (fun i => r ^ i) = 1 + r * (Finset.range e).sum (fun i => r ^ i) := by
  rw [Finset.sum_range_succ', pow_zero, add_comm, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => pow_succ' r i)

end modn

end LT8

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (m : ℕ) (hm : m ≠ 0) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (hℓL : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L)
    (hL_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L → (y : ℍ[ℚ, a, b]) * x ∈ L)
    (hL_index : L.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ c d : ↥Λ,
      (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L) ∧
      (∀ x : ℍ[ℚ, a, b], x ∈ L → x * (d : ℍ[ℚ, a, b]) ∈ L₀) := by
  classical
  have hO := hΛ.isOrder
  obtain ⟨c₁, d₁, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hc₁, hd₁⟩ :=
    LT8.stepA hB Λ hΛ ℓ hℓ hℓq hℓq' L₀ hL₀ hℓL₀ hL₀_left hL₀_index L hL hℓL hL_left hL_index

  obtain ⟨e, m', hme, hcop, he1⟩ : ∃ e m' : ℕ, ℓ ^ e * m' = m ∧ ℓ.Coprime m' ∧ 1 ≤ e :=
    ⟨m.factorization ℓ, m / ℓ ^ m.factorization ℓ, Nat.ordProj_mul_ordCompl_eq_self m ℓ,
      Nat.coprime_ordCompl hℓ hm, (hℓ.dvd_iff_one_le_factorization hm).1 hℓm⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hcop' : Nat.Coprime (ℓ ^ (e' + 1)) m' := Nat.Coprime.pow_left _ hcop

  set r₁ : ℍ[ℚ, a, b] := (ℓ : ℚ) • (-(x₁ : ℍ[ℚ, a, b])) with hr₁
  set r₂ : ℍ[ℚ, a, b] := (ℓ : ℚ) • (-(x₂ : ℍ[ℚ, a, b])) with hr₂
  have hr₁Λ : r₁ ∈ Λ := LT8.smul_nat_mem Λ ℓ (Λ.neg_mem x₁.2)
  have hr₂Λ : r₂ ∈ Λ := LT8.smul_nat_mem Λ ℓ (Λ.neg_mem x₂.2)
  have hcd₁ : (c₁ : ℍ[ℚ, a, b]) * d₁ = 1 - r₁ := by
    rw [hr₁, smul_neg, sub_neg_eq_add, add_comm]; exact sub_eq_iff_eq_add.mp hx₁
  have hdc₁ : (d₁ : ℍ[ℚ, a, b]) * c₁ = 1 - r₂ := by
    rw [hr₂, smul_neg, sub_neg_eq_add, add_comm]; exact sub_eq_iff_eq_add.mp hx₂
  set w₁ : ℍ[ℚ, a, b] := (Finset.range (e' + 1)).sum (fun i => r₁ ^ i) with hw₁
  set w₂ : ℍ[ℚ, a, b] := (Finset.range (e' + 1)).sum (fun i => r₂ ^ i) with hw₂
  have hw₁Λ : w₁ ∈ Λ := LT8.geom_mem Λ hO hr₁Λ _
  have hw₂Λ : w₂ ∈ Λ := LT8.geom_mem Λ hO hr₂Λ _
  have g1 : (1 - r₁) * w₁ = 1 - r₁ ^ (e' + 1) := mul_neg_geom_sum r₁ (e' + 1)
  have g2 : w₂ * (1 - r₂) = 1 - r₂ ^ (e' + 1) := geom_sum_mul_neg r₂ (e' + 1)

  set d₂ : ℍ[ℚ, a, b] := (d₁ : ℍ[ℚ, a, b]) * w₁ with hd₂
  set d₃ : ℍ[ℚ, a, b] := w₂ * (d₁ : ℍ[ℚ, a, b]) with hd₃
  have hd₂Λ : d₂ ∈ Λ := hO.mul_mem d₁.2 hw₁Λ
  have hd₃Λ : d₃ ∈ Λ := hO.mul_mem hw₂Λ d₁.2
  have hpow₁ : LT8.Mod Λ (ℓ ^ (e' + 1)) (r₁ ^ (e' + 1)) := LT8.Mod.smul_pow Λ hO ℓ _ (Λ.neg_mem x₁.2) _
  have hpow₂ : LT8.Mod Λ (ℓ ^ (e' + 1)) (r₂ ^ (e' + 1)) := LT8.Mod.smul_pow Λ hO ℓ _ (Λ.neg_mem x₂.2) _
  have hA : LT8.Mod Λ (ℓ ^ (e' + 1)) ((c₁ : ℍ[ℚ, a, b]) * d₂ - 1) := by
    have : (c₁ : ℍ[ℚ, a, b]) * d₂ - 1 = -(r₁ ^ (e' + 1)) := by
      rw [hd₂, ← mul_assoc, hcd₁, g1]; abel
    rw [this]; exact LT8.Mod.neg Λ hpow₁
  have hB' : LT8.Mod Λ (ℓ ^ (e' + 1)) (d₃ * (c₁ : ℍ[ℚ, a, b]) - 1) := by
    have : d₃ * (c₁ : ℍ[ℚ, a, b]) - 1 = -(r₂ ^ (e' + 1)) := by
      rw [hd₃, mul_assoc, hdc₁, g2]; abel
    rw [this]; exact LT8.Mod.neg Λ hpow₂
  have hdiff : LT8.Mod Λ (ℓ ^ (e' + 1)) (d₂ - d₃) := by
    have : d₂ - d₃ = -((d₃ * (c₁ : ℍ[ℚ, a, b]) - 1) * d₂) + d₃ * ((c₁ : ℍ[ℚ, a, b]) * d₂ - 1) := by noncomm_ring
    rw [this]
    exact LT8.Mod.add Λ (LT8.Mod.neg Λ (LT8.Mod.mul_right Λ hO _ hd₂Λ hB')) (LT8.Mod.mul_left Λ hO _ hd₃Λ hA)
  have hB : LT8.Mod Λ (ℓ ^ (e' + 1)) (d₂ * (c₁ : ℍ[ℚ, a, b]) - 1) := by
    have : d₂ * (c₁ : ℍ[ℚ, a, b]) - 1 = (d₂ - d₃) * c₁ + (d₃ * (c₁ : ℍ[ℚ, a, b]) - 1) := by noncomm_ring
    rw [this]; exact LT8.Mod.add Λ (LT8.Mod.mul_right Λ hO _ c₁.2 hdiff) hB'

  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (ℓ ^ (e' + 1) : ℕ) + v * m' = 1 := by
    refine ⟨Nat.gcdA (ℓ ^ (e' + 1)) m', Nat.gcdB (ℓ ^ (e' + 1)) m', ?_⟩
    have := Nat.gcd_eq_gcd_ab (ℓ ^ (e' + 1)) m'
    rw [Nat.Coprime.gcd_eq_one hcop'] at this; push_cast at this ⊢; linarith [this]
  set α : ℚ := ((u * (ℓ ^ (e' + 1) : ℕ) : ℤ) : ℚ) with hα
  set c : ℍ[ℚ, a, b] := (c₁ : ℍ[ℚ, a, b]) + α • (1 - (c₁ : ℍ[ℚ, a, b])) with hc
  set d : ℍ[ℚ, a, b] := d₂ + α • (1 - d₂) with hd
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hO.one_mem
  have hcΛ : c ∈ Λ := Λ.add_mem c₁.2 (by rw [hα]; exact LT8.smul_int_mem Λ _ (Λ.sub_mem h1Λ c₁.2))
  have hdΛ : d ∈ Λ := Λ.add_mem hd₂Λ (by rw [hα]; exact LT8.smul_int_mem Λ _ (Λ.sub_mem h1Λ hd₂Λ))

  have hcc₁ : LT8.Mod Λ (ℓ ^ (e' + 1)) (c - c₁) := by
    rw [hc, add_sub_cancel_left, hα]; exact LT8.Mod.of_zsmul Λ u _ (Λ.sub_mem h1Λ c₁.2)
  have hdd₂ : LT8.Mod Λ (ℓ ^ (e' + 1)) (d - d₂) := by
    rw [hd, add_sub_cancel_left, hα]; exact LT8.Mod.of_zsmul Λ u _ (Λ.sub_mem h1Λ hd₂Λ)
  have hα' : 1 - α = ((v * m' : ℤ) : ℚ) := by
    have h' : (u : ℚ) * (ℓ : ℚ) ^ (e' + 1) + v * m' = 1 := by exact_mod_cast huv
    rw [hα]; push_cast; linarith
  have hc1 : LT8.Mod Λ m' (c - 1) := by
    have : c - 1 = ((v * m' : ℤ) : ℚ) • ((c₁ : ℍ[ℚ, a, b]) - 1) := by
      rw [← hα', hc, sub_smul, one_smul, smul_sub, smul_sub]; abel
    rw [this]; exact LT8.Mod.of_zsmul Λ v _ (Λ.sub_mem c₁.2 h1Λ)
  have hd1 : LT8.Mod Λ m' (d - 1) := by
    have : d - 1 = ((v * m' : ℤ) : ℚ) • (d₂ - 1) := by
      rw [← hα', hd, sub_smul, one_smul, smul_sub, smul_sub]; abel
    rw [this]; exact LT8.Mod.of_zsmul Λ v _ (Λ.sub_mem hd₂Λ h1Λ)
  have hcd : LT8.Mod Λ m (c * d - 1) := by
    rw [← hme]; apply LT8.Mod.crt Λ hcop'
    · have : c * d - 1 = (c - c₁) * d + (c₁ : ℍ[ℚ, a, b]) * (d - d₂) + ((c₁ : ℍ[ℚ, a, b]) * d₂ - 1) := by noncomm_ring
      rw [this]
      exact LT8.Mod.add Λ (LT8.Mod.add Λ (LT8.Mod.mul_right Λ hO _ hdΛ hcc₁) (LT8.Mod.mul_left Λ hO _ c₁.2 hdd₂)) hA
    · have : c * d - 1 = (c - 1) * d + (d - 1) := by noncomm_ring
      rw [this]; exact LT8.Mod.add Λ (LT8.Mod.mul_right Λ hO _ hdΛ hc1) hd1
  have hdc : LT8.Mod Λ m (d * c - 1) := by
    rw [← hme]; apply LT8.Mod.crt Λ hcop'
    · have : d * c - 1 = (d - d₂) * c + d₂ * (c - c₁) + (d₂ * (c₁ : ℍ[ℚ, a, b]) - 1) := by noncomm_ring
      rw [this]
      exact LT8.Mod.add Λ (LT8.Mod.add Λ (LT8.Mod.mul_right Λ hO _ hcΛ hdd₂) (LT8.Mod.mul_left Λ hO _ hd₂Λ hcc₁)) hB
    · have : d * c - 1 = (d - 1) * c + (c - 1) := by noncomm_ring
      rw [this]; exact LT8.Mod.add Λ (LT8.Mod.mul_right Λ hO _ hcΛ hd1) hc1

  have hαL : ∀ (L' : Submodule ℤ ℍ[ℚ, a, b]), (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L') →
      ∀ t : ℍ[ℚ, a, b], t ∈ Λ → α • t ∈ L' := by
    intro L' hℓL' t ht
    have : α • t = ((u * (ℓ ^ e' : ℕ) : ℤ)) • ((ℓ : ℚ) • t) := by
      rw [hα, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]; congr 1; push_cast; ring
    rw [this]; exact L'.smul_mem _ (hℓL' ⟨t, ht⟩)
  refine ⟨⟨c, hcΛ⟩, ⟨d, hdΛ⟩, hcd, hdc, ?_, ?_⟩
  · intro x hx
    have hxΛ : x ∈ Λ := hL₀ hx
    show x * c ∈ L
    have : x * c = x * (c₁ : ℍ[ℚ, a, b]) + α • (x - x * (c₁ : ℍ[ℚ, a, b])) := by
      rw [hc, mul_add, mul_smul_comm, mul_sub, mul_one]
    rw [this]
    exact L.add_mem (hc₁ x hx) (hαL L hℓL _ (Λ.sub_mem hxΛ (hO.mul_mem hxΛ c₁.2)))
  · intro x hx
    have hxΛ : x ∈ Λ := hL hx
    show x * d ∈ L₀
    have hxd₁ : x * (d₁ : ℍ[ℚ, a, b]) ∈ L₀ := hd₁ x hx
    have hxd₂ : x * d₂ ∈ L₀ := by

      have heq : x * d₂ = x * (d₁ : ℍ[ℚ, a, b]) +
          (ℓ : ℚ) • (x * ((d₁ : ℍ[ℚ, a, b]) * (-(x₁ : ℍ[ℚ, a, b]) * (Finset.range e').sum (fun i => r₁ ^ i)))) := by
        rw [hd₂, hw₁, LT8.geom_succ, hr₁]
        simp only [mul_add, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
      rw [heq]
      refine L₀.add_mem hxd₁ ?_
      exact hℓL₀ ⟨_, hO.mul_mem hxΛ (hO.mul_mem d₁.2 (hO.mul_mem (Λ.neg_mem x₁.2) (LT8.geom_mem Λ hO hr₁Λ e')))⟩
    have : x * d = x * d₂ + α • (x - x * d₂) := by
      rw [hd, mul_add, mul_smul_comm, mul_sub, mul_one]
    rw [this]
    exact L₀.add_mem hxd₂ (hαL L₀ hℓL₀ _ (Λ.sub_mem hxΛ (hO.mul_mem hxΛ hd₂Λ)))

end S_QuaternionAlgebra_IsMaximalOrder_exists_mul_mem_line_of_line
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mul_mem_line_of_line (solution)
