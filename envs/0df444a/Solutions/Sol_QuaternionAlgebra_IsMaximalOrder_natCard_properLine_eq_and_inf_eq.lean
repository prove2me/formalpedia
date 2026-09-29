-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/42acb453-3802-583c-8ba8-c82e44455ce3

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_Matrix_natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace ASM21
namespace C3P

theorem natCast_zsmul_eq_ratCast_smul {a b : ℚ} (ℓ : ℕ) (y : ℍ[ℚ, a, b]) : (ℓ : ℤ) • y = (ℓ : ℚ) • y := by
  rw [← Int.cast_smul_eq_zsmul ℚ (ℓ : ℤ) y, Int.cast_natCast]

section dict
variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {ℓ : ℕ}
  (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))

def fromIdeal (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) :
    Submodule ℤ ℍ[ℚ, a, b] where
  carrier := {x | ∃ hx : x ∈ Λ, φ ⟨x, hx⟩ ∈ I}
  zero_mem' := ⟨Λ.zero_mem, by rw [show (⟨0, Λ.zero_mem⟩ : ↥Λ) = 0 from rfl, map_zero]; exact I.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hx, hxI⟩ ⟨hy, hyI⟩
    refine ⟨Λ.add_mem hx hy, ?_⟩
    rw [show (⟨x + y, Λ.add_mem hx hy⟩ : ↥Λ) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]
    exact I.add_mem hxI hyI
  smul_mem' := by
    rintro c x ⟨hx, hxI⟩
    refine ⟨Λ.smul_mem c hx, ?_⟩
    rw [show (⟨c • x, Λ.smul_mem c hx⟩ : ↥Λ) = c • ⟨x, hx⟩ from rfl, map_zsmul]
    exact I.toAddSubgroup.zsmul_mem hxI c

theorem mem_fromIdeal (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) (x : ℍ[ℚ, a, b]) :
    x ∈ fromIdeal Λ φ I ↔ ∃ hx : x ∈ Λ, φ ⟨x, hx⟩ ∈ I := Iff.rfl

theorem mem_fromIdeal' (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) (x : ↥Λ) :
    (x : ℍ[ℚ, a, b]) ∈ fromIdeal Λ φ I ↔ φ x ∈ I := by
  rw [mem_fromIdeal]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem fromIdeal_le (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) : fromIdeal Λ φ I ≤ Λ :=
  fun _ ⟨hx, _⟩ => hx

theorem phi_eq_zero_iff
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (x : ↥Λ) : φ x = 0 ↔ ∃ y ∈ Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℤ) • y := by
  rw [hφker]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, y.2, by rw [hy, natCast_zsmul_eq_ratCast_smul]⟩
  · rintro ⟨y, hyΛ, hy⟩; exact ⟨⟨y, hyΛ⟩, by rw [hy, natCast_zsmul_eq_ratCast_smul]⟩

theorem zsmul_mem_fromIdeal
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) (y : ℍ[ℚ, a, b]) (hy : y ∈ Λ) :
    (ℓ : ℤ) • y ∈ fromIdeal Λ φ I := by
  refine ⟨Λ.smul_mem _ hy, ?_⟩
  have : φ ⟨(ℓ : ℤ) • y, Λ.smul_mem _ hy⟩ = 0 := (phi_eq_zero_iff Λ φ hφker _).2 ⟨y, hy, rfl⟩
  rw [this]; exact I.zero_mem

theorem mul_mem_fromIdeal
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hmulΛ : ∀ x y : ↥Λ, (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)))
    (m : ℍ[ℚ, a, b]) (hm : m ∈ Λ) (x : ℍ[ℚ, a, b]) (hx : x ∈ fromIdeal Λ φ I) : m * x ∈ fromIdeal Λ φ I := by
  obtain ⟨hxΛ, hxI⟩ := hx
  refine ⟨hmulΛ ⟨m, hm⟩ ⟨x, hxΛ⟩, ?_⟩
  rw [hφmul ⟨m, hm⟩ ⟨x, hxΛ⟩]
  exact I.smul_mem _ hxI

variable
  (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
  (hφsurj : Function.Surjective φ)
  (hmulΛ : ∀ x y : ↥Λ, (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)

def toIdeal (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {M | ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ J ∧ φ x = M}
  zero_mem' := ⟨0, J.zero_mem, map_zero φ⟩
  add_mem' := by
    rintro M N ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, J.add_mem hx hy, map_add φ x y⟩
  smul_mem' := by
    rintro N M ⟨x, hx, rfl⟩
    obtain ⟨n, rfl⟩ := hφsurj N
    exact ⟨⟨_, hmulΛ n x⟩, hJ _ n.2 _ hx, by rw [hφmul]; rfl⟩

theorem mem_toIdeal (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) (M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :
    M ∈ toIdeal Λ φ hφmul hφsurj hmulΛ J hJ ↔ ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ J ∧ φ x = M := Iff.rfl

theorem fromIdeal_toIdeal
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hJ : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    fromIdeal Λ φ (toIdeal Λ φ hφmul hφsurj hmulΛ J hJ) = J := by
  ext x
  rw [mem_fromIdeal]
  constructor
  · rintro ⟨hx, hxI⟩
    obtain ⟨j, hj, hjx⟩ := (mem_toIdeal Λ φ hφmul hφsurj hmulΛ J hJ _).1 hxI
    have h0 : φ (⟨x, hx⟩ - j) = 0 := by rw [map_sub, hjx, sub_self]
    obtain ⟨y, hyΛ, hy⟩ := (phi_eq_zero_iff Λ φ hφker _).1 h0
    have hxeq : x = (j : ℍ[ℚ, a, b]) + (ℓ : ℤ) • y := by
      have hcoe : ((⟨x, hx⟩ - j : ↥Λ) : ℍ[ℚ, a, b]) = x - (j : ℍ[ℚ, a, b]) := rfl
      have h2 : x - (j : ℍ[ℚ, a, b]) = (ℓ : ℤ) • y := hcoe ▸ hy
      rw [sub_eq_iff_eq_add] at h2
      rw [h2, add_comm]
    rw [hxeq]
    exact J.add_mem hj (hℓJ _ hyΛ)
  · intro hxJ
    exact ⟨hJΛ hxJ, (mem_toIdeal Λ φ hφmul hφsurj hmulΛ J hJ _).2 ⟨⟨x, hJΛ hxJ⟩, hxJ, rfl⟩⟩

theorem toIdeal_fromIdeal (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) :
    toIdeal Λ φ hφmul hφsurj hmulΛ (fromIdeal Λ φ I) (fun m hm x hx => mul_mem_fromIdeal Λ φ hφmul hmulΛ I m hm x hx) = I := by
  ext M
  rw [mem_toIdeal]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (mem_fromIdeal' Λ φ I x).1 hx
  · intro hM
    obtain ⟨x, rfl⟩ := hφsurj M
    exact ⟨x, (mem_fromIdeal' Λ φ I x).2 hM, rfl⟩

theorem toIdeal_eq_bot_iff
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hJ : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    toIdeal Λ φ hφmul hφsurj hmulΛ J hJ = ⊥ ↔ ∀ x ∈ J, ∃ y ∈ Λ, x = (ℓ : ℤ) • y := by
  constructor
  · intro h x hx
    have : φ ⟨x, hJΛ hx⟩ ∈ toIdeal Λ φ hφmul hφsurj hmulΛ J hJ := ⟨⟨x, hJΛ hx⟩, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact (phi_eq_zero_iff Λ φ hφker _).1 this
  · intro h
    rw [eq_bot_iff]
    rintro M ⟨x, hx, rfl⟩
    rw [Submodule.mem_bot]
    exact (phi_eq_zero_iff Λ φ hφker x).2 (h _ hx)

theorem toIdeal_eq_top_iff
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hJ : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    toIdeal Λ φ hφmul hφsurj hmulΛ J hJ = ⊤ ↔ J = Λ := by
  constructor
  · intro h
    apply le_antisymm hJΛ
    intro x hx
    rw [← fromIdeal_toIdeal Λ φ hφmul hφsurj hmulΛ hφker J hJΛ hℓJ hJ, h, mem_fromIdeal]
    exact ⟨hx, Submodule.mem_top⟩
  · intro h; subst h
    rw [eq_top_iff]
    intro M _
    obtain ⟨x, rfl⟩ := hφsurj M
    exact ⟨x, x.2, rfl⟩

end dict

end ASM21.C3P

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
        (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ} = ℓ + 1 ∧
    ∀ J J' : Submodule ℤ ℍ[ℚ, a, b],
      J ≤ Λ → (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) → (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) →
      J' ≤ Λ → (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J') → (∀ m ∈ Λ, ∀ x ∈ J', m * x ∈ J') →
      J ≠ Λ → J' ≠ Λ → J ≠ J' →
      ∀ x : ℍ[ℚ, a, b], x ∈ J → x ∈ J' → ∃ y ∈ Λ, x = (ℓ : ℤ) • y := by
  classical
  have hO := hΛ.isOrder
  have hmulΛ : ∀ x y : ↥Λ, (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ := fun x y => hO.mul_mem x.2 y.2
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  obtain ⟨hcount, hinf⟩ := Matrix.natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot ℓ

  have hT := fun (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) =>
    ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J hJ
  refine ⟨?_, ?_⟩
  · rw [← hcount]
    apply Nat.card_congr
    refine
      { toFun := fun J => ⟨ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J.1 J.2.2.2.1, ?ne_bot, ?ne_top⟩
        invFun := fun I => ⟨ASM21.C3P.fromIdeal Λ φ I.1, ASM21.C3P.fromIdeal_le Λ φ I.1,
          fun y hy => ASM21.C3P.zsmul_mem_fromIdeal Λ φ hφker I.1 y hy,
          fun m hm x hx => ASM21.C3P.mul_mem_fromIdeal Λ φ hφmul hmulΛ I.1 m hm x hx, ?ex, ?ne_Λ⟩
        left_inv := ?li
        right_inv := ?ri }
    case ne_bot =>
      obtain ⟨J, hJΛ, hℓJ, hJ, ⟨x, hxJ, hxn⟩, hJne⟩ := J
      intro hb
      exact hxn ((ASM21.C3P.toIdeal_eq_bot_iff Λ φ hφmul hφsurj hmulΛ hφker J hJΛ hJ).1 hb x hxJ)
    case ne_top =>
      obtain ⟨J, hJΛ, hℓJ, hJ, hex, hJne⟩ := J
      intro ht
      exact hJne ((ASM21.C3P.toIdeal_eq_top_iff Λ φ hφmul hφsurj hmulΛ hφker J hJΛ hℓJ hJ).1 ht)
    case ex =>
      obtain ⟨I, hIb, hIt⟩ := I
      obtain ⟨M, hMI, hM0⟩ := (Submodule.ne_bot_iff I).1 hIb
      obtain ⟨x, rfl⟩ := hφsurj M
      refine ⟨x, (ASM21.C3P.mem_fromIdeal' Λ φ I x).2 hMI, fun h => hM0 ((ASM21.C3P.phi_eq_zero_iff Λ φ hφker x).2 h)⟩
    case ne_Λ =>
      obtain ⟨I, hIb, hIt⟩ := I
      intro hΛeq
      apply hIt
      rw [← ASM21.C3P.toIdeal_fromIdeal Λ φ hφmul hφsurj hmulΛ I]
      exact (ASM21.C3P.toIdeal_eq_top_iff Λ φ hφmul hφsurj hmulΛ hφker _ (ASM21.C3P.fromIdeal_le Λ φ I)
        (fun y hy => ASM21.C3P.zsmul_mem_fromIdeal Λ φ hφker I y hy) _).2 hΛeq
    case li =>
      intro J
      obtain ⟨J, hJΛ, hℓJ, hJ, hex, hJne⟩ := J
      apply Subtype.ext
      exact ASM21.C3P.fromIdeal_toIdeal Λ φ hφmul hφsurj hmulΛ hφker J hJΛ hℓJ hJ
    case ri =>
      intro I
      apply Subtype.ext
      exact ASM21.C3P.toIdeal_fromIdeal Λ φ hφmul hφsurj hmulΛ I.1
  · intro J J' hJΛ hℓJ hJ hJ'Λ hℓJ' hJ' hJne hJ'ne hne x hx hx'
    by_cases hb : ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J hJ = ⊥
    · exact (ASM21.C3P.toIdeal_eq_bot_iff Λ φ hφmul hφsurj hmulΛ hφker J hJΛ hJ).1 hb x hx
    by_cases hb' : ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J' hJ' = ⊥
    · exact (ASM21.C3P.toIdeal_eq_bot_iff Λ φ hφmul hφsurj hmulΛ hφker J' hJ'Λ hJ').1 hb' x hx'
    have ht : ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J hJ ≠ ⊤ := fun h =>
      hJne ((ASM21.C3P.toIdeal_eq_top_iff Λ φ hφmul hφsurj hmulΛ hφker J hJΛ hℓJ hJ).1 h)
    have ht' : ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J' hJ' ≠ ⊤ := fun h =>
      hJ'ne ((ASM21.C3P.toIdeal_eq_top_iff Λ φ hφmul hφsurj hmulΛ hφker J' hJ'Λ hℓJ' hJ').1 h)
    have hII : ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J hJ ≠ ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J' hJ' := by
      intro h
      apply hne
      rw [← ASM21.C3P.fromIdeal_toIdeal Λ φ hφmul hφsurj hmulΛ hφker J hJΛ hℓJ hJ,
        ← ASM21.C3P.fromIdeal_toIdeal Λ φ hφmul hφsurj hmulΛ hφker J' hJ'Λ hℓJ' hJ']
      exact congrArg (ASM21.C3P.fromIdeal Λ φ) h
    have hbot := hinf _ _ hb ht hb' ht' hII
    have hxΛ : x ∈ Λ := hJΛ hx
    have hmem : φ ⟨x, hxΛ⟩ ∈ ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J hJ ⊓ ASM21.C3P.toIdeal Λ φ hφmul hφsurj hmulΛ J' hJ' :=
      Submodule.mem_inf.2 ⟨⟨⟨x, hxΛ⟩, hx, rfl⟩, ⟨⟨x, hxΛ⟩, hx', rfl⟩⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact (ASM21.C3P.phi_eq_zero_iff Λ φ hφker _).1 hmem

end S_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq (solution)
