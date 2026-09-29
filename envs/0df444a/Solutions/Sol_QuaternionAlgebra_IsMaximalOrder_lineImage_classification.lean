-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.lineImage_classification
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8f57efcd-abb6-58ed-8b63-7a483431842e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_natCard_properLine_eq_and_inf_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace ASM21
namespace M2L

variable {ℓ : ℕ}

def row0 (x : Fin 2 → ZMod ℓ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := Matrix.of ![x, 0]

@[scoped simp] theorem row0_apply_zero (x : Fin 2 → ZMod ℓ) : row0 x 0 = x := rfl
@[scoped simp] theorem row0_apply_one (x : Fin 2 → ZMod ℓ) : row0 x 1 = 0 := rfl

theorem row0_add (x y : Fin 2 → ZMod ℓ) : row0 (x + y) = row0 x + row0 y := by
  ext i j; fin_cases i <;> simp [row0]
theorem row0_zero : row0 (0 : Fin 2 → ZMod ℓ) = 0 := by
  ext i j; fin_cases i <;> simp [row0]
theorem row0_smul (c : ZMod ℓ) (x : Fin 2 → ZMod ℓ) : row0 (c • x) = (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) c) * row0 x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  ext i j; fin_cases i <;> simp [row0]
theorem row0_eq_zero_iff (x : Fin 2 → ZMod ℓ) : row0 x = 0 ↔ x = 0 := by
  constructor
  · intro h; funext j; have := congrFun (congrFun h 0) j; simpa [row0] using this
  · rintro rfl; exact row0_zero

theorem single_mul_eq_row0 (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (i : Fin 2) :
    Matrix.of (fun a b => if a = 0 ∧ b = i then (1 : ZMod ℓ) else 0) * X = row0 (X i) := by
  ext a b; fin_cases a <;> fin_cases i <;> simp [row0, Matrix.mul_apply, Fin.sum_univ_two]

theorem low_mul_row0 (y : Fin 2 → ZMod ℓ) :
    Matrix.of (fun a b => if a = 1 ∧ b = 0 then (1 : ZMod ℓ) else 0) * row0 y = Matrix.of ![0, y] := by
  ext a b; fin_cases a <;> simp [row0, Matrix.mul_apply, Fin.sum_univ_two]
theorem eq_row0_add (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : X = row0 (X 0) + Matrix.of ![0, X 1] := by
  ext a b; fin_cases a <;> simp [row0]

def rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) where
  carrier := {x | row0 x ∈ I}
  zero_mem' := by show row0 0 ∈ I; rw [row0_zero]; exact I.zero_mem
  add_mem' := by intro x y hx hy; show row0 (x + y) ∈ I; rw [row0_add]; exact I.add_mem hx hy
  smul_mem' := by intro c x hx; show row0 (c • x) ∈ I; rw [row0_smul]; exact I.smul_mem _ hx

theorem mem_rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) (x : Fin 2 → ZMod ℓ) : x ∈ rowSp I ↔ row0 x ∈ I := Iff.rfl

def idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {X | ∀ i, X i ∈ W}
  zero_mem' := by
    show ∀ i, (0 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i ∈ W
    intro i; exact W.zero_mem
  add_mem' := by
    intro X Y hX hY
    show ∀ i, (X + Y) i ∈ W
    intro i; exact W.add_mem (hX i) (hY i)
  smul_mem' := by
    intro Y X hX i
    have : (Y • X) i = ∑ k, Y i k • X k := by
      funext j; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact W.sum_mem (fun k _ => W.smul_mem _ (hX k))

theorem mem_idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : X ∈ idealOf W ↔ ∀ i, X i ∈ W := Iff.rfl

theorem rowSp_idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : rowSp (idealOf W) = W := by
  ext x
  rw [mem_rowSp, mem_idealOf]
  constructor
  · intro h; simpa using h 0
  · intro h i; fin_cases i <;> simp [h]

theorem idealOf_rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) : idealOf (rowSp I) = I := by
  ext X
  rw [mem_idealOf]
  constructor
  · intro h
    have h0 : row0 (X 0) ∈ I := (mem_rowSp I _).1 (h 0)
    have h1 : row0 (X 1) ∈ I := (mem_rowSp I _).1 (h 1)
    rw [eq_row0_add X, ← low_mul_row0]
    exact I.add_mem h0 (I.smul_mem _ h1)
  · intro hX i
    rw [mem_rowSp, ← single_mul_eq_row0]
    exact I.smul_mem _ hX

def idealEquiv : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ≃ Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) where
  toFun := rowSp
  invFun := idealOf
  left_inv := idealOf_rowSp
  right_inv := rowSp_idealOf

theorem rowSp_bot : rowSp (⊥ : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) = ⊥ := by
  ext x; rw [mem_rowSp, Submodule.mem_bot, Submodule.mem_bot, row0_eq_zero_iff]
theorem rowSp_top : rowSp (⊤ : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) = ⊤ := by
  ext x; simp [mem_rowSp]
theorem idealOf_inf (W W' : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : idealOf (W ⊓ W') = idealOf W ⊓ idealOf W' := by
  ext X; simp only [mem_idealOf, Submodule.mem_inf]; exact forall_and
theorem idealOf_bot : idealOf (⊥ : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) = ⊥ := by
  rw [← rowSp_bot, idealOf_rowSp]

def properEquiv :
    {I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) // I ≠ ⊥ ∧ I ≠ ⊤} ≃
    {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤} where
  toFun I := ⟨rowSp I.1, fun h => I.2.1 (by rw [← idealOf_rowSp I.1, h, ← rowSp_bot, idealOf_rowSp]),
    fun h => I.2.2 (by rw [← idealOf_rowSp I.1, h, ← rowSp_top, idealOf_rowSp])⟩
  invFun W := ⟨idealOf W.1, fun h => W.2.1 (by rw [← rowSp_idealOf W.1, h, rowSp_bot]),
    fun h => W.2.2 (by rw [← rowSp_idealOf W.1, h, rowSp_top])⟩
  left_inv I := Subtype.ext (idealOf_rowSp I.1)
  right_inv W := Subtype.ext (rowSp_idealOf W.1)

section lines
variable [Fact ℓ.Prime]

theorem finrank_two : Module.finrank (ZMod ℓ) (Fin 2 → ZMod ℓ) = 2 := by simp

theorem exists_eq_span {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)} (h1 : W ≠ ⊥) (h2 : W ≠ ⊤) :
    ∃ (v : Fin 2 → ZMod ℓ) (hv : v ≠ 0), W = (Projectivization.mk (ZMod ℓ) v hv).submodule := by
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).1 h1
  refine ⟨v, hv0, ?_⟩
  rw [Projectivization.submodule_mk]
  have hle : Submodule.span (ZMod ℓ) {v} ≤ W := Submodule.span_le.2 (by simpa using hvW)
  have hlt : Module.finrank (ZMod ℓ) W < Module.finrank (ZMod ℓ) (Fin 2 → ZMod ℓ) :=
    Submodule.finrank_lt h2
  rw [finrank_two] at hlt
  have h1' : Module.finrank (ZMod ℓ) (Submodule.span (ZMod ℓ) {v}) = 1 := finrank_span_singleton hv0
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

theorem span_ne_bot_ne_top (p : Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ)) : p.submodule ≠ ⊥ ∧ p.submodule ≠ ⊤ := by
  have h := p.finrank_submodule
  constructor
  · intro hb; rw [hb, finrank_bot] at h; exact zero_ne_one h
  · intro ht; rw [ht, finrank_top, finrank_two] at h; omega

noncomputable def linesEquiv :
    {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤} ≃ Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ) := by
  classical
  refine (Equiv.ofBijective (fun p : Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ) =>
    (⟨p.submodule, span_ne_bot_ne_top p⟩ : {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤})) ⟨?_, ?_⟩).symm
  · intro p q h; exact Projectivization.submodule_injective (congrArg Subtype.val h)
  · rintro ⟨W, hW1, hW2⟩
    obtain ⟨v, hv, rfl⟩ := exists_eq_span hW1 hW2
    exact ⟨_, rfl⟩

theorem natCard_lines : Nat.card {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤} = ℓ + 1 := by
  rw [Nat.card_congr linesEquiv, Projectivization.card_of_finrank_two (ZMod ℓ) (Fin 2 → ZMod ℓ) finrank_two,
    Nat.card_eq_fintype_card, ZMod.card]

theorem inf_eq_bot_of_ne {W W' : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)} (h1 : W ≠ ⊥) (h2 : W ≠ ⊤) (h1' : W' ≠ ⊥) (h2' : W' ≠ ⊤)
    (hne : W ≠ W') : W ⊓ W' = ⊥ := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_span h1 h2
  obtain ⟨v', hv', rfl⟩ := exists_eq_span h1' h2'
  by_contra h
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨huv, huv'⟩ := Submodule.mem_inf.1 hu
  apply hne
  have key : ∀ (p : Projectivization (ZMod ℓ) (Fin 2 → ZMod ℓ)), u ∈ p.submodule → p.submodule = Submodule.span (ZMod ℓ) {u} := by
    intro p hup
    have hle : Submodule.span (ZMod ℓ) {u} ≤ p.submodule := Submodule.span_le.2 (by simpa using hup)
    symm
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [p.finrank_submodule, finrank_span_singleton hu0]
  rw [key _ huv, key _ huv']

end lines

end ASM21.M2L
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21 P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21.M2L"
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21"

namespace LOP29

abbrev Mat (ℓ : ℕ) : Type := Matrix (Fin 2) (Fin 2) (ZMod ℓ)

section Dict

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hord : IsOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime]
  (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
  (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
  (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
  (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
  (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
  (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
  (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
  (hφsurj : Function.Surjective φ)
  (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))

theorem coe_mul_eq_ratsmul (y : ℍ[ℚ, a, b]) : ((ℓ : ℚ) : ℍ[ℚ, a, b]) * y = (ℓ : ℚ) • y :=
  QuaternionAlgebra.coe_mul_eq_smul _ _

theorem zsmul_eq_coe_mul (y : ℍ[ℚ, a, b]) : (ℓ : ℤ) • y = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * y := by
  rw [zsmul_eq_mul, Int.cast_natCast, ← QuaternionAlgebra.coe_natCast]

include hann hφker in
theorem rho_eq_zero_iff_phi (m : ↥Λ) : ρ m P₀ = 0 ↔ φ m = 0 := by
  rw [hann, hφker]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [hy, coe_mul_eq_ratsmul]⟩
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [hy, coe_mul_eq_ratsmul]⟩

def ev : ↥Λ →+ M := AddMonoidHom.mk' (fun m => ρ m P₀) (fun x y => by simp [ρ_add])

include ρ_add in
theorem ev_apply (m : ↥Λ) : ev Λ M ρ ρ_add P₀ m = ρ m P₀ := rfl

include ρ_add hann hφker in
theorem rho_eq_iff_phi (m m' : ↥Λ) : ρ m P₀ = ρ m' P₀ ↔ φ m = φ m' := by
  rw [← sub_eq_zero, ← ev_apply Λ M ρ ρ_add P₀, ← ev_apply Λ M ρ ρ_add P₀, ← map_sub, ev_apply,
    rho_eq_zero_iff_phi Λ ℓ M ρ P₀ hann φ hφker, map_sub, sub_eq_zero]

include hord ρ_mul in
theorem rho_mul_apply (n m : ↥Λ) (P : M) :
    ρ ⟨(n : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hord.mul_mem n.2 m.2⟩ P = ρ n (ρ m P) := by
  rw [ρ_mul]; rfl

def idealImg (J : Submodule ℤ ℍ[ℚ, a, b]) (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {A | ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ φ m = A}
  zero_mem' := ⟨0, J.zero_mem, map_zero φ⟩
  add_mem' := by
    rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', J.add_mem hm hm', map_add φ m m'⟩
  smul_mem' := by
    rintro A _ ⟨m, hm, rfl⟩
    obtain ⟨n, rfl⟩ := hφsurj A
    exact ⟨⟨(n : ℍ[ℚ, a, b]) * m, hord.mul_mem n.2 m.2⟩, hleft _ n.2 _ hm, by rw [hφmul, smul_eq_mul]⟩

theorem mem_idealImg (J : Submodule ℤ ℍ[ℚ, a, b]) (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :
    A ∈ idealImg Λ hord ℓ φ hφmul hφsurj J hleft ↔ ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ φ m = A := Iff.rfl

include hφker in

theorem mem_of_phi_mem_idealImg (J : Submodule ℤ ℍ[ℚ, a, b]) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) (m : ↥Λ)
    (hm : φ m ∈ idealImg Λ hord ℓ φ hφmul hφsurj J hleft) : (m : ℍ[ℚ, a, b]) ∈ J := by
  obtain ⟨m', hm', he⟩ := hm
  have : φ (m - m') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨y, hy⟩ := (hφker _).mp this
  have : (m : ℍ[ℚ, a, b]) = m' + (ℓ : ℤ) • (y : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_coe_mul, coe_mul_eq_ratsmul, ← hy]; simp
  rw [this]
  exact J.add_mem hm' (hℓJ _ y.2)

include ρ_add hann hφker in

theorem mem_of_rho_eq (J : Submodule ℤ ℍ[ℚ, a, b]) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) (m m' : ↥Λ)
    (hm' : (m' : ℍ[ℚ, a, b]) ∈ J) (h : ρ m P₀ = ρ m' P₀) : (m : ℍ[ℚ, a, b]) ∈ J := by
  have hφ : φ (m - m') = 0 := by
    rw [map_sub, sub_eq_zero]; exact (rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker m m').mp h
  obtain ⟨y, hy⟩ := (hφker _).mp hφ
  have : (m : ℍ[ℚ, a, b]) = m' + (ℓ : ℤ) • (y : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_coe_mul, coe_mul_eq_ratsmul, ← hy]; simp
  rw [this]
  exact J.add_mem hm' (hℓJ _ y.2)

include hann in
theorem rho_zsmul_ell (y : ↥Λ) : ρ ((ℓ : ℤ) • y) P₀ = 0 :=
  (hann _).mpr ⟨y, by rw [Submodule.coe_smul, zsmul_eq_coe_mul]⟩

noncomputable def equivMat : M ≃ Matrix (Fin 2) (Fin 2) (ZMod ℓ) where
  toFun P := φ (Classical.choose (hgen P))
  invFun A := ρ (Classical.choose (hφsurj A)) P₀
  left_inv P := by
    have h1 := Classical.choose_spec (hgen P)
    have h2 := Classical.choose_spec (hφsurj (φ (Classical.choose (hgen P))))
    exact ((rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker _ _).mpr h2).trans h1.symm
  right_inv A := by
    have h2 := Classical.choose_spec (hφsurj A)
    have h1 := Classical.choose_spec (hgen (ρ (Classical.choose (hφsurj A)) P₀))
    exact ((rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker _ _).mp h1.symm).trans h2

include ρ_add hgen hann hφsurj hφker in
theorem natCard_M : Nat.card M = ℓ ^ 4 := by
  rw [Nat.card_congr (equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker), Nat.card_eq_fintype_card]
  show Fintype.card (Fin 2 → Fin 2 → ZMod ℓ) = ℓ ^ 4
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]

theorem eq_bot_or_eq_of_le_span {v : Fin 2 → ZMod ℓ} (hv : v ≠ 0) (W' : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ))
    (h : W' ≤ Submodule.span (ZMod ℓ) {v}) : W' = ⊥ ∨ W' = Submodule.span (ZMod ℓ) {v} := by
  by_cases hb : W' = ⊥
  · exact Or.inl hb
  · right
    apply le_antisymm h
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W').1 hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (h hw)
    have hc : c ≠ 0 := by rintro rfl; exact hw0 (zero_smul _ v)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have : v = c⁻¹ • (c • v) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [SetLike.mem_coe, this]
    exact W'.smul_mem _ hw

end Dict
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21 P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21.M2L"

end LOP29
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21 P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21.M2L"

namespace LOP29

section PartA

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hord : IsOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime]
  (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
  (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
  (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
  (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
  (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
  (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
  (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
  (hφsurj : Function.Surjective φ)
  (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))

include ρ_add hgen hann hφsurj hφker in

theorem equivMat_apply_rho (m : ↥Λ) :
    equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker (ρ m P₀) = φ m := by
  have h1 := Classical.choose_spec (hgen (ρ m P₀))
  show φ (Classical.choose (hgen (ρ m P₀))) = φ m
  exact ((rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker _ _).mp h1).symm

include ρ_add hgen hann hφsurj hφker in
theorem equivMat_symm_apply_phi (m : ↥Λ) :
    (equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker).symm (φ m) = ρ m P₀ := by
  rw [Equiv.symm_apply_eq, equivMat_apply_rho]

include ρ_add hgen hann hφsurj hφker in
theorem equivMat_add (P Q : M) :
    equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker (P + Q) =
      equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker P + equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker Q := by
  obtain ⟨m, rfl⟩ := hgen P
  obtain ⟨m', rfl⟩ := hgen Q
  have : ρ m P₀ + ρ m' P₀ = ρ (m + m') P₀ := by rw [ρ_add, AddMonoidHom.add_apply]
  rw [this, equivMat_apply_rho, equivMat_apply_rho, equivMat_apply_rho, map_add]

include hord ρ_mul ρ_add hgen hann hφmul hφsurj hφker in

theorem partA_equiv (J : Submodule ℤ ℍ[ℚ, a, b])
    (hJ : J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)},
      ∀ x y : ZMod ℓ × ZMod ℓ,
        ((e (x + y) : {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)}) : M) = (e x : M) + (e y : M) := by
  classical
  obtain ⟨hJle, hJℓ, hJmul, ⟨x₀, hx₀J, hx₀⟩, hJne⟩ := hJ

  let EM := equivMat Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  have hEM : ∀ m : ↥Λ, EM (ρ m P₀) = φ m := equivMat_apply_rho Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  have hEMs : ∀ m : ↥Λ, EM.symm (φ m) = ρ m P₀ := equivMat_symm_apply_phi Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  have hEMadd : ∀ P Q : M, EM (P + Q) = EM P + EM Q := equivMat_add Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
  let I := idealImg Λ hord ℓ φ hφmul hφsurj J hJmul
  have hImem : ∀ A, A ∈ I ↔ ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ φ m = A := fun A => Iff.rfl
  let W := ASM21.M2L.rowSp I
  have hIW : ∀ X, X ∈ I ↔ ∀ i, X i ∈ W := fun X => by
    rw [← ASM21.M2L.mem_idealOf, ASM21.M2L.idealOf_rowSp]

  have hIb : I ≠ ⊥ := by
    intro h
    have hmem : φ ⟨x₀, hJle hx₀J⟩ ∈ I := ⟨⟨x₀, hJle hx₀J⟩, hx₀J, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    obtain ⟨y, hy⟩ := (hφker _).mp hmem
    exact hx₀ ⟨y, y.2, by rw [zsmul_eq_coe_mul, coe_mul_eq_ratsmul]; exact hy⟩
  have hIt : I ≠ ⊤ := by
    intro h
    apply hJne
    apply le_antisymm hJle
    intro m hm
    exact mem_of_phi_mem_idealImg Λ hord ℓ φ hφmul hφsurj hφker J hJℓ hJmul ⟨m, hm⟩
      (by rw [show idealImg Λ hord ℓ φ hφmul hφsurj J hJmul = ⊤ from h]; exact Submodule.mem_top)
  have hWb : W ≠ ⊥ := by
    intro h; apply hIb
    rw [← ASM21.M2L.idealOf_rowSp I, show ASM21.M2L.rowSp I = ⊥ from h, ASM21.M2L.idealOf_bot]
  have hWt : W ≠ ⊤ := by
    intro h; apply hIt
    rw [← ASM21.M2L.idealOf_rowSp I, show ASM21.M2L.rowSp I = ⊤ from h, ← ASM21.M2L.rowSp_top, ASM21.M2L.idealOf_rowSp]
  obtain ⟨v, hv0, hWv⟩ := ASM21.M2L.exists_eq_span hWb hWt
  rw [Projectivization.submodule_mk] at hWv

  let eW : ZMod ℓ ≃ₗ[ZMod ℓ] W :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod ℓ) (Fin 2 → ZMod ℓ) v hv0).trans (LinearEquiv.ofEq _ _ hWv.symm)

  let S := {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)}
  have hSmem : ∀ P : S, EM P.1 ∈ I := by
    rintro ⟨P, m, hm, rfl⟩
    rw [hEM]; exact ⟨m, hm, rfl⟩
  have hrow : ∀ (P : S) (i : Fin 2), EM P.1 i ∈ W := fun P i => (hIW _).mp (hSmem P) i
  let f : S → ZMod ℓ × ZMod ℓ := fun P => (eW.symm ⟨EM P.1 0, hrow P 0⟩, eW.symm ⟨EM P.1 1, hrow P 1⟩)

  let mk : ZMod ℓ × ZMod ℓ → Matrix (Fin 2) (Fin 2) (ZMod ℓ) := fun c i =>
    if i = 0 then ((eW c.1 : W) : Fin 2 → ZMod ℓ) else ((eW c.2 : W) : Fin 2 → ZMod ℓ)
  have hmk0 : ∀ c, mk c 0 = ((eW c.1 : W) : Fin 2 → ZMod ℓ) := fun c => by simp [mk]
  have hmk1 : ∀ c, mk c 1 = ((eW c.2 : W) : Fin 2 → ZMod ℓ) := fun c => by simp [mk]
  have hmk : ∀ c : ZMod ℓ × ZMod ℓ, mk c ∈ I := by
    intro c
    apply (hIW _).mpr
    rw [Fin.forall_fin_two, hmk0, hmk1]
    exact ⟨(eW c.1).2, (eW c.2).2⟩
  let g : ZMod ℓ × ZMod ℓ → S := fun c =>
    ⟨EM.symm (mk c), by
      obtain ⟨m, hm, hφm⟩ := (hImem _).mp (hmk c)
      exact ⟨m, hm, by rw [← hφm, hEMs]⟩⟩
  have hg : ∀ c, (g c : M) = EM.symm (mk c) := fun c => rfl
  have hgf : ∀ P : S, g (f P) = P := by
    intro P
    apply Subtype.ext
    rw [hg, Equiv.symm_apply_eq]
    funext i
    revert i
    rw [Fin.forall_fin_two, hmk0, hmk1]
    simp [f]
  have hfg : ∀ c, f (g c) = c := by
    intro c
    obtain ⟨c1, c2⟩ := c
    simp only [f]
    have h0 : (⟨EM (g (c1, c2)).1 0, hrow (g (c1, c2)) 0⟩ : W) = eW c1 := by
      apply Subtype.ext
      show EM (g (c1, c2)).1 0 = _
      rw [hg, Equiv.apply_symm_apply, hmk0]
    have h1 : (⟨EM (g (c1, c2)).1 1, hrow (g (c1, c2)) 1⟩ : W) = eW c2 := by
      apply Subtype.ext
      show EM (g (c1, c2)).1 1 = _
      rw [hg, Equiv.apply_symm_apply, hmk1]
    rw [h0, h1, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  let e : ZMod ℓ × ZMod ℓ ≃ S := ⟨g, f, hfg, hgf⟩

  have hf_add : ∀ (P Q : S) (h : (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P.1 + Q.1 = ρ m P₀)),
      f ⟨P.1 + Q.1, h⟩ = f P + f Q := by
    intro P Q h
    have hW0 : (⟨EM (P.1 + Q.1) 0, hrow ⟨P.1 + Q.1, h⟩ 0⟩ : W) = ⟨EM P.1 0, hrow P 0⟩ + ⟨EM Q.1 0, hrow Q 0⟩ :=
      Subtype.ext (by simp only [Submodule.coe_add, hEMadd]; rfl)
    have hW1 : (⟨EM (P.1 + Q.1) 1, hrow ⟨P.1 + Q.1, h⟩ 1⟩ : W) = ⟨EM P.1 1, hrow P 1⟩ + ⟨EM Q.1 1, hrow Q 1⟩ :=
      Subtype.ext (by simp only [Submodule.coe_add, hEMadd]; rfl)
    simp only [f]
    rw [hW0, hW1, map_add, map_add, Prod.mk_add_mk]
  refine ⟨e, fun x y => ?_⟩

  have hmemxy : ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ (e x : M) + (e y : M) = ρ m P₀ := by
    obtain ⟨m, hm, hme⟩ := (e x).2
    obtain ⟨m', hm', hme'⟩ := (e y).2
    exact ⟨m + m', J.add_mem hm hm', by rw [hme, hme', ρ_add, AddMonoidHom.add_apply]⟩
  have key : f (e (x + y)) = f ⟨(e x : M) + (e y : M), hmemxy⟩ := by
    rw [hf_add, show f (e (x + y)) = x + y from hfg (x + y), show f (e x) = x from hfg x, show f (e y) = y from hfg y]
  have := congrArg g key
  rw [hgf, hgf] at this
  exact congrArg Subtype.val this

end PartA
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21 P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21.M2L"

end LOP29
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21 P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.ASM21.M2L"

open LOP29

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = AddMonoidHom.id M)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
    (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) :

    (∀ J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) →
      (∃ e : ZMod ℓ × ZMod ℓ ≃ {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)},
          ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)}) : M) = (e x : M) + (e y : M)) ∧
      (∀ (n : ↥Λ) (P : M), (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ ρ n P = ρ m P₀))) ∧

    (∀ J J' : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) → (J' ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J') ∧ (∀ m ∈ Λ, ∀ x ∈ J', m * x ∈ J') ∧
          (∃ x ∈ J', ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J' ≠ Λ) → J ≠ J' →
      ∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J' ∧ P = ρ m P₀) → P = 0) ∧

    (∀ S : AddSubgroup M, (∀ (n : ↥Λ) (P : M), P ∈ S → ρ n P ∈ S) →
      (∃ e : ZMod ℓ × ZMod ℓ ≃ S, ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : S) : M) = (e x : M) + (e y : M)) →
      ∃! J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) ∧ ∀ P : M, P ∈ S ↔ (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)) ∧

    (∀ T : AddSubgroup M, (∀ (n : ↥Λ) (P : M), P ∈ T → ρ n P ∈ T) →
      ∀ J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) →
        (∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → P ∈ T → P = 0) ∨ (∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → P ∈ T)) := by
  classical
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ := exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  have hord : IsOrder Λ := hΛ.isOrder
  have hC3 := (QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq hqq' hB Λ hΛ ℓ hℓq hℓq').2
  refine ⟨?partA, ?partB, ?partC, ?partD⟩
  case partA =>
    intro J hJ
    refine ⟨partA_equiv Λ hord ℓ M ρ ρ_mul ρ_add P₀ hgen hann φ hφmul hφsurj hφker J hJ, ?_⟩
    rintro n P ⟨m, hm, rfl⟩
    exact ⟨⟨(n : ℍ[ℚ, a, b]) * m, hord.mul_mem n.2 m.2⟩, hJ.2.2.1 _ n.2 _ hm,
      (rho_mul_apply Λ hord M ρ ρ_mul n m P₀).symm⟩
  case partB =>
    rintro J J' ⟨hJΛ, hℓJ, hleftJ, -, hJne⟩ ⟨hJ'Λ, hℓJ', hleftJ', -, hJ'ne⟩ hne P ⟨m, hmJ, rfl⟩ ⟨m', hm'J', he⟩
    have hmJ' : (m : ℍ[ℚ, a, b]) ∈ J' := mem_of_rho_eq Λ ℓ M ρ ρ_add P₀ hann φ hφker J' hℓJ' m m' hm'J' he
    obtain ⟨z, hz, hmz⟩ := hC3 J J' hJΛ hℓJ hleftJ hJ'Λ hℓJ' hleftJ' hJne hJ'ne hne m hmJ hmJ'
    have : m = (ℓ : ℤ) • (⟨z, hz⟩ : ↥Λ) := Subtype.ext (by rw [hmz]; rfl)
    rw [this]
    exact rho_zsmul_ell Λ ℓ M ρ P₀ hann ⟨z, hz⟩
  case partC =>
    intro S hS hSe
    obtain ⟨e, he⟩ := hSe

    let J : Submodule ℤ ℍ[ℚ, a, b] :=
      { carrier := {x | ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) = x ∧ ρ m P₀ ∈ S}
        zero_mem' := ⟨0, rfl, by rw [← ev_apply Λ M ρ ρ_add P₀, map_zero]; exact S.zero_mem⟩
        add_mem' := by
          rintro _ _ ⟨m, rfl, hm⟩ ⟨m', rfl, hm'⟩
          exact ⟨m + m', rfl, by rw [← ev_apply Λ M ρ ρ_add P₀, map_add]; exact S.add_mem hm hm'⟩
        smul_mem' := by
          rintro c _ ⟨m, rfl, hm⟩
          exact ⟨c • m, rfl, by rw [← ev_apply Λ M ρ ρ_add P₀, map_zsmul]; exact S.zsmul_mem hm c⟩ }
    have hJmem' : ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ↔ ρ m P₀ ∈ S := by
      intro m
      constructor
      · rintro ⟨m₁, h1, h2⟩; rw [Subtype.ext h1] at h2; exact h2
      · intro h; exact ⟨m, rfl, h⟩
    have hJΛ : J ≤ Λ := by rintro x ⟨m, rfl, -⟩; exact m.2
    have hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := fun y hy =>
      ⟨(ℓ : ℤ) • (⟨y, hy⟩ : ↥Λ), rfl, by rw [rho_zsmul_ell Λ ℓ M ρ P₀ hann]; exact S.zero_mem⟩
    have hleftJ : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
      rintro n hn x ⟨m, rfl, hm⟩
      refine ⟨⟨n * m, hord.mul_mem hn m.2⟩, rfl, ?_⟩
      rw [rho_mul_apply Λ hord M ρ ρ_mul ⟨n, hn⟩ m P₀]
      exact hS _ _ hm
    have himg : ∀ P : M, P ∈ S ↔ ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀ := by
      intro P
      constructor
      · intro hP
        obtain ⟨m, rfl⟩ := hgen P
        exact ⟨m, (hJmem' m).mpr hP, rfl⟩
      · rintro ⟨m, hm, rfl⟩; exact (hJmem' m).mp hm

    have he0 : ((e 0 : ↥S) : M) = 0 := by
      have h := he 0 0
      rw [add_zero] at h

      have : ((e 0 : ↥S) : M) + ((e 0 : ↥S) : M) = ((e 0 : ↥S) : M) + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel this
    have hne0 : ((e (1, 0) : ↥S) : M) ≠ 0 := by
      intro h0
      have : e (1, 0) = e 0 := Subtype.ext (h0.trans he0.symm)
      have h10 : ((1, 0) : ZMod ℓ × ZMod ℓ) = 0 := e.injective this
      exact one_ne_zero (Prod.mk.inj h10).1

    have hcardS : Nat.card ↥S = ℓ ^ 2 := by
      rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card, pow_two]
    have hcardM := natCard_M Λ ℓ M ρ ρ_add P₀ hgen hann φ hφsurj hφker
    have hℓ2 : ℓ ^ 2 ≠ ℓ ^ 4 := by
      intro h
      have := Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le h
      omega
    refine ⟨J, ⟨⟨hJΛ, hℓJ, hleftJ, ?_, ?_⟩, himg⟩, ?_⟩
    ·
      obtain ⟨m, hm⟩ := hgen ((e (1, 0) : ↥S) : M)
      refine ⟨m, (hJmem' m).mpr (hm ▸ (e (1, 0)).2), ?_⟩
      rintro ⟨y, hy, hmy⟩
      apply hne0
      rw [hm]
      have : m = (ℓ : ℤ) • (⟨y, hy⟩ : ↥Λ) := Subtype.ext (by rw [hmy]; rfl)
      rw [this]
      exact rho_zsmul_ell Λ ℓ M ρ P₀ hann ⟨y, hy⟩
    ·
      intro hJtop
      apply hℓ2
      rw [← hcardS, ← hcardM]
      have hStop : S = ⊤ := by
        rw [eq_top_iff]
        intro P _
        obtain ⟨m, rfl⟩ := hgen P
        exact (hJmem' m).mp (hJtop.symm ▸ m.2 : (m : ℍ[ℚ, a, b]) ∈ J)
      rw [hStop]
      exact Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup M) ≃+ M).toEquiv
    ·
      rintro J' ⟨⟨hJ'Λ, hℓJ', hleftJ', -, -⟩, himg'⟩
      ext x
      constructor
      · intro hx
        have hxS : ρ ⟨x, hJ'Λ hx⟩ P₀ ∈ S := (himg' _).mpr ⟨⟨x, hJ'Λ hx⟩, hx, rfl⟩
        exact ⟨⟨x, hJ'Λ hx⟩, rfl, hxS⟩
      · rintro ⟨m, rfl, hm⟩
        obtain ⟨m', hm', he'⟩ := (himg' _).mp hm
        exact mem_of_rho_eq Λ ℓ M ρ ρ_add P₀ hann φ hφker J' hℓJ' m m' hm' he'
  case partD =>
    rintro T hT J ⟨hJΛ, hℓJ, hleftJ, ⟨x₀, hx₀J, hx₀⟩, hJne⟩

    let I := idealImg Λ hord ℓ φ hφmul hφsurj J hleftJ
    let I' : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :=
      { carrier := {A | ∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ ρ m P₀ ∈ T ∧ φ m = A}
        zero_mem' := ⟨0, J.zero_mem, by rw [← ev_apply Λ M ρ ρ_add P₀, map_zero]; exact T.zero_mem, map_zero φ⟩
        add_mem' := by
          rintro _ _ ⟨m, hm, hmT, rfl⟩ ⟨m', hm', hm'T, rfl⟩
          exact ⟨m + m', J.add_mem hm hm', by rw [← ev_apply Λ M ρ ρ_add P₀, map_add]; exact T.add_mem hmT hm'T,
            map_add φ m m'⟩
        smul_mem' := by
          rintro A _ ⟨m, hm, hmT, rfl⟩
          obtain ⟨n, rfl⟩ := hφsurj A
          refine ⟨⟨(n : ℍ[ℚ, a, b]) * m, hord.mul_mem n.2 m.2⟩, hleftJ _ n.2 _ hm, ?_, by rw [hφmul, smul_eq_mul]⟩
          rw [rho_mul_apply Λ hord M ρ ρ_mul n m P₀]
          exact hT _ _ hmT }
    have hI'le : I' ≤ I := by rintro A ⟨m, hm, -, rfl⟩; exact ⟨m, hm, rfl⟩

    have hIbot : I ≠ ⊥ := by
      intro hb
      have hx₀Λ := hJΛ hx₀J
      have : φ ⟨x₀, hx₀Λ⟩ ∈ I := ⟨⟨x₀, hx₀Λ⟩, hx₀J, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      obtain ⟨y, hy⟩ := (hφker _).mp this
      exact hx₀ ⟨y, y.2, by rw [zsmul_eq_coe_mul, coe_mul_eq_ratsmul]; exact hy⟩
    have hItop : I ≠ ⊤ := by
      intro ht
      apply hJne
      apply le_antisymm hJΛ
      intro y hy
      have : φ ⟨y, hy⟩ ∈ I := ht.symm ▸ Submodule.mem_top
      exact mem_of_phi_mem_idealImg Λ hord ℓ φ hφmul hφsurj hφker J hℓJ hleftJ ⟨y, hy⟩ this
    have hW1 : ASM21.M2L.rowSp I ≠ ⊥ := fun h =>
      hIbot (by rw [← ASM21.M2L.idealOf_rowSp I, h, ← ASM21.M2L.rowSp_bot, ASM21.M2L.idealOf_rowSp])
    have hW2 : ASM21.M2L.rowSp I ≠ ⊤ := fun h =>
      hItop (by rw [← ASM21.M2L.idealOf_rowSp I, h, ← ASM21.M2L.rowSp_top, ASM21.M2L.idealOf_rowSp])
    obtain ⟨v, hv, hWv⟩ := ASM21.M2L.exists_eq_span hW1 hW2
    rw [Projectivization.submodule_mk] at hWv
    have hW'le : ASM21.M2L.rowSp I' ≤ Submodule.span (ZMod ℓ) {v} := by
      rw [← hWv]; intro x hx; exact hI'le hx
    rcases eq_bot_or_eq_of_le_span ℓ hv _ hW'le with hbot | htop
    ·
      left
      rintro P ⟨m, hm, rfl⟩ hPT
      have hA : φ m ∈ I' := ⟨m, hm, hPT, rfl⟩
      rw [← ASM21.M2L.idealOf_rowSp I', hbot, ASM21.M2L.idealOf_bot, Submodule.mem_bot] at hA
      exact (rho_eq_zero_iff_phi Λ ℓ M ρ P₀ hann φ hφker m).mpr hA
    ·
      right
      rintro P ⟨m, hm, rfl⟩
      have hII' : I = I' := by
        rw [← ASM21.M2L.idealOf_rowSp I, ← ASM21.M2L.idealOf_rowSp I', hWv, htop]
      have hA : φ m ∈ I' := hII' ▸ (⟨m, hm, rfl⟩ : φ m ∈ I)
      obtain ⟨m₁, hm₁, hm₁T, he⟩ := hA
      rw [(rho_eq_iff_phi Λ ℓ M ρ ρ_add P₀ hann φ hφker m m₁).mpr he.symm]
      exact hm₁T

end S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification (solution)
