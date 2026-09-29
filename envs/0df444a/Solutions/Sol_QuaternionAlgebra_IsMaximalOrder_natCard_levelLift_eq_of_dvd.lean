-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.natCard_levelLift_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9ce6049a-f594-5992-b6e5-a0def4f90e0d

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_exists_module_matrix_zmod_smul_eq_of_linearMap
import Theorems.Thm_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace B14Lec

noncomputable section

abbrev Mat (ℓ : ℕ) : Type := Matrix (Fin 2) (Fin 2) (ZMod ℓ)

theorem zsmul_eq_coe_mul {a b : ℚ} (k : ℕ) (y : ℍ[ℚ, a, b]) :
    ((k : ℕ) : ℤ) • y = (((k : ℕ) : ℚ) : ℍ[ℚ, a, b]) * y := by
  rw [zsmul_eq_mul, Int.cast_natCast, ← QuaternionAlgebra.coe_natCast]

theorem zsmul_cancel {a b : ℚ} (k : ℕ) (hk : k ≠ 0) (x y : ℍ[ℚ, a, b])
    (h : ((k : ℕ) : ℤ) • x = ((k : ℕ) : ℤ) • y) : x = y := by
  rw [zsmul_eq_coe_mul, zsmul_eq_coe_mul, QuaternionAlgebra.coe_mul_eq_smul,
    QuaternionAlgebra.coe_mul_eq_smul] at h
  have hk' : ((k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have h2 := congrArg (fun z => ((k : ℕ) : ℚ)⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hk', one_smul] using h2

theorem zmod_torsion_iff (N ℓ : ℕ) [NeZero N] (hℓ : 0 < ℓ) (x : ZMod (N * ℓ)) :
    ℓ • x = 0 ↔ ∃ y : ZMod (N * ℓ), x = N • y := by
  haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) hℓ.ne'⟩
  constructor
  · intro h
    have hx : ((x.val : ℕ) : ZMod (N * ℓ)) = x := ZMod.natCast_zmod_val x
    rw [← hx, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    have h' : ℓ * N ∣ ℓ * x.val := (dvd_of_eq (Nat.mul_comm ℓ N)).trans h
    obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_left hℓ h'
    exact ⟨(c : ZMod (N * ℓ)), by rw [← hx, hc, Nat.cast_mul, nsmul_eq_mul]⟩
  · rintro ⟨y, rfl⟩
    rw [smul_smul]
    have e : ℓ * N = N * ℓ := Nat.mul_comm _ _
    rw [e, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem natCard_zmod_torsion (N ℓ : ℕ) [NeZero N] (hℓ : 0 < ℓ) :
    Nat.card {x : ZMod (N * ℓ) // ℓ • x = 0} = ℓ := by
  haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) hℓ.ne'⟩
  have hset : ∀ x : ZMod (N * ℓ), ℓ • x = 0 ↔ x ∈ AddSubgroup.zmultiples ((N : ℕ) : ZMod (N * ℓ)) := by
    intro x
    rw [zmod_torsion_iff N ℓ hℓ, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(y.val : ℤ), ?_⟩
      rw [nsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]; exact mul_comm _ _
    · rintro ⟨k, rfl⟩
      refine ⟨(k : ZMod (N * ℓ)), ?_⟩
      rw [nsmul_eq_mul, zsmul_eq_mul]; exact mul_comm _ _
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_zmultiples,
    ZMod.addOrderOf_coe _ (NeZero.ne _)]
  have hg : (N * ℓ).gcd N = N := Nat.gcd_eq_right (Dvd.intro ℓ rfl)
  rw [hg, Nat.mul_div_cancel_left ℓ (NeZero.pos N)]

structure Setup {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ N : ℕ) (M : Type) [AddCommGroup M] where
  hord : IsOrder Λ
  hℓN : ℓ ∣ N
  ρ : ↥Λ → M →+ M
  ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = AddMonoidHom.id M
  ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y)
  ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y
  P₀ : M
  hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀
  hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔
    ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((N * ℓ : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])
  φ : ↥Λ →ₗ[ℤ] Mat ℓ
  hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1
  hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y
  hφsurj : Function.Surjective φ
  hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])
  C : AddSubgroup M
  hC : ∀ (n : ↥Λ) (P : M), P ∈ C → ρ n P ∈ C
  cardC : Nat.card C = N ^ 2
  S₀ : AddSubgroup M
  hS₀ : ∀ (n : ↥Λ) (P : M), P ∈ S₀ → ρ n P ∈ S₀
  e₀ : ZMod (N * ℓ) × ZMod (N * ℓ) ≃+ S₀
  hS₀C : ∀ Q : M, Q ∈ S₀ → ℓ • Q ∈ C

def nsmulHom (M : Type) [AddCommGroup M] (k : ℕ) : M →+ M :=
  AddMonoidHom.mk' (fun P => k • P) (fun P Q => smul_add k P Q)

@[scoped simp] theorem nsmulHom_apply (M : Type) [AddCommGroup M] (k : ℕ) (P : M) : nsmulHom M k P = k • P := rfl

namespace Setup

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {ℓ N : ℕ} [hℓ : Fact ℓ.Prime] [NeZero N]
  {M : Type} [AddCommGroup M] (X : Setup Λ ℓ N M)

theorem ℓ_pos : 0 < ℓ := hℓ.out.pos
theorem ℓ_ne : ℓ ≠ 0 := hℓ.out.ne_zero

theorem rho_mul_apply (n m : ↥Λ) (P : M) :
    X.ρ ⟨(n : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), X.hord.mul_mem n.2 m.2⟩ P = X.ρ n (X.ρ m P) := by
  rw [X.ρ_mul]; rfl

theorem rho_one_apply (P : M) : X.ρ ⟨1, X.hord.one_mem⟩ P = P := by
  rw [X.ρ_one]; rfl

def ρhom : ↥Λ →+ (M →+ M) := AddMonoidHom.mk' X.ρ X.ρ_add

theorem ρhom_apply (m : ↥Λ) : X.ρhom m = X.ρ m := rfl

theorem rho_zero_apply (P : M) : X.ρ 0 P = 0 := by
  rw [← X.ρhom_apply, map_zero]; rfl

theorem rho_nsmul (k : ℕ) (m : ↥Λ) (P : M) : X.ρ (k • m) P = k • X.ρ m P := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, X.rho_zero_apply]
  | succ k ih => rw [succ_nsmul, succ_nsmul, X.ρ_add, AddMonoidHom.add_apply, ih]

theorem rho_natzsmul (k : ℕ) (m : ↥Λ) (P : M) : X.ρ (((k : ℕ) : ℤ) • m) P = k • X.ρ m P := by
  rw [natCast_zsmul, X.rho_nsmul]

theorem coe_natzsmul (k : ℕ) (m : ↥Λ) : (((((k : ℕ) : ℤ) • m) : ↥Λ) : ℍ[ℚ, a, b]) = ((k : ℕ) : ℤ) • (m : ℍ[ℚ, a, b]) :=
  Submodule.coe_smul _ _

theorem rho_P₀_eq_zero_iff (m : ↥Λ) :
    X.ρ m X.P₀ = 0 ↔ ∃ m' : ↥Λ, m = (((N * ℓ : ℕ)) : ℤ) • m' := by
  rw [X.hann]
  constructor
  · rintro ⟨m', h⟩
    exact ⟨m', Subtype.ext (by rw [coe_natzsmul, zsmul_eq_coe_mul]; exact h)⟩
  · rintro ⟨m', rfl⟩
    exact ⟨m', by rw [coe_natzsmul, zsmul_eq_coe_mul]⟩

theorem phi_eq_zero_iff (m : ↥Λ) : X.φ m = 0 ↔ ∃ m' : ↥Λ, m = ((ℓ : ℕ) : ℤ) • m' := by
  rw [X.hφker]
  constructor
  · rintro ⟨m', h⟩
    refine ⟨m', Subtype.ext ?_⟩
    rw [coe_natzsmul, zsmul_eq_coe_mul, QuaternionAlgebra.coe_mul_eq_smul]; exact h
  · rintro ⟨m', rfl⟩
    exact ⟨m', by rw [coe_natzsmul, zsmul_eq_coe_mul, QuaternionAlgebra.coe_mul_eq_smul]⟩

theorem Nℓ_smul_P₀ : (N * ℓ) • X.P₀ = 0 := by
  have : X.ρ (((N * ℓ : ℕ) : ℤ) • ⟨1, X.hord.one_mem⟩) X.P₀ = 0 :=
    (X.rho_P₀_eq_zero_iff _).mpr ⟨⟨1, X.hord.one_mem⟩, rfl⟩
  rwa [X.rho_natzsmul, X.rho_one_apply] at this

def T (X : Setup Λ ℓ N M) : AddSubgroup M := (nsmulHom M ℓ).ker

theorem mem_T (X : Setup Λ ℓ N M) (P : M) : P ∈ X.T ↔ ℓ • P = 0 := (nsmulHom M ℓ).mem_ker

theorem T_stable (n : ↥Λ) (P : M) (h : P ∈ X.T) : X.ρ n P ∈ X.T := by
  rw [X.mem_T] at h ⊢
  rw [← map_nsmul, h, map_zero]

def K₀ : AddSubgroup M := X.C ⊓ X.T

theorem mem_K₀ (P : M) : P ∈ X.K₀ ↔ P ∈ X.C ∧ ℓ • P = 0 := by
  rw [K₀, AddSubgroup.mem_inf, X.mem_T]

theorem K₀_stable (n : ↥Λ) (P : M) (h : P ∈ X.K₀) : X.ρ n P ∈ X.K₀ :=
  ⟨X.hC n P h.1, X.T_stable n P h.2⟩

theorem K₀_le_T : X.K₀ ≤ X.T := inf_le_right
theorem K₀_le_C : X.K₀ ≤ X.C := inf_le_left

theorem natCard_S₀ : Nat.card X.S₀ = (N * ℓ) ^ 2 := by
  rw [← Nat.card_congr X.e₀.toEquiv, Nat.card_prod, Nat.card_zmod]; ring

scoped instance finite_S₀ : Finite X.S₀ :=
  Nat.finite_of_card_ne_zero (by rw [X.natCard_S₀]; exact pow_ne_zero _ (Nat.mul_ne_zero (NeZero.ne N) ℓ_ne))

scoped instance finite_C : Finite X.C :=
  Nat.finite_of_card_ne_zero (by rw [X.cardC]; exact pow_ne_zero _ (NeZero.ne N))

theorem coe_nsmul_S₀ (k : ℕ) (P : X.S₀) : (((k • P) : X.S₀) : M) = k • (P : M) := rfl

theorem S₀_torsion (P : M) (hP : P ∈ X.S₀) (hℓP : ℓ • P = 0) : ∃ Q ∈ X.S₀, P = N • Q := by
  set v := X.e₀.symm ⟨P, hP⟩ with hv
  have hv0 : ℓ • v = 0 := by
    have : (ℓ • (⟨P, hP⟩ : X.S₀)) = 0 := Subtype.ext hℓP
    rw [hv, ← map_nsmul, this, map_zero]
  obtain ⟨y1, hy1⟩ := (zmod_torsion_iff N ℓ ℓ_pos v.1).mp (by rw [← Prod.smul_fst, hv0]; rfl)
  obtain ⟨y2, hy2⟩ := (zmod_torsion_iff N ℓ ℓ_pos v.2).mp (by rw [← Prod.smul_snd, hv0]; rfl)
  refine ⟨(X.e₀ (y1, y2) : M), (X.e₀ (y1, y2)).2, ?_⟩
  have h1 : v = N • (y1, y2) := Prod.ext (by rw [Prod.smul_fst]; exact hy1) (by rw [Prod.smul_snd]; exact hy2)
  have h2 : (⟨P, hP⟩ : X.S₀) = N • X.e₀ (y1, y2) := by
    rw [← map_nsmul, ← h1, hv, AddEquiv.apply_symm_apply]
  exact congrArg Subtype.val h2

theorem S₀_torsion_mem_C (P : M) (hP : P ∈ X.S₀) (hℓP : ℓ • P = 0) : P ∈ X.C := by
  obtain ⟨Q, hQ, rfl⟩ := X.S₀_torsion P hP hℓP
  obtain ⟨d, hd⟩ := X.hℓN
  have e : N • Q = d • (ℓ • Q) := by rw [smul_smul, Nat.mul_comm d ℓ, ← hd]
  rw [e]
  exact X.C.nsmul_mem (X.hS₀C Q hQ) d

theorem natCard_S₀_torsion : Nat.card {P : X.S₀ // ℓ • (P : M) = 0} = ℓ ^ 2 := by
  let e1 : {P : X.S₀ // ℓ • (P : M) = 0} ≃ {v : ZMod (N * ℓ) × ZMod (N * ℓ) // ℓ • v = 0} :=
    Equiv.subtypeEquiv X.e₀.symm.toEquiv (fun P => by
      show ℓ • (P : M) = 0 ↔ ℓ • X.e₀.symm P = 0
      rw [← map_nsmul, AddEquiv.map_eq_zero_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
  let e2 : {v : ZMod (N * ℓ) × ZMod (N * ℓ) // ℓ • v = 0} ≃
      {x : ZMod (N * ℓ) // ℓ • x = 0} × {x : ZMod (N * ℓ) // ℓ • x = 0} :=
    { toFun := fun v => (⟨v.1.1, by rw [← Prod.smul_fst, v.2]; rfl⟩, ⟨v.1.2, by rw [← Prod.smul_snd, v.2]; rfl⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), Prod.ext p.1.2 p.2.2⟩
      left_inv := fun v => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_prod, natCard_zmod_torsion N ℓ ℓ_pos, sq]

def mulℓ : X.S₀ →+ M := (nsmulHom M ℓ).comp X.S₀.subtype

theorem mulℓ_apply (P : X.S₀) : X.mulℓ P = ℓ • (P : M) := rfl

theorem range_mulℓ_le : X.mulℓ.range ≤ X.C := by
  rintro _ ⟨P, rfl⟩; exact X.hS₀C _ P.2

theorem natCard_ker_mulℓ : Nat.card X.mulℓ.ker = ℓ ^ 2 := by
  rw [← X.natCard_S₀_torsion]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun P => X.mulℓ.mem_ker))

theorem natCard_range_mulℓ : Nat.card X.mulℓ.range = N ^ 2 := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X.mulℓ.ker
  rw [X.natCard_S₀, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange X.mulℓ).toEquiv,
    X.natCard_ker_mulℓ, mul_pow] at h
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos ℓ_pos 2) h).symm

theorem range_mulℓ_eq : X.mulℓ.range = X.C :=
  AddSubgroup.eq_of_le_of_card_ge X.range_mulℓ_le (by rw [X.cardC, X.natCard_range_mulℓ])

theorem mem_C_iff (P : M) : P ∈ X.C ↔ ∃ Q ∈ X.S₀, P = ℓ • Q := by
  rw [← X.range_mulℓ_eq, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨Q, rfl⟩; exact ⟨Q, Q.2, rfl⟩
  · rintro ⟨Q, hQ, rfl⟩; exact ⟨⟨Q, hQ⟩, rfl⟩

theorem C_le_S₀ : X.C ≤ X.S₀ := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := (X.mem_C_iff P).mp hP
  exact X.S₀.nsmul_mem hQ ℓ

theorem mem_K₀_iff_S₀ (P : M) : P ∈ X.K₀ ↔ P ∈ X.S₀ ∧ ℓ • P = 0 := by
  rw [X.mem_K₀]
  constructor
  · rintro ⟨hC, hT⟩; exact ⟨X.C_le_S₀ hC, hT⟩
  · rintro ⟨hS, hT⟩; exact ⟨X.S₀_torsion_mem_C P hS hT, hT⟩

theorem natCard_K₀ : Nat.card X.K₀ = ℓ ^ 2 := by
  rw [← X.natCard_S₀_torsion]
  exact Nat.card_congr
    { toFun := fun P => ⟨⟨P.1, ((X.mem_K₀_iff_S₀ P.1).mp P.2).1⟩, ((X.mem_K₀_iff_S₀ P.1).mp P.2).2⟩
      invFun := fun Q => ⟨Q.1.1, (X.mem_K₀_iff_S₀ Q.1.1).mpr ⟨Q.1.2, Q.2⟩⟩
      left_inv := fun P => rfl
      right_inv := fun Q => rfl }

def χ : ↥Λ →+ M := AddMonoidHom.mk' (fun m => X.ρ m (N • X.P₀)) (fun x y => by
    show X.ρ (x + y) _ = _; rw [X.ρ_add]; rfl)

theorem χ_apply (m : ↥Λ) : X.χ m = N • X.ρ m X.P₀ := map_nsmul (X.ρ m) N X.P₀

theorem mem_range_χ_iff (P : M) : P ∈ X.χ.range ↔ P ∈ X.T := by
  rw [X.mem_T, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    rw [X.χ_apply, smul_smul, mul_comm, ← map_nsmul, X.Nℓ_smul_P₀, map_zero]
  · intro hP
    obtain ⟨m, rfl⟩ := X.hgen P
    rw [← X.rho_natzsmul] at hP
    obtain ⟨m', hm'⟩ := (X.rho_P₀_eq_zero_iff _).mp hP
    have : m = ((N : ℕ) : ℤ) • m' := by
      apply Subtype.ext
      apply zsmul_cancel ℓ ℓ_ne
      rw [← coe_natzsmul, hm', coe_natzsmul, coe_natzsmul, smul_smul, ← Nat.cast_mul,
        mul_comm]
    refine ⟨m', ?_⟩
    rw [this, X.rho_natzsmul, X.χ_apply]

theorem χ_eq_zero_iff (m : ↥Λ) : X.χ m = 0 ↔ X.φ m = 0 := by
  rw [X.χ_apply, ← X.rho_natzsmul, X.rho_P₀_eq_zero_iff, X.phi_eq_zero_iff]
  constructor
  · rintro ⟨m', hm'⟩
    refine ⟨m', Subtype.ext (zsmul_cancel N (NeZero.ne N) _ _ ?_)⟩
    rw [← coe_natzsmul, hm', coe_natzsmul, coe_natzsmul, smul_smul, ← Nat.cast_mul]
  · rintro ⟨m', rfl⟩
    exact ⟨m', by rw [smul_smul, ← Nat.cast_mul]⟩

theorem natCard_T : Nat.card X.T = ℓ ^ 4 := by
  have hker : X.χ.ker = X.φ.toAddMonoidHom.ker := by
    ext m; rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, X.χ_eq_zero_iff]; rfl
  have e1 : X.T ≃ X.χ.range := (Equiv.subtypeEquivRight (fun P => (X.mem_range_χ_iff P))).symm
  rw [Nat.card_congr e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange X.χ).toEquiv, hker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective X.φ.toAddMonoidHom X.hφsurj).toEquiv,
    Nat.card_eq_fintype_card]
  show Fintype.card (Fin 2 → Fin 2 → ZMod ℓ) = ℓ ^ 4
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]

scoped instance finite_T : Finite X.T :=
  Nat.finite_of_card_ne_zero (by rw [X.natCard_T]; exact pow_ne_zero _ ℓ_ne)

def IsLift (S : AddSubgroup M) : Prop :=
  (∀ (n : ↥Λ) (P : M), P ∈ S → X.ρ n P ∈ S) ∧
  (∀ P : M, P ∈ X.C ↔ ∃ Q ∈ S, P = ℓ • Q) ∧
  (∀ P : M, P ∈ S → ℓ • P = 0 → P ∈ X.C)

def Lifts : Type := {S : AddSubgroup M // X.IsLift S}

section IsLift

variable {S : AddSubgroup M} (hS : X.IsLift S)
include hS

theorem IsLift.C_le : X.C ≤ S := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := (hS.2.1 P).mp hP
  exact S.nsmul_mem hQ ℓ

theorem IsLift.mem_K₀ (P : M) (hP : P ∈ S) (h : ℓ • P = 0) : P ∈ X.K₀ :=
  (X.mem_K₀ P).mpr ⟨hS.2.2 P hP h, h⟩

theorem IsLift.K₀_le : X.K₀ ≤ S := fun P hP => IsLift.C_le X hS (X.K₀_le_C hP)

theorem IsLift.exists_pt (s₀ : M) (hs₀ : s₀ ∈ X.S₀) : ∃ s, s ∈ S ∧ ℓ • s = ℓ • s₀ := by
  obtain ⟨Q, hQ, hQe⟩ := (hS.2.1 (ℓ • s₀)).mp (X.hS₀C s₀ hs₀)
  exact ⟨Q, hQ, hQe.symm⟩

theorem IsLift.diff_mem_K₀ (s s' : M) (hs : s ∈ S) (hs' : s' ∈ S) (h : ℓ • s = ℓ • s') :
    s - s' ∈ X.K₀ :=
  IsLift.mem_K₀ X hS _ (S.sub_mem hs hs') (by rw [smul_sub, h, sub_self])

end IsLift

theorem sub_mem_T (s s₀ : M) (h : ℓ • s = ℓ • s₀) : s - s₀ ∈ X.T :=
  (X.mem_T _).mpr (by rw [smul_sub, h, sub_self])

def CS₀ : AddSubgroup X.S₀ := X.C.addSubgroupOf X.S₀

def KT : AddSubgroup X.T := X.K₀.addSubgroupOf X.T

abbrev U : Type := X.S₀ ⧸ X.CS₀
abbrev W : Type := X.T ⧸ X.KT

theorem mem_CS₀ (P : X.S₀) : P ∈ X.CS₀ ↔ (P : M) ∈ X.C := AddSubgroup.mem_addSubgroupOf
theorem mem_KT (P : X.T) : P ∈ X.KT ↔ (P : M) ∈ X.K₀ := AddSubgroup.mem_addSubgroupOf

theorem U_mk_eq_mk (s s' : X.S₀) :
    (QuotientAddGroup.mk s : X.U) = QuotientAddGroup.mk s' ↔ (s : M) - s' ∈ X.C := by
  rw [QuotientAddGroup.eq_iff_sub_mem, X.mem_CS₀, AddSubgroup.coe_sub]

theorem U_mk_eq_zero (s : X.S₀) : (QuotientAddGroup.mk s : X.U) = 0 ↔ (s : M) ∈ X.C := by
  rw [QuotientAddGroup.eq_zero_iff, X.mem_CS₀]

theorem W_mk_eq_mk (t t' : X.T) :
    (QuotientAddGroup.mk t : X.W) = QuotientAddGroup.mk t' ↔ (t : M) - t' ∈ X.K₀ := by
  rw [QuotientAddGroup.eq_iff_sub_mem, X.mem_KT, AddSubgroup.coe_sub]

theorem W_mk_eq_zero (t : X.T) : (QuotientAddGroup.mk t : X.W) = 0 ↔ (t : M) ∈ X.K₀ := by
  rw [QuotientAddGroup.eq_zero_iff, X.mem_KT]

def ρS₀ (n : ↥Λ) : X.S₀ →+ X.S₀ :=
  ((X.ρ n).comp X.S₀.subtype).codRestrict X.S₀ (fun P => X.hS₀ n P P.2)

def ρT (n : ↥Λ) : X.T →+ X.T :=
  ((X.ρ n).comp X.T.subtype).codRestrict X.T (fun P => X.T_stable n P P.2)

@[scoped simp] theorem coe_ρS₀ (n : ↥Λ) (P : X.S₀) : ((X.ρS₀ n P : X.S₀) : M) = X.ρ n P := rfl
@[scoped simp] theorem coe_ρT (n : ↥Λ) (P : X.T) : ((X.ρT n P : X.T) : M) = X.ρ n P := rfl

def actU (n : ↥Λ) : X.U →+ X.U :=
  QuotientAddGroup.map X.CS₀ X.CS₀ (X.ρS₀ n) (fun P hP => by
    rw [AddSubgroup.mem_comap, X.mem_CS₀, X.coe_ρS₀]
    exact X.hC n P ((X.mem_CS₀ P).mp hP))

def actW (n : ↥Λ) : X.W →+ X.W :=
  QuotientAddGroup.map X.KT X.KT (X.ρT n) (fun P hP => by
    rw [AddSubgroup.mem_comap, X.mem_KT, X.coe_ρT]
    exact X.K₀_stable n P ((X.mem_KT P).mp hP))

theorem actU_mk (n : ↥Λ) (P : X.S₀) : X.actU n (QuotientAddGroup.mk P) = QuotientAddGroup.mk (X.ρS₀ n P) :=
  QuotientAddGroup.map_mk _ _ _ _ _
theorem actW_mk (n : ↥Λ) (P : X.T) : X.actW n (QuotientAddGroup.mk P) = QuotientAddGroup.mk (X.ρT n P) :=
  QuotientAddGroup.map_mk _ _ _ _ _

theorem actU_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) : X.actU ⟨1, h⟩ = AddMonoidHom.id X.U := by
  refine AddMonoidHom.ext (fun u => ?_)
  induction u using QuotientAddGroup.induction_on with
  | H P =>
    rw [X.actU_mk, AddMonoidHom.id_apply]
    congr 1
    exact Subtype.ext (by rw [X.coe_ρS₀, X.ρ_one]; rfl)

theorem actW_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) : X.actW ⟨1, h⟩ = AddMonoidHom.id X.W := by
  refine AddMonoidHom.ext (fun w => ?_)
  induction w using QuotientAddGroup.induction_on with
  | H P =>
    rw [X.actW_mk, AddMonoidHom.id_apply]
    congr 1
    exact Subtype.ext (by rw [X.coe_ρT, X.ρ_one]; rfl)

theorem actU_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    X.actU ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (X.actU x).comp (X.actU y) := by
  refine AddMonoidHom.ext (fun u => ?_)
  induction u using QuotientAddGroup.induction_on with
  | H P =>
    rw [AddMonoidHom.comp_apply, X.actU_mk, X.actU_mk, X.actU_mk]
    congr 1
    exact Subtype.ext (by rw [X.coe_ρS₀, X.coe_ρS₀, X.coe_ρS₀, X.ρ_mul]; rfl)

theorem actW_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    X.actW ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (X.actW x).comp (X.actW y) := by
  refine AddMonoidHom.ext (fun w => ?_)
  induction w using QuotientAddGroup.induction_on with
  | H P =>
    rw [AddMonoidHom.comp_apply, X.actW_mk, X.actW_mk, X.actW_mk]
    congr 1
    exact Subtype.ext (by rw [X.coe_ρT, X.coe_ρT, X.coe_ρT, X.ρ_mul]; rfl)

theorem actU_add (x y : ↥Λ) : X.actU (x + y) = X.actU x + X.actU y := by
  refine AddMonoidHom.ext (fun u => ?_)
  induction u using QuotientAddGroup.induction_on with
  | H P =>
    rw [AddMonoidHom.add_apply, X.actU_mk, X.actU_mk, X.actU_mk, ← QuotientAddGroup.mk_add]
    congr 1
    exact Subtype.ext (by rw [AddSubgroup.coe_add, X.coe_ρS₀, X.coe_ρS₀, X.coe_ρS₀, X.ρ_add]; rfl)

theorem actW_add (x y : ↥Λ) : X.actW (x + y) = X.actW x + X.actW y := by
  refine AddMonoidHom.ext (fun w => ?_)
  induction w using QuotientAddGroup.induction_on with
  | H P =>
    rw [AddMonoidHom.add_apply, X.actW_mk, X.actW_mk, X.actW_mk, ← QuotientAddGroup.mk_add]
    congr 1
    exact Subtype.ext (by rw [AddSubgroup.coe_add, X.coe_ρT, X.coe_ρT, X.coe_ρT, X.ρ_add]; rfl)

theorem U_torsion (u : X.U) : ℓ • u = 0 := by
  induction u using QuotientAddGroup.induction_on with
  | H P =>
    rw [← QuotientAddGroup.mk_nsmul, X.U_mk_eq_zero]
    exact X.hS₀C _ P.2

theorem W_torsion (w : X.W) : ℓ • w = 0 := by
  induction w using QuotientAddGroup.induction_on with
  | H P =>
    rw [← QuotientAddGroup.mk_nsmul]
    have : ℓ • P = 0 := Subtype.ext ((X.mem_T P).mp P.2)
    rw [this, QuotientAddGroup.mk_zero]

theorem natCard_U : Nat.card X.U = ℓ ^ 2 := by
  have hCS : Nat.card X.CS₀ = N ^ 2 := by
    rw [← X.cardC]; exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe X.C_le_S₀).toEquiv
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X.CS₀
  rw [X.natCard_S₀, hCS, mul_pow, mul_comm] at h
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos N) 2) h).symm

theorem natCard_W : Nat.card X.W = ℓ ^ 2 := by
  have hKT : Nat.card X.KT = ℓ ^ 2 := by
    rw [← X.natCard_K₀]; exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe X.K₀_le_T).toEquiv
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X.KT
  rw [X.natCard_T, hKT, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring, mul_comm] at h
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos ℓ_pos 2) h).symm

scoped instance finite_U : Finite X.U := Nat.finite_of_card_ne_zero (by rw [X.natCard_U]; exact pow_ne_zero _ ℓ_ne)
scoped instance finite_W : Finite X.W := Nat.finite_of_card_ne_zero (by rw [X.natCard_W]; exact pow_ne_zero _ ℓ_ne)

def EqHom : Type := {g : X.U →+ X.W // ∀ (n : ↥Λ) (u : X.U), g (X.actU n u) = X.actW n (g u)}

section ToHom

variable {S : AddSubgroup M} (hS : X.IsLift S)

def IsLift.pt (s₀ : X.S₀) : M := Classical.choose (IsLift.exists_pt X hS s₀ s₀.2)

theorem IsLift.pt_mem (s₀ : X.S₀) : IsLift.pt X hS s₀ ∈ S :=
  (Classical.choose_spec (IsLift.exists_pt X hS s₀ s₀.2)).1

theorem IsLift.pt_eq (s₀ : X.S₀) : ℓ • IsLift.pt X hS s₀ = ℓ • (s₀ : M) :=
  (Classical.choose_spec (IsLift.exists_pt X hS s₀ s₀.2)).2

def IsLift.gRaw (s₀ : X.S₀) : X.W :=
  QuotientAddGroup.mk (⟨IsLift.pt X hS s₀ - s₀, X.sub_mem_T _ _ (IsLift.pt_eq X hS s₀)⟩ : X.T)

theorem IsLift.gRaw_spec (s₀ : X.S₀) (s : M) (hs : s ∈ S) (h : ℓ • s = ℓ • (s₀ : M)) :
    IsLift.gRaw X hS s₀ = QuotientAddGroup.mk (⟨s - s₀, X.sub_mem_T s s₀ h⟩ : X.T) := by
  rw [IsLift.gRaw, X.W_mk_eq_mk]
  have e : (IsLift.pt X hS s₀ - (s₀ : M)) - (s - s₀) = IsLift.pt X hS s₀ - s := by abel
  show (IsLift.pt X hS s₀ - (s₀ : M)) - (s - s₀) ∈ X.K₀
  rw [e]
  exact IsLift.diff_mem_K₀ X hS _ _ (IsLift.pt_mem X hS s₀) hs ((IsLift.pt_eq X hS s₀).trans h.symm)

def IsLift.gHom : X.S₀ →+ X.W :=
  AddMonoidHom.mk' (IsLift.gRaw X hS) (fun s₀ s₀' => by
    have hs : IsLift.pt X hS s₀ + IsLift.pt X hS s₀' ∈ S := S.add_mem (IsLift.pt_mem X hS s₀) (IsLift.pt_mem X hS s₀')
    have he : ℓ • (IsLift.pt X hS s₀ + IsLift.pt X hS s₀') = ℓ • ((s₀ + s₀' : X.S₀) : M) := by
      rw [smul_add, IsLift.pt_eq, IsLift.pt_eq, AddSubgroup.coe_add, smul_add]
    rw [IsLift.gRaw_spec X hS (s₀ + s₀') _ hs he, IsLift.gRaw, IsLift.gRaw, ← QuotientAddGroup.mk_add]
    congr 1
    apply Subtype.ext
    simp only [AddSubgroup.coe_add]
    abel)

theorem IsLift.gHom_apply (s₀ : X.S₀) : IsLift.gHom X hS s₀ = IsLift.gRaw X hS s₀ := rfl

theorem IsLift.gHom_C (s₀ : X.S₀) (h : (s₀ : M) ∈ X.C) : IsLift.gHom X hS s₀ = 0 := by
  rw [IsLift.gHom_apply, IsLift.gRaw_spec X hS s₀ s₀ (IsLift.C_le X hS h) rfl, X.W_mk_eq_zero]
  show (s₀ : M) - s₀ ∈ X.K₀
  rw [sub_self]; exact X.K₀.zero_mem

def IsLift.gU : X.U →+ X.W :=
  QuotientAddGroup.lift X.CS₀ (IsLift.gHom X hS) (fun s₀ hs₀ =>
    (AddMonoidHom.mem_ker).mpr (IsLift.gHom_C X hS s₀ ((X.mem_CS₀ s₀).mp hs₀)))

theorem IsLift.gU_mk (s₀ : X.S₀) : IsLift.gU X hS (QuotientAddGroup.mk s₀) = IsLift.gRaw X hS s₀ :=
  QuotientAddGroup.lift_mk' _ _ _

theorem IsLift.gU_mk_spec (s₀ : X.S₀) (s : M) (hs : s ∈ S) (h : ℓ • s = ℓ • (s₀ : M)) :
    IsLift.gU X hS (QuotientAddGroup.mk s₀) = QuotientAddGroup.mk (⟨s - s₀, X.sub_mem_T s s₀ h⟩ : X.T) := by
  rw [IsLift.gU_mk, IsLift.gRaw_spec X hS s₀ s hs h]

theorem IsLift.gU_equivariant (n : ↥Λ) (u : X.U) : IsLift.gU X hS (X.actU n u) = X.actW n (IsLift.gU X hS u) := by
  induction u using QuotientAddGroup.induction_on with
  | H s₀ =>
    have hs : X.ρ n (IsLift.pt X hS s₀) ∈ S := hS.1 n _ (IsLift.pt_mem X hS s₀)
    have he : ℓ • X.ρ n (IsLift.pt X hS s₀) = ℓ • ((X.ρS₀ n s₀ : X.S₀) : M) := by
      rw [X.coe_ρS₀, ← map_nsmul, IsLift.pt_eq, map_nsmul]
    rw [X.actU_mk, IsLift.gU_mk_spec X hS _ _ hs he, IsLift.gU_mk, IsLift.gRaw, X.actW_mk]
    congr 1
    apply Subtype.ext
    simp only [X.coe_ρT, X.coe_ρS₀, map_sub]

def toEqHom (S : X.Lifts) : X.EqHom := ⟨IsLift.gU X S.2, IsLift.gU_equivariant X S.2⟩

end ToHom

section OfHom

variable (g : X.EqHom)

def SOf : AddSubgroup M where
  carrier := {x | ∃ (s₀ : X.S₀) (t : X.T), x = (s₀ : M) + (t : M) ∧
    (QuotientAddGroup.mk t : X.W) = g.1 (QuotientAddGroup.mk s₀)}
  zero_mem' := ⟨0, 0, by simp, by rw [QuotientAddGroup.mk_zero, QuotientAddGroup.mk_zero, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨s, t, rfl, hst⟩ ⟨s', t', rfl, hst'⟩
    refine ⟨s + s', t + t', ?_, ?_⟩
    · simp only [AddSubgroup.coe_add]; abel
    · rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add, map_add, hst, hst']
  neg_mem' := by
    rintro _ ⟨s, t, rfl, hst⟩
    refine ⟨-s, -t, ?_, ?_⟩
    · simp only [AddSubgroup.coe_neg]; abel
    · rw [QuotientAddGroup.mk_neg, QuotientAddGroup.mk_neg, map_neg, hst]

theorem mem_SOf (x : M) : x ∈ X.SOf g ↔ ∃ (s₀ : X.S₀) (t : X.T), x = (s₀ : M) + (t : M) ∧
    (QuotientAddGroup.mk t : X.W) = g.1 (QuotientAddGroup.mk s₀) := Iff.rfl

theorem SOf_isLift : X.IsLift (X.SOf g) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro n _ ⟨s, t, rfl, hst⟩
    refine ⟨X.ρS₀ n s, X.ρT n t, by rw [map_add, X.coe_ρS₀, X.coe_ρT], ?_⟩
    rw [← X.actW_mk, ← X.actU_mk, hst, g.2]
  · intro P
    constructor
    · intro hP
      obtain ⟨s, hs, rfl⟩ := (X.mem_C_iff P).mp hP
      obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (g.1 (QuotientAddGroup.mk (⟨s, hs⟩ : X.S₀)))
      refine ⟨s + t, ⟨⟨s, hs⟩, t, rfl, ht⟩, ?_⟩
      rw [smul_add, (X.mem_T _).mp t.2, add_zero]
    · rintro ⟨Q, ⟨s, t, rfl, -⟩, rfl⟩
      rw [smul_add, (X.mem_T _).mp t.2, add_zero]
      exact X.hS₀C _ s.2
  · rintro _ ⟨s, t, rfl, hst⟩ h
    rw [smul_add, (X.mem_T _).mp t.2, add_zero] at h
    have hsC : (s : M) ∈ X.C := X.S₀_torsion_mem_C _ s.2 h
    rw [(X.U_mk_eq_zero s).mpr hsC, map_zero, X.W_mk_eq_zero] at hst
    exact X.C.add_mem hsC (X.K₀_le_C hst)

def ofEqHom : X.Lifts := ⟨X.SOf g, X.SOf_isLift g⟩

end OfHom

theorem SOf_toEqHom (S : X.Lifts) : X.SOf (X.toEqHom S) = S.1 := by
  ext x
  rw [X.mem_SOf]
  constructor
  · rintro ⟨s₀, t, rfl, hst⟩

    change (QuotientAddGroup.mk t : X.W) = IsLift.gU X S.2 (QuotientAddGroup.mk s₀) at hst
    rw [IsLift.gU_mk, IsLift.gRaw, X.W_mk_eq_mk] at hst
    have hk : (t : M) - (IsLift.pt X S.2 s₀ - s₀) ∈ S.1 := IsLift.K₀_le X S.2 hst
    have : (s₀ : M) + t = IsLift.pt X S.2 s₀ + ((t : M) - (IsLift.pt X S.2 s₀ - s₀)) := by abel
    rw [this]
    exact S.1.add_mem (IsLift.pt_mem X S.2 s₀) hk
  · intro hx
    have hC : ℓ • x ∈ X.C := by
      rw [(S.2).2.1]; exact ⟨x, hx, rfl⟩
    obtain ⟨s₀, hs₀, he⟩ := (X.mem_C_iff _).mp hC
    refine ⟨⟨s₀, hs₀⟩, ⟨x - s₀, X.sub_mem_T x s₀ he⟩, by simp, ?_⟩
    change _ = IsLift.gU X S.2 (QuotientAddGroup.mk (⟨s₀, hs₀⟩ : X.S₀))
    rw [IsLift.gU_mk_spec X S.2 ⟨s₀, hs₀⟩ x hx he]

theorem toEqHom_ofEqHom (g : X.EqHom) : X.toEqHom (X.ofEqHom g) = g := by
  apply Subtype.ext
  refine AddMonoidHom.ext (fun u => ?_)
  induction u using QuotientAddGroup.induction_on with
  | H s₀ =>
    change IsLift.gU X (X.SOf_isLift g) (QuotientAddGroup.mk s₀) = g.1 (QuotientAddGroup.mk s₀)
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (g.1 (QuotientAddGroup.mk s₀))
    have hs : (s₀ : M) + t ∈ X.SOf g := ⟨s₀, t, rfl, ht⟩
    have he : ℓ • ((s₀ : M) + t) = ℓ • (s₀ : M) := by rw [smul_add, (X.mem_T _).mp t.2, add_zero]
    rw [IsLift.gU_mk_spec X (X.SOf_isLift g) s₀ _ hs he, ← ht]
    congr 1
    exact Subtype.ext (by simp)

def liftsEquiv : X.Lifts ≃ X.EqHom where
  toFun := X.toEqHom
  invFun := X.ofEqHom
  left_inv S := Subtype.ext (X.SOf_toEqHom S)
  right_inv g := X.toEqHom_ofEqHom g

def eqHomEquivLinear [Module (Mat ℓ) X.U] [Module (Mat ℓ) X.W]
    (hU : ∀ (m : ↥Λ) (u : X.U), X.φ m • u = X.actU m u)
    (hW : ∀ (m : ↥Λ) (w : X.W), X.φ m • w = X.actW m w) : X.EqHom ≃ (X.U →ₗ[Mat ℓ] X.W) where
  toFun g :=
    { toFun := g.1
      map_add' := map_add g.1
      map_smul' := fun r u => by
        obtain ⟨m, rfl⟩ := X.hφsurj r
        rw [RingHom.id_apply, hU, hW, g.2] }
  invFun f := ⟨f.toAddMonoidHom, fun m u => by
    rw [← hU, ← hW, LinearMap.toAddMonoidHom_coe, map_smul]⟩
  left_inv g := rfl
  right_inv f := rfl

end Setup
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.B14Lec.Setup"

theorem natCard_linearMap_eq (ℓ : ℕ) [Fact ℓ.Prime] (U W : Type) [AddCommGroup U] [Module (Mat ℓ) U]
    [AddCommGroup W] [Module (Mat ℓ) W] [Finite U] [Finite W]
    (hU : Nat.card U = ℓ ^ 2) (hW : Nat.card W = ℓ ^ 2) : Nat.card (U →ₗ[Mat ℓ] W) = ℓ := by
  have hUU : Nat.card (U × U) = ℓ ^ 4 := by rw [Nat.card_prod, hU, ← pow_add]
  obtain ⟨e⟩ := Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_four ℓ (U × U) hUU
  haveI : Finite (U →ₗ[Mat ℓ] W) :=
    Finite.of_injective (fun f : U →ₗ[Mat ℓ] W => (f : U → W)) DFunLike.coe_injective

  let e1 : (U × U →ₗ[Mat ℓ] W) ≃ (U →ₗ[Mat ℓ] W) × (U →ₗ[Mat ℓ] W) :=
    { toFun := fun h => (h.comp (LinearMap.inl (Mat ℓ) U U), h.comp (LinearMap.inr (Mat ℓ) U U))
      invFun := fun p => p.1.coprod p.2
      left_inv := fun h => by
        apply LinearMap.ext
        rintro ⟨u, v⟩
        rw [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.inl_apply,
          LinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
      right_inv := fun p => by rw [Prod.mk.injEq]; exact ⟨LinearMap.coprod_inl _ _, LinearMap.coprod_inr _ _⟩ }

  let e2 : (U × U →ₗ[Mat ℓ] W) ≃ (Mat ℓ →ₗ[Mat ℓ] W) :=
    { toFun := fun h => h.comp e.symm.toLinearMap
      invFun := fun h => h.comp e.toLinearMap
      left_inv := fun h => by apply LinearMap.ext; intro x; simp
      right_inv := fun h => by apply LinearMap.ext; intro x; simp }
  let e3 : (Mat ℓ →ₗ[Mat ℓ] W) ≃ W :=
    { toFun := fun h => h 1
      invFun := fun w => LinearMap.toSpanSingleton (Mat ℓ) W w
      left_inv := fun h => by
        apply LinearMap.ext; intro r
        rw [LinearMap.toSpanSingleton_apply, ← map_smul, smul_eq_mul, mul_one]
      right_inv := fun w => by
        show LinearMap.toSpanSingleton (Mat ℓ) W w 1 = w
        rw [LinearMap.toSpanSingleton_apply, one_smul] }
  have key : Nat.card (U →ₗ[Mat ℓ] W) ^ 2 = ℓ ^ 2 := by
    rw [sq, ← Nat.card_prod, ← Nat.card_congr e1, Nat.card_congr e2, Nat.card_congr e3, hW]
  exact Nat.pow_left_injective two_ne_zero key

namespace Setup

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {ℓ N : ℕ} [hℓ : Fact ℓ.Prime] [NeZero N]
  {M : Type} [AddCommGroup M] (X : Setup Λ ℓ N M)

theorem natCard_lifts : Nat.card X.Lifts = ℓ := by
  obtain ⟨instU, hU⟩ := QuaternionAlgebra.exists_module_matrix_zmod_smul_eq_of_linearMap Λ ℓ X.φ X.hφ1 X.hφmul
    X.hφsurj X.hφker X.hord.one_mem (fun x y => X.hord.mul_mem x.2 y.2) X.U X.U_torsion X.actU
    (X.actU_one _) (fun x y => X.actU_mul x y _) X.actU_add
  obtain ⟨instW, hW⟩ := QuaternionAlgebra.exists_module_matrix_zmod_smul_eq_of_linearMap Λ ℓ X.φ X.hφ1 X.hφmul
    X.hφsurj X.hφker X.hord.one_mem (fun x y => X.hord.mul_mem x.2 y.2) X.W X.W_torsion X.actW
    (X.actW_one _) (fun x y => X.actW_mul x y _) X.actW_add
  letI := instU
  letI := instW
  rw [Nat.card_congr X.liftsEquiv, Nat.card_congr (X.eqHomEquivLinear hU hW)]
  exact natCard_linearMap_eq ℓ X.U X.W X.natCard_U X.natCard_W

end Setup
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.B14Lec.Setup"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.B14Lec.Setup"

end B14Lec
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.B14Lec.Setup P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.B14Lec"

open B14Lec

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') {N : ℕ} [NeZero N] (hℓN : ℓ ∣ N)
    (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = AddMonoidHom.id M)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
    (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔
      ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((N * ℓ : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
    (C : AddSubgroup M) (hC : ∀ (n : ↥Λ) (P : M), P ∈ C → ρ n P ∈ C)
    (eC : ZMod N × ZMod N ≃ C) (heC : ∀ x y : ZMod N × ZMod N, ((eC (x + y) : C) : M) = (eC x : M) + (eC y : M))
    (S₀ : AddSubgroup M) (hS₀ : ∀ (n : ↥Λ) (P : M), P ∈ S₀ → ρ n P ∈ S₀)
    (eS₀ : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ S₀)
    (heS₀ : ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ), ((eS₀ (x + y) : S₀) : M) = (eS₀ x : M) + (eS₀ y : M))
    (hS₀C : ∀ Q : M, Q ∈ S₀ → ℓ • Q ∈ C) :
    Nat.card {S : AddSubgroup M //
        (∀ (n : ↥Λ) (P : M), P ∈ S → ρ n P ∈ S) ∧
        (∀ P : M, P ∈ C ↔ ∃ Q ∈ S, P = ℓ • Q) ∧
        (∀ P : M, P ∈ S → ℓ • P = 0 → P ∈ C)} = ℓ := by
  classical
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  have cardC : Nat.card C = N ^ 2 := by
    rw [← Nat.card_congr eC, Nat.card_prod, Nat.card_zmod, sq]
  let e₀ : ZMod (N * ℓ) × ZMod (N * ℓ) ≃+ S₀ :=
    AddEquiv.mk' eS₀ (fun x y => Subtype.ext (by rw [AddSubgroup.coe_add]; exact heS₀ x y))
  let X : Setup Λ ℓ N M :=
    { hord := hΛ.isOrder, hℓN := hℓN, ρ := ρ, ρ_one := ρ_one, ρ_mul := ρ_mul, ρ_add := ρ_add, P₀ := P₀,
      hgen := hgen, hann := hann, φ := φ, hφ1 := hφ1, hφmul := hφmul, hφsurj := hφsurj, hφker := hφker,
      C := C, hC := hC, cardC := cardC, S₀ := S₀, hS₀ := hS₀, e₀ := e₀, hS₀C := hS₀C }
  exact X.natCard_lifts

end S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd (solution)
