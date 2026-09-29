-- Prove2me | solution 1 for WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/09c1c655-3b33-5668-9057-89fa2c9ea695

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
import Theorems.Thm_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
import Theorems.Thm_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups

namespace P2MKcORB

section Scalars

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M]

theorem nsmul_eq_of_modEq {P : A} (hP : M • P = 0) {a b : ℕ} (h : a ≡ b [MOD M]) : a • P = b • P := by
  have key : ∀ c : ℕ, c • P = (c % M) • P := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c M]
    rw [add_nsmul, mul_comm, mul_nsmul', hP, nsmul_zero, add_zero]
  rw [key a, key b, h]

theorem nsmul_eq_zero_of_dvd {P : A} (hP : M • P = 0) {a : ℕ} (h : M ∣ a) : a • P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_comm, mul_nsmul', hP, nsmul_zero]

def usmul (u : (ZMod M)ˣ) (P : A) : A := (u : ZMod M).val • P

theorem usmul_def (u : (ZMod M)ˣ) (P : A) : usmul u P = (u : ZMod M).val • P := rfl

theorem torsion_usmul {P : A} (hP : M • P = 0) (u : (ZMod M)ˣ) : M • usmul u P = 0 := by
  rw [usmul_def, ← mul_nsmul', mul_comm, mul_nsmul', hP, nsmul_zero]

theorem usmul_mul {P : A} (hP : M • P = 0) (u v : (ZMod M)ˣ) :
    usmul (u * v) P = usmul u (usmul v P) := by
  rw [usmul_def, usmul_def, usmul_def, ← mul_nsmul', Units.val_mul, ZMod.val_mul]
  exact nsmul_eq_of_modEq hP (Nat.mod_modEq _ _)

theorem usmul_one {P : A} (hP : M • P = 0) : usmul (1 : (ZMod M)ˣ) P = P := by
  rw [usmul_def, Units.val_one, ZMod.val_one_eq_one_mod, nsmul_eq_of_modEq hP (Nat.mod_modEq 1 M), one_nsmul]

theorem usmul_neg {P : A} (hP : M • P = 0) (u : (ZMod M)ˣ) : usmul (-u) P = -usmul u P := by
  rw [eq_neg_iff_add_eq_zero, usmul_def, usmul_def, ← add_nsmul]
  apply nsmul_eq_zero_of_dvd hP
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  simp

theorem usmul_inv_usmul {P : A} (hP : M • P = 0) (u : (ZMod M)ˣ) : usmul u⁻¹ (usmul u P) = P := by
  rw [← usmul_mul hP, inv_mul_cancel, usmul_one hP]

theorem map_usmul {B : Type*} [AddCommGroup B] (φ : A →+ B) (u : (ZMod M)ˣ) (P : A) :
    φ (usmul u P) = usmul u (φ P) := by
  rw [usmul_def, usmul_def, map_nsmul]

theorem neg_usmul (u : (ZMod M)ˣ) (P : A) : -usmul u P = usmul u (-P) := by
  rw [usmul_def, usmul_def, neg_nsmul]

variable (H : Subgroup (ZMod M)ˣ)

abbrev Hpm : Subgroup (ZMod M)ˣ := H ⊔ Subgroup.zpowers (-1)

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ Hpm H :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem neg_mem_Hpm {u : (ZMod M)ˣ} (hu : u ∈ Hpm H) : -u ∈ Hpm H := by
  rw [← neg_one_mul]; exact Subgroup.mul_mem _ (neg_one_mem_Hpm H) hu

theorem le_Hpm : H ≤ Hpm H := le_sup_left

theorem exists_of_mem_Hpm {u : (ZMod M)ˣ} (hu : u ∈ Hpm H) : ∃ h ∈ H, u = h ∨ u = -h := by
  rw [Subgroup.mem_sup] at hu
  obtain ⟨y, hy, z, hz, rfl⟩ := hu
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  refine ⟨y, hy, ?_⟩
  have h2 : (-1 : (ZMod M)ˣ) ^ (2 : ℤ) = 1 := by rw [zpow_two, neg_one_mul, neg_neg]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow, mul_one]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, mul_neg_one]

def orbH (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

theorem mem_orbH_iff (P T : A) : T ∈ orbH H P ↔ ∃ u : (ZMod M)ˣ, u ∈ Hpm H ∧ T = usmul u P := Iff.rfl

theorem self_mem_orbH {P : A} (hP : M • P = 0) : P ∈ orbH H P := ⟨1, one_mem _, (usmul_one hP).symm⟩

theorem orbH_eq_of_mem {P T : A} (hP : M • P = 0) (hT : T ∈ orbH H P) : orbH H T = orbH H P := by
  rw [mem_orbH_iff] at hT
  obtain ⟨u₀, hu₀, rfl⟩ := hT
  ext Q
  rw [mem_orbH_iff, mem_orbH_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u * u₀, Subgroup.mul_mem _ hu hu₀, (usmul_mul hP u u₀).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u * u₀⁻¹, Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hu₀), ?_⟩
    rw [usmul_mul (torsion_usmul hP u₀), usmul_inv_usmul hP]

theorem torsion_of_addOrderOf {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

variable (A M) in

abbrev XX : Type _ :=
  {s : Set A // ∃ P : A, addOrderOf P = M ∧
    s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}}

noncomputable def gen (s : XX A M H) : A := Classical.choose s.2

theorem gen_spec (s : XX A M H) : addOrderOf (gen H s) = M ∧ s.1 = orbH H (gen H s) :=
  Classical.choose_spec s.2

theorem gen_mem (s : XX A M H) : gen H s ∈ s.1 := by
  rw [(gen_spec H s).2]; exact self_mem_orbH H (torsion_of_addOrderOf (gen_spec H s).1)

theorem eq_iff_gen_mem (s s' : XX A M H) : s = s' ↔ gen H s ∈ s'.1 := by
  constructor
  · rintro rfl; exact gen_mem H s
  · intro h
    apply Subtype.ext
    rw [(gen_spec H s).2, (gen_spec H s').2]
    rw [(gen_spec H s').2] at h
    exact orbH_eq_of_mem H (torsion_of_addOrderOf (gen_spec H s').1) h

def cls (P : A) (hP : addOrderOf P = M) : XX A M H := ⟨orbH H P, P, hP, rfl⟩

theorem gen_cls_mem (P : A) (hP : addOrderOf P = M) : gen H (cls H P hP) ∈ orbH H P :=
  gen_mem H (cls H P hP)

end Scalars

section Coord

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M]
variable (E : (Fin 2 → ZMod M) ≃+ Submodule.torsionBy ℤ A M)

def pt (v : Fin 2 → ZMod M) : A := (E v : A)

theorem pt_add (v v' : Fin 2 → ZMod M) : pt E (v + v') = pt E v + pt E v' := by
  simp [pt]

theorem pt_nsmul (n : ℕ) (v : Fin 2 → ZMod M) : pt E (n • v) = n • pt E v := by
  show ((E (n • v) : Submodule.torsionBy ℤ A M) : A) = n • (E v : A)
  rw [map_nsmul]
  simp

theorem pt_neg (v : Fin 2 → ZMod M) : pt E (-v) = -pt E v := by
  simp [pt]

theorem zsmul_eq_nsmul (c : ZMod M) (v : Fin 2 → ZMod M) : c • v = c.val • v := by
  ext i; simp [nsmul_eq_mul]

theorem pt_smul (h : (ZMod M)ˣ) (v : Fin 2 → ZMod M) : pt E ((h : ZMod M) • v) = usmul h (pt E v) := by
  rw [zsmul_eq_nsmul, pt_nsmul, usmul_def]

theorem pt_injective : Function.Injective (pt E) :=
  Subtype.val_injective.comp E.injective

theorem torsion_pt (v : Fin 2 → ZMod M) : M • pt E v = 0 := by
  have := (E v).2
  rw [Submodule.mem_torsionBy_iff] at this
  rw [pt, ← natCast_zsmul]
  exact this

theorem addOrderOf_pt (v : Fin 2 → ZMod M) : addOrderOf (pt E v) = addOrderOf v := by
  rw [pt]
  have h1 : addOrderOf ((E v : Submodule.torsionBy ℤ A M) : A) = addOrderOf (E v) :=
    addOrderOf_injective (Submodule.torsionBy ℤ A M).subtype.toAddMonoidHom Subtype.val_injective (E v)
  rw [h1, AddEquiv.addOrderOf_eq]

theorem exists_pt_eq {P : A} (hP : M • P = 0) : ∃ v, pt E v = P := by
  have hmem : P ∈ Submodule.torsionBy ℤ A M := by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hP
  exact ⟨E.symm ⟨P, hmem⟩, by rw [pt, AddEquiv.apply_symm_apply]⟩

end Coord

section Matrices

variable {M : ℕ} [NeZero M]

abbrev red (M : ℕ) : SL(2, ℤ) →* SL(2, ZMod M) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

def mv (γ : SL(2, ℤ)) (v : Fin 2 → ZMod M) : Fin 2 → ZMod M := (red M γ).1.mulVec v

theorem mv_mul (a b : SL(2, ℤ)) (v : Fin 2 → ZMod M) : mv (a * b) v = mv a (mv b v) := by
  rw [mv, mv, mv, map_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

theorem mv_one (v : Fin 2 → ZMod M) : mv 1 v = v := by
  rw [mv, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mv_smul (γ : SL(2, ℤ)) (c : ZMod M) (v : Fin 2 → ZMod M) : mv γ (c • v) = c • mv γ v := by
  rw [mv, mv, Matrix.mulVec_smul]

theorem mv_add (γ : SL(2, ℤ)) (v v' : Fin 2 → ZMod M) : mv γ (v + v') = mv γ v + mv γ v' := by
  rw [mv, mv, mv, Matrix.mulVec_add]

theorem mv_apply (γ : SL(2, ℤ)) (v : Fin 2 → ZMod M) (i : Fin 2) :
    mv γ v i = ((γ.1 i 0 : ℤ) : ZMod M) * v 0 + ((γ.1 i 1 : ℤ) : ZMod M) * v 1 := by
  simp [mv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mv_neg_one (v : Fin 2 → ZMod M) : mv (-1) v = -v := by
  ext i
  rw [mv_apply]
  fin_cases i <;> simp [Matrix.SpecialLinearGroup.coe_neg]

theorem mv_ST (v : Fin 2 → ZMod M) :
    mv (ModularGroup.S * ModularGroup.T) v = ![-v 1, v 0 + v 1] := by
  have hST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ext i
  rw [mv_apply]
  fin_cases i <;> simp [hST]

theorem mv_S (v : Fin 2 → ZMod M) : mv ModularGroup.S v = ![-v 1, v 0] := by
  ext i
  rw [mv_apply]
  fin_cases i <;> simp [ModularGroup.coe_S]

theorem ST_pow_three : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) ^ 3 = -1 := by
  ext i j
  rw [pow_succ, pow_two]
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem S_pow_two : (ModularGroup.S : SL(2, ℤ)) ^ 2 = -1 := by
  ext i j
  rw [pow_two]
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ST_pow_six : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, ST_pow_three]; simp

theorem S_pow_four : (ModularGroup.S : SL(2, ℤ)) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, S_pow_two]; simp

theorem exists_zpow_eq_pow {G : Type*} [Group G] (g : G) {N : ℕ} (hN : 0 < N) (hg : g ^ N = 1) (k : ℤ) :
    ∃ n : ℕ, g ^ k = g ^ n := by
  refine ⟨(k % N).toNat, ?_⟩
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have h0 : 0 ≤ k % N := Int.emod_nonneg _ hN'
  conv_lhs => rw [← Int.mul_ediv_add_emod k N]
  rw [zpow_add, zpow_mul, zpow_natCast, hg, one_zpow, one_mul, ← zpow_natCast, Int.toNat_of_nonneg h0]

variable {A : Type*} [AddCommGroup A]

def itHom (τ : A →+ A) : ℕ → (A →+ A)
  | 0 => AddMonoidHom.id A
  | k + 1 => (itHom τ k).comp τ

theorem itHom_apply (τ : A →+ A) (k : ℕ) (P : A) : itHom τ k P = τ^[k] P := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
    show itHom τ k (τ P) = τ^[k + 1] P
    rw [ih, Function.iterate_succ_apply]

theorem itHom_succ' (τ : A →+ A) (k : ℕ) (P : A) : itHom τ (k + 1) P = τ (itHom τ k P) := by
  rw [itHom_apply, itHom_apply, Function.iterate_succ_apply']

theorem itHom_neg (τ : A →+ A) (k : ℕ) (P : A) :
    itHom (-τ) k P = itHom τ k P ∨ itHom (-τ) k P = -itHom τ k P := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [itHom_succ', itHom_succ']
    rcases ih with h | h
    · right; rw [h, AddMonoidHom.neg_apply]
    · left; rw [h, AddMonoidHom.neg_apply, map_neg, neg_neg]

variable (E : (Fin 2 → ZMod M) ≃+ Submodule.torsionBy ℤ A M)

theorem itHom_pt (τ : A →+ A) (g : SL(2, ℤ)) (hτ : ∀ v, τ (pt E v) = pt E (mv g v)) (k : ℕ)
    (v : Fin 2 → ZMod M) : itHom τ k (pt E v) = pt E (mv (g ^ k) v) := by
  induction k generalizing v with
  | zero => rw [pow_zero, mv_one]; rfl
  | succ k ih =>
    show itHom τ k (τ (pt E v)) = pt E (mv (g ^ (k + 1)) v)
    rw [hτ, ih, pow_succ, mv_mul]

end Matrices

section Classify

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)
variable (E : (Fin 2 → ZMod M) ≃+ Submodule.torsionBy ℤ A M)

noncomputable def coord (s : XX A M H) : {v : Fin 2 → ZMod M // addOrderOf v = M} :=
  ⟨Classical.choose (exists_pt_eq E (torsion_of_addOrderOf (gen_spec H s).1)), by
    have h := Classical.choose_spec (exists_pt_eq E (torsion_of_addOrderOf (gen_spec H s).1))
    rw [← addOrderOf_pt E, h]
    exact (gen_spec H s).1⟩

theorem pt_coord (s : XX A M H) : pt E (coord H E s).1 = gen H s :=
  Classical.choose_spec (exists_pt_eq E (torsion_of_addOrderOf (gen_spec H s).1))

variable (τ : A →+ A) (g : SL(2, ℤ)) (hτ : ∀ v, τ (pt E v) = pt E (mv g v))
variable {k₀ N : ℕ} (hk₀ : g ^ k₀ = -1) (hN : 0 < N) (hgN : g ^ N = 1)

def RelT (s s' : XX A M H) : Prop :=
  ∃ (k : ℕ) (u : (ZMod M)ˣ), u ∈ Hpm H ∧ gen H s' = usmul u (itHom τ k (gen H s))

include hτ hk₀ hN hgN in

theorem rel_iff (s s' : XX A M H) :
    (∃ (k : ℤ) (h : (ZMod M)ˣ), h ∈ H ∧
      (coord H E s').1 = (h : ZMod M) • (red M (g ^ k)).1.mulVec (coord H E s).1) ↔ RelT H τ s s' := by
  constructor
  · rintro ⟨k, h, hh, hv⟩
    obtain ⟨n, hn⟩ := exists_zpow_eq_pow g hN hgN k
    refine ⟨n, h, le_Hpm H hh, ?_⟩
    rw [← pt_coord H E s', hv, pt_smul, hn, ← pt_coord H E s, itHom_pt E τ g hτ]
    rfl
  · rintro ⟨k, u, hu, hgen⟩
    obtain ⟨h, hh, hu'⟩ := exists_of_mem_Hpm H hu
    have key : ∀ (k' : ℕ) (h' : (ZMod M)ˣ), gen H s' = usmul h' (itHom τ k' (gen H s)) →
        (coord H E s').1 = (h' : ZMod M) • (red M (g ^ (k' : ℤ))).1.mulVec (coord H E s).1 := by
      intro k' h' hk'
      apply pt_injective E
      rw [pt_coord, hk', ← pt_coord H E s, itHom_pt E τ g hτ, pt_smul, zpow_natCast]
      rfl
    rcases hu' with hcase | hcase
    · exact ⟨k, h, hh, key k h (by rw [hgen, hcase])⟩
    · refine ⟨((k + k₀ : ℕ) : ℤ), h, hh, key (k + k₀) h ?_⟩
      have htor : M • itHom τ k (gen H s) = 0 := by
        rw [← map_nsmul, torsion_of_addOrderOf (gen_spec H s).1, map_zero]
      rw [hgen, hcase, usmul_neg htor, neg_usmul]
      congr 1
      rw [← pt_coord H E s, itHom_pt E τ g hτ, itHom_pt E τ g hτ, ← pt_neg, pow_add, hk₀,
        show g ^ k * -1 = -1 * g ^ k by rw [mul_neg_one, neg_one_mul], mv_mul, mv_neg_one]

include hτ hk₀ hN hgN in

theorem exists_classifying :
    ∃ c : XX A M H → DoubleCoset.Quotient (CohCarrier.GammaH M H : Set SL(2, ℤ))
        (Subgroup.zpowers g : Set SL(2, ℤ)),
      Function.Surjective c ∧ ∀ s s', c s = c s' ↔ RelT H τ s s' := by
  obtain ⟨c₀, hc₀s, hc₀⟩ := CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq M H g
  refine ⟨fun s => c₀ (coord H E s), ?_, fun s s' => (hc₀ _ _).trans (rel_iff H E τ g hτ hk₀ hN hgN s s')⟩
  intro q
  obtain ⟨v, rfl⟩ := hc₀s q

  have hv : addOrderOf (pt E v.1) = M := by rw [addOrderOf_pt]; exact v.2
  refine ⟨cls H (pt E v.1) hv, ?_⟩
  show c₀ (coord H E (cls H (pt E v.1) hv)) = c₀ v
  rw [eq_comm, hc₀]

  obtain ⟨u, hu, hgen⟩ := (mem_orbH_iff H _ _).1 (gen_cls_mem H (pt E v.1) hv)
  obtain ⟨h, hh, hu'⟩ := exists_of_mem_Hpm H hu
  have key : ∀ (k' : ℕ) (h' : (ZMod M)ˣ), gen H (cls H (pt E v.1) hv) = usmul h' (pt E (mv (g ^ k') v.1)) →
      (coord H E (cls H (pt E v.1) hv)).1 = (h' : ZMod M) • (red M (g ^ (k' : ℤ))).1.mulVec v.1 := by
    intro k' h' hk'
    apply pt_injective E
    rw [pt_coord, hk', pt_smul, zpow_natCast]
    rfl
  rcases hu' with hcase | hcase
  · exact ⟨(0 : ℕ), h, hh, key 0 h (by rw [hgen, hcase, pow_zero, mv_one])⟩
  · refine ⟨(k₀ : ℕ), h, hh, key k₀ h ?_⟩
    rw [hgen, hcase, usmul_neg (torsion_pt E v.1), neg_usmul, ← pt_neg, hk₀, mv_neg_one]

end Classify

section Card

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)
variable (E : (Fin 2 → ZMod M) ≃+ Submodule.torsionBy ℤ A M)

theorem gammaH_Hpm : CohCarrier.GammaH M (Hpm H) = CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1) := by
  have hneg0 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp
  have hnegu : CohCarrier.gamma0Units M ⟨-1, hneg0⟩ = -1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    simp [CongruenceSubgroup.Gamma0Map]
  apply le_antisymm
  · intro γ hγ
    obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    obtain ⟨h, hh, hcase⟩ := exists_of_mem_Hpm H hH
    rcases hcase with hc | hc
    · apply Subgroup.mem_sup_left
      exact CohCarrier.mem_GammaH_iff.mpr ⟨h0, hc ▸ hh⟩
    · have hprod : (-1 : SL(2, ℤ)) * γ ∈ CohCarrier.GammaH M H := by
        rw [CohCarrier.mem_GammaH_iff]
        refine ⟨(CongruenceSubgroup.Gamma0 M).mul_mem hneg0 h0, ?_⟩
        have : CohCarrier.gamma0Units M ⟨-1 * γ, (CongruenceSubgroup.Gamma0 M).mul_mem hneg0 h0⟩ =
            CohCarrier.gamma0Units M ⟨-1, hneg0⟩ * CohCarrier.gamma0Units M ⟨γ, h0⟩ :=
          map_mul (CohCarrier.gamma0Units M) ⟨-1, hneg0⟩ ⟨γ, h0⟩
        rw [this, hnegu, hc, neg_one_mul, neg_neg]
        exact hh
      have : γ = (-1 : SL(2, ℤ)) * ((-1 : SL(2, ℤ)) * γ) := by rw [← mul_assoc]; simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left hprod)
  · apply sup_le
    · intro γ hγ
      obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
      exact CohCarrier.mem_GammaH_iff.mpr ⟨h0, le_Hpm H hH⟩
    · rw [Subgroup.zpowers_le, CohCarrier.mem_GammaH_iff]
      exact ⟨hneg0, by rw [hnegu]; exact neg_one_mem_Hpm H⟩

theorem natCard_doubleCoset_bot {G : Type*} [Group G] (Γ : Subgroup G) :
    Nat.card (DoubleCoset.Quotient (Γ : Set G) ((Subgroup.zpowers (1 : G)) : Set G)) = Γ.index := by
  rw [Subgroup.zpowers_one_eq_bot]
  have hset : DoubleCoset.setoid (Γ : Set G) ((⊥ : Subgroup G) : Set G) = QuotientGroup.rightRel Γ :=
    Setoid.ext fun a b => by
      have := congrFun (congrFun (DoubleCoset.rel_bot_eq_right_group_rel Γ) a) b
      exact Iff.of_eq this
  rw [DoubleCoset.Quotient, hset, Subgroup.index]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)

theorem natCard_XX (E : (Fin 2 → ZMod M) ≃+ Submodule.torsionBy ℤ A M) :
    Nat.card (XX A M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by

  obtain ⟨c₀, hc₀s, hc₀⟩ :=
    CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq M (Hpm H) 1
  let c : XX A M H → _ := fun s => c₀ (coord H E s)
  have hrel : ∀ s s' : XX A M H, c s = c s' ↔ s = s' := by
    intro s s'
    show c₀ _ = c₀ _ ↔ _
    rw [hc₀]
    constructor
    · rintro ⟨k, h, hh, hv⟩
      refine ((eq_iff_gen_mem H s' s).2 ?_).symm
      rw [(gen_spec H s).2, mem_orbH_iff]
      refine ⟨h, hh, ?_⟩
      rw [← pt_coord H E s', hv, one_zpow, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
        pt_smul, pt_coord]
    · rintro rfl
      exact ⟨0, 1, one_mem _, by
        rw [zpow_zero, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Units.val_one, one_smul]⟩
  have hinj : Function.Injective c := fun s s' h => (hrel s s').1 h
  have hsurj : Function.Surjective c := by
    intro q
    obtain ⟨v, rfl⟩ := hc₀s q
    have hv : addOrderOf (pt E v.1) = M := by rw [addOrderOf_pt]; exact v.2
    refine ⟨cls H (pt E v.1) hv, ?_⟩
    show c₀ (coord H E (cls H (pt E v.1) hv)) = c₀ v
    rw [eq_comm, hc₀]
    obtain ⟨u, hu, hgen⟩ := (mem_orbH_iff H _ _).1 (gen_cls_mem H (pt E v.1) hv)
    refine ⟨0, u, hu, ?_⟩
    apply pt_injective E
    rw [pt_coord, hgen, zpow_zero, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, pt_smul]
  rw [Nat.card_congr (Equiv.ofBijective c ⟨hinj, hsurj⟩), ← gammaH_Hpm H]
  exact natCard_doubleCoset_bot _

end Card

section Curve

open WeierstrassCurve WeierstrassCurve.Affine

variable {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]

abbrev E₀ (L : Type*) [Field L] : WeierstrassCurve L := ⟨0, 0, 1, 0, 0⟩

theorem E₀_Δ : (E₀ L).Δ = 1 := by
  have h2 : (2 : L) = 0 := by simpa using CharP.cast_eq_zero L 2
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (-14 : L) * h2

scoped instance E₀_isElliptic : (E₀ L).IsElliptic := ⟨by rw [E₀_Δ]; exact isUnit_one⟩

variable {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem carries_iff {γ : VariableChange L} (φ : (E₀ L).toAffine.Point →+ (E₀ L).toAffine.Point)
    (hφ : ∀ P, HEq (Point.vcInvFun γ (E₀ L).toAffine P) (φ P))
    (s s' : XX (E₀ L).toAffine.Point M H) :
    (∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ (E₀ L).toAffine T) T') ↔ φ (gen H s) ∈ s'.1 := by
  constructor
  · intro h
    obtain ⟨T', hT', hh⟩ := h (gen H s) (gen_mem H s)
    have : φ (gen H s) = T' := eq_of_heq ((hφ _).symm.trans hh)
    rw [this]; exact hT'
  · intro hmem T hT
    refine ⟨φ T, ?_, hφ T⟩
    rw [(gen_spec H s).2, mem_orbH_iff] at hT
    obtain ⟨u, hu, rfl⟩ := hT
    rw [map_usmul]
    rw [(gen_spec H s').2] at hmem ⊢
    rw [← orbH_eq_of_mem H (torsion_of_addOrderOf (gen_spec H s').1) hmem]
    exact ⟨u, hu, rfl⟩

theorem relT_iff_of_sign (τ φ : (E₀ L).toAffine.Point →+ (E₀ L).toAffine.Point)
    (hsign : ∀ (k : ℕ) (P : (E₀ L).toAffine.Point),
      itHom φ k P = itHom τ k P ∨ itHom φ k P = -itHom τ k P)
    (s s' : XX (E₀ L).toAffine.Point M H) :
    RelT H τ s s' ↔ ∃ k : ℕ, itHom φ k (gen H s) ∈ s'.1 := by
  have htor : ∀ (ψ : (E₀ L).toAffine.Point →+ (E₀ L).toAffine.Point) (k : ℕ),
      M • itHom ψ k (gen H s) = 0 := fun ψ k => by
    rw [← map_nsmul, torsion_of_addOrderOf (gen_spec H s).1, map_zero]
  have hgen' := (gen_spec H s').2
  constructor
  · rintro ⟨k, u, hu, hgen⟩
    refine ⟨k, ?_⟩
    rw [hgen', mem_orbH_iff]
    rcases hsign k (gen H s) with h | h
    · refine ⟨u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
      rw [h, hgen, usmul_inv_usmul (htor τ k)]
    · refine ⟨-u⁻¹, neg_mem_Hpm H (Subgroup.inv_mem _ hu), ?_⟩
      rw [h, hgen, usmul_neg (torsion_usmul (htor τ k) u), usmul_inv_usmul (htor τ k)]
  · rintro ⟨k, hk⟩
    rw [hgen', mem_orbH_iff] at hk
    obtain ⟨u, hu, hk⟩ := hk
    rcases hsign k (gen H s) with h | h
    · refine ⟨k, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
      rw [← h, hk, usmul_inv_usmul (torsion_of_addOrderOf (gen_spec H s').1)]
    · refine ⟨k, -u⁻¹, neg_mem_Hpm H (Subgroup.inv_mem _ hu), ?_⟩
      have h' : itHom τ k (gen H s) = -itHom φ k (gen H s) := by rw [h, neg_neg]
      rw [h', hk, ← neg_usmul, usmul_neg (torsion_usmul (torsion_of_addOrderOf (gen_spec H s').1) u),
        neg_neg, usmul_inv_usmul (torsion_of_addOrderOf (gen_spec H s').1)]

variable (w : Lˣ) (hw : (w : L) ^ 3 = 1) (hw1 : (w : L) ≠ 1) (hM : (M : L) ≠ 0)
include hw hw1 hM

theorem main :
    Nat.card (XX (E₀ L).toAffine.Point M H) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ∧
    (∃ c : XX (E₀ L).toAffine.Point M H →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set SL(2, ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ)),
      Function.Surjective c ∧
      ∀ s s', c s = c s' ↔ ∃ k : ℕ, ∀ T ∈ s.1, ∃ T' ∈ s'.1,
        HEq (Point.vcInvFun ((⟨w, 0, 0, 0⟩ : VariableChange L) ^ k) (E₀ L).toAffine T) T') ∧
    (∃ c : XX (E₀ L).toAffine.Point M H →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set SL(2, ℤ))
          (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ)),
      Function.Surjective c ∧
      ∀ s s', c s = c s' ↔ ∃ k : ℕ, ∀ T ∈ s.1, ∃ T' ∈ s'.1,
        HEq (Point.vcInvFun ((⟨1, 1, 1, (w : L)⟩ : VariableChange L) ^ k) (E₀ L).toAffine T) T') := by

  obtain ⟨σ, ι, hσpow, hιpow, hσσ, hιι, hnsσ, hnsι⟩ :=
    WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two w hw hw1 M hM

  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := L) (K := L) (E₀ L) (n := M) hM
  have hb : ((E₀ L)⁄L) = (E₀ L).toAffine := by
    show ((E₀ L).baseChange L).toAffine = (E₀ L).toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at e

  have hnsσ' : ∀ p : ℕ, p.Prime → p ∣ M → ∃ a : (E₀ L).toAffine.Point,
      addOrderOf a = p ∧ ∀ k : ℕ, (-σ) a ≠ k • a := by
    intro p hp hpM
    obtain ⟨a, ha, hka⟩ := hnsσ p hp hpM
    refine ⟨a, ha, fun k hk => hka (k * (p - 1)) ?_⟩
    rw [AddMonoidHom.neg_apply, neg_eq_iff_eq_neg] at hk
    have hp1 : (p - 1) • a = -a := by
      have h0 : (p - 1 + 1) • a = 0 := by
        rw [Nat.sub_add_cancel hp.one_lt.le, ← ha]; exact addOrderOf_nsmul_eq_zero a
      rw [add_nsmul, one_nsmul, add_eq_zero_iff_eq_neg] at h0
      exact h0
    rw [hk, mul_nsmul', hp1, smul_neg]
  obtain ⟨em, hem⟩ := AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
    M e (-σ) hnsσ'
  obtain ⟨ep, hep⟩ := AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
    M e ι hnsι

  let f2 : (Fin 2 → ZMod M) ≃+ ZMod M × ZMod M := (LinearEquiv.finTwoArrow ℤ (ZMod M)).toAddEquiv
  have f2_apply : ∀ v : Fin 2 → ZMod M, f2 v = (v 0, v 1) := fun v => rfl
  let Em : (Fin 2 → ZMod M) ≃+ _ := f2.trans em
  let Ep : (Fin 2 → ZMod M) ≃+ _ := f2.trans ep

  have decomp : ∀ (E' : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ (E₀ L).toAffine.Point M)
      (v : Fin 2 → ZMod M),
      pt (f2.trans E') v = (v 0).val • (E' (1, 0) : (E₀ L).toAffine.Point) +
        (v 1).val • (E' (0, 1) : (E₀ L).toAffine.Point) := by
    intro E' v
    have hv : (v 0, v 1) = (v 0).val • ((1 : ZMod M), (0 : ZMod M)) + (v 1).val • ((0 : ZMod M), (1 : ZMod M)) := by
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.smul_mk, smul_zero, add_zero, nsmul_eq_mul, mul_one,
          ZMod.natCast_zmod_val]
      · simp only [Prod.snd_add, Prod.smul_mk, smul_zero, zero_add, nsmul_eq_mul, mul_one,
          ZMod.natCast_zmod_val]
    show ((E' (f2 v) : Submodule.torsionBy ℤ (E₀ L).toAffine.Point M) : (E₀ L).toAffine.Point) = _
    rw [f2_apply, hv, map_add, map_nsmul, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
      AddSubmonoidClass.coe_nsmul]

  have hστ : ∀ v, (-σ) (pt Em v) = pt Em (mv (ModularGroup.S * ModularGroup.T) v) := by
    intro v
    set v₀ : (E₀ L).toAffine.Point := (em (1, 0) : (E₀ L).toAffine.Point) with hv₀
    set w₀ : (E₀ L).toAffine.Point := (em (0, 1) : (E₀ L).toAffine.Point) with hw₀
    have h1 : (-σ) v₀ = w₀ := hem.symm
    have h2 : (-σ) w₀ = w₀ - v₀ := by
      rw [← h1, AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, map_neg, neg_neg, ← sub_eq_zero]
      have : σ (σ v₀) - (-σ v₀ - v₀) = σ (σ v₀) + σ v₀ + v₀ := by abel
      rw [this]
      exact hσσ v₀
    show (-σ) (pt (f2.trans em) v) = pt (f2.trans em) (mv (ModularGroup.S * ModularGroup.T) v)
    rw [decomp, decomp, mv_ST, map_add, map_nsmul, map_nsmul, ← hv₀, ← hw₀, h1, h2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

    have hMv : M • v₀ = 0 := by
      have := (em (1, 0)).2; rw [Submodule.mem_torsionBy_iff] at this
      rw [hv₀, ← natCast_zsmul]; exact this
    have hMw : M • w₀ = 0 := by
      have := (em (0, 1)).2; rw [Submodule.mem_torsionBy_iff] at this
      rw [hw₀, ← natCast_zsmul]; exact this
    have hneg : (-(v 1)).val • v₀ = -((v 1).val • v₀) := by
      rw [eq_neg_iff_add_eq_zero, ← add_nsmul]
      apply nsmul_eq_zero_of_dvd hMv
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp
    have hadd : (v 0 + v 1).val • w₀ = (v 0).val • w₀ + (v 1).val • w₀ := by
      rw [← add_nsmul]
      apply nsmul_eq_of_modEq hMw
      rw [ZMod.val_add]; exact Nat.mod_modEq _ _
    rw [hneg, hadd, nsmul_sub]
    abel

  have hιτ : ∀ v, ι (pt Ep v) = pt Ep (mv ModularGroup.S v) := by
    intro v
    set v₀ : (E₀ L).toAffine.Point := (ep (1, 0) : (E₀ L).toAffine.Point) with hv₀
    set w₀ : (E₀ L).toAffine.Point := (ep (0, 1) : (E₀ L).toAffine.Point) with hw₀
    have h1 : ι v₀ = w₀ := hep.symm
    have h2 : ι w₀ = -v₀ := by rw [← h1, hιι]
    show ι (pt (f2.trans ep) v) = pt (f2.trans ep) (mv ModularGroup.S v)
    rw [decomp, decomp, mv_S, map_add, map_nsmul, map_nsmul, ← hv₀, ← hw₀, h1, h2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hMv : M • v₀ = 0 := by
      have := (ep (1, 0)).2; rw [Submodule.mem_torsionBy_iff] at this
      rw [hv₀, ← natCast_zsmul]; exact this
    have hneg : (-(v 1)).val • v₀ = -((v 1).val • v₀) := by
      rw [eq_neg_iff_add_eq_zero, ← add_nsmul]
      apply nsmul_eq_zero_of_dvd hMv
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp
    rw [hneg, smul_neg]
    abel
  refine ⟨natCard_XX H Ep, ?_, ?_⟩
  · obtain ⟨c, hcs, hc⟩ := exists_classifying H Em (-σ) (ModularGroup.S * ModularGroup.T) hστ
      ST_pow_three (by norm_num : 0 < 6) ST_pow_six
    refine ⟨c, hcs, fun s s' => (hc s s').trans ?_⟩
    rw [relT_iff_of_sign H (-σ) σ (fun k P => ?_)]
    · refine exists_congr fun k => ?_
      rw [carries_iff H (itHom σ k) (fun P => ?_)]
      rw [itHom_apply]; exact hσpow k P
    · rcases itHom_neg σ k P with h | h
      · left; exact h.symm
      · right; rw [h, neg_neg]
  · obtain ⟨c, hcs, hc⟩ := exists_classifying H Ep ι ModularGroup.S hιτ S_pow_two (by norm_num : 0 < 4)
      S_pow_four
    refine ⟨c, hcs, fun s s' => (hc s s').trans ?_⟩
    rw [relT_iff_of_sign H ι ι (fun k P => Or.inl rfl)]
    refine exists_congr fun k => ?_
    rw [carries_iff H (itHom ι k) (fun P => ?_)]
    rw [itHom_apply]; exact hιpow k P

end Curve

end P2MKcORB
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two.P2MKcORB"

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (w : Lˣ) (hw : (w : L) ^ 3 = 1) (hw1 : (w : L) ≠ 1)
    (M : ℕ) [NeZero M] (hM : (M : L) ≠ 0) (H : Subgroup (ZMod M)ˣ) :
    Nat.card {s : Set (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
        ∃ P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf P = M ∧
          s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ∧
    (∃ c : {s : Set (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
          ∃ P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
            Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ s s', c s = c s' ↔ ∃ k : ℕ, ∀ T ∈ s.1, ∃ T' ∈ s'.1,
        HEq (Point.vcInvFun ((⟨w, 0, 0, 0⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine T) T') ∧
    (∃ c : {s : Set (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
          ∃ P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ s s', c s = c s' ↔ ∃ k : ℕ, ∀ T ∈ s.1, ∃ T' ∈ s'.1,
        HEq (Point.vcInvFun ((⟨1, 1, 1, (w : L)⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine T) T') :=
  P2MKcORB.main H w hw hw1 hM

end S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
end P2MW
export P2MW.S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two (solution)
