-- Prove2me | solution 1 for WeierstrassCurve.natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/50435fb6-4407-564b-b7b2-0fa3681963cc

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_nsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair.WeierstrassCurve WeierstrassCurve.Affine"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map toAffine baseChange rationalHomSet comp_mem_rationalHomSet surjective_of_mem_rationalHomSet exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero exists_nsmul_eq_of_isAlgClosed card_torsion_of_isAlgClosed_light"
namespace DualPairCount
p2m_open "WeierstrassCurve"

section Group

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem exists_zmultiples_eq (C : AddSubgroup G) (hC : IsAddCyclic C) (n : ℕ) (hn : Nat.card C = n) :
    ∃ P : G, AddSubgroup.zmultiples P = C ∧ addOrderOf P = n := by
  obtain ⟨P, hP⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC
  refine ⟨P, hP, ?_⟩
  rw [← Nat.card_zmultiples, hP, hn]

theorem nsmul_id_apply (n : ℕ) (T : G) : (n • AddMonoidHom.id G) T = n • T := rfl

theorem map_nsmul_zmultiples (n : ℕ) (P : G) :
    (AddSubgroup.zmultiples P).map (n • AddMonoidHom.id G) = AddSubgroup.zmultiples (n • P) := by
  rw [AddMonoidHom.map_zmultiples]; rfl

theorem mem_map_nsmul_iff (n : ℕ) (A : AddSubgroup G) (T : G) :
    T ∈ A.map (n • AddMonoidHom.id G) ↔ ∃ S ∈ A, n • S = T := by
  simp only [AddSubgroup.mem_map, nsmul_id_apply]

theorem map_nsmul_le (n : ℕ) (A : AddSubgroup G) : A.map (n • AddMonoidHom.id G) ≤ A := by
  rintro T ⟨S, hS, rfl⟩
  exact A.nsmul_mem hS n

theorem addOrderOf_nsmul_of_mul {P : G} {m n : ℕ} (hn : n ≠ 0) (h : addOrderOf P = m * n) :
    addOrderOf (n • P) = m := by
  rw [addOrderOf_nsmul' P hn, h, Nat.gcd_eq_right (dvd_mul_left n m), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn)]

variable {N ℓ : ℕ}

theorem cyclic_map_nsmul_ell (hℓ : ℓ ≠ 0) (C : AddSubgroup G) (hC : IsAddCyclic C ∧ Nat.card C = N * ℓ) :
    IsAddCyclic (C.map (ℓ • AddMonoidHom.id G)) ∧ Nat.card (C.map (ℓ • AddMonoidHom.id G)) = N := by
  obtain ⟨P, rfl, hP⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  rw [map_nsmul_zmultiples]
  exact ⟨inferInstance, by rw [Nat.card_zmultiples, addOrderOf_nsmul_of_mul hℓ hP]⟩

theorem cyclic_map_nsmul_N (hN : N ≠ 0) (C : AddSubgroup G) (hC : IsAddCyclic C ∧ Nat.card C = N * ℓ) :
    IsAddCyclic (C.map (N • AddMonoidHom.id G)) ∧ Nat.card (C.map (N • AddMonoidHom.id G)) = ℓ := by
  obtain ⟨P, rfl, hP⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  rw [map_nsmul_zmultiples]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zmultiples, addOrderOf_nsmul_of_mul hN]
  rw [hP, Nat.mul_comm]

theorem mem_map_N_of_nsmul_eq_zero (hN : N ≠ 0) (hℓ : ℓ ≠ 0) (C : AddSubgroup G)
    (hC : IsAddCyclic C ∧ Nat.card C = N * ℓ) {S : G} (hS : S ∈ C) (hℓS : ℓ • S = 0) :
    S ∈ C.map (N • AddMonoidHom.id G) := by
  obtain ⟨P, hPC, hP⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  rw [← hPC] at hS ⊢
  rw [map_nsmul_zmultiples]
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hS
  have h1 : ((ℓ : ℤ) * k) • P = 0 := by rw [mul_smul, natCast_zsmul]; exact hℓS
  have hdvd : ((N * ℓ : ℕ) : ℤ) ∣ (ℓ : ℤ) * k := by
    rw [← hP]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
  push_cast at hdvd
  rw [mul_comm (N : ℤ)] at hdvd
  obtain ⟨m, hm⟩ := (mul_dvd_mul_iff_left (by exact_mod_cast hℓ : (ℓ : ℤ) ≠ 0)).mp hdvd
  rw [hm, mul_comm (N : ℤ) m, mul_smul, natCast_zsmul]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) m

theorem natCard_comap_of_le_range (f : G →+ H) (A : AddSubgroup H) (hA : A ≤ f.range) :
    Nat.card (A.comap f) = Nat.card A * Nat.card f.ker := by
  set B := A.comap f with hB
  let g : B →+ A := (f.comp B.subtype).codRestrict A (fun b => b.2)
  have hg : Function.Surjective g := by
    rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := hA ha
    exact ⟨⟨x, ha⟩, rfl⟩
  have hker : g.ker = f.ker.addSubgroupOf B := by
    ext b
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hle : f.ker ≤ B := fun x hx => by
    show f x ∈ A
    rw [AddMonoidHom.mem_ker.mp hx]; exact A.zero_mem
  have e1 : B ⧸ g.ker ≃+ A := QuotientAddGroup.quotientKerEquivOfSurjective g hg
  have e2 : g.ker ≃+ f.ker := by
    rw [hker]; exact AddSubgroup.addSubgroupOfEquivOfLe hle
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, Nat.card_congr e1.toEquiv,
    Nat.card_congr e2.toEquiv]

theorem zmultiples_eq_of_prime_card (hℓ : ℓ.Prime) (K : AddSubgroup G) (hK : Nat.card K = ℓ) {Q : G} (hQ : Q ∈ K)
    (hQ0 : Q ≠ 0) : AddSubgroup.zmultiples Q = K := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hℓ.ne_zero)
  apply AddSubgroup.eq_of_le_of_card_ge ((AddSubgroup.zmultiples_le_of_mem) hQ)
  rw [hK, Nat.card_zmultiples]
  have hdvd : addOrderOf Q ∣ ℓ := hK ▸ AddSubgroup.addOrderOf_dvd_natCard K hQ
  rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h1
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hQ0
  · rw [h1]

theorem isAddCyclic_comap (hℓ : ℓ.Prime) (hN : N ≠ 0) (f : G →+ H) (C : AddSubgroup H)
    (hC : IsAddCyclic C ∧ Nat.card C = N)
    (hBcard : Nat.card (C.comap f) = N * ℓ) (hK : Nat.card f.ker = ℓ)
    (honto : ∀ T ∈ C, ∃ S, f S = T)
    (htors : ∀ S ∈ C.comap f, ℓ • S = 0 → S ∈ f.ker) :
    IsAddCyclic (C.comap f) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set B := C.comap f with hB
  haveI : Finite B := Nat.finite_of_card_ne_zero (by rw [hBcard]; exact Nat.mul_ne_zero hN hℓ.ne_zero)
  obtain ⟨P₁, hP₁C, hP₁⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  have hKB : f.ker ≤ B := fun x hx => by
    show f x ∈ C
    rw [AddMonoidHom.mem_ker.mp hx]; exact C.zero_mem

  have key : ∀ S : G, f S = P₁ → f.ker ≤ AddSubgroup.zmultiples S → B = AddSubgroup.zmultiples S := by
    intro S hS hKS
    have hSB : S ∈ B := by show f S ∈ C; rw [hS, ← hP₁C]; exact AddSubgroup.mem_zmultiples P₁
    refine le_antisymm ?_ ((AddSubgroup.zmultiples_le_of_mem) hSB)
    intro P hP
    have hfP : f P ∈ AddSubgroup.zmultiples P₁ := by rw [hP₁C]; exact hP
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hfP
    have hmem : P - k • S ∈ f.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, map_zsmul, hS, hk, sub_self]
    have h2 : P = (P - k • S) + k • S := by abel
    rw [h2]
    exact AddSubgroup.add_mem _ (hKS hmem) (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples S) k)
  have hcyc_of : ∀ S : G, f S = P₁ → f.ker ≤ AddSubgroup.zmultiples S → IsAddCyclic B := by
    intro S hS hKS
    rw [key S hS hKS]
    infer_instance

  obtain ⟨S, hS⟩ := honto P₁ (by rw [← hP₁C]; exact AddSubgroup.mem_zmultiples P₁)
  have hSB : S ∈ B := by show f S ∈ C; rw [hS, ← hP₁C]; exact AddSubgroup.mem_zmultiples P₁
  have hordS : addOrderOf S ≠ 0 := by
    have h := addOrderOf_pos (⟨S, hSB⟩ : B)
    rw [← AddSubgroup.addOrderOf_coe] at h
    exact h.ne'
  by_cases hdvd : ℓ ∣ addOrderOf S
  ·
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact hordS hm
    have hordQ : addOrderOf (m • S) = ℓ := by
      rw [addOrderOf_nsmul' S hm0, hm, Nat.gcd_eq_right (dvd_mul_left m ℓ), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have hQ0 : m • S ≠ 0 := by
      intro h0
      have : addOrderOf (m • S) = 1 := by rw [h0, addOrderOf_zero]
      rw [hordQ] at this
      exact hℓ.one_lt.ne' this
    have hQK : m • S ∈ f.ker := htors _ (B.nsmul_mem hSB m) (by rw [← hordQ]; exact addOrderOf_nsmul_eq_zero _)
    have hKeq := zmultiples_eq_of_prime_card hℓ f.ker hK hQK hQ0
    refine hcyc_of S hS ?_
    rw [← hKeq]
    exact (AddSubgroup.zmultiples_le_of_mem) (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples S) m)
  ·
    have hKc : IsAddCyclic f.ker := isAddCyclic_of_prime_card hK
    obtain ⟨k, hkK, hk⟩ := exists_zmultiples_eq f.ker hKc _ hK
    have hkker : f k = 0 := by
      have : k ∈ f.ker := by rw [← hkK]; exact AddSubgroup.mem_zmultiples k
      exact this
    have hcop : (addOrderOf S).Coprime (addOrderOf k) := by
      rw [hk]; exact ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hdvd).symm
    have hord : addOrderOf (S + k) = addOrderOf S * ℓ := by
      rw [← hk]; exact (AddCommute.all S k).addOrderOf_add_eq_mul_addOrderOf_of_coprime hcop
    refine hcyc_of (S + k) (by rw [map_add, hS, hkker, add_zero]) ?_

    have h1 : addOrderOf S • (S + k) = addOrderOf S • k := by
      rw [nsmul_add, addOrderOf_nsmul_eq_zero, zero_add]
    have hordk' : addOrderOf (addOrderOf S • k) = ℓ := by
      rw [addOrderOf_nsmul' k hordS, Nat.Coprime.gcd_eq_one hcop.symm, Nat.div_one, hk]
    have hQ0 : addOrderOf S • k ≠ 0 := by
      intro h0
      have : addOrderOf (addOrderOf S • k) = 1 := by rw [h0, addOrderOf_zero]
      rw [hordk'] at this
      exact hℓ.one_lt.ne' this
    have hQK : addOrderOf S • k ∈ f.ker := f.ker.nsmul_mem (by rw [← hkK]; exact AddSubgroup.mem_zmultiples k) _
    have hKeq := zmultiples_eq_of_prime_card hℓ f.ker hK hQK hQ0
    rw [← hKeq, ← h1]
    exact (AddSubgroup.zmultiples_le_of_mem) (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _)

end Group

section Isogeny

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  {E E' : WeierstrassCurve κ} [E.IsElliptic] [E'.IsElliptic] {ℓ : ℕ}

theorem divisible (hℓκ : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) : ∃ T : E.toAffine.Point, ℓ • T = Q :=
  WeierstrassCurve.exists_nsmul_eq_of_isAlgClosed E ℓ hℓκ Q

def torsion (E : WeierstrassCurve κ) (ℓ : ℕ) : AddSubgroup E.toAffine.Point :=
  (Submodule.torsionBy ℤ E.toAffine.Point (ℓ : ℤ)).toAddSubgroup

theorem mem_torsion_iff (P : E.toAffine.Point) : P ∈ torsion E ℓ ↔ ℓ • P = 0 := by
  show P ∈ Submodule.torsionBy ℤ E.toAffine.Point (ℓ : ℤ) ↔ _
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

theorem natCard_torsion (hℓκ : (ℓ : κ) ≠ 0) : Nat.card (torsion E ℓ) = ℓ ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed_light (K := κ) E hℓκ

theorem comp_nsmul_id {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (n : ℕ) :
    f.comp (n • AddMonoidHom.id A) = (n • AddMonoidHom.id B).comp f := by
  ext P
  show f (n • P) = n • f P
  rw [map_nsmul]

section Pair

variable {ψ : E.toAffine.Point →+ E'.toAffine.Point} {ψ' : E'.toAffine.Point →+ E.toAffine.Point}

theorem dual_apply (hd : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (P : E.toAffine.Point) : ψ' (ψ P) = ℓ • P :=
  congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f P) hd

theorem ker_le_torsion (hd : ψ'.comp ψ = ℓ • AddMonoidHom.id _) : ψ.ker ≤ torsion E ℓ := by
  intro P hP
  rw [mem_torsion_iff, ← dual_apply hd P, AddMonoidHom.mem_ker.mp hP, map_zero]

theorem ne_zero_of_natCard_ker (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0) (hd : ψ'.comp ψ = ℓ • AddMonoidHom.id _)
    (hker : Nat.card ψ.ker = ℓ) : ψ ≠ 0 := by
  rintro rfl
  have htop : (0 : E.toAffine.Point →+ E'.toAffine.Point).ker = ⊤ := by
    ext P; simp
  have hle : (torsion E ℓ) ≤ (0 : E.toAffine.Point →+ E'.toAffine.Point).ker := by rw [htop]; exact le_top
  haveI : Finite (0 : E.toAffine.Point →+ E'.toAffine.Point).ker :=
    Nat.finite_of_card_ne_zero (by rw [hker]; exact hℓ.ne_zero)
  have h1 := AddSubgroup.card_le_of_le hle
  rw [natCard_torsion hℓκ, hker] at h1
  have h2 : ℓ < ℓ ^ 2 := by
    have := hℓ.two_le
    nlinarith
  omega

theorem surjective_of_ne_zero (hψ : ψ ∈ rationalHomSet κ E E') (h0 : ψ ≠ 0) : Function.Surjective ψ :=
  WeierstrassCurve.surjective_of_mem_rationalHomSet (F := κ) κ (W₁ := E) (W₂ := E') hψ h0

theorem dual_ne_zero (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0) (hd' : ψ.comp ψ' = ℓ • AddMonoidHom.id _) : ψ' ≠ 0 := by
  rintro rfl
  rw [AddMonoidHom.comp_zero] at hd'

  have hall : ∀ P : E'.toAffine.Point, ℓ • P = 0 := fun P => by
    have := congrArg (fun f : E'.toAffine.Point →+ E'.toAffine.Point => f P) hd'
    simpa [nsmul_id_apply] using this.symm
  have hzero : ∀ Q : E'.toAffine.Point, Q = 0 := fun Q => by
    obtain ⟨T, rfl⟩ := divisible hℓκ Q
    exact hall T
  have hcard : Nat.card (torsion E' ℓ) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((hzero a.1).trans (hzero b.1).symm)⟩, ⟨0⟩⟩
  rw [natCard_torsion hℓκ] at hcard
  have := hℓ.two_le
  nlinarith

theorem ker_dual_eq_map_torsion (hψ : ψ ∈ rationalHomSet κ E E') (h0 : ψ ≠ 0)
    (hd : ψ'.comp ψ = ℓ • AddMonoidHom.id _) : ψ'.ker = (torsion E ℓ).map ψ := by
  ext P
  constructor
  · intro hP
    obtain ⟨R, rfl⟩ := surjective_of_ne_zero hψ h0 P
    exact AddSubgroup.mem_map.mpr ⟨R, (mem_torsion_iff R).mpr (by rw [← dual_apply hd R]; exact hP), rfl⟩
  · rintro ⟨R, hR, rfl⟩
    rw [AddMonoidHom.mem_ker, dual_apply hd R]
    exact (mem_torsion_iff R).mp hR

theorem natCard_ker_dual (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0) (hψ : ψ ∈ rationalHomSet κ E E')
    (hd : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (hker : Nat.card ψ.ker = ℓ) : Nat.card ψ'.ker = ℓ := by
  have h0 := ne_zero_of_natCard_ker hℓ hℓκ hd hker
  have hle := ker_le_torsion hd
  have heq : (ψ'.ker).comap ψ = torsion E ℓ := by
    rw [ker_dual_eq_map_torsion hψ h0 hd, AddSubgroup.comap_map_eq, sup_eq_left.mpr hle]
  have hrange : ψ'.ker ≤ ψ.range := by
    rw [AddMonoidHom.range_eq_top.mpr (surjective_of_ne_zero hψ h0)]; exact le_top
  have hcount := natCard_comap_of_le_range ψ ψ'.ker hrange
  rw [heq, natCard_torsion hℓκ, hker, pow_two] at hcount
  exact (Nat.eq_of_mul_eq_mul_right hℓ.pos hcount.symm)

end Pair

theorem exists_aut_of_ker_eq (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    {ψ₀ ψ : E.toAffine.Point →+ E'.toAffine.Point} {ψ₀' ψ' : E'.toAffine.Point →+ E.toAffine.Point}
    (h₀ : ψ₀ ∈ rationalHomSet κ E E') (h : ψ ∈ rationalHomSet κ E E')
    (h₀' : ψ₀' ∈ rationalHomSet κ E' E) (h' : ψ' ∈ rationalHomSet κ E' E)
    (d₀ : ψ₀'.comp ψ₀ = ℓ • AddMonoidHom.id _) (d₀' : ψ₀.comp ψ₀' = ℓ • AddMonoidHom.id _)
    (d : ψ'.comp ψ = ℓ • AddMonoidHom.id _) (d' : ψ.comp ψ' = ℓ • AddMonoidHom.id _)
    (hker : ψ.ker = ψ₀.ker) :
    ∃ u : E'.toAffine.Point →+ E'.toAffine.Point, u ∈ rationalHomSet κ E' E' ∧
      ∃ v : E'.toAffine.Point →+ E'.toAffine.Point, v ∈ rationalHomSet κ E' E' ∧
      v.comp u = AddMonoidHom.id _ ∧ u.comp v = AddMonoidHom.id _ ∧ ψ = u.comp ψ₀ ∧ ψ' = ψ₀'.comp v := by

  have hu₀ : ψ.comp ψ₀' ∈ rationalHomSet κ E' E' := WeierstrassCurve.comp_mem_rationalHomSet κ E' E E' h₀' h
  have hv₀ : ψ₀.comp ψ' ∈ rationalHomSet κ E' E' := WeierstrassCurve.comp_mem_rationalHomSet κ E' E E' h' h₀
  have hu₀k : ∀ P : (E'.baseChange κ).toAffine.Point, (ℓ : ℤ) • P = 0 → (ψ.comp ψ₀') P = 0 := by
    intro P hP
    have h1 : ψ₀' P ∈ ψ₀.ker := by
      rw [AddMonoidHom.mem_ker, dual_apply d₀' P]
      rw [natCast_zsmul] at hP; exact hP
    rw [← hker] at h1
    exact h1
  have hv₀k : ∀ P : (E'.baseChange κ).toAffine.Point, (ℓ : ℤ) • P = 0 → (ψ₀.comp ψ') P = 0 := by
    intro P hP
    have h1 : ψ' P ∈ ψ.ker := by
      rw [AddMonoidHom.mem_ker, dual_apply d' P]
      rw [natCast_zsmul] at hP; exact hP
    rw [hker] at h1
    exact h1
  obtain ⟨u₀, hu, hu₀'⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero (F := κ) κ E' E'
    (N := ℓ) hℓκ hu₀ hu₀k
  obtain ⟨v₀, hv, hv₀'⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero (F := κ) κ E' E'
    (N := ℓ) hℓκ hv₀ hv₀k

  let u : E'.toAffine.Point →+ E'.toAffine.Point := u₀
  let v : E'.toAffine.Point →+ E'.toAffine.Point := v₀
  have hu' : ∀ P : E'.toAffine.Point, ψ (ψ₀' P) = ℓ • u P := fun P => by
    have := hu₀' P; rw [natCast_zsmul] at this; exact this
  have hv' : ∀ P : E'.toAffine.Point, ψ₀ (ψ' P) = ℓ • v P := fun P => by
    have := hv₀' P; rw [natCast_zsmul] at this; exact this

  have eu : ∀ T : E'.toAffine.Point, u (ℓ • T) = ψ (ψ₀' T) := fun T => by rw [map_nsmul, ← hu' T]
  have ev : ∀ T : E'.toAffine.Point, v (ℓ • T) = ψ₀ (ψ' T) := fun T => by rw [map_nsmul, ← hv' T]

  have hi : ψ = u.comp ψ₀ := by
    ext P
    obtain ⟨T, rfl⟩ := divisible (E := E) hℓκ P
    show ψ (ℓ • T) = u (ψ₀ (ℓ • T))
    rw [map_nsmul ψ₀, eu, dual_apply d₀ T]

  have hii : ψ' = ψ₀'.comp v := by
    ext Q
    obtain ⟨T, rfl⟩ := divisible (E := E') hℓκ Q
    show ψ' (ℓ • T) = ψ₀' (v (ℓ • T))
    rw [ev, dual_apply d₀ (ψ' T), map_nsmul]

  have hiii : u.comp v = AddMonoidHom.id _ := by
    ext Q
    obtain ⟨T, rfl⟩ := divisible (E := E') hℓκ Q
    show u (v (ℓ • T)) = ℓ • T
    have e2 : u (ψ₀ (ψ' T)) = ψ (ψ' T) := by rw [hi]; rfl
    rw [ev, e2]
    exact congrArg (fun f : E'.toAffine.Point →+ E'.toAffine.Point => f T) d'

  have hinj : Function.Injective u := by
    intro P₁ P₂ h12
    obtain ⟨T₁, rfl⟩ := divisible (E := E') hℓκ P₁
    obtain ⟨T₂, rfl⟩ := divisible (E := E') hℓκ P₂
    rw [eu, eu] at h12
    have hk : ψ₀' T₁ - ψ₀' T₂ ∈ ψ.ker := by
      rw [AddMonoidHom.mem_ker, map_sub]; exact sub_eq_zero.mpr h12
    rw [hker, AddMonoidHom.mem_ker, map_sub, dual_apply d₀', dual_apply d₀'] at hk
    exact sub_eq_zero.mp hk
  have hiv : v.comp u = AddMonoidHom.id _ := by
    ext P
    apply hinj
    show u (v (u P)) = u P
    exact congrArg (fun f : E'.toAffine.Point →+ E'.toAffine.Point => f (u P)) hiii
  exact ⟨u, hu, v, hv, hiv, hiii, hi, hii⟩

end Isogeny

section Count

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
  (N : ℕ) [NeZero N] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
  (C : AddSubgroup E.toAffine.Point) (C' : AddSubgroup E'.toAffine.Point)
  (hC : IsAddCyclic C ∧ Nat.card C = N) (hC' : IsAddCyclic C' ∧ Nat.card C' = N)

abbrev Stab (W : WeierstrassCurve κ) (A : AddSubgroup W.toAffine.Point) : Type :=
  {ι : W.toAffine.Point →+ W.toAffine.Point //
    ι ∈ rationalHomSet κ W W ∧
    (∃ ι' ∈ rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
    A.map ι = A}

abbrev DD : Type :=
  {D : AddSubgroup (E.baseChange κ).toAffine.Point //
    Nat.card D = ℓ ∧ ∃ ψ ∈ rationalHomSet κ E E', ∃ ψ' ∈ rationalHomSet κ E' E,
      ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
      (∀ T ∈ C, ψ T ∈ C') ∧ ∀ T ∈ C, ψ T = 0 → T = 0}

abbrev CC : Type :=
  {Cp : AddSubgroup E'.toAffine.Point //
    (IsAddCyclic Cp ∧ Nat.card Cp = N * ℓ) ∧ Cp.map (ℓ • AddMonoidHom.id _) = C' ∧
    ∃ ψ' ∈ rationalHomSet κ E' E, ∃ ψ ∈ rationalHomSet κ E E',
      ψ'.ker = Cp.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
      ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ Cp, ψ' T ∈ C}

abbrev Pairs : Type :=
  {p : (E.toAffine.Point →+ E'.toAffine.Point) × (E'.toAffine.Point →+ E.toAffine.Point) //
    p.1 ∈ rationalHomSet κ E E' ∧ p.2 ∈ rationalHomSet κ E' E ∧
    p.2.comp p.1 = ℓ • AddMonoidHom.id _ ∧ p.1.comp p.2 = ℓ • AddMonoidHom.id _ ∧
    Nat.card p.1.ker = ℓ ∧ (∀ T ∈ C, p.1 T ∈ C') ∧ ∀ T ∈ C, p.1 T = 0 → T = 0}

variable {E E' N ℓ C C'}

namespace Stab

variable {W : WeierstrassCurve κ} [W.IsElliptic] {A : AddSubgroup W.toAffine.Point}

def inv (u : Stab W A) : W.toAffine.Point →+ W.toAffine.Point := u.2.2.1.choose

theorem inv_mem (u : Stab W A) : inv u ∈ rationalHomSet κ W W := u.2.2.1.choose_spec.1
theorem inv_comp (u : Stab W A) : (inv u).comp u.1 = AddMonoidHom.id _ := u.2.2.1.choose_spec.2.1
theorem comp_inv (u : Stab W A) : u.1.comp (inv u) = AddMonoidHom.id _ := u.2.2.1.choose_spec.2.2

theorem inv_apply (u : Stab W A) (P : W.toAffine.Point) : inv u (u.1 P) = P :=
  congrArg (fun f : W.toAffine.Point →+ W.toAffine.Point => f P) (inv_comp u)

theorem apply_inv (u : Stab W A) (P : W.toAffine.Point) : u.1 (inv u P) = P :=
  congrArg (fun f : W.toAffine.Point →+ W.toAffine.Point => f P) (comp_inv u)

theorem injective (u : Stab W A) : Function.Injective u.1 :=
  Function.LeftInverse.injective (g := inv u) (inv_apply u)

theorem map_eq (u : Stab W A) : A.map u.1 = A := u.2.2.2

theorem mem_iff (u : Stab W A) (P : W.toAffine.Point) : u.1 P ∈ A ↔ P ∈ A := by
  constructor
  · intro h
    have h' : u.1 P ∈ A.map u.1 := by rw [map_eq u]; exact h
    obtain ⟨Q, hQ, hQP⟩ := h'
    rw [← injective u hQP]; exact hQ
  · intro h
    have h' : u.1 P ∈ A.map u.1 := ⟨P, h, rfl⟩
    rw [map_eq u] at h'
    exact h'

theorem inv_mem_iff (u : Stab W A) (P : W.toAffine.Point) : inv u P ∈ A ↔ P ∈ A := by
  rw [← mem_iff u, apply_inv]

theorem map_inv_eq (u : Stab W A) : A.map (inv u) = A := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩; exact (inv_mem_iff u Q).mpr hQ
  · intro hP; exact ⟨u.1 P, (mem_iff u P).mpr hP, inv_apply u P⟩

theorem comap_eq (u : Stab W A) : A.comap u.1 = A := by
  ext P; exact mem_iff u P

theorem inv_unique (u : Stab W A) {v : W.toAffine.Point →+ W.toAffine.Point}
    (hv : u.1.comp v = AddMonoidHom.id _) : inv u = v := by
  ext P
  have h1 : u.1 (v P) = P := congrArg (fun f : W.toAffine.Point →+ W.toAffine.Point => f P) hv
  rw [← h1, inv_apply, h1]

end Stab

section PairFacts

variable (p : Pairs E E' ℓ C C')

include hℓ hℓκ in
theorem fst_ne_zero : p.1.1 ≠ 0 := ne_zero_of_natCard_ker hℓ hℓκ p.2.2.2.1 p.2.2.2.2.2.1

include hℓ hℓκ in
theorem fst_surjective : Function.Surjective p.1.1 := surjective_of_ne_zero p.2.1 (fst_ne_zero hℓ hℓκ p)

include hℓ hℓκ in
theorem snd_ne_zero : p.1.2 ≠ 0 := dual_ne_zero hℓ hℓκ p.2.2.2.2.1

include hℓ hℓκ in
theorem snd_surjective : Function.Surjective p.1.2 := surjective_of_ne_zero p.2.2.1 (snd_ne_zero hℓ hℓκ p)

include hℓ hℓκ in
theorem natCard_ker_snd : Nat.card p.1.2.ker = ℓ :=
  natCard_ker_dual hℓ hℓκ p.2.1 p.2.2.2.1 p.2.2.2.2.2.1

include hC hC' in

theorem map_fst_eq : C.map p.1.1 = C' := by
  haveI : Finite C' := Nat.finite_of_card_ne_zero (by rw [hC'.2]; exact NeZero.ne N)
  apply AddSubgroup.eq_of_le_of_card_ge
  · rintro _ ⟨T, hT, rfl⟩; exact p.2.2.2.2.2.2.1 T hT
  · have hinj : Set.InjOn p.1.1 C := by
      intro T₁ h₁ T₂ h₂ h12
      have h0 : p.1.1 (T₁ - T₂) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h12
      exact sub_eq_zero.mp (p.2.2.2.2.2.2.2 _ (C.sub_mem h₁ h₂) h0)
    have h1 : Nat.card (C.map p.1.1) = Nat.card (p.1.1 '' (C : Set E.toAffine.Point)) := by
      rw [← AddSubgroup.coe_map]; rfl
    rw [h1, Nat.card_image_of_injOn hinj, hC'.2]
    exact le_of_eq hC.2.symm

def ovG : AddSubgroup E'.toAffine.Point := C.comap p.1.2

theorem mem_ovG_iff (P : E'.toAffine.Point) : P ∈ ovG p ↔ p.1.2 P ∈ C := Iff.rfl

theorem ker_le_ovG : p.1.2.ker ≤ ovG p := fun P hP => by
  rw [mem_ovG_iff, AddMonoidHom.mem_ker.mp hP]; exact C.zero_mem

include hℓ hℓκ hC in
theorem natCard_ovG : Nat.card (ovG p) = N * ℓ := by
  have hrange : C ≤ p.1.2.range := by
    rw [AddMonoidHom.range_eq_top.mpr (snd_surjective hℓ hℓκ p)]; exact le_top
  rw [ovG, natCard_comap_of_le_range _ _ hrange, hC.2, natCard_ker_snd hℓ hℓκ p]

include hℓ hℓκ hC in
theorem ovG_cyclic : IsAddCyclic (ovG p) ∧ Nat.card (ovG p) = N * ℓ := by
  refine ⟨?_, natCard_ovG hℓ hℓκ hC p⟩
  refine isAddCyclic_comap hℓ (NeZero.ne N) p.1.2 C hC (natCard_ovG hℓ hℓκ hC p) (natCard_ker_snd hℓ hℓκ p)
    (fun T _ => snd_surjective hℓ hℓκ p T) ?_
  intro S hS hℓS

  rw [AddMonoidHom.mem_ker]
  apply p.2.2.2.2.2.2.2 _ hS
  rw [dual_apply p.2.2.2.2.1 S]
  exact hℓS

include hℓ hℓκ hC hC' in
theorem ovG_map_ell : (ovG p).map (ℓ • AddMonoidHom.id _) = C' := by
  haveI : Finite C' := Nat.finite_of_card_ne_zero (by rw [hC'.2]; exact NeZero.ne N)
  apply AddSubgroup.eq_of_le_of_card_ge
  · rintro _ ⟨P, hP, rfl⟩
    rw [nsmul_id_apply, ← dual_apply p.2.2.2.2.1 P]
    exact p.2.2.2.2.2.2.1 _ hP
  · rw [hC'.2, (cyclic_map_nsmul_ell hℓ.ne_zero _ (ovG_cyclic hℓ hℓκ hC p)).2]

include hℓ hℓκ hC in
theorem ovG_map_N : (ovG p).map (N • AddMonoidHom.id _) = p.1.2.ker := by
  haveI : Finite p.1.2.ker := Nat.finite_of_card_ne_zero (by rw [natCard_ker_snd hℓ hℓκ p]; exact hℓ.ne_zero)
  apply AddSubgroup.eq_of_le_of_card_ge
  · rintro _ ⟨P, hP, rfl⟩
    rw [AddMonoidHom.mem_ker, nsmul_id_apply, map_nsmul]
    have hmem : p.1.2 P ∈ C := hP
    have h := card_nsmul_eq_zero' (x := (⟨p.1.2 P, hmem⟩ : C))
    rw [hC.2] at h
    exact congrArg Subtype.val h
  · rw [natCard_ker_snd hℓ hℓκ p, (cyclic_map_nsmul_N (NeZero.ne N) _ (ovG_cyclic hℓ hℓκ hC p)).2]

end PairFacts

section Projections

def piD (p : Pairs E E' ℓ C C') : DD E E' ℓ C C' :=
  ⟨p.1.1.ker, p.2.2.2.2.2.1, p.1.1, p.2.1, p.1.2, p.2.2.1, rfl, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2⟩

theorem piD_val (p : Pairs E E' ℓ C C') : (piD p).1 = p.1.1.ker := rfl

theorem piD_surjective : Function.Surjective (piD (E := E) (E' := E') (ℓ := ℓ) (C := C) (C' := C')) := by
  rintro ⟨D, hD, ψ, hψ, ψ', hψ', hker, hd, hd', hCC, hinj⟩
  refine ⟨⟨(ψ, ψ'), hψ, hψ', hd, hd', by show Nat.card ψ.ker = ℓ; rw [hker]; exact hD, hCC, hinj⟩, ?_⟩
  exact Subtype.ext hker

include hℓ hℓκ hC hC' in

theorem ovG_mem (p : Pairs E E' ℓ C C') :
    (IsAddCyclic (ovG p) ∧ Nat.card (ovG p) = N * ℓ) ∧ (ovG p).map (ℓ • AddMonoidHom.id _) = C' ∧
    ∃ ψ' ∈ rationalHomSet κ E' E, ∃ ψ ∈ rationalHomSet κ E E',
      ψ'.ker = (ovG p).map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
      ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ ovG p, ψ' T ∈ C :=
  ⟨ovG_cyclic hℓ hℓκ hC p, ovG_map_ell hℓ hℓκ hC hC' p, p.1.2, p.2.2.1, p.1.1, p.2.1,
    (ovG_map_N hℓ hℓκ hC p).symm, p.2.2.2.2.1, p.2.2.2.1, fun T hT => hT⟩

def piC (p : Pairs E E' ℓ C C') : CC E E' N ℓ C C' := ⟨ovG p, ovG_mem hℓ hℓκ hC hC' p⟩

theorem piC_val (p : Pairs E E' ℓ C C') : (piC hℓ hℓκ hC hC' p).1 = C.comap p.1.2 := rfl

include hℓ hℓκ hC in
theorem piC_surjective : Function.Surjective (piC (E := E) (E' := E') hℓ hℓκ hC hC') := by
  rintro ⟨Cp, hcyc, hmap, ψ'₀, hψ'₀, ψ₀, hψ₀, hker₀, hd'₀, hd₀, hCC₀⟩

  let ψ' : E'.toAffine.Point →+ E.toAffine.Point := ψ'₀
  let ψ : E.toAffine.Point →+ E'.toAffine.Point := ψ₀
  have hψ' : ψ' ∈ rationalHomSet κ E' E := hψ'₀
  have hψ : ψ ∈ rationalHomSet κ E E' := hψ₀
  have hker : ψ'.ker = Cp.map (N • AddMonoidHom.id _) := hker₀
  have hd' : ψ.comp ψ' = ℓ • AddMonoidHom.id _ := hd'₀
  have hd : ψ'.comp ψ = ℓ • AddMonoidHom.id _ := hd₀
  have hCC : ∀ T ∈ Cp, ψ' T ∈ C := hCC₀

  have hkercard : Nat.card ψ'.ker = ℓ := by
    rw [hker]; exact (cyclic_map_nsmul_N (NeZero.ne N) Cp hcyc).2
  have hkerψ : Nat.card ψ.ker = ℓ := natCard_ker_dual (E := E') (E' := E) hℓ hℓκ hψ' hd' hkercard
  have hψ'0 : ψ' ≠ 0 := ne_zero_of_natCard_ker (E := E') (E' := E) hℓ hℓκ hd' hkercard
  have hψ'surj := surjective_of_ne_zero hψ' hψ'0
  haveI : Finite Cp := Nat.finite_of_card_ne_zero (by rw [hcyc.2]; exact Nat.mul_ne_zero (NeZero.ne N) hℓ.ne_zero)
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hC.2]; exact NeZero.ne N)

  have hrangeAll : ∀ A : AddSubgroup E.toAffine.Point, A ≤ ψ'.range := fun A => by
    rw [AddMonoidHom.range_eq_top.mpr hψ'surj]; exact le_top
  have hcomapC : Nat.card (C.comap ψ') = N * ℓ := by
    rw [natCard_comap_of_le_range _ _ (hrangeAll C), hC.2, hkercard]
  have himage : Cp.map ψ' = C := by
    have hle : Cp.map ψ' ≤ C := by rintro _ ⟨T, hT, rfl⟩; exact hCC T hT
    apply AddSubgroup.eq_of_le_of_card_ge hle

    have h1 : Cp ≤ (Cp.map ψ').comap ψ' := AddSubgroup.le_comap_map _ _
    haveI : Finite ((Cp.map ψ').comap ψ') := by
      apply Nat.finite_of_card_ne_zero
      rw [natCard_comap_of_le_range _ _ (hrangeAll _), hkercard]
      haveI : Finite (Cp.map ψ') := Finite.of_injective (AddSubgroup.inclusion hle) (AddSubgroup.inclusion_injective hle)
      exact Nat.mul_ne_zero (Nat.card_pos.ne') hℓ.ne_zero
    have h2 := AddSubgroup.card_le_of_le h1
    rw [natCard_comap_of_le_range _ _ (hrangeAll _), hkercard, hcyc.2] at h2
    rw [hC.2]
    exact Nat.le_of_mul_le_mul_right h2 hℓ.pos

  have hCC' : ∀ T ∈ C, ψ T ∈ C' := by
    intro T hT
    rw [← himage] at hT
    obtain ⟨S, hS, rfl⟩ := hT
    rw [dual_apply hd' S, ← hmap]
    exact ⟨S, hS, rfl⟩
  have hinj : ∀ T ∈ C, ψ T = 0 → T = 0 := by
    intro T hT h0
    rw [← himage] at hT
    obtain ⟨S, hS, rfl⟩ := hT
    rw [dual_apply hd' S] at h0
    have hSker : S ∈ ψ'.ker := by
      rw [hker]; exact mem_map_N_of_nsmul_eq_zero (NeZero.ne N) hℓ.ne_zero Cp hcyc hS h0
    exact hSker
  let p : Pairs E E' ℓ C C' := ⟨(ψ, ψ'), hψ, hψ', hd, hd', hkerψ, hCC', hinj⟩
  refine ⟨p, Subtype.ext ?_⟩

  show C.comap ψ' = Cp
  symm
  haveI : Finite (C.comap ψ') := Nat.finite_of_card_ne_zero (by rw [hcomapC]; exact Nat.mul_ne_zero (NeZero.ne N) hℓ.ne_zero)
  apply AddSubgroup.eq_of_le_of_card_ge
  · intro T hT; exact hCC T hT
  · rw [hcomapC, hcyc.2]

def actD (u : Stab E' C') (p : Pairs E E' ℓ C C') : Pairs E E' ℓ C C' :=
  ⟨(u.1.comp p.1.1, p.1.2.comp (Stab.inv u)),
    WeierstrassCurve.comp_mem_rationalHomSet κ E E' E' p.2.1 u.2.1,
    WeierstrassCurve.comp_mem_rationalHomSet κ E' E' E (Stab.inv_mem u) p.2.2.1,
    by
      ext P
      show p.1.2 (Stab.inv u (u.1 (p.1.1 P))) = ℓ • P
      rw [Stab.inv_apply]
      exact dual_apply p.2.2.2.1 P,
    by
      ext P
      show u.1 (p.1.1 (p.1.2 (Stab.inv u P))) = ℓ • P
      rw [dual_apply p.2.2.2.2.1 (Stab.inv u P), map_nsmul, Stab.apply_inv],
    by
      have : (u.1.comp p.1.1).ker = p.1.1.ker := by
        ext P
        rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
        constructor
        · intro h; exact Stab.injective u (h.trans (map_zero u.1).symm)
        · intro h; rw [h, map_zero]
      show Nat.card (u.1.comp p.1.1).ker = ℓ
      rw [this]; exact p.2.2.2.2.2.1,
    fun T hT => (Stab.mem_iff u _).mpr (p.2.2.2.2.2.2.1 T hT),
    fun T hT h0 => p.2.2.2.2.2.2.2 T hT (Stab.injective u ((h0.trans (map_zero u.1).symm)))⟩

theorem actD_fst (u : Stab E' C') (p : Pairs E E' ℓ C C') : (actD u p).1.1 = u.1.comp p.1.1 := rfl
theorem actD_snd (u : Stab E' C') (p : Pairs E E' ℓ C C') : (actD u p).1.2 = p.1.2.comp (Stab.inv u) := rfl

theorem piD_actD (u : Stab E' C') (p : Pairs E E' ℓ C C') : piD (actD u p) = piD p := by
  apply Subtype.ext
  show (u.1.comp p.1.1).ker = p.1.1.ker
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
  constructor
  · intro h; exact Stab.injective u (h.trans (map_zero u.1).symm)
  · intro h; rw [h, map_zero]

include hℓ hℓκ hC hC' in

theorem bijective_actD (p₀ : Pairs E E' ℓ C C') :
    Function.Bijective (fun u : Stab E' C' => (⟨actD u p₀, piD_actD u p₀⟩ : {p : Pairs E E' ℓ C C' // piD p = piD p₀})) := by
  constructor
  · intro u₁ u₂ h
    have h1 : u₁.1.comp p₀.1.1 = u₂.1.comp p₀.1.1 := by
      have := congrArg (fun q : {p : Pairs E E' ℓ C C' // piD p = piD p₀} => q.1.1.1) h
      exact this
    apply Subtype.ext
    ext P
    obtain ⟨T, rfl⟩ := fst_surjective hℓ hℓκ p₀ P
    exact congrArg (fun f : E.toAffine.Point →+ E'.toAffine.Point => f T) h1
  · rintro ⟨p, hp⟩
    have hker : p.1.1.ker = p₀.1.1.ker := congrArg Subtype.val hp
    obtain ⟨u, hu, v, hv, hvu, huv, hi, hii⟩ := exists_aut_of_ker_eq hℓ hℓκ p₀.2.1 p.2.1 p₀.2.2.1 p.2.2.1
      p₀.2.2.2.1 p₀.2.2.2.2.1 p.2.2.2.1 p.2.2.2.2.1 hker

    have hstab : C'.map u = C' := by
      conv_lhs => rw [← map_fst_eq hC hC' p₀]
      rw [AddSubgroup.map_map, ← hi, map_fst_eq hC hC' p]
    let U : Stab E' C' := ⟨u, hu, ⟨v, hv, hvu, huv⟩, hstab⟩
    refine ⟨U, Subtype.ext (Subtype.ext (Prod.ext hi.symm ?_))⟩
    show p₀.1.2.comp (Stab.inv U) = p.1.2
    rw [Stab.inv_unique U (v := v) huv, ← hii]

def actC (u : Stab E C) (p : Pairs E E' ℓ C C') : Pairs E E' ℓ C C' :=
  ⟨(p.1.1.comp (Stab.inv u), u.1.comp p.1.2),
    WeierstrassCurve.comp_mem_rationalHomSet κ E E E' (Stab.inv_mem u) p.2.1,
    WeierstrassCurve.comp_mem_rationalHomSet κ E' E E p.2.2.1 u.2.1,
    by
      ext P
      show u.1 (p.1.2 (p.1.1 (Stab.inv u P))) = ℓ • P
      rw [dual_apply p.2.2.2.1 (Stab.inv u P), map_nsmul, Stab.apply_inv],
    by
      ext P
      show p.1.1 (Stab.inv u (u.1 (p.1.2 P))) = ℓ • P
      rw [Stab.inv_apply]
      exact dual_apply p.2.2.2.2.1 P,
    by

      have hset : ((p.1.1.comp (Stab.inv u)).ker : Set E.toAffine.Point) = u.1 '' (p.1.1.ker : Set E.toAffine.Point) := by
        ext P
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Set.mem_image]
        constructor
        · intro h; exact ⟨Stab.inv u P, h, Stab.apply_inv u P⟩
        · rintro ⟨Q, hQ, rfl⟩; rw [Stab.inv_apply]; exact hQ
      show Nat.card (p.1.1.comp (Stab.inv u)).ker = ℓ
      have h1 : Nat.card (p.1.1.comp (Stab.inv u)).ker = Nat.card (u.1 '' (p.1.1.ker : Set E.toAffine.Point)) := by
        rw [← hset]; rfl
      rw [h1, Nat.card_image_of_injective (Stab.injective u)]
      exact p.2.2.2.2.2.1,
    fun T hT => p.2.2.2.2.2.2.1 _ ((Stab.inv_mem_iff u T).mpr hT),
    fun T hT h0 => by
      have := p.2.2.2.2.2.2.2 _ ((Stab.inv_mem_iff u T).mpr hT) h0
      rw [← Stab.apply_inv u T, this, map_zero]⟩

theorem piC_actC (u : Stab E C) (p : Pairs E E' ℓ C C') : piC hℓ hℓκ hC hC' (actC u p) = piC hℓ hℓκ hC hC' p := by
  apply Subtype.ext
  show C.comap (u.1.comp p.1.2) = C.comap p.1.2
  rw [← AddSubgroup.comap_comap, Stab.comap_eq]

include hℓ hℓκ hC hC' in

theorem bijective_actC (p₀ : Pairs E E' ℓ C C') :
    Function.Bijective (fun u : Stab E C =>
      (⟨actC u p₀, piC_actC hℓ hℓκ hC hC' u p₀⟩ : {p : Pairs E E' ℓ C C' // piC hℓ hℓκ hC hC' p = piC hℓ hℓκ hC hC' p₀})) := by
  constructor
  · intro u₁ u₂ h
    have h1 : u₁.1.comp p₀.1.2 = u₂.1.comp p₀.1.2 := by
      have := congrArg (fun q : {p : Pairs E E' ℓ C C' // piC hℓ hℓκ hC hC' p = piC hℓ hℓκ hC hC' p₀} => q.1.1.2) h
      exact this
    apply Subtype.ext
    ext P
    obtain ⟨T, rfl⟩ := snd_surjective hℓ hℓκ p₀ P
    exact congrArg (fun f : E'.toAffine.Point →+ E.toAffine.Point => f T) h1
  · rintro ⟨p, hp⟩
    have hover : C.comap p.1.2 = C.comap p₀.1.2 := congrArg Subtype.val hp

    have hker : p.1.2.ker = p₀.1.2.ker := by
      rw [← ovG_map_N hℓ hℓκ hC p, ← ovG_map_N hℓ hℓκ hC p₀]
      exact congrArg (fun A : AddSubgroup E'.toAffine.Point => A.map (N • AddMonoidHom.id _)) hover
    obtain ⟨u, hu, v, hv, hvu, huv, hi, hii⟩ := exists_aut_of_ker_eq (E := E') (E' := E) hℓ hℓκ
      p₀.2.2.1 p.2.2.1 p₀.2.1 p.2.1 p₀.2.2.2.2.1 p₀.2.2.2.1 p.2.2.2.2.1 p.2.2.2.1 hker

    have himg : ∀ q : Pairs E E' ℓ C C', (C.comap q.1.2).map q.1.2 = C := fun q =>
      AddSubgroup.map_comap_eq_self_of_surjective (snd_surjective hℓ hℓκ q) C
    have hstab : C.map u = C := by
      conv_lhs => rw [← himg p₀]
      rw [AddSubgroup.map_map, ← hi, ← hover, himg p]
    let U : Stab E C := ⟨u, hu, ⟨v, hv, hvu, huv⟩, hstab⟩
    refine ⟨U, Subtype.ext (Subtype.ext (Prod.ext ?_ hi.symm))⟩
    show p₀.1.1.comp (Stab.inv U) = p.1.1
    rw [Stab.inv_unique U (v := v) huv, ← hii]

include hℓ hℓκ hC hC' in
theorem natCard_pairs_eq_D : Nat.card (Pairs E E' ℓ C C') = Nat.card (DD E E' ℓ C C') * Nat.card (Stab E' C') := by
  classical
  have e1 : Pairs E E' ℓ C C' ≃ Σ D : DD E E' ℓ C C', {p : Pairs E E' ℓ C C' // piD p = D} :=
    (Equiv.sigmaFiberEquiv piD).symm
  have e2 : ∀ D : DD E E' ℓ C C', Nonempty ({p : Pairs E E' ℓ C C' // piD p = D} ≃ Stab E' C') := by
    intro D
    obtain ⟨p₀, rfl⟩ := piD_surjective D
    exact ⟨(Equiv.ofBijective _ (bijective_actD hℓ hℓκ hC hC' p₀)).symm⟩
  have e3 : (Σ D : DD E E' ℓ C C', {p : Pairs E E' ℓ C C' // piD p = D}) ≃ DD E E' ℓ C C' × Stab E' C' :=
    (Equiv.sigmaCongrRight fun D => (e2 D).some).trans (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr (e1.trans e3), Nat.card_prod]

include hℓ hℓκ hC hC' in
theorem natCard_pairs_eq_C : Nat.card (Pairs E E' ℓ C C') = Nat.card (CC E E' N ℓ C C') * Nat.card (Stab E C) := by
  classical
  have e1 : Pairs E E' ℓ C C' ≃ Σ A : CC E E' N ℓ C C', {p : Pairs E E' ℓ C C' // piC hℓ hℓκ hC hC' p = A} :=
    (Equiv.sigmaFiberEquiv (piC hℓ hℓκ hC hC')).symm
  have e2 : ∀ A : CC E E' N ℓ C C', Nonempty ({p : Pairs E E' ℓ C C' // piC hℓ hℓκ hC hC' p = A} ≃ Stab E C) := by
    intro A
    obtain ⟨p₀, rfl⟩ := piC_surjective hℓ hℓκ hC hC' A
    exact ⟨(Equiv.ofBijective _ (bijective_actC hℓ hℓκ hC hC' p₀)).symm⟩
  have e3 : (Σ A : CC E E' N ℓ C C', {p : Pairs E E' ℓ C C' // piC hℓ hℓκ hC hC' p = A}) ≃ CC E E' N ℓ C C' × Stab E C :=
    (Equiv.sigmaCongrRight fun A => (e2 A).some).trans (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr (e1.trans e3), Nat.card_prod]

end Projections

end Count

end WeierstrassCurve.DualPairCount

end

open WeierstrassCurve.DualPairCount in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
    (N : ℕ) [NeZero N] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    (C : AddSubgroup E.toAffine.Point) (C' : AddSubgroup E'.toAffine.Point)
    (hC : IsAddCyclic C ∧ Nat.card C = N) (hC' : IsAddCyclic C' ∧ Nat.card C' = N) :
    Nat.card {ι : E.toAffine.Point →+ E.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ E E ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E E, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C.map ι = C} *
      Nat.card {Cp : AddSubgroup E'.toAffine.Point //
        (IsAddCyclic Cp ∧ Nat.card Cp = N * ℓ) ∧ Cp.map (ℓ • AddMonoidHom.id _) = C' ∧
        ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E' E, ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E E',
          ψ'.ker = Cp.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ Cp, ψ' T ∈ C} =
    Nat.card {ι : E'.toAffine.Point →+ E'.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ E' E' ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E' E', ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C'.map ι = C'} *
      Nat.card {D : AddSubgroup (E.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E E', ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E' E,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          (∀ T ∈ C, ψ T ∈ C') ∧ ∀ T ∈ C, ψ T = 0 → T = 0} := by
  have h1 := natCard_pairs_eq_D (E := E) (E' := E') (N := N) hℓ hℓκ hC hC'
  have h2 := natCard_pairs_eq_C (E := E) (E' := E') (N := N) hℓ hℓκ hC hC'
  show Nat.card (Stab E C) * Nat.card (CC E E' N ℓ C C') = Nat.card (Stab E' C') * Nat.card (DD E E' ℓ C C')
  rw [mul_comm, ← h2, h1, mul_comm]

end S_WeierstrassCurve_natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair
end P2MW
export P2MW.S_WeierstrassCurve_natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair (solution)
