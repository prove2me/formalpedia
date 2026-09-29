-- Prove2me | solution 1 for ValuationSubring.normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fe84956c-0e24-5eda-8d9b-4151635151b6

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.Pointwise
import Theorems.Thm_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
import Theorems.Thm_ValuationSubring_mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois

set_option autoImplicit false

noncomputable section

attribute [local instance] Ideal.Quotient.field

namespace EsbCapG3b

open IsLocalRing ValuationSubring Pointwise

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

section galois
variable [FiniteDimensional E F] [IsGalois E F] (O : ValuationSubring E)

noncomputable scoped instance msaGalB : MulSemiringAction Gal(F/E) ↥(integralClosure (↥O) F) :=
  IsIntegralClosure.MulSemiringAction ↥O E F ↥(integralClosure (↥O) F)

omit [FiniteDimensional E F] in
theorem smul_coe (σ : Gal(F/E)) (b : integralClosure (↥O) F) :
    ((σ • b : integralClosure (↥O) F) : F) = σ (b : F) :=
  algebraMap_galRestrict_apply ↥O σ b

scoped instance sccGalOB : SMulCommClass Gal(F/E) ↥O ↥(integralClosure (↥O) F) where
  smul_comm g a b := by
    have key : ∀ c : integralClosure (↥O) F, ((a • c : integralClosure (↥O) F) : F)
        = algebraMap E F (a : E) * (c : F) := fun c => by
      rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ↥O E F]; rfl
    exact Subtype.ext <| by rw [smul_coe, key, key, smul_coe, map_mul, g.commutes]

scoped instance ifrBF : IsFractionRing ↥(integralClosure (↥O) F) F :=
  integralClosure.isFractionRing_of_finite_extension E F

scoped instance invOBGal : Algebra.IsInvariant ↥O ↥(integralClosure (↥O) F) Gal(F/E) :=
  Algebra.isInvariant_of_isGalois ↥O E F ↥(integralClosure (↥O) F)

end galois

section center
variable (O : ValuationSubring E) (O' : ValuationSubring F)
  (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)

include hO in
theorem val_le_one (b : integralClosure (↥O) F) : O'.valuation (b : F) ≤ 1 := by
  obtain ⟨_, _, h⟩ :=
    (ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
      (F := F) O).1 O' hO
  exact (h b).1

def inclBtoO' : integralClosure (↥O) F →+* ↥O' where
  toFun b := ⟨b.1, (O'.valuation_le_one_iff _).mp (val_le_one O O' hO b)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem inclBtoO'_coe (b : integralClosure (↥O) F) :
    ((inclBtoO' O O' hO b : ↥O') : F) = (b : F) := rfl

def centerQ : Ideal ↥(integralClosure (↥O) F) :=
  (IsLocalRing.maximalIdeal ↥O').comap (inclBtoO' O O' hO)

theorem mem_centerQ_iff (b : integralClosure (↥O) F) :
    b ∈ centerQ O O' hO ↔ O'.valuation (b : F) < 1 :=
  ValuationSubring.valuation_lt_one_iff O' _

scoped instance centerQ_isMaximal : (centerQ O O' hO).IsMaximal := by
  obtain ⟨M, hMmax, hM⟩ :=
    (ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
      (F := F) O).1 O' hO
  have hQM : centerQ O O' hO = M := by
    ext b; rw [mem_centerQ_iff]; exact (hM b).2
  exact hQM ▸ hMmax

include hO in
theorem valO'_lt_one_iff (a : E) :
    O'.valuation (algebraMap E F a) < 1 ↔ O.valuation a < 1 := by
  simp only [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ← map_inv₀, hO, FaithfulSMul.algebraMap_eq_zero_iff]

scoped instance centerQ_liesOver :
    (centerQ O O' hO).LiesOver (IsLocalRing.maximalIdeal ↥O) := by
  constructor
  ext a
  rw [Ideal.mem_under, mem_centerQ_iff]
  have hcoe : ((algebraMap ↥O (integralClosure (↥O) F) a : integralClosure (↥O) F) : F)
      = algebraMap E F (a : E) :=
    (IsScalarTower.algebraMap_apply ↥O E F a :)
  rw [hcoe, valO'_lt_one_iff O O' hO]
  exact ValuationSubring.valuation_lt_one_iff O a

def eToRes : ↥(integralClosure (↥O) F) →+* IsLocalRing.ResidueField ↥O' :=
  (IsLocalRing.residue ↥O').comp (inclBtoO' O O' hO)

theorem eToRes_apply (b : integralClosure (↥O) F) :
    eToRes O O' hO b = IsLocalRing.residue ↥O' (inclBtoO' O O' hO b) := rfl

theorem ker_eToRes : RingHom.ker (eToRes O O' hO) = centerQ O O' hO := by
  unfold eToRes centerQ
  rw [← RingHom.comap_ker, IsLocalRing.ker_residue]

def eLift : (↥(integralClosure (↥O) F) ⧸ centerQ O O' hO) →+* IsLocalRing.ResidueField ↥O' :=
  Ideal.Quotient.lift _ (eToRes O O' hO)
    (fun _ hb => RingHom.mem_ker.mp ((ker_eToRes O O' hO).symm ▸ hb))

@[scoped simp] theorem eLift_mk (b : integralClosure (↥O) F) :
    eLift O O' hO (Ideal.Quotient.mk _ b) = eToRes O O' hO b := rfl

theorem eLift_injective : Function.Injective (eLift O O' hO) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  unfold eLift
  rw [Ideal.ker_quotient_lift, ker_eToRes, Ideal.map_quotient_self]

theorem eLift_surjective [Algebra.IsAlgebraic E F] : Function.Surjective (eLift O O' hO) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := ↥O') y
  obtain ⟨b, s, hs, hxsb⟩ :=
    ((ValuationSubring.mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic
      O O' hO).1 (x : F)).mp x.2
  have hsne : eToRes O O' hO s ≠ 0 := by
    rw [ne_eq, ← RingHom.mem_ker, ker_eToRes, mem_centerQ_iff]
    exact not_lt.mpr hs.ge

  have key : IsLocalRing.residue ↥O' x * eToRes O O' hO s = eToRes O O' hO b := by
    rw [eToRes_apply, eToRes_apply, ← map_mul]
    exact congrArg _ (Subtype.ext hxsb)

  have hsne' : Ideal.Quotient.mk (centerQ O O' hO) s ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, mem_centerQ_iff]; exact not_lt.mpr hs.ge
  obtain ⟨t', ht'⟩ := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
    (centerQ_isMaximal O O' hO)).mul_inv_cancel hsne'
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
  refine ⟨Ideal.Quotient.mk _ (b * t), ?_⟩
  rw [eLift_mk, map_mul]

  have hst : eToRes O O' hO s * eToRes O O' hO t = 1 := by
    have h := congrArg (eLift O O' hO) ht'
    rwa [map_mul, map_one, eLift_mk, eLift_mk] at h
  rw [show eToRes O O' hO t = (eToRes O O' hO s)⁻¹ from
    (inv_eq_of_mul_eq_one_right hst).symm, ← key, mul_inv_cancel_right₀ hsne]

theorem eLift_bijective [Algebra.IsAlgebraic E F] : Function.Bijective (eLift O O' hO) :=
  ⟨eLift_injective O O' hO, eLift_surjective O O' hO⟩

section galois
variable [FiniteDimensional E F] [IsGalois E F]

include hO in
omit [FiniteDimensional E F] [IsGalois E F] in
theorem smul_O'_over (σ : Gal(F/E)) : ∀ x : E, algebraMap E F x ∈ σ • O' ↔ x ∈ O := by
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    show (σ⁻¹ : Gal(F/E)) • algebraMap E F x = algebraMap E F x from (σ⁻¹).commutes x]
  exact hO x

omit [FiniteDimensional E F] in
theorem val_smul_lt_one_iff (σ : Gal(F/E)) (b : integralClosure (↥O) F) :
    (σ • O').valuation (b : F) < 1 ↔ σ⁻¹ • b ∈ centerQ O O' hO := by
  rw [mem_centerQ_iff, smul_coe, ← ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_nonunits_iff_or]
  refine or_congr ?_ (not_congr ?_)
  · exact ⟨fun h => by rw [h, map_zero], fun h => σ⁻¹.injective (by rwa [map_zero])⟩
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      show (σ⁻¹ : Gal(F/E)) • ((↑b : F)⁻¹) = (σ⁻¹ : Gal(F/E)) ((↑b : F)⁻¹) from rfl,
      map_inv₀]

omit [FiniteDimensional E F] in
theorem stab_eq_decomp :
    MulAction.stabilizer Gal(F/E) (centerQ O O' hO) = O'.decompositionSubgroup E := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff]
  show σ • centerQ O O' hO = centerQ O O' hO ↔ σ • O' = O'
  constructor
  · intro hσ
    refine (ValuationSubring.mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic
      O O' hO).2 (σ • O') (smul_O'_over O O' hO σ) ?_
    intro b
    rw [← mem_centerQ_iff O O' hO, val_smul_lt_one_iff O O' hO σ b]
    conv_lhs => rw [← hσ]
    exact Ideal.mem_pointwise_smul_iff_inv_smul_mem
  · intro hσ
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← val_smul_lt_one_iff O O' hO σ b, hσ,
      mem_centerQ_iff]

omit [FiniteDimensional E F] in
theorem eLift_stabilizerHom (σ : MulAction.stabilizer Gal(F/E) (centerQ O O' hO))
    (y : ↥(integralClosure (↥O) F) ⧸ centerQ O O' hO) :
    eLift O O' hO (Ideal.Quotient.stabilizerHom (centerQ O O' hO)
        (IsLocalRing.maximalIdeal ↥O) Gal(F/E) σ y) =
      (⟨σ.1, (stab_eq_decomp O O' hO).le σ.2⟩ : O'.decompositionSubgroup E) •
        (eLift O O' hO y) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.stabilizerHom_apply, eLift_mk, eLift_mk,
    eToRes_apply, eToRes_apply, ← IsLocalRing.ResidueField.residue_smul]
  congr 1
  apply Subtype.ext
  exact smul_coe O σ.1 b

variable [Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')]
  (hcompat : ∀ a : O, algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')
      (IsLocalRing.residue O a) = IsLocalRing.residue O' ⟨algebraMap E F a, (hO a).mpr a.2⟩)

scoped instance algResQuot :
    Algebra (IsLocalRing.ResidueField ↥O) (↥(integralClosure (↥O) F) ⧸ centerQ O O' hO) :=
  inferInstanceAs (Algebra (↥O ⧸ IsLocalRing.maximalIdeal ↥O) _)

scoped instance algQuotRes :
    Algebra (↥O ⧸ IsLocalRing.maximalIdeal ↥O) (IsLocalRing.ResidueField ↥O') :=
  inferInstanceAs (Algebra (IsLocalRing.ResidueField ↥O) _)

def eEquiv : (↥(integralClosure (↥O) F) ⧸ centerQ O O' hO) ≃ₐ[IsLocalRing.ResidueField ↥O]
    IsLocalRing.ResidueField ↥O' :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (eLift O O' hO) (eLift_bijective O O' hO))
    (by
      intro r
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
      rw [hcompat]
      exact congrArg _ (Subtype.ext (IsScalarTower.algebraMap_apply ↥O E F a).symm))

omit [FiniteDimensional E F] in
theorem eEquiv_apply (y) : eEquiv O O' hO hcompat y = eLift O O' hO y := rfl

end galois

end center

end EsbCapG3b
p2m_reactivate "P2MW.S_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois.EsbCapG3b"

end
p2m_reactivate "P2MW.S_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois.EsbCapG3b"

attribute [local instance] Ideal.Quotient.field in
open EsbCapG3b IsLocalRing Pointwise in
theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    [IsGalois E F]
    (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    [Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')]
    (hcompat : ∀ a : O, algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')
        (IsLocalRing.residue O a) = IsLocalRing.residue O' ⟨algebraMap E F a, (hO a).mpr a.2⟩) :
    (∀ (σ : O'.decompositionSubgroup E) (a : IsLocalRing.ResidueField O),
        σ • algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') a =
          algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') a) ∧
    Normal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') ∧
    ∀ τ : IsLocalRing.ResidueField O' ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O',
      ∃ σ : O'.decompositionSubgroup E, ∀ x : IsLocalRing.ResidueField O', σ • x = τ x := by
  refine ⟨?part1, ?part2, ?part3⟩
  case part1 =>
    intro σ a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    rw [hcompat, ← IsLocalRing.ResidueField.residue_smul]
    exact congrArg _ (Subtype.ext ((σ : Gal(F/E)).commutes a))
  case part2 =>
    have hnormal : Normal (IsLocalRing.ResidueField ↥O)
        (↥(integralClosure (↥O) F) ⧸ centerQ O O' hO) :=
      Ideal.Quotient.normal (A := ↥O) (B := ↥(integralClosure (↥O) F))
        Gal(F/E) (IsLocalRing.maximalIdeal ↥O) (centerQ O O' hO)
    exact hnormal.of_algEquiv (eEquiv O O' hO hcompat)
  case part3 =>
    intro τ
    let e := eEquiv O O' hO hcompat

    let τ' : (↥(integralClosure (↥O) F) ⧸ centerQ O O' hO) ≃ₐ[IsLocalRing.ResidueField ↥O] _ :=
      e.trans (τ.trans e.symm)
    obtain ⟨σ, hσ⟩ :=
      Ideal.Quotient.stabilizerHom_surjective Gal(F/E) (IsLocalRing.maximalIdeal ↥O)
        (centerQ O O' hO) τ'
    refine ⟨⟨σ.1, (stab_eq_decomp O O' hO).le σ.2⟩, ?_⟩
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    have heq : e y = eLift O O' hO y := rfl
    rw [heq, ← eLift_stabilizerHom O O' hO σ y, hσ]
    show e (e.symm (τ (e y))) = τ (e y)
    exact e.apply_symm_apply _

end S_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
end P2MW
export P2MW.S_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois (solution)
