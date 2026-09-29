-- Prove2me | solution 1 for ValuationSubring.map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1f1c1b50-9a9b-59b1-99f6-3f9ab1abe529

import Mathlib
import Theorems.Thm_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
import Theorems.Thm_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia

set_option autoImplicit false

open scoped Pointwise
open IsLocalRing

namespace CoreGlue

theorem perfectField_of_ringEquiv {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K') [PerfectField K] :
    PerfectField K' := by
  refine ⟨fun {f} hf => ?_⟩
  have hirr : Irreducible (f.map (e.symm : K' →+* K)) := by
    have : Irreducible ((Polynomial.mapEquiv e.symm) f) := (MulEquiv.irreducible_iff (Polynomial.mapEquiv e.symm)).mpr hf
    simpa using this
  have hsep := PerfectField.separable_of_irreducible hirr
  have := hsep.map (f := (e : K →+* K'))
  rwa [Polynomial.map_map, show (e : K →+* K').comp (e.symm : K' →+* K) = RingHom.id K' from by
    ext x; simp, Polynomial.map_id] at this

end CoreGlue

theorem solution
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P]
    [PerfectField (IsLocalRing.ResidueField ↥(P.comap (FixedPoints.subfield G F).subtype))] :
    Ideal.map (show ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥P from
        { toFun := fun r => ⟨(FixedPoints.subfield G F).subtype r, r.2⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun a b => Subtype.ext (map_add _ _ _) })
        (IsLocalRing.maximalIdeal ↥(P.comap (FixedPoints.subfield G F).subtype)) =
      IsLocalRing.maximalIdeal ↥P ^
        Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} := by
  classical
  obtain ⟨inst, 𝔓, hGSF, hRdvr, hRded, hfracK, hSded, hfin, htf, hfrF, hgal, hSP, h𝔓max, hpmax, hpne, hpR, hcent, hfrac⟩ :=
    ValuationSubring.exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing (G := G) P
  letI := inst
  haveI := hRdvr; haveI := hRded; haveI := hSded; haveI := hfin; haveI := htf; haveI := hfrF; haveI := hgal; haveI := h𝔓max

  have hp_eq : Ideal.comap (algebraMap (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) (↥(integralClosure (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) F))) 𝔓 = maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) :=
    IsLocalRing.eq_maximalIdeal hpmax
  haveI hlies : 𝔓.LiesOver (maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) := ⟨hp_eq.symm⟩
  have hm2 : maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) ≠ ⊥ := by rw [← hp_eq]; exact hpne

  let e : ↥(P.comap (FixedPoints.subfield G F).subtype) ≃+* ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) :=
    { toFun := fun r => ⟨(r : ↥(FixedPoints.subfield G F)), ⟨r.2, (r : ↥(FixedPoints.subfield G F)).2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, by
        show (FixedPoints.subfield G F).subtype ⟨x.1, x.2.2⟩ ∈ P
        exact x.2.1⟩
      left_inv := fun r => by rfl
      right_inv := fun x => by rfl
      map_mul' := fun a b => rfl
      map_add' := fun a b => rfl }

  letI : Field ((↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) ⧸ maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) := Ideal.Quotient.field _
  letI : Field ((↥(integralClosure (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) F)) ⧸ 𝔓) := Ideal.Quotient.field _
  haveI : PerfectField ((↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) ⧸ maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) :=
    CoreGlue.perfectField_of_ringEquiv (K := ResidueField ↥(P.comap (FixedPoints.subfield G F).subtype)) (IsLocalRing.ResidueField.mapEquiv e)
  haveI : Algebra.IsSeparable ((↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) ⧸ maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) ((↥(integralClosure (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) F)) ⧸ 𝔓) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  have hcard := (ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
    (R := ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) hGSF 𝔓 P hSP hcent hfrac).2 (maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) hm2

  have hgalidx : (maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))).ramificationIdxIn (↥(integralClosure (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) F)) =
      Ideal.ramificationIdx' (maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) 𝔓 :=
    (Ideal.ramificationIdxIn_eq_ramificationIdx
      (maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) 𝔓 G).trans
      (Ideal.ramificationIdx'_eq_ramificationIdx _ 𝔓 hm2).symm

  let φ₂ : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) →+* ↥P :=
    { toFun := fun x => ⟨x.1, x.2.1⟩
      map_one' := rfl
      map_mul' := fun a b => rfl
      map_zero' := rfl
      map_add' := fun a b => rfl }
  have hφ₂ : ∀ r : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring), ((φ₂ r : ↥P) : F) = algebraMap (↥(integralClosure (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) F)) F (algebraMap (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) (↥(integralClosure (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) F)) r) := fun r => rfl
  have hbridge := Ideal.map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx (maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring))) hm2 𝔓 P hSP hcent hfrac φ₂ hφ₂

  have hmap_e : Ideal.map (e : ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) (maximalIdeal ↥(P.comap (FixedPoints.subfield G F).subtype)) = maximalIdeal (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) := by
    rw [Ideal.map_comap_of_equiv]
    ext x
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (MulEquiv.isUnit_map e.symm).not
  have hhom : (show ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥P from
        { toFun := fun r => ⟨(FixedPoints.subfield G F).subtype r, r.2⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun a b => Subtype.ext (map_add _ _ _) }) = φ₂.comp (e : ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) := by
    ext r; rfl
  rw [hhom, ← Ideal.map_map, hmap_e, hbridge, ← hgalidx, ← hcard]

end S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia
end P2MW
export P2MW.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia (solution)
