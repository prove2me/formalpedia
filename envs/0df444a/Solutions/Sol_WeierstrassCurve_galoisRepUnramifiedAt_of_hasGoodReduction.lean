-- Prove2me | solution 1 for WeierstrassCurve.galoisRepUnramifiedAt_of_hasGoodReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/43e8434d-cc9e-573b-bc2b-367a86610e13

import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq
import Theorems.Thm_WeierstrassCurve_hasGoodReduction_baseChange_of_valuation_lt_one
import Theorems.Thm_WeierstrassCurve_reducePoint_some
import Theorems.Thm_WeierstrassCurve_reducePoint_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_reducePoint_add
import Theorems.Thm_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_PointReduction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum
open scoped WeierstrassCurve.Affine

local notation "Qb" => AlgebraicClosure ℚ

namespace NOSAssembly

theorem reduceCoord_map (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (σR : R ≃+* R) (σK : K ≃+* K)
    (hcomp : ∀ r : R, σK (algebraMap R K r) = algebraMap R K (σR r))
    (σk : ResidueField R ≃+* ResidueField R)
    (hres : ∀ r : R, σk (residue R r) = residue R (σR r)) (x : K) :
    reduceCoord R (σK x) = σk (reduceCoord R x) := by
  classical
  by_cases hx : ∃ r : R, algebraMap R K r = x
  · have hσx : ∃ r : R, algebraMap R K r = σK x :=
      ⟨σR hx.choose, by rw [← hcomp, hx.choose_spec]⟩
    simp only [reduceCoord, dif_pos hx, dif_pos hσx, hres]
    have hc : hσx.choose = σR hx.choose :=
      IsFractionRing.injective R K (by rw [hσx.choose_spec, ← hcomp, hx.choose_spec])
    rw [hc]
  · have hσx : ¬ ∃ r : R, algebraMap R K r = σK x := by
      rintro ⟨r, hr⟩
      exact hx ⟨σR.symm r, σK.injective (by rw [hcomp, RingEquiv.apply_symm_apply, hr])⟩
    simp only [reduceCoord, dif_neg hx, dif_neg hσx, map_zero]

theorem point_descend_of_mem (W : WeierstrassCurve ℚ) (L : IntermediateField ℚ Qb)
    (x y : Qb) (hx : x ∈ L) (hy : y ∈ L)
    (h : (W.baseChange Qb).toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange L).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩,
      WeierstrassCurve.Affine.Point.map L.val
          (WeierstrassCurve.Affine.Point.some ⟨x, hx⟩ ⟨y, hy⟩ h')
        = WeierstrassCurve.Affine.Point.some x y h := by
  have h' : (W.baseChange L).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
    (W.toAffine.baseChange_nonsingular (f := L.val) L.val.injective (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)).mp h
  exact ⟨h', rfl⟩

end NOSAssembly

open NOSAssembly

set_option maxHeartbeats 3200000 in

theorem galoisRepUnramifiedAt_of_hasGoodReduction'
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ]
    [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) [E.HasGoodReduction R]
    {q n : ℕ} (hq : q.Prime) (hqR : Irreducible (q : R)) (hqn : ¬ q ∣ n) :
    WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := Qb) ℚ E n q := by
  classical

  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ Qb := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb
  intro A hA σ₀ hσ₀ P

  obtain ⟨σ, hσI, rfl⟩ := Subgroup.mem_map.mp hσ₀
  have hAval : A.valuation ((q : ℕ) : Qb) < 1 := hA
  apply Subtype.ext
  show (σ : Qb ≃ₐ[ℚ] Qb) • (P : (E⁄Qb).Point) = P
  rw [WeierstrassCurve.Affine.Point.algEquiv_smul_def]
  set σ₁ : Qb ≃ₐ[ℚ] Qb := ((A.decompositionSubgroup ℚ).subtype σ) with hσ₁def

  obtain ⟨Pv, hPn⟩ := P
  simp only
  cases Pv with
  | zero => rfl
  | some x y h =>
  set L₀ : IntermediateField ℚ Qb := IntermediateField.adjoin ℚ {x, y} with hL₀def
  haveI : FiniteDimensional ℚ L₀ := by
    rw [hL₀def]
    exact IntermediateField.finiteDimensional_adjoin_pair
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hx0 : x ∈ L₀ := IntermediateField.subset_adjoin ℚ {x, y} (Set.mem_insert x {y})
  have hy0 : y ∈ L₀ := IntermediateField.subset_adjoin ℚ {x, y} (Set.mem_insert_of_mem x rfl)
  set L : IntermediateField ℚ Qb := IntermediateField.normalClosure ℚ (↥L₀) Qb with hLdef
  haveI : FiniteDimensional ℚ L := by rw [hLdef]; infer_instance
  haveI : Normal ℚ L := by rw [hLdef]; exact normalClosure.normal ℚ (↥L₀) Qb
  have hx : x ∈ L := L₀.le_normalClosure hx0
  have hy : y ∈ L := L₀.le_normalClosure hy0

  set S : ValuationSubring L := A.comap (algebraMap L Qb) with hSdef
  haveI hSdvr : IsDiscreteValuationRing S :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L A hq hA
  have hqmem : ((q : ℕ) : L) ∈ S := by
    show algebraMap L Qb ((q : ℕ) : L) ∈ A
    rw [map_natCast]
    exact natCast_mem A q
  set ι : S →+* A :=
    RingHom.codRestrict ((algebraMap L Qb).comp S.subtype) A.toSubring
      (fun z => z.2) with hιdef
  have hq_nonunit : ¬ IsUnit (⟨((q : ℕ) : L), hqmem⟩ : S) := by
    intro hu
    have hu' : IsUnit (ι ⟨((q : ℕ) : L), hqmem⟩) := hu.map ι
    have h1 := (A.valuation_eq_one_iff _).mp hu'
    have h2 : ((ι ⟨((q : ℕ) : L), hqmem⟩ : A) : Qb) = ((q : ℕ) : Qb) := by
      show algebraMap L Qb ((q : ℕ) : L) = _
      rw [map_natCast]
    rw [h2] at h1
    exact hAval.ne h1
  have hSval : S.valuation ((q : ℕ) : L) < 1 := by
    refine lt_of_le_of_ne (S.valuation_le_one ⟨((q : ℕ) : L), hqmem⟩) ?_
    intro h1
    exact hq_nonunit ((S.valuation_eq_one_iff _).mpr h1)

  haveI hGood : (E.baseChange L).HasGoodReduction S :=
    WeierstrassCurve.hasGoodReduction_baseChange_of_valuation_lt_one R E L S hq hqR hSval

  obtain ⟨τ, hτ⟩ := ValuationSubring.exists_inertiaSubgroup_restrictNormal_eq L A ⟨σ, hσI⟩
  have hτ' : ((τ : S.decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L) = AlgEquiv.restrictNormalHom L σ₁ := hτ
  have hcomm : ∀ z : L, algebraMap L Qb
      (((τ : S.decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L) z) = σ₁ (algebraMap L Qb z) := by
    intro z
    rw [hτ']
    exact AlgEquiv.restrictNormal_commutes σ₁ L z

  obtain ⟨h', hmap⟩ := point_descend_of_mem E L x y hx hy h
  set PL : (E.baseChange L).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some ⟨x, hx⟩ ⟨y, hy⟩ h' with hPLdef

  have hnP : (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (E⁄Qb).Point) = 0 := by
    simpa using hPn
  have hnPL : (n : ℤ) • PL = 0 := by
    apply WeierstrassCurve.Affine.Point.map_injective (f := L.val)
    rw [map_zsmul, hmap, map_zero]
    exact hnP
  have hnPL' : n • PL = 0 := by
    have := hnPL; rwa [natCast_zsmul] at this

  set τL : L ≃ₐ[ℚ] L := ((τ : S.decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L) with hτLdef

  have hstab : ∀ z : L, z ∈ S → τL z ∈ S := fun z hz =>
    (((τ : S.decompositionSubgroup ℚ)) • (⟨z, hz⟩ : S)).2
  have hstab' : ∀ z : L, τL z ∈ S → z ∈ S := by
    intro z hz
    have h2 := ((((τ : S.decompositionSubgroup ℚ))⁻¹) • (⟨τL z, hz⟩ : S)).2
    have h3 : (((((τ : S.decompositionSubgroup ℚ))⁻¹ :
        S.decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L)) (τL z) = z := by
      show ((τL)⁻¹) (τL z) = z
      rw [AlgEquiv.aut_inv]
      exact AlgEquiv.symm_apply_apply _ _
    rwa [show ((((τ : S.decompositionSubgroup ℚ))⁻¹ • (⟨τL z, hz⟩ : S) : S) : L)
      = (((((τ : S.decompositionSubgroup ℚ))⁻¹ :
          S.decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L)) (τL z) from rfl, h3] at h2
  have hv_mem : ∀ z : L, valuation L (maximalIdeal S) z ≤ 1 ↔ z ∈ S := by
    intro z
    constructor
    · intro hz
      obtain ⟨s, hs⟩ := exists_lift_of_le_one hz
      rw [← hs]
      exact s.2
    · intro hz
      have h1 : algebraMap S L (⟨z, hz⟩ : S) = z := rfl
      rw [← h1]
      exact (IsDiscreteValuationRing.maximalIdeal S).valuation_le_one (K := L) _
  have hvτ : ∀ z : L, valuation L (maximalIdeal S) (τL z) ≤ 1
      ↔ valuation L (maximalIdeal S) z ≤ 1 := by
    intro z
    rw [hv_mem, hv_mem]
    exact ⟨hstab' z, hstab z⟩

  set σR : S ≃+* S :=
    MulSemiringAction.toRingAut (S.decompositionSubgroup ℚ) S
      (τ : S.decompositionSubgroup ℚ) with hσRdef
  set σk : ResidueField S ≃+* ResidueField S :=
    MulSemiringAction.toRingAut (S.decompositionSubgroup ℚ) (ResidueField S)
      (τ : S.decompositionSubgroup ℚ) with hσkdef
  have hσk1 : σk = 1 := MonoidHom.mem_ker.mp τ.2
  have hrc : ∀ z : L, reduceCoord S (τL z) = reduceCoord S z := by
    intro z
    have hres : ∀ s : S, σk (residue S s) = residue S (σR s) := fun s =>
      (IsLocalRing.ResidueField.residue_smul (S.decompositionSubgroup ℚ)
        ((τ : S.decompositionSubgroup ℚ)) s).symm
    have h1 := reduceCoord_map S σR τL.toRingEquiv (fun s => rfl) σk hres z
    rw [hσk1] at h1
    exact h1

  have hzero : ∀ (a b : L) (hab : (E.baseChange L).toAffine.Nonsingular a b),
      ¬ (valuation L (maximalIdeal S) a ≤ 1 ∧ valuation L (maximalIdeal S) b ≤ 1) →
      reducePoint_alt S (E.baseChange L) (.some a b hab) = 0 := by
    intro a b hab hguard
    show (if _ : valuation L (maximalIdeal S) a ≤ 1 ∧ valuation L (maximalIdeal S) b ≤ 1
        then _ else WeierstrassCurve.Affine.Point.zero) = _
    rw [dif_neg hguard]
    rfl
  have hred_fix : ∀ Q : (E.baseChange L).toAffine.Point,
      reducePoint_alt S (E.baseChange L) (WeierstrassCurve.Affine.Point.map τL.toAlgHom Q)
        = reducePoint_alt S (E.baseChange L) Q := by
    intro Q
    cases Q with
    | zero => rfl
    | some a b hQ =>
      have hcoe : ∀ z : L, τL.toAlgHom z = τL z := fun z => rfl
      rw [WeierstrassCurve.Affine.Point.map_some]
      simp only [hcoe]
      by_cases hva : valuation L (maximalIdeal S) a ≤ 1
      · by_cases hvb : valuation L (maximalIdeal S) b ≤ 1
        · have hnsτ : (E.baseChange L).toAffine.Nonsingular (τL a) (τL b) :=
            (E.toAffine.baseChange_nonsingular (f := τL.toAlgHom)
              τL.toAlgHom.injective a b).mpr hQ
          obtain ⟨hh1, he1⟩ := WeierstrassCurve.reducePoint_some S (E.baseChange L)
            hnsτ ((hvτ a).mpr hva) ((hvτ b).mpr hvb)
          obtain ⟨hh2, he2⟩ := WeierstrassCurve.reducePoint_some S (E.baseChange L) hQ hva hvb
          rw [he1, he2]
          simp only [WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hrc a, hrc b⟩
        · rw [hzero _ _ _ (fun hc => hvb hc.2),
            hzero _ _ _ (fun hc => hvb ((hvτ b).mp hc.2))]
      · rw [(WeierstrassCurve.reducePoint_some_eq_zero_iff S (E.baseChange L) hQ).mpr hva,
          (WeierstrassCurve.reducePoint_some_eq_zero_iff S (E.baseChange L) _).mpr
            (fun hc => hva ((hvτ a).mp hc))]

  have hn0 : ((n : ℕ) : ResidueField S) ≠ 0 := by
    intro h0
    have hmemn : ((n : ℕ) : S) ∈ IsLocalRing.maximalIdeal S := by
      rw [← residue_eq_zero_iff, map_natCast]
      exact h0
    have hnu : ¬ IsUnit ((n : ℕ) : S) := mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hmemn)
    have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hcop : IsCoprime (q : ℤ) (n : ℤ) := hqp.coprime_iff_not_dvd.mpr (by exact_mod_cast hqn)
    obtain ⟨u, v, huv⟩ := hcop.map (algebraMap ℤ S)
    have h1 : IsUnit (u * algebraMap ℤ S (q : ℤ) + v * algebraMap ℤ S (n : ℤ)) := by
      rw [huv]; exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h2 | h2
    · refine hq_nonunit ?_
      have h3 : (algebraMap ℤ S (q : ℤ)) = (⟨((q : ℕ) : L), hqmem⟩ : S) := by
        apply Subtype.ext
        push_cast
        rfl
      rw [h3] at h2
      exact isUnit_of_mul_isUnit_right h2
    · refine hnu ?_
      have h3 : (algebraMap ℤ S (n : ℤ)) = ((n : ℕ) : S) := by push_cast; rfl
      rw [h3] at h2
      exact isUnit_of_mul_isUnit_right h2

  have hD : WeierstrassCurve.Affine.Point.map τL.toAlgHom PL = PL := by
    have hnPLτ : n • WeierstrassCurve.Affine.Point.map τL.toAlgHom PL = 0 :=
      calc n • WeierstrassCurve.Affine.Point.map τL.toAlgHom PL
          = WeierstrassCurve.Affine.Point.map τL.toAlgHom (n • PL) := (map_nsmul _ _ _).symm
        _ = WeierstrassCurve.Affine.Point.map τL.toAlgHom 0 := by rw [hnPL']
        _ = 0 := map_zero _
    have hnD : n • (WeierstrassCurve.Affine.Point.map τL.toAlgHom PL - PL) = 0 :=
      calc n • (WeierstrassCurve.Affine.Point.map τL.toAlgHom PL - PL)
          = n • WeierstrassCurve.Affine.Point.map τL.toAlgHom PL - n • PL := nsmul_sub _ _ _
        _ = 0 - 0 := by rw [hnPLτ, hnPL']
        _ = 0 := by rw [sub_zero]
    have hred0 : reducePoint_alt S (E.baseChange L)
        (WeierstrassCurve.Affine.Point.map τL.toAlgHom PL - PL) = 0 := by
      have h4 : reducePoint_alt S (E.baseChange L)
            (WeierstrassCurve.Affine.Point.map τL.toAlgHom PL - PL)
          + reducePoint_alt S (E.baseChange L) PL
          = 0 + reducePoint_alt S (E.baseChange L) PL := by
        rw [← WeierstrassCurve.reducePoint_add, sub_add_cancel, zero_add]
        exact hred_fix PL
      exact add_right_cancel h4
    have := WeierstrassCurve.eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero S (E.baseChange L)
      hn0 _ hnD hred0
    exact sub_eq_zero.mp this

  have hcoe2 : ∀ z : L, τL.toAlgHom z = τL z := fun z => rfl
  have hD' := hD
  rw [hPLdef, WeierstrassCurve.Affine.Point.map_some] at hD'
  simp only [hcoe2, WeierstrassCurve.Affine.Point.some.injEq] at hD'
  obtain ⟨hDx, hDy⟩ := hD'
  show WeierstrassCurve.Affine.Point.map σ₁.toAlgHom
      (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.map_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · calc σ₁.toAlgHom x = σ₁ (algebraMap L Qb ⟨x, hx⟩) := rfl
      _ = algebraMap L Qb (τL ⟨x, hx⟩) := (hcomm ⟨x, hx⟩).symm
      _ = algebraMap L Qb ⟨x, hx⟩ := by rw [hDx]
      _ = x := rfl
  · calc σ₁.toAlgHom y = σ₁ (algebraMap L Qb ⟨y, hy⟩) := rfl
      _ = algebraMap L Qb (τL ⟨y, hy⟩) := (hcomm ⟨y, hy⟩).symm
      _ = algebraMap L Qb ⟨y, hy⟩ := by rw [hDy]
      _ = y := rfl

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) [E.HasGoodReduction R]
    {q n : ℕ} (hq : q.Prime) (hqR : Irreducible (q : R)) (hqn : ¬ q ∣ n) :
    WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ E n q :=
  galoisRepUnramifiedAt_of_hasGoodReduction' R E hq hqR hqn

end

end S_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction
end P2MW
export P2MW.S_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction (solution)
