-- Prove2me | solution 1 for WeierstrassCurve.exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e01b5721-1021-513c-8564-86684388f25a

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Theorems.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty"

p2m_open "Polynomial ModularCurve WeierstrassCurve P2MW.S_WeierstrassCurve_exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero.WeierstrassCurve WeierstrassCurve.Affine"

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ map Affine.Point.some Affine.Point.some.injEq Affine.Point.zero_def toAffine Affine.Point Affine.Point.some_ne_zero Δ Affine.Y_eq_of_X_eq Affine.Point.zero Affine.Point.neg_some j fullKernelQuotient fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet fullKernelQuotient_two oddOrderSummingSet veluGy veluQuotient veluQuotient2 natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow isElliptic_veluQuotient2_of_isElliptic exists_addMonoidHom_coe_eq_veluPointMap2 veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2"
p2m_open "WeierstrassCurve"

private theorem _root_.WeierstrassCurve.some_eq_of_X_eq_of_veluGy_eq_zero {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x₀ y₀ y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (h : W.toAffine.Nonsingular x₀ y) :
    (Affine.Point.some x₀ y h : W.toAffine.Point) = Affine.Point.some x₀ y₀ h₀ := by
  have hneg : W.toAffine.negY x₀ y₀ = y₀ := by
    simp only [veluGy] at hgy
    simp only [Affine.negY]
    linear_combination hgy
  have hy : y = y₀ := by
    rcases Affine.Y_eq_of_X_eq h.1 h₀.1 rfl with hy | hy
    · exact hy
    · rw [hy, hneg]
  subst hy
  rfl

p2m_export "WeierstrassCurve" "some_eq_of_X_eq_of_veluGy_eq_zero"

private theorem natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_self
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card {G : AddSubgroup W.toAffine.Point // IsAddCyclic G ∧ Nat.card G = N} =
      dedekindPsi N :=
  WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
    (F := K) (K := K) W hN

private theorem _root_.WeierstrassCurve.exists_enum_cyclic_fullKernelQuotient_of_forall_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    (hD : ∀ Q : W.toAffine.Point, addOrderOf Q = N → (W.fullKernelQuotient Q N).Δ ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = dedekindPsi N ∧
      ∃ Q : ι → W.toAffine.Point, (∀ i, addOrderOf (Q i) = N) ∧
        Function.Injective (fun i => AddSubgroup.zmultiples (Q i)) ∧
        ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0 := by
  classical

  set S := {G : AddSubgroup W.toAffine.Point // IsAddCyclic G ∧ Nat.card G = N} with hS
  have hcard : Nat.card S = dedekindPsi N :=
    natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_self hN W
  have hψ : 0 < dedekindPsi N := ModularCurve.dedekindPsi_pos N (NeZero.ne N)
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hψ.ne')
  letI : Fintype S := Fintype.ofFinite S
  have hcardF : Fintype.card S = dedekindPsi N := by rw [← Nat.card_eq_fintype_card, hcard]
  let e : S ≃ Fin (dedekindPsi N) := Fintype.equivFinOfCardEq hcardF

  have hgen : ∀ G : S, ∃ g : W.toAffine.Point, AddSubgroup.zmultiples g = G.1 := fun G =>
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top G.1).mp G.2.1
  choose g hg using hgen
  have hord : ∀ G : S, addOrderOf (g G) = N := fun G => by
    rw [← Nat.card_zmultiples (g G), hg G]
    exact G.2.2
  refine ⟨Fin (dedekindPsi N), inferInstance, Fintype.card_fin _, fun i => g (e.symm i),
    fun i => hord _, ?_, fun i => hD _ (hord _)⟩
  intro i j hij
  have h1 : (e.symm i).1 = (e.symm j).1 := by
    have hij' : AddSubgroup.zmultiples (g (e.symm i)) = AddSubgroup.zmultiples (g (e.symm j)) := hij
    rwa [hg, hg] at hij'
  exact e.symm.injective (Subtype.ext h1)

p2m_export "WeierstrassCurve" "exists_enum_cyclic_fullKernelQuotient_of_forall_discriminant_ne_zero"

private theorem _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_isElliptic
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0 := by
  intro h0
  have h := W.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow Q hQ
  rw [h0, zero_mul] at h
  exact pow_ne_zero _ W.isUnit_Δ.ne_zero h.symm

p2m_export "WeierstrassCurve" "veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_isElliptic"

private theorem _root_.WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {N : ℕ} (hN : Odd N) (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  obtain ⟨n, rfl⟩ := hN
  rw [W.fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet Q n hQ]
  exact W.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_isElliptic n Q hQ

p2m_export "WeierstrassCurve" "fullKernelQuotient_discriminant_ne_zero_of_odd"

private theorem _root_.WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero_two
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2) :
    (W.fullKernelQuotient Q 2).Δ ≠ 0 := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, addOrderOf_zero] at hQ
    exact absurd hQ (by decide)
  ·
    have h2 : (2 : ℕ) • (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      rw [← hQ]; exact addOrderOf_nsmul_eq_zero _
    have hneg : -(Affine.Point.some x y h : W.toAffine.Point) = Affine.Point.some x y h := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul]; exact h2
    rw [Affine.Point.neg_some] at hneg
    have hy : W.toAffine.negY x y = y := by
      have := (Affine.Point.some.injEq _ _ _ _ _ _).mp hneg
      exact this.2
    have hgy : W.veluGy x y = 0 := by
      simp only [veluGy, Affine.negY] at hy ⊢
      linear_combination hy
    rw [W.fullKernelQuotient_two h hgy]
    exact (isElliptic_veluQuotient2_of_isElliptic h.1 hgy).isUnit.ne_zero

p2m_export "WeierstrassCurve" "fullKernelQuotient_discriminant_ne_zero_two"

private theorem _root_.WeierstrassCurve.addOrderOf_veluPointMap2_eq {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {m : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    {x₀ y₀ : F} {h₀ : W.toAffine.Nonsingular x₀ y₀}
    (hT : (m + 1) • Q = Affine.Point.some x₀ y₀ h₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    addOrderOf (veluPointMap2 h2 h₀.1 hgy hΔ Q) = m + 1 := by
  obtain ⟨φ, hφ⟩ := W.exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₀.1 hgy hΔ
  rw [← hφ]
  have hne : ∀ k, 0 < k → k < 2 * (m + 1) → k • Q ≠ 0 := fun k hk1 hk2 =>
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; exact hk2)

  have hcoords : ∀ i, i < m → ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      (i + 1) • Q = Affine.Point.some x y h ∧ x ≠ x₀ := by
    intro i hi
    rcases hP : (i + 1) • Q with _ | ⟨x, y, h⟩
    · exact absurd (hP.trans Affine.Point.zero_def.symm) (hne (i + 1) (by omega) (by omega))
    · refine ⟨x, y, h, rfl, fun hx => ?_⟩
      subst hx
      have hPT : (i + 1) • Q = (m + 1) • Q := by
        rw [hP, hT, W.some_eq_of_X_eq_of_veluGy_eq_zero h₀ hgy h]
      have := nsmul_injOn_Iio_addOrderOf (x := Q) (by simp only [Set.mem_Iio]; omega)
        (by simp only [Set.mem_Iio]; omega) hPT
      omega

  have hzero : (m + 1) • φ Q = 0 := by
    rw [← map_nsmul φ (m + 1) Q, hT, hφ, veluPointMap2_some_of_eq h2 h₀.1 hgy hΔ h₀ rfl]
    rfl
  have hfin : IsOfFinAddOrder (φ Q) :=
    φ.isOfFinAddOrder (addOrderOf_pos_iff.mp (by rw [hQ]; omega))
  have hk : 0 < addOrderOf (φ Q) := addOrderOf_pos_iff.mpr hfin
  have hdvd : addOrderOf (φ Q) ∣ m + 1 := addOrderOf_dvd_of_nsmul_eq_zero hzero
  have hle : addOrderOf (φ Q) ≤ m + 1 := Nat.le_of_dvd (by omega) hdvd

  have hgt : m < addOrderOf (φ Q) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, y, h, hP, hx⟩ := hcoords (addOrderOf (φ Q) - 1) (by omega)
    have h0 : (addOrderOf (φ Q) - 1 + 1) • φ Q = 0 := by
      rw [Nat.sub_add_cancel hk, addOrderOf_nsmul_eq_zero]
    rw [← map_nsmul φ (addOrderOf (φ Q) - 1 + 1) Q, hP, hφ,
      veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx] at h0
    exact Affine.Point.some_ne_zero _ h0
  omega

p2m_export "WeierstrassCurve" "addOrderOf_veluPointMap2_eq"

private theorem fullKernelQuotient_discriminant_ne_zero
    {F : Type*} [Field F] [DecidableEq F] :
    ∀ (N : ℕ) (W : WeierstrassCurve F) [W.IsElliptic], (N : F) ≠ 0 →
      ∀ (Q : W.toAffine.Point), addOrderOf Q = N → (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro W _ hN Q hQ
  rcases Nat.even_or_odd N with ⟨d, rfl⟩ | hodd
  ·
    have hd0 : d ≠ 0 := by rintro rfl; exact hN (by simp)
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have h2 : (2 : F) ≠ 0 := by
      intro h; apply hN; rw [show ((m + 1 + (m + 1) : ℕ) : F) = 2 * (m + 1 : ℕ) by push_cast; ring, h,
        zero_mul]
    have hm1 : ((m + 1 : ℕ) : F) ≠ 0 := by
      intro h; apply hN; rw [show ((m + 1 + (m + 1) : ℕ) : F) = 2 * (m + 1 : ℕ) by push_cast; ring, h,
        mul_zero]
    have hQ' : addOrderOf Q = 2 * (m + 1) := by rw [hQ]; ring

    have hTne : (m + 1) • Q ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ']; omega)
    have hT2 : 2 • ((m + 1) • Q) = 0 := by
      rw [← mul_nsmul', ← hQ', addOrderOf_nsmul_eq_zero]
    rcases hT : (m + 1) • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd (hT.trans Affine.Point.zero_def.symm) hTne
    rw [hT] at hT2 hTne
    have hneg : -(Affine.Point.some x₀ y₀ h₀ : W.toAffine.Point) = Affine.Point.some x₀ y₀ h₀ := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul]; exact hT2
    rw [Affine.Point.neg_some] at hneg
    have hy : W.toAffine.negY x₀ y₀ = y₀ := ((Affine.Point.some.injEq _ _ _ _ _ _).mp hneg).2
    have hgy : W.veluGy x₀ y₀ = 0 := by
      simp only [veluGy, Affine.negY] at hy ⊢
      linear_combination hy

    have hΔ₁ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
      have hord : addOrderOf (Affine.Point.some x₀ y₀ h₀ : W.toAffine.Point) = 2 :=
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        addOrderOf_eq_prime hT2 hTne
      have := W.fullKernelQuotient_discriminant_ne_zero_two _ hord
      rwa [W.fullKernelQuotient_two h₀ hgy] at this
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩

    rw [show m + 1 + (m + 1) = 2 * (m + 1) by ring,
      W.fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 h2 Q hQ' hT hgy hΔ₁]
    exact ih (m + 1) (by omega) (W.veluQuotient2 x₀ y₀) hm1 _
      (W.addOrderOf_veluPointMap2_eq h2 Q hQ' hT hgy hΔ₁)
  · exact W.fullKernelQuotient_discriminant_ne_zero_of_odd hodd Q hQ

end WeierstrassCurve

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = dedekindPsi N ∧
      ∃ Q : ι → W.toAffine.Point, (∀ i, addOrderOf (Q i) = N) ∧
        Function.Injective (fun i => AddSubgroup.zmultiples (Q i)) ∧
        ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0 :=
  W.exists_enum_cyclic_fullKernelQuotient_of_forall_discriminant_ne_zero hN
    fun Q hQ => WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N W hN Q hQ

end S_WeierstrassCurve_exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero (solution)
