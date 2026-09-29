-- Prove2me | solution 1 for WeierstrassCurve.exists_torsion_forall_unitKummer_exists_inertia_smul_ne_of_not_dvd_padicValInt_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1c9464bb-1e54-50ed-9480-4b09ad4381fa

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_TateCurve_TateParameter
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le
import Theorems.Thm_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_torsion_forall_unitKummer_exists_inertia_smul_ne_of_not_dvd_padicValInt_of_five_le
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"

set_option autoImplicit false
open scoped WeierstrassCurve.Affine NNReal Classical Pointwise
p2m_open "WeierstrassCurve~card WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace E87T35

variable (p : ℕ) [Fact p.Prime]

theorem mem_nonunits_padicIntegers_iff (z : PadicAlgCl p) :
    z ∈ (padicIntegers p).nonunits ↔ ‖z‖₊ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_or, mem_padicIntegers_iff, nnnorm_inv, not_le]
  by_cases hz : z = 0
  · simp [hz]
  · have hpos : 0 < ‖z‖₊ := nnnorm_pos.mpr hz
    rw [one_lt_inv₀ hpos]
    simp [hz]

theorem mem_nonunits_padicPlace_iff (x : AlgebraicClosure ℚ) :
    x ∈ (padicPlace p).nonunits ↔ ‖padicEmbedding p x‖₊ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_or, ← mem_nonunits_padicIntegers_iff,
    ValuationSubring.mem_nonunits_iff_or, mem_padicPlace_iff, mem_padicIntegers_iff, map_inv₀,
    map_eq_zero_iff (padicEmbedding p) (padicEmbedding p).injective]

theorem apply_mem_and_sub_mem_nonunits_of_mem_inertiaSubgroupIn {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K)
    (a : L) (ha : a ∈ A) :
    τ a ∈ A ∧ τ a - a ∈ A.nonunits := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hτ
  have hgA : (g : L ≃ₐ[K] L) • A = A := g.2
  have hmem : (g : L ≃ₐ[K] L) a ∈ A := by
    have : (g : L ≃ₐ[K] L) • a ∈ (g : L ≃ₐ[K] L) • (A : ValuationSubring L) :=
      Set.smul_mem_smul_set (a := (g : L ≃ₐ[K] L)) ha
    rw [hgA] at this
    exact this
  refine ⟨hmem, ?_⟩
  have hker := (MonoidHom.mem_ker).mp hg
  have hres : IsLocalRing.residue A (g • (⟨a, ha⟩ : A)) = IsLocalRing.residue A ⟨a, ha⟩ := by
    have h1 := congrArg (fun φ => φ (IsLocalRing.residue A ⟨a, ha⟩)) hker
    simpa using h1
  have hsub : g • (⟨a, ha⟩ : A) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hres
  have hcoe : ((g • (⟨a, ha⟩ : A) - ⟨a, ha⟩ : A) : L) = (g : L ≃ₐ[K] L) a - a := rfl
  rw [← ValuationSubring.coe_mem_nonunits_iff, hcoe] at hsub
  exact hsub

theorem mem_inertiaSubgroupIn_of {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hdec : σ ∈ A.decompositionSubgroup K)
    (h : ∀ a : L, a ∈ A → σ a - a ∈ A.nonunits) :
    σ ∈ A.inertiaSubgroupIn K := by
  refine Subgroup.mem_map.mpr ⟨⟨σ, hdec⟩, ?_, rfl⟩
  show (⟨σ, hdec⟩ : A.decompositionSubgroup K) ∈
    MonoidHom.ker (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A))
  rw [MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
    ← IsLocalRing.ResidueField.residue_smul]
  change IsLocalRing.residue A _ = IsLocalRing.residue A a
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  exact h a a.2

end E87T35

namespace E87T35

theorem localGaloisToGlobal_mem_inertiaSubgroupIn (p : ℕ) [Fact p.Prime]
    {τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hτ : τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) :
    localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ := by
  apply mem_inertiaSubgroupIn_of _ (localGaloisToGlobal_mem_decompositionSubgroup p τ)
  intro a ha
  rw [mem_nonunits_padicPlace_iff, map_sub, padicEmbedding_localGaloisToGlobal,
    ← mem_nonunits_padicIntegers_iff]
  exact (apply_mem_and_sub_mem_nonunits_of_mem_inertiaSubgroupIn (padicIntegers p) hτ _
    ((mem_padicPlace_iff p).mp ha)).2

theorem exists_exponents (p : ℕ) [Fact p.Prime] {ζ t : AlgebraicClosure ℚ_[p]} (hζ : IsPrimitiveRoot ζ p)
    {qT : ℚ_[p]} (ht : t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT) (hqT0 : qT ≠ 0)
    (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) :
    ∃ e c : ℕ, τ ζ = ζ ^ e ∧ τ t = ζ ^ c * t := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h1 : (τ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one h1
  have ht0 : t ≠ 0 := by
    intro h; rw [h, zero_pow hp0.ne'] at ht
    exact hqT0 ((map_eq_zero_iff _ (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective).mp ht.symm)
  have h2 : (τ t / t) ^ p = 1 := by
    rw [div_pow, ← map_pow, ht, AlgEquiv.commutes, div_self]
    rw [← ht]; exact pow_ne_zero _ ht0
  obtain ⟨c, -, hc⟩ := hζ.eq_pow_of_pow_eq_one h2
  refine ⟨e, c, he.symm, ?_⟩
  rw [hc, div_mul_cancel₀ _ ht0]

theorem valuation_eq_of_nnnorm_eq (p : ℕ) [Fact p.Prime] {q : ℚ_[p]} (hq0 : q ≠ 0) {v : ℕ}
    (hv : ‖q‖₊ = ((p : ℝ≥0) ^ v)⁻¹) : q.valuation = v := by
  have h := Padic.norm_eq_zpow_neg_valuation hq0
  have h' : ‖q‖ = ((p : ℝ) ^ v)⁻¹ := by
    have := congrArg ((↑) : ℝ≥0 → ℝ) hv
    simpa using this
  rw [h', ← zpow_natCast, ← zpow_neg] at h
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have := zpow_right_injective₀ (zero_lt_one.trans hp1) hp1.ne' h
  omega

theorem main
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄) (htres : ¬ p ∣ padicValInt p W.Δ)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    ∃ Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, (p : ℤ) • Q = 0 ∧
      ∀ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
        (∀ i, (padicPlace p).valuation (u i) = 1) →
        (∀ i, ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, σ (u i) = u i) →
        (∀ i, β i ^ p = u i) →
        ∃ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) ∧ (∀ i, σ (β i) = β i) ∧ σ • Q ≠ Q := by
  obtain ⟨qT, ζ, t, Φ, hqT0, hv, hζ, ht, hact⟩ :=
    W.exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le p hp5 hΔ hpΔ hpc₄ hcard

  refine ⟨(Φ (0, 1) : Submodule.torsionBy ℤ _ p), (Submodule.mem_torsionBy_iff _ _).mp (Φ (0, 1)).2, ?_⟩
  intro n u β hu huI hβ

  have hval : ¬ (p : ℤ) ∣ Padic.valuation qT := by
    rw [valuation_eq_of_nnnorm_eq p hqT0 hv]
    exact_mod_cast htres

  have hu' : ∀ i, ‖padicEmbedding p (u i)‖₊ = 1 := by
    intro i
    have h1 : u i ∈ padicPlace p := (ValuationSubring.valuation_le_one_iff _ _).mp (hu i).le
    have hne : u i ≠ 0 := by
      intro h; have := hu i; rw [h, _root_.map_zero] at this; exact zero_ne_one this
    have h2 : (u i)⁻¹ ∈ padicPlace p :=
      (ValuationSubring.valuation_le_one_iff _ _).mp (by rw [map_inv₀, hu i, inv_one])
    rw [mem_padicPlace_iff] at h1 h2
    rw [map_inv₀, nnnorm_inv] at h2
    have hpos : 0 < ‖padicEmbedding p (u i)‖₊ :=
      nnnorm_pos.mpr ((map_ne_zero_iff _ (padicEmbedding p).injective).mpr hne)
    exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)
  have huI' : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      τ (padicEmbedding p (u i)) = padicEmbedding p (u i) := by
    intro i τ hτ
    rw [← padicEmbedding_localGaloisToGlobal, huI i _ (localGaloisToGlobal_mem_inertiaSubgroupIn p hτ)]
  have hβ' : ∀ i, (padicEmbedding p (β i)) ^ p = padicEmbedding p (u i) := by
    intro i; rw [← map_pow, hβ i]

  obtain ⟨τ, hτI, hτζ, hτβ, hτt⟩ :=
    PadicAlgCl.exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation p
      (fun i => padicEmbedding p (u i)) (fun i => padicEmbedding p (β i)) hu' huI' hβ' qT hval t ht

  obtain ⟨-, c, -, hc⟩ := exists_exponents p hζ ht hqT0 τ
  have he : τ ζ = ζ ^ (1 : ℕ) := by rw [pow_one]; exact hτζ ζ hζ.pow_eq_one
  have hc0 : (c : ZMod p) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    apply hτt
    rw [hc, (hζ.pow_eq_one_iff_dvd c).mpr h0, one_mul]

  refine ⟨localGaloisToGlobal p τ, localGaloisToGlobal_mem_inertiaSubgroupIn p hτI, ?_, ?_, ?_⟩
  · intro ζ₀ hζ₀
    apply (padicEmbedding p).injective
    show padicEmbedding p ((localGaloisToGlobal p τ) ζ₀) = padicEmbedding p ζ₀
    rw [padicEmbedding_localGaloisToGlobal]
    exact hτζ _ (by rw [← map_pow, hζ₀, map_one])
  · intro i
    apply (padicEmbedding p).injective
    show padicEmbedding p ((localGaloisToGlobal p τ) (β i)) = padicEmbedding p (β i)
    rw [padicEmbedding_localGaloisToGlobal]
    exact hτβ i
  · intro hQ
    have h1 : (localGaloisToGlobal p τ) • Φ (0, 1) = Φ (0, 1) := Subtype.ext hQ
    rw [hact τ hτI 1 c he hc 0 1] at h1
    have h2 := Φ.injective h1
    simp only [smul_zero, zero_add, Prod.mk.injEq, and_true] at h2
    exact hc0 (by simpa using h2)

end E87T35

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄) (htres : ¬ p ∣ padicValInt p W.Δ)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    ∃ Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, (p : ℤ) • Q = 0 ∧
      ∀ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
        (∀ i, (padicPlace p).valuation (u i) = 1) →
        (∀ i, ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, σ (u i) = u i) →
        (∀ i, β i ^ p = u i) →
        ∃ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) ∧ (∀ i, σ (β i) = β i) ∧ σ • Q ≠ Q :=
  E87T35.main W p hp5 hΔ hpΔ hpc₄ htres hcard

end S_WeierstrassCurve_exists_torsion_forall_unitKummer_exists_inertia_smul_ne_of_not_dvd_padicValInt_of_five_le
end P2MW
export P2MW.S_WeierstrassCurve_exists_torsion_forall_unitKummer_exists_inertia_smul_ne_of_not_dvd_padicValInt_of_five_le (solution)
