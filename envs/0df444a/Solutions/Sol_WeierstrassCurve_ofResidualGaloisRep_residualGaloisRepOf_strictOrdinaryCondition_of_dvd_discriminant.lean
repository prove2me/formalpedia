-- Prove2me | solution 1 for WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_strictOrdinaryCondition_of_dvd_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/34b2b17a-4b48-5f03-a671-2539b59b6194

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Theorems.Thm_WeierstrassCurve_exists_stableLine_character_of_not_isGoodPrimeFor
import Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_ordinaryCondition
import Theorems.Thm_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_strictOrdinaryCondition_of_dvd_discriminant
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open scoped WeierstrassCurve.Affine

namespace TateCurveTorsion

private theorem exists_basis_of_ne_bot_of_ne_top {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [Module.Finite k V] (h2 : Module.finrank k V = 2) (L : Submodule k V)
    (hbot : L ≠ ⊥) (htop : L ≠ ⊤) : ∃ b : Module.Basis (Fin 2) k V, L = k ∙ b 0 := by
  obtain ⟨w, hwL, hw0⟩ := (Submodule.ne_bot_iff L).mp hbot
  obtain ⟨u, huL⟩ : ∃ u : V, u ∉ L := not_forall.mp (mt Submodule.eq_top_iff'.mpr htop)
  have hli : LinearIndependent k ![w, u] :=
    (LinearIndependent.pair_iff' hw0).mpr fun a ha => huL (ha ▸ L.smul_mem a hwL)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h2, Fintype.card_fin]), ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero]
  refine (Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem w L).mpr hwL) ?_).symm
  rw [finrank_span_singleton hw0]
  have hlt : Module.finrank k L < 2 := h2 ▸ Submodule.finrank_lt htop
  have hne : Module.finrank k L ≠ 0 := fun h0 => hbot (Submodule.finrank_eq_zero.mp h0)
  omega

private theorem pow_prime_pow_eq_one_of_pow_eq_one {K : Type} [Monoid K] {μ : K} {p n : ℕ}
    (hμ : μ ^ p = 1) (hn : 0 < n) : μ ^ p ^ n = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [pow_succ', pow_mul, hμ, one_pow]

private theorem isStrictOrdinaryAt_torsion (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hpΔ : (p : ℤ) ∣ W.Δ)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p)) :
    (GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).IsStrictOrdinaryAt p := by
  have hbad : ¬ W.IsGoodPrimeFor p := fun h => h hpΔ
  refine ⟨?_, fun P hP => ?_⟩
  · rw [ZMod.natCast_self]
    exact Submodule.zero_mem _
  obtain ⟨L, ψ, hbot, htop, hD, hquot, hscal, hI, -⟩ :=
    WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor p hp2 W hΔ hW hbad P hP
  obtain ⟨b, hb⟩ := exists_basis_of_ne_bot_of_ne_top
    ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).finrank_eq L hbot htop
  have hb0 : b 0 ∈ L := by
    rw [hb]
    exact Submodule.mem_span_singleton_self (b 0)
  refine ⟨L, ⟨b, hb⟩, fun σ hσ v hv => hD ⟨σ, hσ⟩ v hv, fun σ hσ v => ?_, fun σ hσ => ?_⟩
  · obtain ⟨σ', hσ', rfl⟩ := Subgroup.mem_map.mp hσ
    have h := hquot σ' v
    rw [hI σ' hσ', Units.val_one, one_smul] at h
    exact h
  · have hmem : (GaloisRepAdic.ofResidualGaloisRep
        ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).ρ σ (b 0) ∈ L :=
      hD ⟨σ, hσ⟩ (b 0) hb0
    rw [hb] at hmem
    obtain ⟨x, hx⟩ := (@Submodule.mem_span_singleton _ _ (_) (_) (_) _ _).mp hmem
    refine ⟨x, ((ψ ⟨σ, hσ⟩ : (ZMod p)ˣ) : ZMod p), fun w hw => ?_, fun v => hquot ⟨σ, hσ⟩ v,
      fun n a ha => ?_⟩
    · rw [hb] at hw
      obtain ⟨c, rfl⟩ := (@Submodule.mem_span_singleton _ _ (_) (_) (_) _ _).mp hw
      exact (LinearMap.map_smul _ c (b 0)).trans
        ((congrArg (fun t => c • t) hx.symm).trans (smul_comm c x (b 0)))
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have ha1 : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a :=
          fun μ hμ => ha μ (pow_prime_pow_eq_one_of_pow_eq_one hμ hn)
        have hsc := hscal ⟨σ, hσ⟩ a ha1 (b 0) hb0
        have hxeq : x = (a : ZMod p) * ((ψ ⟨σ, hσ⟩ : (ZMod p)ˣ) : ZMod p) :=
          b.linearIndependent.smul_left_injective 0 (hx.trans hsc)
        rw [hxeq, sub_self]
        exact Submodule.zero_mem _

end TateCurveTorsion

theorem solution
    (𝒪 : Type) [CommRing 𝒪] {k : Type} [Field k] [Algebra 𝒪 k]
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ι : ZMod p →+* k)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (hpΔ : (p : ℤ) ∣ W.Δ)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    {S : Finset ℕ} (hpS : p ∈ S) (hS : ∀ q : ℕ, q.Prime → q ∉ S → W.IsGoodPrimeFor q) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S (GaloisRepAdic.ofResidualGaloisRep
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι)) := by
  have hι : IsLocalHom ι := inferInstance
  have hord := WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_ordinaryCondition 𝒪 W p hp2 ι
    hΔ hW (Or.inl hpΔ) hcard hker hpS hS
  change GaloisRep.strictOrdinaryCondition 𝒪 p S ((GaloisRepAdic.ofResidualGaloisRep
    ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).baseChangeAlong ι hι)
  exact ⟨hord.1, GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong ι hι _
    (TateCurveTorsion.isStrictOrdinaryAt_torsion W p hp2 hΔ hW hpΔ hcard hker), hord.2.2⟩

end S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_strictOrdinaryCondition_of_dvd_discriminant
end P2MW
export P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_strictOrdinaryCondition_of_dvd_discriminant (solution)
