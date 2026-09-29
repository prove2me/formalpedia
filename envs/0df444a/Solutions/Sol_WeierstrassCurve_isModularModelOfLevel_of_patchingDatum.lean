-- Prove2me | solution 1 for WeierstrassCurve.isModularModelOfLevel_of_patchingDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/64550ace-bf8d-54f0-a4a6-272b710845e0

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_Algebra_PatchingDatum
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong
import Theorems.Thm_Algebra_PatchingDatum_nonempty_patchingLevel_bot
import Theorems.Thm_Algebra_PatchingLevel_free_and_ker_eq_span
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_charpoly_eq_of_isEquiv
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_Ideal_exists_ringHom_integralClosure_ker_eq
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum

open Polynomial

theorem solution
    (p : ℕ) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)

    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)

    {N : ℕ} [NeZero N] {S : Finset ℕ} (hSprime : ∀ q ∈ S, q.Prime)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hN : CuspForm.HasIntegralStructure N 2)
    {θ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N (S : Set ℕ) 𝒪 θ T)

    (φ : D.R →ₐ[𝒪] T) (hφ : IsLocalHom (φ : D.R →+* T))
    (hφρ : (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ)

    {M : Type} [AddCommGroup M] [Module D.R M] [Module T M] [Nontrivial M]
    (hcompat : ∀ (x : D.R) (m : M), φ x • m = x • m)
    {r : ℕ} (P : Algebra.PatchingDatum 𝒪 p r D.R M)

    (ρW : GaloisRepAdic 𝒪) (h𝒟W : 𝒟 ρW)
    (hWres : ρW.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪))))
    (hWfrob : ∀ (ℓ : ℕ), ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρW.ρ σ) = X ^ 2 - C ((W.apOfModel ℓ : ℤ) : 𝒪) * X + C ((ℓ : 𝒪))) :
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) := by
  classical

  have hsurj : Function.Surjective φ :=
    H.surjective_of_isEquiv_baseChangeAlong (fun q hq hqN => Finset.mem_coe.mpr (hNS q hq hqN))
      D.ρ φ hφ hφρ

  obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hp𝒪
  obtain ⟨hfree, -, -⟩ := L.free_and_ker_eq_span
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hann : x ∈ Module.annihilator D.R M := Module.mem_annihilator.mpr fun m => by
      rw [← hcompat x m, hx, zero_smul]
    rwa [(Module.annihilator_eq_bot (R := D.R) (M := M)).mpr inferInstance] at hann
  let e : D.R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

  have hres𝒪 : Function.Surjective (IsLocalRing.residue 𝒪 ∘ algebraMap 𝒪 𝒪) := fun x => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨y, rfl⟩
  obtain ⟨φW, ⟨hφW, hEqW⟩, -⟩ := D.universal 𝒪 hres𝒪 ρW h𝒟W hWres

  let ψW : T →ₐ[𝒪] 𝒪 := φW.comp (e.symm : T →ₐ[𝒪] D.R)
  have hψW : ∀ x : D.R, ψW (φ x) = φW x := fun x => by
    show φW (e.symm (e x)) = φW x
    rw [e.symm_apply_apply]

  have hχ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), W.IsGoodPrimeFor ℓ →
      ψW (H.π (CuspForm.heckeAlgebra.T hℓ hℓN (show ℓ ∉ (S : Set ℕ) from
        fun h => hℓS (Finset.mem_coe.mp h)))) = ((W.apOfModel ℓ : ℤ) : 𝒪) := by
    intro ℓ hℓ hℓN hℓS hgood
    obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
    have h1 := H.charpoly_frob ℓ hℓ hℓN (fun h => hℓS (Finset.mem_coe.mp h)) A hA σ hσ
    have h2 := GaloisRepAdic.charpoly_eq_of_isEquiv hφρ σ
    have h3 := GaloisRepAdic.charpoly_baseChangeAlong (φ : D.R →+* T) hφ D.ρ σ
    have h4 := GaloisRepAdic.charpoly_eq_of_isEquiv hEqW σ
    have h5 := GaloisRepAdic.charpoly_baseChangeAlong (φW : D.R →+* 𝒪) hφW D.ρ σ
    have h6 := hWfrob ℓ hℓ hgood hℓS A hA σ hσ

    have hcomp : (ψW : T →+* 𝒪).comp (φ : D.R →+* T) = (φW : D.R →+* 𝒪) := by
      ext x
      exact hψW x
    have h7 : (LinearMap.charpoly (H.ρ.ρ σ)).map (ψW : T →+* 𝒪) = LinearMap.charpoly (ρW.ρ σ) := by
      rw [← h2, h3, Polynomial.map_map, hcomp, ← h5, h4]
    rw [h1, h6] at h7
    have h8 := congrArg (fun q : 𝒪[X] => q.coeff 1) h7
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C,
      mul_one, if_neg (show (1 : ℕ) ≠ 2 by decide),
      if_neg (show (1 : ℕ) ≠ 0 by decide), zero_sub, add_zero, RingHom.coe_coe] at h8
    exact neg_injective h8

  let χ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* 𝒪 := (ψW : T →+* 𝒪).comp H.π
  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra N 2 (S : Set ℕ)) :=
    CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN one_le_two _
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨f𝔓, hf𝔓⟩ := Ideal.exists_ringHom_integralClosure_ker_eq (RingHom.ker χ) inferInstance
    (fun n hn => by
      rw [RingHom.mem_ker, map_intCast] at hn
      exact Int.cast_injective (α := 𝒪) (hn.trans Int.cast_zero.symm))
  let χℂ : CuspForm.heckeAlgebra N 2 (S : Set ℕ) →+* ℂ :=
    (algebraMap (integralClosure ℤ ℂ) ℂ).comp f𝔓
  have hχℂ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), W.IsGoodPrimeFor ℓ →
      χℂ (CuspForm.heckeAlgebra.T hℓ hℓN (show ℓ ∉ (S : Set ℕ) from
        fun h => hℓS (Finset.mem_coe.mp h))) = ((W.apOfModel ℓ : ℤ) : ℂ) := by
    intro ℓ hℓ hℓN hℓS hgood
    have hmem : CuspForm.heckeAlgebra.T hℓ hℓN (show ℓ ∉ (S : Set ℕ) from
        fun h => hℓS (Finset.mem_coe.mp h)) - ((W.apOfModel ℓ : ℤ) : CuspForm.heckeAlgebra N 2 (S : Set ℕ))
          ∈ RingHom.ker f𝔓 := by
      rw [hf𝔓, RingHom.sub_mem_ker_iff, map_intCast]
      exact hχ ℓ hℓ hℓN hℓS hgood
    have hmem' := (RingHom.sub_mem_ker_iff f𝔓).mp hmem
    rw [map_intCast f𝔓] at hmem'
    show algebraMap (integralClosure ℤ ℂ) ℂ (f𝔓 _) = _
    rw [hmem', map_intCast]

  obtain ⟨f, hf, hfT, -⟩ :=
    CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq hN χℂ

  have hN0 : N ≠ 0 := NeZero.ne N
  have hP0 : (∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => (hSprime q (Finset.mem_filter.mp hq).1).ne_zero
  haveI : NeZero (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q) := ⟨mul_ne_zero hN0 hP0⟩
  obtain ⟨g, hg, hgf⟩ :=
    CuspForm.exists_isNormalizedEigenform_of_dvd (N := N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q)
      (dvd_mul_right N _) f hf
  refine ⟨g, hg, fun ℓ hℓ hgood hℓN' => ?_⟩
  have hℓN : ¬ ℓ ∣ N := fun h => hℓN' (h.mul_right _)
  have hℓS : ℓ ∉ S := fun h =>
    hℓN' ((Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_filter.mpr ⟨h, hℓN⟩)).mul_left N)
  rw [hgf ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN'), hfT ℓ hℓ hℓN (fun h => hℓS (Finset.mem_coe.mp h)),
    hχℂ ℓ hℓ hℓN hℓS hgood]

end S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum
end P2MW
export P2MW.S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum (solution)
