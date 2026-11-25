-- Prove2me | solution 1 for PI.Dv.Tr.muPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:20.366568+00:00
-- url     : https://prove2.me/submissions/0cb0a5bf-bec5-4ca0-8699-6c594c8e0bcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_PI_Dv_Tr_epsSum_eq
import Theorems.Thm_PI_Dv_Tr_eps_mul_epsSum
import Theorems.Thm_PI_Dv_Tr_exists_g
import Theorems.Thm_PI_Dv_Tr_phi_apply
import Theorems.Thm_PI_Dv_Tr_chi_pow
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_smul__30a616144aad
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c
import Theorems.Thm_PI_Dv_Tr_realize_le
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HN_muChar
import Theorems.Thm_Formalism_HN_plLat
import Theorems.Thm_Formalism_HN_slopeIneq
import Theorems.Thm_PI_Dv_Tr_eG_comm
import Theorems.Thm_PI_Dv_Tr_eG_idem
import Theorems.Thm_PI_Dv_Tr_rankPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
namespace PI.Dv.Tr
theorem _root_.solution : MuPart := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA hR
  classical
  have : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR
  set L1 := cut A ρ (eps P * eG T) A.L with hL1def
  set L0 := cut A ρ (eps P0 * eG T) A.L with hL0def
  have hfg : A.L.FG := hA.1.2.1
  have hnoeth : IsNoetherian (𝓞 K) A.L := isNoetherian_of_fg_of_noetherian A.L hfg
  have fg_of_le : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → N.FG := fun N hN => isNoetherian_submodule.mp hnoeth N hN
  have hL1 : L1 ≤ A.L := inf_le_left
  have hL0 : L0 ≤ A.L := inf_le_left
  have lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N :=
    fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le N hN)).1
  have hL1ne : L1 ≠ ⊥ := by
    intro h
    have hr := rankPart K G T P0 P hM A ρ hA
    rw [← hL1def, h] at hr
    have h0 : rkL A (⊥ : Submodule (𝓞 K) A.V) = 0 := by
      simp [rkL, Formalism.HN.rkK]
    omega
  obtain ⟨hmax1, -, ⟨N, hNsat, hN0, hNslope⟩, -⟩ := Formalism.HN.muChar (𝓞 K) A.V _ ρR L1 (lat L1 hL1) hL1ne
  have hNL1 : N ≤ L1 := hNsat.1
  have hNL : N ≤ A.L := hNL1.trans hL1
  obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hN0
  have hrkN : (Formalism.HN.rk ρR N : ℝ) ≠ 0 := by
    have hpl := (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le N hNL)).2.1
    have hspan : Submodule.span K (N : Set A.V) ≠ ⊥ := by
      intro h
      apply hx0
      have hmem := Submodule.subset_span (R := K) hxN
      rw [h] at hmem
      exact (Submodule.mem_bot K).mp hmem
    have hk : Formalism.HN.rkK N ≠ 0 := fun h => hspan (Submodule.finrank_eq_zero.mp h)
    have hq : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
    rw [hpl]
    exact_mod_cast mul_ne_zero hq hk
  have hminN : Formalism.HN.muMax ρR L1 ≤ Formalism.HN.muMin ρR N := by
    obtain ⟨-, hmin, -⟩ := Formalism.HN.muChar (𝓞 K) A.V _ ρR N (lat N hNL) hN0
    rw [hmin]
    intro N' hN'
    have h1 := (hmax1 (Formalism.HN.muMax ρR L1)).mp le_rfl N' (hN'.trans hNL1)
    have h2 : Formalism.HN.deg ρR N = Formalism.HN.muMax ρR L1 * Formalism.HN.rk ρR N := by
      rw [← hNslope]
      unfold Formalism.HN.slope Formalism.F.slope
      unfold Formalism.HN.deg Formalism.HN.rk at *
      field_simp
    rw [mul_sub]
    linarith
  have hxR : x ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T)) := (Submodule.mem_inf.mp (hNL1 hxN)).2
  obtain ⟨g, hg⟩ := exists_g T P0 P hM ρ x hxR hx0
  set φ : A.V →ₗ[K] A.V := ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G g) with hφdef
  have hcardK : ((Fintype.card P0.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hφx : φ x ≠ 0 := by
    rw [hφdef, epsSum_eq, smul_mul_assoc, map_smul, map_mul, LinearMap.smul_apply, Module.End.mul_apply,
      Representation.asAlgebraHom_of]
    exact smul_ne_zero hcardK hg
  have hmapL : ∀ y ∈ A.L, φ y ∈ A.L := by
    intro y hy
    rw [hφdef, phi_apply]
    refine A.L.sum_mem fun h _ => ?_
    have hint : IsIntegral ℤ ((((P0.chi h)⁻¹ : Kˣ) : K)) :=
      IsIntegral.of_pow Fintype.card_pos (by rw [chi_pow]; exact isIntegral_one)
    have hmem : ρ (h : G) (ρ g y) ∈ A.L := hA.2.1 _ _ (hA.2.1 _ _ hy)
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (((P0.chi h)⁻¹ : Kˣ) : K) := ⟨⟨_, hint⟩, rfl⟩
    rw [← hr, algebraMap_smul]
    exact A.L.smul_mem r hmem
  have hmapR : ∀ y ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T)),
      φ y ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eG T)) := by
    rintro y ⟨z, rfl⟩
    refine ⟨ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T)) z, ?_⟩
    have alg : eps P0 * eG T * (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T)) =
        epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T) := by
      calc eps P0 * eG T * (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T))
          = eps P0 * (eG T * (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T))) := by rw [mul_assoc]
        _ = eps P0 * ((epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T)) * eG T) := by rw [← eG_comm]
        _ = (eps P0 * epsSum P0) * (MonoidAlgebra.of K G g * (eps P * (eG T * eG T))) := by
          simp only [mul_assoc]
        _ = epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T) := by
          rw [eps_mul_epsSum, eG_idem]
          simp only [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, alg, hφdef, map_mul, Module.End.mul_apply]
  have hmap : ∀ y : N, φ (y : A.V) ∈ L0 := fun y =>
    Submodule.mem_inf.mpr ⟨hmapL _ (hNL y.2), hmapR _ (Submodule.mem_inf.mp (hNL1 y.2)).2⟩
  let ψ : N →ₗ[𝓞 K] L0 := LinearMap.codRestrict L0 ((φ.restrictScalars (𝓞 K)).domRestrict N) hmap
  have hψ : ∀ y : N, ((ψ y : L0) : A.V) = φ y := fun y => rfl
  have hψ0 : ψ ≠ 0 := by
    intro h
    apply hφx
    have := congrArg (fun f : N →ₗ[𝓞 K] L0 => ((f ⟨x, hxN⟩ : L0) : A.V)) h
    simpa [hψ] using this
  set C : ℝ := (Fintype.card P0.H : ℝ) with hCdef
  have hC : 0 < C := by rw [hCdef]; exact_mod_cast Fintype.card_pos
  have hplace : ∀ v y, Formalism.HermitianLatticesTheory.normAt A.b A.X v (φ y) ≤ C * Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
    intro v y
    rw [hφdef, phi_apply]
    refine (normAt_sum_le' A.b A.X v _ _).trans (le_of_eq ?_)
    have hterm : ∀ h : P0.H, Formalism.HermitianLatticesTheory.normAt A.b A.X v ((((P0.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y)) =
        Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
      intro h
      rw [normAt_smul', hA.2.2, hA.2.2]
      have hn : ‖v.embedding ((((P0.chi h)⁻¹ : Kˣ) : K))‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, chi_pow, map_one]) Fintype.card_ne_zero
      rw [hn, one_mul]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hCdef]
  have hbound : ∀ y : N, ‖ρR ((ψ y : L0) : A.V)‖ ≤ C * ‖ρR (y : A.V)‖ := by
    intro y
    rw [hψ]
    exact realize_le A.b A.X φ C hC.le hplace y
  obtain ⟨h1, -⟩ := Formalism.HN.slopeIneq (𝓞 K) A.V A.V _ _ ρR ρR N L0 (lat N hNL) (lat L0 hL0) ψ C hC hbound
  have key := (h1 hψ0).2
  have hlogC : Real.log C ≤ laG G := by
    unfold laG
    apply Real.log_le_log hC
    rw [hCdef]
    exact_mod_cast Fintype.card_subtype_le _
  have hla : 0 ≤ laG G := by
    unfold laG
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  unfold muMaxL Formalism.HN.muMaxDef
  linarith
end PI.Dv.Tr
