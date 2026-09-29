-- Prove2me | solution 1 for TwistedUnipotentTerm.exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e909c450-e1a6-5e8d-b0b9-949fc3081abb

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Theorems.Thm_TwistedUnipotentTerm_wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount
import Theorems.Thm_TwistedUnipotentTerm_wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem
import Theorems.Thm_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits
import Theorems.Thm_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped TensorProduct Pointwise

noncomputable section

namespace KcOrbitalEval

section Local

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem valued_algebraMap_uniformiser {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Valued.v (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ) := by
  change Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1 : ℤ)

  obtain ⟨p, hp⟩ := HeightOneSpectrum.intValuation_exists_uniformizer u
  have hpv : Valued.v ((p : 𝓞 F) : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hp]
  set p' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) p with hp'
  have hp'v : Valued.v (p' : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := hpv
  have hp'max : p' ∈ IsLocalRing.maximalIdeal (u.adicCompletionIntegers F) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 F) F u, hp'v, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hp'max
  obtain ⟨a, ha⟩ := hp'max
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : u.adicCompletion F) := by
    rw [← hp'v, ← ha]
    push_cast
    rw [map_mul]
    calc Valued.v (a : u.adicCompletion F) * Valued.v (ϖ : u.adicCompletion F)
        ≤ 1 * Valued.v (ϖ : u.adicCompletion F) := mul_le_mul_of_nonneg_right a.2 zero_le'
      _ = Valued.v (ϖ : u.adicCompletion F) := one_mul _
  have hlt : Valued.v (ϖ : u.adicCompletion F) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hne : Valued.v (ϖ : u.adicCompletion F) ≠ 0 := by
    refine (Valuation.ne_zero_iff _).2 fun h => hϖ.ne_zero ?_
    exact_mod_cast h
  refine le_antisymm ?_ hle
  rw [← WithZero.log_le_iff_le_exp hne]
  have h0 : WithZero.log (Valued.v (ϖ : u.adicCompletion F)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]; exact hlt
  omega

theorem exists_valued_eq_exp_neg_one : ∃ π : u.adicCompletion F, Valued.v π = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer F u
  refine ⟨algebraMap F (u.adicCompletion F) π, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

theorem exists_unit_valued_eq_exp_neg (a : ℤ) :
    ∃ t : (u.adicCompletion F)ˣ, Valued.v (t : u.adicCompletion F) = WithZero.exp (-a) := by
  obtain ⟨π, hπ⟩ := exists_valued_eq_exp_neg_one F u
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π hπ0 ^ a, ?_⟩
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, hπ, ← WithZero.exp_zsmul]
  simp

end Local

section Coordinates

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

abbrev E : (L ⊗[K] v.adicCompletion K) ≃ₐ[L] (Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

def Ψ : (L ⊗[K] v.adicCompletion K)ˣ ≃* (Π w' : v.Extension (𝓞 L), (w'.1.adicCompletion L)ˣ) :=
  (Units.mapEquiv (E K L v).toRingEquiv.toMulEquiv).trans MulEquiv.piUnits

theorem semiLocalUnitComponent_eq (w' : v.Extension (𝓞 L)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalUnitComponent K L v w' ζ = Ψ K L v ζ w' :=
  Units.ext rfl

def cshell (a : ℤ) : Set (L ⊗[K] v.adicCompletion K)ˣ :=
  {ζ | (∀ w' : v.Extension (𝓞 L), w' ≠ w →
      Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w' ζ : (w'.1.adicCompletion L)ˣ) :
        w'.1.adicCompletion L) = 1) ∧
    Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
        w.1.adicCompletion L) = WithZero.exp (-a)}

theorem mem_cshell_iff (a : ℤ) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    ζ ∈ cshell K L v w a ↔ (∀ w' : v.Extension (𝓞 L), w' ≠ w →
      Valued.v ((Ψ K L v ζ w' : (w'.1.adicCompletion L)ˣ) : w'.1.adicCompletion L) = 1) ∧
        Valued.v ((Ψ K L v ζ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) = WithZero.exp (-a) := by
  simp only [cshell, Set.mem_setOf_eq, semiLocalUnitComponent_eq]

theorem exists_cshell_eq_preimage (a : ℤ) :
    ∃ t : (L ⊗[K] v.adicCompletion K)ˣ,
      cshell K L v w a = (fun ζ => t * ζ) ⁻¹'
        (TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  classical
  obtain ⟨u, hu⟩ := exists_unit_valued_eq_exp_neg L w.1 a
  refine ⟨(Ψ K L v).symm (Pi.mulSingle w u⁻¹), ?_⟩
  ext ζ
  rw [Set.mem_preimage, SetLike.mem_coe,
    (TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one K L v).2.2,
    mem_cshell_iff]
  simp only [semiLocalUnitComponent_eq, map_mul, MulEquiv.apply_symm_apply, Pi.mul_apply, Units.val_mul]
  have hu0 : Valued.v (u : w.1.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  constructor
  · rintro ⟨h1, h2⟩ w'
    by_cases hw' : w' = w
    · subst hw'
      rw [Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val, map_inv₀, h2, hu, inv_mul_cancel₀ WithZero.exp_ne_zero]
    · rw [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one, one_mul]
      exact h1 w' hw'
  · intro h
    refine ⟨fun w' hw' => ?_, ?_⟩
    · have h' := h w'
      rwa [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one, one_mul] at h'
    · have h' := h w
      rw [Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val, map_inv₀, hu] at h'
      have h0 : Valued.v ((Ψ K L v ζ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
          WithZero.exp (-a) * ((WithZero.exp (-a))⁻¹ *
            Valued.v ((Ψ K L v ζ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L)) := by
        rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
      rw [h0, h', mul_one]

end Coordinates

section Integrand

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hξv : ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1)
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm w.1.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm w.1.asIdeal * W k (d + 2))
    (k j : ℕ)

def awaySet : Set (L ⊗[K] v.adicCompletion K) :=
  {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}

def rhsVal (x : L ⊗[K] v.adicCompletion K) : ℂ :=
  (awaySet K L v w).indicator
    (fun x => (W k (2 * (WithZero.log (Valued.v
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) : ℂ)) x

def xiw : ℂ := ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)

theorem mul_comm_of_coe_eq_smul_one {F : Type} [Field F] {z : GL (Fin 2) F} {a : F}
    (hz : (z : Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F)) (y : GL (Fin 2) F) :
    z * y = y * z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hz, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

include hϖ in

theorem shell_iff (t : (w.1.adicCompletion L)ˣ) :
    Valued.v (t : w.1.adicCompletion L) ^ 2 =
        Valued.v (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ) ^ (k + 2 * j) ↔
      Even k ∧ Valued.v (t : w.1.adicCompletion L) = WithZero.exp (-((k / 2 + j : ℕ) : ℤ)) := by
  have ht0 : Valued.v (t : w.1.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  rw [valued_algebraMap_uniformiser L w.1 hϖ, ← WithZero.exp_log ht0, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    (WithZero.exp_injective).eq_iff, (WithZero.exp_injective).eq_iff]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_neg, mul_one]
  constructor
  · intro h
    have hk : Even k := by
      rcases Nat.even_or_odd k with hk | hk
      · exact hk
      · exfalso
        obtain ⟨m, rfl⟩ := hk
        push_cast at h
        omega
    refine ⟨hk, ?_⟩
    obtain ⟨m, rfl⟩ := hk
    have hm : (m + m) / 2 = m := by omega
    rw [hm]
    push_cast at h ⊢
    omega
  · rintro ⟨hk, h⟩
    obtain ⟨m, rfl⟩ := hk
    have hm : (m + m) / 2 = m := by omega
    rw [hm] at h
    rw [h]
    push_cast
    ring

include hξv in

theorem semiLocalCharacter_eq_pow_of_mem_cshell (a : ℕ) (ζ : (L ⊗[K] v.adicCompletion K)ˣ)
    (hζ : ζ ∈ cshell K L v w a) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = xiw K L ξL v w ^ a := by
  rw [TwistedUnipotentTerm.semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits K L ξL v hξv ζ]
  obtain ⟨h1, h2⟩ := hζ
  rw [finprod_eq_single _ w fun w' hw' => by
    rw [h1 w' hw', ← WithZero.exp_zero, WithZero.log_exp, neg_zero, zpow_zero]]
  · rw [h2, WithZero.log_exp, neg_neg, zpow_natCast]
    rfl

include hϖ hrT hz h00 h0s hroot hstep in

theorem wordIndicator_central_unipotent_eq (ζ : (L ⊗[K] v.adicCompletion K)ˣ) (x : L ⊗[K] v.adicCompletion K) :
    TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
        (TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) =
      (cshell K L v w ((k / 2 + j : ℕ) : ℤ)).indicator
        (fun _ => (1 + (-1 : ℂ) ^ k) / 2 * rhsVal K L v w W k x) ζ := by
  classical
  have hcard := TwistedUnipotentTerm.wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount K L v w
    ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep k j ζ x
  obtain ⟨hgate, hval⟩ := hcard
  by_cases hζ : ζ ∈ cshell K L v w ((k / 2 + j : ℕ) : ℤ)
  · rw [Set.indicator_of_mem hζ]
    obtain ⟨hζ1, hζ2⟩ := hζ
    rcases Nat.even_or_odd k with hk | hk
    ·
      have hsh : Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
          w.1.adicCompletion L) ^ 2 =
          Valued.v (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ) ^ (k + 2 * j) :=
        (shell_iff K L v w ϖ hϖ k j _).2 ⟨hk, hζ2⟩
      rw [hk.neg_one_pow, show ((1 : ℂ) + 1) / 2 = 1 by norm_num, one_mul, rhsVal]
      by_cases hx : x ∈ awaySet K L v w
      · rw [Set.indicator_of_mem hx]
        exact hval (fun w' hw' => ⟨hζ1 w' hw', hx w' hw'⟩) hsh
      · rw [Set.indicator_of_notMem hx]
        by_contra hne
        exact hx fun w' hw' => ((hgate hne).1 w' hw').2
    ·
      rw [hk.neg_one_pow, show ((1 : ℂ) + -1) / 2 = 0 by norm_num, zero_mul]
      by_contra hne
      have hsh := (hgate hne).2
      rw [shell_iff K L v w ϖ hϖ k j] at hsh
      exact (Nat.not_even_iff_odd.2 hk) hsh.1
  · rw [Set.indicator_of_notMem hζ]
    by_contra hne
    apply hζ
    obtain ⟨haway, hsh⟩ := hgate hne
    rw [shell_iff K L v w ϖ hϖ k j] at hsh
    exact ⟨fun w' hw' => (haway w' hw').1, hsh.2⟩

include hrT hz in
open scoped TensorProduct.RightActions in

theorem inner_integral_eq (ζ : (L ⊗[K] v.adicCompletion K)ˣ) (x : L ⊗[K] v.adicCompletion K) :
    (letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
          (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x)
          ∂(AutomorphicForm.semiLocalHaar K L v)) =
      TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
        (TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  have hzc : ∀ y : GL (Fin 2) (w.1.adicCompletion L), z * y = y * z := mul_comm_of_coe_eq_smul_one hz
  set c := TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
    (TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) with hc
  have h1 : (∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
      TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
        (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x)
        ∂(AutomorphicForm.semiLocalHaar K L v)) =
      ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, c ∂(AutomorphicForm.semiLocalHaar K L v) := by
    refine setIntegral_congr_fun (isOpen_semiLocalIntegralSet K L v).measurableSet fun κ hκ => ?_
    show TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
        (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) = c
    have hκ' : κ⁻¹ ∈ semiLocalIntegralSet K L v := by
      rw [semiLocalIntegralSet, mem_integralUnitsSet] at hκ ⊢
      rw [inv_inv]
      exact ⟨hκ.2, hκ.1⟩
    rw [mul_assoc]
    exact (TwistedUnipotentTerm.wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem K L v w
      (LocalGL2.diagPi ϖ hϖ0) n rT hrT z hzc k j _ hκ' _).1
  rw [h1, setIntegral_const, measureReal_def, semiLocalHaar_semiLocalIntegralSet, ENNReal.toReal_one, one_smul]

include hξv hϖ hrT hz h00 h0s hroot hstep in
open scoped TensorProduct.RightActions in

theorem integrand_eq (ζ : (L ⊗[K] v.adicCompletion K)ˣ) (x : L ⊗[K] v.adicCompletion K) :
    (letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
      ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
          (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x)
          ∂(AutomorphicForm.semiLocalHaar K L v)) =
      (cshell K L v w ((k / 2 + j : ℕ) : ℤ)).indicator
        (fun _ => xiw K L ξL v w ^ (k / 2 + j) * ((1 + (-1 : ℂ) ^ k) / 2 * rhsVal K L v w W k x)) ζ := by
  have hinner := inner_integral_eq K L v w ϖ hϖ0 n rT hrT z hz k j ζ x
  rw [hinner, wordIndicator_central_unipotent_eq K L v w ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep k j ζ x]
  by_cases hζ : ζ ∈ cshell K L v w ((k / 2 + j : ℕ) : ℤ)
  · rw [Set.indicator_of_mem hζ, Set.indicator_of_mem hζ,
      semiLocalCharacter_eq_pow_of_mem_cshell K L ξL v w hξv (k / 2 + j) ζ hζ]
  · rw [Set.indicator_of_notMem hζ, Set.indicator_of_notMem hζ, mul_zero]

end Integrand

section Assembly

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

open scoped TensorProduct.RightActions in
theorem isOpen_cshell (a : ℤ) :
    haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
    IsOpen (cshell K L v w a) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  obtain ⟨t, ht⟩ := exists_cshell_eq_preimage K L v w a
  rw [ht]
  exact (TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one K L v).2.1.preimage
    (continuous_const_mul t)

end Assembly

end KcOrbitalEval

end

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

open KcOrbitalEval AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hξv : ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1)
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm w.1.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm w.1.asIdeal * W k (d + 2)) :
    ∃ V : ℂ, V ≠ 0 ∧ ∀ (k j : ℕ) (x : L ⊗[K] v.adicCompletion K),
      TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j x =
        V * ((1 + (-1 : ℂ) ^ k) / 2 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (k / 2 + j)) *
          {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
                w'.1.adicCompletionIntegers L}.indicator
            (fun x => (W k (2 * (WithZero.log (Valued.v
              (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) : ℂ)) x := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI : LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  letI : MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ := borel _
  haveI : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := ⟨rfl⟩
  set U : Set (L ⊗[K] v.adicCompletion K)ˣ := (TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)
    with hU
  have hUo : IsOpen U := (TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one K L v).2.1
  have hUc : IsCompact U := (TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one K L v).1
  set μ : Measure (L ⊗[K] v.adicCompletion K)ˣ := Measure.haar with hμ
  refine ⟨(μ.real U : ℂ), ?_, fun k j x => ?_⟩
  · have hpos : 0 < μ U := hUo.measure_pos μ ⟨1, by rw [hU]; exact SetLike.mem_coe.2 (one_mem _)⟩
    have hlt : μ U < ⊤ := hUc.measure_lt_top
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hlt.ne).ne'
  ·
    have hshell : μ.real (cshell K L v w ((k / 2 + j : ℕ) : ℤ)) = μ.real U := by
      obtain ⟨t, ht⟩ := exists_cshell_eq_preimage K L v w ((k / 2 + j : ℕ) : ℤ)
      rw [measureReal_def, measureReal_def, ht, hU, measure_preimage_mul]
    have hmeas : MeasurableSet (cshell K L v w ((k / 2 + j : ℕ) : ℤ)) := (isOpen_cshell K L v w _).measurableSet
    unfold TwistedUnipotentTerm.unipotentOrbitalFn
    rw [show (∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ, TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
        ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x)
            ∂(AutomorphicForm.semiLocalHaar K L v) ∂μ) =
        ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ, (cshell K L v w ((k / 2 + j : ℕ) : ℤ)).indicator
          (fun _ => xiw K L ξL v w ^ (k / 2 + j) * ((1 + (-1 : ℂ) ^ k) / 2 * rhsVal K L v w W k x)) ζ ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall fun ζ =>
        integrand_eq K L ξL v w hξv ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep k j ζ x)]
    rw [integral_indicator_const _ hmeas, hshell, Complex.real_smul]
    simp only [xiw, rhsVal, awaySet]
    ring

end S_TwistedUnipotentTerm_exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits
end P2MW
export P2MW.S_TwistedUnipotentTerm_exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits (solution)
