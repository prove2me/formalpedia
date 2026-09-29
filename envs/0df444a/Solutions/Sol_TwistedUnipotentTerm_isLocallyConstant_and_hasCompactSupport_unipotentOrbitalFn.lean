-- Prove2me | solution 1 for TwistedUnipotentTerm.isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/826c24a7-f2fd-54d0-afc1-6f08b2cd4810

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_TwistedUnipotentTerm_wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem
import Theorems.Thm_TwistedUnipotentTerm_wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace ORBSB

open MeasureTheory AutomorphicForm TwistedUnipotentTerm
open scoped TensorProduct.RightActions

set_option linter.unusedSectionVars false

def walk (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => (q + 1) * walk q k 1
  | k + 1, d + 1 => walk q k d + q * walk q k (d + 2)

theorem walk_zero_zero (q : ℕ) : walk q 0 0 = 1 := rfl
theorem walk_zero_succ (q d : ℕ) : walk q 0 (d + 1) = 0 := rfl
theorem walk_succ_zero (q k : ℕ) : walk q (k + 1) 0 = (q + 1) * walk q k 1 := rfl
theorem walk_succ_succ (q k d : ℕ) : walk q (k + 1) (d + 1) = walk q k d + q * walk q k (d + 2) := rfl

theorem walk_eq_zero (q : ℕ) : ∀ k d : ℕ, k < d → walk q k d = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, d + 1, h => by
      rw [walk_succ_succ, walk_eq_zero q k d (by omega), walk_eq_zero q k (d + 2) (by omega), mul_zero, add_zero]

section Algebra

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalUnipotent_add (x y : L ⊗[K] v.adicCompletion K) :
    semiLocalUnipotent K L v (x + y) = semiLocalUnipotent K L v x * semiLocalUnipotent K L v y := by
  apply Units.ext
  show !![(1 : L ⊗[K] v.adicCompletion K), x + y; 0, 1] = !![1, x; 0, 1] * !![1, y; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem semiLocalUnipotent_zero : semiLocalUnipotent K L v 0 = 1 := by
  apply Units.ext
  show !![(1 : L ⊗[K] v.adicCompletion K), 0; 0, 1] = 1
  rw [Matrix.one_fin_two]

theorem neg_mem_semiLocalIntegers {y : L ⊗[K] v.adicCompletion K} (hy : y ∈ semiLocalIntegers K L v) :
    -y ∈ semiLocalIntegers K L v := by
  obtain ⟨a, rfl⟩ := hy
  exact ⟨-a, map_neg _ _⟩

theorem semiLocalUnipotent_inv (y : L ⊗[K] v.adicCompletion K) :
    (semiLocalUnipotent K L v y)⁻¹ = semiLocalUnipotent K L v (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [← semiLocalUnipotent_add, add_neg_cancel, semiLocalUnipotent_zero])

theorem semiLocalUnipotent_mem {y : L ⊗[K] v.adicCompletion K} (hy : y ∈ semiLocalIntegers K L v) :
    semiLocalUnipotent K L v y ∈ semiLocalIntegralSet K L v := by
  have h0 := zero_mem_semiLocalIntegers K L v
  have h1 := one_mem_semiLocalIntegers K L v
  have hent : ∀ t : L ⊗[K] v.adicCompletion K, t ∈ semiLocalIntegers K L v →
      ∀ i j, ((semiLocalUnipotent K L v t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈ semiLocalIntegers K L v := by
    intro t ht i j
    show (!![(1 : L ⊗[K] v.adicCompletion K), t; 0, 1]) i j ∈ semiLocalIntegers K L v
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simpa using ht
    · simpa using h0
    · simpa using h1
  refine (mem_integralUnitsSet).2 ⟨hent y hy, ?_⟩
  rw [semiLocalUnipotent_inv]
  exact hent (-y) (neg_mem_semiLocalIntegers K L v hy)

theorem inv_mem_semiLocalIntegralSet {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) : g⁻¹ ∈ semiLocalIntegralSet K L v :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem central_of_coe_eq_smul_one {F : Type} [CommRing F] (z : GL (Fin 2) F) (c : F)
    (hz : (z : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F)) (y : GL (Fin 2) F) :
    z * y = y * z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem semiLocalHomeomorph_apply (x : L ⊗[K] v.adicCompletion K) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v x w = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w :=
  rfl

theorem mem_image_of_valued_le (w : HeightOneSpectrum (𝓞 L)) (m : ℕ) (y : w.adicCompletion L)
    (hy : Valued.v y ≤ WithZero.exp (m : ℤ)) :
    y ∈ (fun t : w.adicCompletion L =>
        (((NumberField.AdelicLevel.uniformizerUnit L w)⁻¹ ^ m : (w.adicCompletion L)ˣ) : w.adicCompletion L) * t) ''
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := by
  set π : (w.adicCompletion L)ˣ := NumberField.AdelicLevel.uniformizerUnit L w with hπdef
  have hπ : Valued.v (π : w.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    NumberField.AdelicLevel.valued_uniformizerUnit L w
  refine ⟨((π ^ m : (w.adicCompletion L)ˣ) : w.adicCompletion L) * y, ?_, ?_⟩
  · show ((π ^ m : (w.adicCompletion L)ˣ) : w.adicCompletion L) * y ∈ w.adicCompletionIntegers L
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Units.val_pow_eq_pow_val, map_pow, hπ,
      ← WithZero.exp_nsmul]
    calc WithZero.exp (m • (-1 : ℤ)) * Valued.v y
        ≤ WithZero.exp (m • (-1 : ℤ)) * WithZero.exp (m : ℤ) := mul_le_mul_right hy _
      _ = 1 := by rw [← WithZero.exp_add, smul_neg, nsmul_eq_mul, mul_one, neg_add_cancel, WithZero.exp_zero]
  · show (((π⁻¹ ^ m : (w.adicCompletion L)ˣ)) : w.adicCompletion L) *
        (((π ^ m : (w.adicCompletion L)ˣ) : w.adicCompletion L) * y) = y
    rw [← mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, one_mul]

theorem isCompact_bigBall (w : HeightOneSpectrum (𝓞 L)) (m : ℕ) :
    IsCompact ((fun t : w.adicCompletion L =>
        (((NumberField.AdelicLevel.uniformizerUnit L w)⁻¹ ^ m : (w.adicCompletion L)ˣ) : w.adicCompletion L) * t) ''
      (w.adicCompletionIntegers L : Set (w.adicCompletion L))) :=
  (isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w)).image
    (continuous_const.mul continuous_id)

end Algebra

end ORBSB

namespace ORBSB

open MeasureTheory AutomorphicForm TwistedUnipotentTerm
open scoped TensorProduct.RightActions

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem unipotentOrbitalFn_add (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (g : GL (Fin 2) (w.1.adicCompletion L))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) g rT)
    (z : GL (Fin 2) (w.1.adicCompletion L)) (hz : ∀ y : GL (Fin 2) (w.1.adicCompletion L), z * y = y * z)
    (k j : ℕ) (x t : L ⊗[K] v.adicCompletion K) (ht : t ∈ semiLocalIntegers K L v) :
    unipotentOrbitalFn K L ξL v w n rT z k j (x + t) = unipotentOrbitalFn K L ξL v w n rT z k j x := by
  unfold unipotentOrbitalFn
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  beta_reduce
  congr 1
  refine integral_congr_ae (ae_of_all _ fun κ => ?_)
  beta_reduce
  rw [semiLocalUnipotent_add, ← mul_assoc]
  exact (wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem K L v w g n rT hrT z hz k j
    _ (semiLocalUnipotent_mem K L v ht) _).2

theorem wordIndicator_eq_zero_of_not_le (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
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
    (k j : ℕ) (x : L ⊗[K] v.adicCompletion K) (w' : v.Extension (𝓞 L))
    (hx : ¬ Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w') ≤
      WithZero.exp (k : ℤ))
    (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    wordIndicator K L v w n rT z k j (semiLocalCentral K L v ζ * semiLocalUnipotent K L v x) = 0 := by
  by_contra hne
  have key := wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount K L v w ϖ hϖ hϖ0 n rT hrT
    z hz (walk (Ideal.absNorm w.1.asIdeal)) (walk_zero_zero _) (walk_zero_succ _) (walk_succ_zero _)
    (walk_succ_succ _) k j ζ x
  have h1 := key.1 hne
  have hk0 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (k : ℤ) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (Int.natCast_nonneg k)
  by_cases hww : w' = w
  · subst hww
    have h2 := key.2 h1.1 h1.2
    apply hne
    rw [h2, Nat.cast_eq_zero]
    apply walk_eq_zero
    have hlt : WithZero.exp (k : ℤ) <
        Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w') := not_le.1 hx
    have hne0 : Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w') ≠ 0 :=
      (lt_trans WithZero.exp_pos hlt).ne'
    have hlog : (k : ℤ) < WithZero.log
        (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w')) :=
      (WithZero.lt_log_iff_exp_lt hne0).2 hlt
    have := Int.lt_toNat.2 hlog
    omega
  · exact hx (((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1.1 w' hww).2).trans hk0)

theorem main (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
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
    (k j : ℕ) :
    IsLocallyConstant (unipotentOrbitalFn K L ξL v w n rT z k j) ∧
      HasCompactSupport (unipotentOrbitalFn K L ξL v w n rT z k j) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  have hz' : ∀ y : GL (Fin 2) (w.1.adicCompletion L), z * y = y * z := central_of_coe_eq_smul_one z _ hz
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y | y - x ∈ semiLocalIntegers K L v},
      (isOpen_semiLocalIntegers K L v).preimage (continuous_id.sub continuous_const), ?_, fun y hy => ?_⟩
    · show x - x ∈ semiLocalIntegers K L v
      rw [sub_self]
      exact zero_mem_semiLocalIntegers K L v
    · calc unipotentOrbitalFn K L ξL v w n rT z k j y
          = unipotentOrbitalFn K L ξL v w n rT z k j (x + (y - x)) := by rw [add_sub_cancel]
        _ = unipotentOrbitalFn K L ξL v w n rT z k j x :=
          unipotentOrbitalFn_add K L ξL v w _ n rT hrT z hz' k j x (y - x) hy
  · haveI : R1Space (L ⊗[K] v.adicCompletion K) := T2Space.r1Space
    refine HasCompactSupport.intro
      ((semiLocalHomeomorph K L v).isCompact_preimage.2
        (isCompact_univ_pi fun w' : v.Extension (𝓞 L) => isCompact_bigBall L w'.1 k)) fun x hx => ?_
    rw [Set.mem_preimage, Set.mem_univ_pi, not_forall] at hx
    obtain ⟨w', hw'⟩ := hx
    have hxv : ¬ Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w') ≤
        WithZero.exp (k : ℤ) :=
      fun h => hw' (by rw [semiLocalHomeomorph_apply]; exact mem_image_of_valued_le L w'.1 k _ h)
    have hW := wordIndicator_eq_zero_of_not_le K L v w ϖ hϖ hϖ0 n rT hrT z hz k j x w' hxv
    unfold unipotentOrbitalFn
    refine integral_eq_zero_of_ae (ae_of_all _ fun ζ => ?_)
    beta_reduce
    rw [Pi.zero_apply]
    refine mul_eq_zero_of_right _ ?_
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf _
    haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
    refine (setIntegral_congr_fun (isOpen_semiLocalIntegralSet K L v).measurableSet
      (g := fun _ => (0 : ℂ)) fun κ hκ => ?_).trans (by simp)
    show wordIndicator K L v w n rT z k j
        (κ⁻¹ * semiLocalCentral K L v ζ * semiLocalUnipotent K L v x) = 0
    rw [mul_assoc, (wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem K L v w _ n rT hrT
      z hz' k j _ (inv_mem_semiLocalIntegralSet K L v hκ) _).1, hW ζ]

end Main

end ORBSB

open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
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
    (k j : ℕ) :
    IsLocallyConstant (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j) ∧
      HasCompactSupport (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j) :=
  ORBSB.main K L ξL v w ϖ hϖ hϖ0 n rT hrT z hz k j

end S_TwistedUnipotentTerm_isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn
end P2MW
export P2MW.S_TwistedUnipotentTerm_isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn (solution)
