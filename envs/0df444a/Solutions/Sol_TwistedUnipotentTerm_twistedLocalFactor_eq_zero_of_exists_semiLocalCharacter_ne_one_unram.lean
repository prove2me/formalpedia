-- Prove2me | solution 1 for TwistedUnipotentTerm.twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/88d147db-f579-54bb-8434-48f65e9639fc

import Mathlib
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace R1TwistedUnipotentVanishing

theorem add_mem_semiLocalIntegers (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) {x y : L ⊗[K] v.adicCompletion K}
    (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) (hy : y ∈ AutomorphicForm.semiLocalIntegers K L v) :
    x + y ∈ AutomorphicForm.semiLocalIntegers K L v := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add _ _ _⟩

theorem mul_mem_semiLocalIntegers (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) {x y : L ⊗[K] v.adicCompletion K}
    (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) (hy : y ∈ AutomorphicForm.semiLocalIntegers K L v) :
    x * y ∈ AutomorphicForm.semiLocalIntegers K L v := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, map_mul _ _ _⟩

theorem matrix_mul_mem (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) {g h : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : ∀ i j, g i j ∈ AutomorphicForm.semiLocalIntegers K L v)
    (hh : ∀ i j, h i j ∈ AutomorphicForm.semiLocalIntegers K L v) (i j : Fin 2) :
    (g * h) i j ∈ AutomorphicForm.semiLocalIntegers K L v := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_semiLocalIntegers K L v (mul_mem_semiLocalIntegers K L v (hg _ _) (hh _ _))
    (mul_mem_semiLocalIntegers K L v (hg _ _) (hh _ _))

theorem mul_mem_semiLocalIntegralSet (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) (hh : h ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    g * h ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact matrix_mul_mem K L v hg.1 hh.1 i j
  · rw [mul_inv_rev, Units.val_mul]
    exact matrix_mul_mem K L v hh.2 hg.2 i j

theorem inv_mem_semiLocalIntegralSet (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    g⁻¹ ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem semiLocalCentral_mem_semiLocalIntegralSet (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) {u : (L ⊗[K] v.adicCompletion K)ˣ}
    (hu : u ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v) :
    TwistedUnipotentTerm.semiLocalCentral K L v u ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  rw [AutomorphicForm.TransversalMeasure.integralUnits, Submonoid.mem_units_iff] at hu
  obtain ⟨hu1, hu2⟩ := hu
  have h1 : (u : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v := by
    obtain ⟨a, ha⟩ := (AlgHom.mem_range _).1 hu1
    exact ⟨a, ha⟩
  have h2 : ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
      AutomorphicForm.semiLocalIntegers K L v := by
    obtain ⟨a, ha⟩ := (AlgHom.mem_range _).1 hu2
    exact ⟨a, ha⟩
  have h0 := AutomorphicForm.zero_mem_semiLocalIntegers K L v
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [TwistedUnipotentTerm.semiLocalCentral, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact h1
    · exact h0
  · rw [TwistedUnipotentTerm.semiLocalCentral, ← map_inv, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact h2
    · exact h0

theorem xi_mk_mul {G : Type*} [Group G] (ξL : (⊤ : Subgroup G) →* ℂˣ) (x y : G) (h : x * y ∈ (⊤ : Subgroup G)) :
    ξL ⟨x * y, h⟩ = ξL ⟨x, Subgroup.mem_top x⟩ * ξL ⟨y, Subgroup.mem_top y⟩ := by
  rw [← map_mul]
  rfl

theorem semiLocalCharacter_mul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (a b : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v (a * b) =
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v a * TwistedUnipotentTerm.semiLocalCharacter K L ξL v b := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  unfold TwistedUnipotentTerm.semiLocalCharacter
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  refine finprod_congr fun w => ?_
  simp only [TwistedUnipotentTerm.semiLocalUnitComponent, map_mul, xi_mk_mul, Units.val_mul]

theorem inner_integral_mul_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (W : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (u ζ : (L ⊗[K] v.adicCompletion K)ˣ)
    (hu : u ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v) :
    (letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
        AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
      ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
        W (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v (u * ζ) * g)
          ∂(AutomorphicForm.semiLocalHaar K L v)) =
    (letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
        AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
      ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
        W (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * g)
          ∂(AutomorphicForm.semiLocalHaar K L v)) := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.isHaarMeasure_semiLocalHaar K L v
  set S := AutomorphicForm.semiLocalIntegralSet K L v with hS
  set c := TwistedUnipotentTerm.semiLocalCentral K L v u with hc
  have hcS : c ∈ S := semiLocalCentral_mem_semiLocalIntegralSet K L v hu
  have hmeas : MeasurableSet S := (AutomorphicForm.isOpen_semiLocalIntegralSet K L v).measurableSet

  have hpt : ∀ κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v (u * ζ) * g =
        (c⁻¹ * κ)⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * g := by
    intro κ
    have hcomm : TwistedUnipotentTerm.semiLocalCentral K L v (u * ζ) =
        c * TwistedUnipotentTerm.semiLocalCentral K L v ζ := by
      simp only [hc, TwistedUnipotentTerm.semiLocalCentral, ← map_mul]
    rw [hcomm, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
  show ∫ κ in S, W (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v (u * ζ) * g)
      ∂(AutomorphicForm.semiLocalHaar K L v) =
    ∫ κ in S, W (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * g) ∂(AutomorphicForm.semiLocalHaar K L v)
  simp_rw [hpt]
  rw [← integral_indicator hmeas, ← integral_indicator hmeas]
  have hind : (S.indicator fun κ => W ((c⁻¹ * κ)⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * g)) =
      fun κ => (S.indicator fun κ' => W (κ'⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * g)) (c⁻¹ * κ) := by
    funext κ
    by_cases hκ : κ ∈ S
    · have hκ' : c⁻¹ * κ ∈ S :=
        mul_mem_semiLocalIntegralSet K L v (inv_mem_semiLocalIntegralSet K L v hcS) hκ
      rw [Set.indicator_of_mem hκ, Set.indicator_of_mem hκ']
    · have hκ' : c⁻¹ * κ ∉ S := by
        intro h'
        apply hκ
        have := mul_mem_semiLocalIntegralSet K L v hcS h'
        rwa [mul_inv_cancel_left] at this
      rw [Set.indicator_of_notMem hκ, Set.indicator_of_notMem hκ']
  rw [hind, integral_mul_left_eq_self]

theorem unipotentOrbitalFn_eq_zero (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L)) (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L))
    (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ)
    (hξv : ∃ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ ≠ 1) :
    TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j = fun _ => 0 := by
  obtain ⟨u, hu, hne⟩ := hξv
  funext x
  unfold TwistedUnipotentTerm.unipotentOrbitalFn
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI : LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  letI : MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ := borel _
  haveI : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := ⟨rfl⟩
  set I : (L ⊗[K] v.adicCompletion K)ˣ → ℂ := fun ζ =>
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
      TwistedUnipotentTerm.wordIndicator K L v w m rT z k j
        (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x)
        ∂(AutomorphicForm.semiLocalHaar K L v) with hI
  have hIinv : ∀ ζ, I (u * ζ) = I ζ := fun ζ =>
    inner_integral_mul_eq K L v (TwistedUnipotentTerm.wordIndicator K L v w m rT z k j)
      (TwistedUnipotentTerm.semiLocalUnipotent K L v x) u ζ hu
  show ∫ ζ, TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * I ζ
      ∂(Measure.haar : Measure (L ⊗[K] v.adicCompletion K)ˣ) = 0
  set J := ∫ ζ, TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * I ζ
      ∂(Measure.haar : Measure (L ⊗[K] v.adicCompletion K)ˣ) with hJ
  have hshift := integral_mul_left_eq_self
    (μ := (Measure.haar : Measure (L ⊗[K] v.adicCompletion K)ˣ))
    (fun ζ => TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * I ζ) u
  simp only [semiLocalCharacter_mul, hIinv, mul_assoc] at hshift
  rw [integral_const_mul] at hshift

  have h1 : (TwistedUnipotentTerm.semiLocalCharacter K L ξL v u - 1) * J = 0 := by
    rw [sub_mul, one_mul, hJ, hshift, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h

end R1TwistedUnipotentVanishing

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (hξv : ∃ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ ≠ 1)
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
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    ∀ k j : ℕ, twistedLocalFactor K L D σ ξL v w n rT z k j = 0 := by
  intro k j
  funext r
  unfold twistedLocalFactor AutomorphicForm.AdelicTracePushforward.localTracePushforward
  simp only [R1TwistedUnipotentVanishing.unipotentOrbitalFn_eq_zero K L ξL v w n rT z k j hξv,
    integral_zero, Pi.zero_apply]

end S_TwistedUnipotentTerm_twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram
end P2MW
export P2MW.S_TwistedUnipotentTerm_twistedLocalFactor_eq_zero_of_exists_semiLocalCharacter_ne_one_unram (solution)
