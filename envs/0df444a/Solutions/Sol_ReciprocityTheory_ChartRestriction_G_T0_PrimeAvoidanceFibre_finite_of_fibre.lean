-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:36:45.873802+00:00
-- url     : https://prove2.me/submissions/9da26ad5-32de-4369-9f75-244bee31260d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpanTopOfComplete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PrimeAvoidanceFibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SpanTopOfComplete_span_eq_top_of_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
theorem _root_.solution {O T : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing T] [IsDomain T] [IsNoetherianRing T] [Algebra O T]
    [Algebra.FiniteType O T] (ϖ : O) (hϖ : Irreducible ϖ)
    (hex : ∃ P : Ideal T, P.IsPrime ∧ algebraMap O T ϖ ∈ P)
    (huniq : ∀ P P' : Ideal T, P.IsPrime → P'.IsPrime → algebraMap O T ϖ ∈ P → algebraMap O T ϖ ∈ P' →
      P = P') : Module.Finite O T := by
  classical
  set w := algebraMap O T ϖ with hw
  set J : Ideal T := Ideal.span {w} with hJ
  obtain ⟨P0, hP0, hwP0⟩ := hex
  have hJtop : J ≠ ⊤ := fun h => hP0.ne_top (eq_top_iff.2 (h ▸ (Ideal.span_singleton_le_iff_mem P0).2 hwP0))

  have hdim : Ring.KrullDimLE 0 (T ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI.ne_top
    have hwI : w ∈ Ideal.comap (Ideal.Quotient.mk J) I := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self w)]
      exact I.zero_mem
    have hwN : w ∈ Ideal.comap (Ideal.Quotient.mk J) N := Ideal.comap_mono hIN hwI
    have e := huniq _ _ (Ideal.comap_isPrime _ I) (Ideal.comap_isPrime _ N) hwI hwN
    have : I = N := by
      have h1 := congrArg (Ideal.map (Ideal.Quotient.mk J)) e
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    rw [this]; exact hN
  have hart : IsArtinianRing (T ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

  have hmJ : maximalIdeal O ≤ Ideal.comap (algebraMap O T) J := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self w
  let _ : Algebra (O ⧸ maximalIdeal O) (T ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hmJ
  have hmk : ∀ c : O, algebraMap (O ⧸ maximalIdeal O) (T ⧸ J) (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk J (algebraMap O T c) := fun c => rfl
  have : IsScalarTower O (O ⧸ maximalIdeal O) (T ⧸ J) := IsScalarTower.of_algebraMap_eq fun c => (hmk c).symm
  have : Algebra.FiniteType O (T ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O J) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (O ⧸ maximalIdeal O) (T ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have : IsJacobsonRing (O ⧸ maximalIdeal O) := by
    let _ := Ideal.Quotient.field (maximalIdeal O); infer_instance
  have : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ J) := Module.finite_of_isArtinianRing _ _
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := O ⧸ maximalIdeal O) (M := T ⧸ J)
  choose S hS using fun i => Ideal.Quotient.mk_surjective (g i)
  have hgen : ∀ x : T, ∃ c : Fin n → O, ∃ y : T, x = ∑ i, c i • S i + ϖ • y := by
    intro x
    have hx : Ideal.Quotient.mk J x ∈ Submodule.span (O ⧸ maximalIdeal O) (Set.range g) := by
      rw [hg]; trivial
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    choose c hc using fun i => Ideal.Quotient.mk_surjective (cb i)
    have hmem : x - ∑ i, c i • S i ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, ← hcb, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc i, ← hS i, Algebra.smul_def, Algebra.smul_def, map_mul, hmk]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨c, y, ?_⟩
    rw [Algebra.smul_def, ← hw, mul_comm, hy]
    abel
  have hsep : ∀ x : T, (∀ k : ℕ, ∃ y : T, x = ϖ ^ k • y) → x = 0 := by
    intro x hx
    have h0 := Ideal.iInf_pow_eq_bot_of_isDomain J hJtop
    have : x ∈ ⨅ k : ℕ, J ^ k := by
      rw [Ideal.mem_iInf]
      intro k
      obtain ⟨y, rfl⟩ := hx k
      rw [hJ, Ideal.span_singleton_pow, Algebra.smul_def, map_pow, ← hw]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h0] at this
    exact (Submodule.mem_bot T).1 this
  have : IsAdicComplete (Ideal.span {ϖ}) O := hϖ.maximalIdeal_eq ▸ inferInstance
  have htop := SpanTopOfComplete.span_eq_top_of_complete ϖ hsep S hgen
  exact ⟨Submodule.fg_def.2 ⟨Set.range S, Set.finite_range S, htop⟩⟩
end ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
