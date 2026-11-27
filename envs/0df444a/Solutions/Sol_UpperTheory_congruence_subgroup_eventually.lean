-- Prove2me | solution 1 for UpperTheory.congruence_subgroup_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:34.693414+00:00
-- url     : https://prove2.me/submissions/6d2a3d35-9e2f-4104-b95c-030d8a8f043e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CongruenceSubgroupEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology ValuativeRel
private theorem small_powers {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (V : Set k) (hV : V ∈ nhds (0 : k)) :
    ∀ᶠ c : ℕ in atTop, ∀ x ∈ IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c,
      (x : k) ∈ V := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hV
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(valuation k).integer
  have hlt : valuation k (π : k) < 1 := by
    refine lt_of_le_of_ne π.2 fun h => hπ.not_isUnit ?_
    exact (Valuation.integer.integers (valuation k)).isUnit_of_one' h
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop N] with c hc x hx
  have hx' := Ideal.pow_le_pow_right hc hx
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx'
  obtain ⟨a, rfl⟩ := hx'
  apply hs
  have ha : valuation k (a : k) ≤ 1 := a.2
  change valuation k ((a : k) * (π : k) ^ N) < γ
  rw [map_mul, map_pow]
  calc _ ≤ 1 * valuation k (π : k) ^ N := by gcongr
    _ < γ := by simpa using hN
private theorem entry_mem {k : Type} [Field k] [ValuativeRel k] {n : ℕ}
    (I : Ideal ↥(valuation k).integer) (g : GL (Fin n) k)
    (hg : g ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker) (i j : Fin n) :
    ∃ x ∈ I, (x : k) = (g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I) h = 1 := hh
  have h2 : Ideal.Quotient.mk I ((h : Matrix (Fin n) (Fin n) _) i j)
      = (1 : Matrix (Fin n) (Fin n) (_ ⧸ I)) i j :=
    by
      have h4 := Units.ext_iff.mp h1
      exact congrFun (congrFun h4 i) j
  refine ⟨(h : Matrix (Fin n) (Fin n) _) i j - (1 : Matrix (Fin n) (Fin n) _) i j, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · have h3 : ((Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k) h :
        GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
        = (((h : Matrix (Fin n) (Fin n) ↥(valuation k).integer) i j : _) : k) := rfl
    rw [h3]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
private theorem tendsto_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {α : Type} (L : Filter α) (c : α → ℕ)
    (hc : Tendsto c L atTop) (g : α → GL (Fin n) k)
    (hg : ∀ᶠ a in L, g a ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c a))).ker) :
    Tendsto (fun a => (g a : Matrix (Fin n) (Fin n) k)) L (nhds 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  rw [← tendsto_sub_nhds_zero_iff]
  refine tendsto_def.mpr fun V hV => ?_
  filter_upwards [hg, hc.eventually (small_powers V hV)] with a ha hs
  obtain ⟨x, hx, e⟩ := entry_mem _ _ ha i j
  have := hs x hx
  rwa [e] at this
end

set_option autoImplicit false
open Filter Topology ValuativeRel
namespace UpperTheory
theorem _root_.solution :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) →
        ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∀ g : GL (Fin n) k, g ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker → g ∈ U := by
  intro k _ _ _ _ n U hU
  let K : ℕ → Subgroup (GL (Fin n) k) := fun c => Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c))).ker
  let L : Filter (ℕ × GL (Fin n) k) := comap Prod.fst atTop ⊓ 𝓟 {p | p.2 ∈ K p.1}
  have hc : Tendsto Prod.fst L atTop := tendsto_comap.mono_left inf_le_left
  have hK : ∀ᶠ p in L, p.2 ∈ K p.1 := mem_inf_of_right (mem_principal_self _)
  have h1 := tendsto_val L Prod.fst hc Prod.snd hK
  have h2 := tendsto_val L Prod.fst hc (fun p => p.2⁻¹) (hK.mono fun p hp => (K p.1).inv_mem hp)
  have h : Tendsto Prod.snd L (nhds (1 : GL (Fin n) k)) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds h1 ?_
    exact (MulOpposite.continuous_op.tendsto _).comp h2
  have h3 : ∀ᶠ p in L, p.2 ∈ U := h hU
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at h3
  obtain ⟨c₀, h₀⟩ := h3
  exact ⟨c₀, fun c hc g hg => h₀ c hc (c, g) rfl hg⟩
end UpperTheory
