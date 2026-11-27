-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CotangentBasisInPrime_proof_ac563dd2e6c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:05.454105+00:00
-- url     : https://prove2.me/submissions/bb692f76-16ab-4c41-a228-225eaa56763e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCotangentBasisInPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCotangentBasisInPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CotangentBasisInPrime
theorem _root_.solution : CotangentBasisInPrime.Statement := by
  intro T _ _ P _

  let g : P → maximalIdeal (Localization.AtPrime P) := fun x =>
    ⟨algebraMap T _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P (x : T)).2 x.2⟩
  let v : P → CotangentSpace (Localization.AtPrime P) := fun x => (maximalIdeal _).toCotangent (g x)
  have hspan : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range v) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := (maximalIdeal (Localization.AtPrime P)).toCotangent_surjective z
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective P.primeCompl (y : Localization.AtPrime P)
    simp only at hxs
    have hx : x ∈ P :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P x s).1 (hxs ▸ y.2)
    have hy : y = IsLocalization.mk' (Localization.AtPrime P) (1 : T) s • g ⟨x, hx⟩ := by
      ext
      simp only [g, Submodule.coe_smul, smul_eq_mul, ← hxs]
      rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
    rw [hy, map_smul, ← algebraMap_smul (ResidueField (Localization.AtPrime P))]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField (Localization.AtPrime P)) v
  have : Finite κ := hli.finite_of_isNoetherian
  let e := Finite.equivFin κ
  let w := (v ∘ a) ∘ e.symm
  have hliw : LinearIndependent (ResidueField (Localization.AtPrime P)) w :=
    hli.comp e.symm e.symm.injective
  have hspw : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) = ⊤ := by
    rw [show Set.range w = Set.range (v ∘ a) from e.symm.surjective.range_comp _, hsp, hspan]
  let G : Fin (Nat.card κ) → maximalIdeal (Localization.AtPrime P) := fun i => g (a (e.symm i))
  have hsum : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      (maximalIdeal _).toCotangent (∑ i, c i • G i) = ∑ i, residue _ (c i) • w i := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rfl
  have hcoe : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      ((∑ i, c i • G i : maximalIdeal (Localization.AtPrime P)) : Localization.AtPrime P) =
        ∑ i, c i * algebraMap T _ (a (e.symm i) : T) := by
    intro c
    simp [G, g]
  refine ⟨Nat.card κ, fun i => (a (e.symm i) : T), fun i => (a (e.symm i)).2, ?_, ?_⟩
  · intro y hy
    have hz : (maximalIdeal _).toCotangent ⟨y, hy⟩ ∈
        Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) := by
      rw [hspw]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    choose c' hc' using fun i => residue_surjective (R := Localization.AtPrime P) (c i)
    have hdiff : (maximalIdeal _).toCotangent (⟨y, hy⟩ - ∑ i, c' i • G i) = 0 := by
      rw [map_sub, hsum, ← hc]
      simp [hc']
    rw [Ideal.toCotangent_eq_zero, Submodule.coe_sub, hcoe] at hdiff
    rw [show y = (y - ∑ i, c' i * algebraMap T _ (a (e.symm i) : T)) +
        ∑ i, c' i * algebraMap T _ (a (e.symm i) : T) by ring]
    refine add_mem (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left (Ideal.sum_mem _ fun i _ => ?_))
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro c hc i
    have h0 : (maximalIdeal _).toCotangent (∑ i, c i • G i) = 0 := by
      rw [Ideal.toCotangent_eq_zero, hcoe]; exact hc
    rw [hsum] at h0
    exact (residue_eq_zero_iff _).1 (Fintype.linearIndependent_iff.1 hliw _ h0 i)
end CotangentBasisInPrime
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
