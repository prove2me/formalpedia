-- Prove2me | solution 1 for PositivityTheory.ThK.Vac.dual_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:18.818667+00:00
-- url     : https://prove2.me/submissions/1fbc69da-8f7a-4e0c-bffb-f270a15f9211

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_VaceigenAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.Vac
open scoped nonZeroDivisors Matrix
namespace PositivityTheory.ThK.Vac
theorem _root_.solution (R K : Type) {V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] (L : Submodule R V) (hfg : L.FG)
    (hsp : Submodule.span K (L : Set V) = ⊤) :
    ∃ (m : ℕ) (g : Fin m → V) (f : Fin m → V →ₗ[K] K), (∀ i, g i ∈ L) ∧ (∀ i, ∀ x ∈ L, ∃ r : R, algebraMap R K r = f i x) ∧
      ∀ x, x = ∑ i, f i x • g i := by
  have : Module.Finite R L := Module.Finite.iff_fg.2 hfg
  have : Module.IsTorsionFree R V := Module.IsTorsionFree.trans_faithfulSMul R K V
  have : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R L
  have : IsLocalizedModule R⁰ L.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
    · rw [Module.End.isUnit_iff]
      have hs : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have : ⇑(algebraMap R (Module.End R V) s) = fun x => algebraMap R K s • x := by
        ext x; simp
      rw [this]
      exact (MulAction.toPerm (Units.mk0 _ hs)).bijective
    · obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span R⁰ K (L : Set V) y (hsp ▸ Submodule.mem_top)
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  let f : Fin m → V →ₗ[K] K := fun i =>
    IsLocalizedModule.mapExtendScalars R⁰ L.subtype (Algebra.linearMap R K) K ((LinearMap.proj i : (Fin m → R) →ₗ[R] R) ∘ₗ s)
  have hf : ∀ i (x : L), f i x = algebraMap R K (s x i) := fun i x =>
    IsLocalizedModule.map_apply R⁰ L.subtype (Algebra.linearMap R K) ((LinearMap.proj i : (Fin m → R) →ₗ[R] R) ∘ₗ s) x
  refine ⟨m, fun i => p (Pi.single i 1), f, fun i => (p _).2, fun i x hx => ⟨_, (hf i ⟨x, hx⟩).symm⟩, fun x => ?_⟩
  have hx : x ∈ Submodule.span K (L : Set V) := hsp ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have h1 : p (s ⟨x, hx⟩) = ⟨x, hx⟩ := LinearMap.congr_fun hps _
    rw [pi_eq_sum_univ' (s ⟨x, hx⟩), map_sum] at h1
    have h2 := congrArg Subtype.val h1
    simp only [map_smul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h2
    conv_lhs => rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [hf i ⟨x, hx⟩, algebraMap_smul]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, ← hx, ← hy]
  | smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]
end PositivityTheory.ThK.Vac
