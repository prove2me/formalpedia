-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_eq_c804c0ba1527
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:26.16771+00:00
-- url     : https://prove2.me/submissions/43d90456-f96d-40d3-990b-65c92155d55a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_add_bf6edbac3a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_add_583a49333333
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_of_subsingleton_23d6f7c0e257
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_free_5ba711a9e1d1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution {C : Type u} [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (hPID : IsPrincipalIdealRing (C ⧸ P)) (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal)
    (k : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
      (∀ p ∈ P ^ k, ∀ m : M, p • m = 0) → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (QuotSMulTop y M) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) := by
  induction k with
  | zero =>
    intro M _ _ _ hann _
    have : Subsingleton M := ⟨fun a b => by
      rw [← one_smul C a, ← one_smul C b, hann 1 (by simp) a, hann 1 (by simp) b]⟩
    rw [(lengths_of_subsingleton P y M).1, (lengths_of_subsingleton P y M).2]
  | succ k ih =>
    intro M _ _ _ hann hinj
    have := hPID

    have : Module.Finite C (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_injective (Submodule.torsionBySet C M (P : Set C)).subtype
        (Submodule.torsionBySet C M (P : Set C)).injective_subtype
    have : Module.Finite (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_restrictScalars_finite C (C ⧸ P) _
    have : Module.IsTorsionFree (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) := by
      refine Module.IsTorsionFree.of_smul_eq_zero fun r n h => ?_
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
      by_cases hs : s ∈ P
      · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.2 hs)
      · right
        rw [Submodule.torsionBySet.mk_smul] at h
        exact Subtype.ext (hinj s hs n (congrArg Subtype.val h))
    obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := C ⧸ P)
      (M := Submodule.torsionBySet C M (P : Set C))
    have hN := lengths_free P hy hmax (b.equivFun.restrictScalars C)

    have hannQ : ∀ p ∈ P ^ k, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), p • q = 0 := by
      intro p hp q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [smul_smul]
      exact hann _ (by rw [pow_succ']; exact Ideal.mul_mem_mul ha hp) m
    have hinjQ : ∀ s ∉ P, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), s • q = 0 → q = 0 := by
      intro s hs q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff] at hq
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      apply hinj s hs
      rw [smul_comm]
      exact hq ⟨a, ha⟩
    have hQ := ih (M ⧸ Submodule.torsionBySet C M (P : Set C)) hannQ hinjQ
    let N := Submodule.torsionBySet C M (P : Set C)
    rw [length_quotSMulTop_add y N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N) (hinjQ y hy),
      length_localized_add P N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hQ, hN.1, hN.2]
end GroundTheory.Heights₂.Heights.LengthCutGlobal
