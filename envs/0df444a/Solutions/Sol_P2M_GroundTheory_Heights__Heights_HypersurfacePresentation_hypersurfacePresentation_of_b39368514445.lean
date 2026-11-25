-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_hypersurfacePresentation_of_b39368514445
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:04.781749+00:00
-- url     : https://prove2.me/submissions/cb64c699-19ef-4861-8b0c-63ed3fd6cbf0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_separable_presentation_c7d32058bf05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_transcendenceBasis_fin_c8a021ddf186
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_isAlgebraic_aeval_of_isTranscendenceBasis_b6ebe60b22a2

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
variable {σ ι : Type} [Finite σ] [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) [K.IsPrime]
local notation "𝔸" => MvPolynomial ι (MvPolynomial σ ℂ) ⧸ K
omit [Finite σ]
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.HypersurfacePresentation
theorem _root_.solution (hKS : ∀ s : MvPolynomial σ ℂ, C s ∈ K → s = 0) :
    ∃ (d : ℕ) (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
      (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
      (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
      (u v : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      m.Monic ∧ D ≠ 0 ∧ u * m + v * Polynomial.derivative m = Polynomial.C D ∧
      (∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
        Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H) ∧
      ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K := by
  classical
  have := Fintype.ofFinite ι
  have hmkC : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial σ ℂ) 𝔸 s := fun s => rfl
  have hSinj : Function.Injective (algebraMap (MvPolynomial σ ℂ) 𝔸) := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    rw [← hmkC, Ideal.Quotient.eq_zero_iff_mem] at hs
    exact hKS s hs
  have : FaithfulSMul (MvPolynomial σ ℂ) 𝔸 := (faithfulSMul_iff_algebraMap_injective _ _).2 hSinj
  let x : ι → 𝔸 := fun i => Ideal.Quotient.mk K (X i)
  have hadj : Algebra.adjoin (MvPolynomial σ ℂ) (Set.range x) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    clear ‹a ∈ ⊤›
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C s => rw [hmkC]; exact Subalgebra.algebraMap_mem _ s
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  obtain ⟨d, yA, hbd⟩ := exists_transcendenceBasis_fin x hadj

  let : Algebra (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 := (MvPolynomial.aeval yA).toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r = MvPolynomial.aeval yA r :=
    fun _ => rfl
  have hRinj : Function.Injective (algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸) := fun a b h =>
    algebraicIndependent_iff_injective_aeval.1 hbd.1 (by rwa [hmap, hmap] at h)
  have : FaithfulSMul (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hRinj
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 :=
    isAlgebraic_aeval_of_isTranscendenceBasis hbd
  have hmkCR : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 (C s) :=
    fun s => by
      rw [hmkC]
      show _ = MvPolynomial.aeval yA (C s)
      rw [MvPolynomial.aeval_C]
  let eι := Finite.equivFin ι
  have hadjR : Algebra.adjoin (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (Set.range fun j => x (eι.symm j)) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    clear ‹a ∈ ⊤›
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C s => rw [hmkCR]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin ⟨eι i, by simp [x]⟩)
  obtain ⟨θA, hmon, hker, D, hD, q, u, v, huv, hq⟩ :=
    exists_separable_presentation (R := MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (fun j => x (eι.symm j)) hadjR x

  choose y hy using fun j => Ideal.Quotient.mk_surjective (yA j)
  obtain ⟨θ, hθmk⟩ := Ideal.Quotient.mk_surjective θA
  have hcompA : (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) K).comp (aeval y) = MvPolynomial.aeval yA :=
    MvPolynomial.algHom_ext fun j => by
      rw [AlgHom.comp_apply, aeval_X, aeval_X, Ideal.Quotient.mkₐ_eq_mk, hy]
  have hcomp : ∀ r, Ideal.Quotient.mk K (aeval y r) =
      algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r := fun r => by
    rw [hmap, ← hcompA, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  have heval : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
      Ideal.Quotient.mk K (Polynomial.eval₂ (aeval y).toRingHom θ H) = Polynomial.aeval θA H := by
    intro H
    rw [Polynomial.hom_eval₂, hθmk, Polynomial.aeval_def]
    congr 1
    exact RingHom.ext hcomp
  refine ⟨d, y, θ, minpoly (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) θA, D, q, u, v, hmon, hD, huv,
    fun H => ?_, fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, heval]
    exact hker H
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, heval, hcomp, hq i, sub_eq_zero]
end GroundTheory.Heights₂.Heights.HypersurfacePresentation
