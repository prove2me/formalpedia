-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_comp_323d1cf2b56f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:22.970317+00:00
-- url     : https://prove2.me/submissions/0eec32ab-9347-4da6-b09e-8b42b60667cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germPull_comp_apply_d7155d8709bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_affineGerm_eq_eval__674a1cd1cc41

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
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ τ : Type} [Fintype σ] [Fintype τ] (w : σ → ℂ) (P : Ideal (holGerms w))
    (π : (σ → ℂ) →L[ℂ] (τ → ℂ)) (T : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) (n : ℕ)
    (hdiv : ∀ ψ : holGerms w, ∃ a : Fin n → holGerms (π w),
      ψ - ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T c ^ (j : ℕ) ∈ P)
    {d : ℕ} (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ))
    (hB : IsFiniteGermProjection (π w) (P.comap (germPull π (π.analyticAt w) rfl)) B) :
    IsFiniteGermProjection w P (B.comp π) := by
  classical
  obtain ⟨hBinj, hBgen, hBint⟩ := hB
  have hcompR : germPull (B.comp π) ((B.comp π).analyticAt w) rfl =
      (germPull π (π.analyticAt w) rfl).comp (germPull B (B.analyticAt (π w)) rfl) :=
    RingHom.ext fun x => germPull_comp_apply w π B x
  have hcoordι : ∀ k, germPull π (π.analyticAt w) rfl (coordGerm (π w) k) =
      affineGerm w ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) k).comp π) 0 := by
    intro k
    apply Subtype.ext
    rw [germPull_coe _ _ rfl _ (fun u : τ → ℂ => u k) rfl]
    show (↑((fun u : τ → ℂ => u k) ∘ π) : Germ (𝓝 w) ℂ) = ↑(fun z : σ → ℂ => π z k + 0)
    simp only [add_zero]
    rfl
  generalize germPull π (π.analyticAt w) rfl = ι at hdiv hBinj hBgen hBint hcompR hcoordι
  generalize germPull B (B.analyticAt (π w)) rfl = pB at hBinj hBgen hBint hcompR
  suffices H : (∀ φ : holGerms (B (π w)), ι (pB φ) ∈ P → φ = 0) ∧
      (∀ ψ : holGerms w, ∃ F : MvPolynomial σ (holGerms (B (π w))),
        ψ - MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F ∈ P) ∧
      (∀ i : σ, ∃ q : Polynomial (holGerms (B (π w))), q.Monic ∧
        q.eval₂ (ι.comp pB) (coordGerm w i) ∈ P) by
    unfold IsFiniteGermProjection
    rw [hcompR]
    exact H
  let _ : Algebra (holGerms (B (π w))) (holGerms w ⧸ P) := ((Ideal.Quotient.mk P).comp (ι.comp pB)).toAlgebra
  have hRH : ((Ideal.Quotient.mk P).comp ι).comp pB = algebraMap (holGerms (B (π w))) (holGerms w ⧸ P) :=
    RingHom.ext fun _ => rfl
  let Adj := Algebra.adjoin (holGerms (B (π w))) (Set.range fun i => Ideal.Quotient.mk P (coordGerm w i))
  have hAdj : Adj = (MvPolynomial.aeval fun i => Ideal.Quotient.mk P (coordGerm w i)).range :=
    Algebra.adjoin_range_eq_range_aeval _ _
  let Icl := integralClosure (holGerms (B (π w))) (holGerms w ⧸ P)
  have hev : ∀ F : MvPolynomial σ (holGerms (B (π w))),
      Ideal.Quotient.mk P (MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F) = MvPolynomial.aeval (fun i => Ideal.Quotient.mk P (coordGerm w i)) F := by
    intro F
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    rfl
  have haff : ∀ (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ), Ideal.Quotient.mk P (affineGerm w L c) ∈ Adj := by
    intro L c
    obtain ⟨F, hF⟩ : ∃ F : MvPolynomial σ (holGerms (B (π w))),
        MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F = affineGerm w L c := by
      have h := affineGerm_eq_eval₂ w (B.comp π) L c
      rw [hcompR] at h
      exact h
    rw [← hF, hev, hAdj]
    exact ⟨F, rfl⟩

  have hcoordAdj : ∀ k, Ideal.Quotient.mk P (ι (coordGerm (π w) k)) ∈ Adj := by
    intro k
    rw [hcoordι]
    exact haff _ _
  have hcoordInt : ∀ k, IsIntegral (holGerms (B (π w))) (Ideal.Quotient.mk P (ι (coordGerm (π w) k))) := by
    intro k
    obtain ⟨q, hq, hqP⟩ := hBint k
    refine ⟨q, hq, ?_⟩
    have h1 := Polynomial.hom_eval₂ q pB ((Ideal.Quotient.mk P).comp ι) (coordGerm (π w) k)
    rw [RingHom.comp_apply, RingHom.comp_apply] at h1
    rw [← hRH, ← h1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hqP

  have hR : ∀ a : holGerms (π w), Ideal.Quotient.mk P (ι a) ∈ Adj ∧ Ideal.Quotient.mk P (ι a) ∈ Icl := by
    intro a
    obtain ⟨F, hF⟩ := hBgen a
    have h1 : Ideal.Quotient.mk P (ι a) = MvPolynomial.aeval (fun k => Ideal.Quotient.mk P (ι (coordGerm (π w) k))) F := by
      rw [MvPolynomial.aeval_def, ← hRH]
      have h2 := MvPolynomial.eval₂_comp_left ((Ideal.Quotient.mk P).comp ι) pB (coordGerm (π w)) F
      rw [RingHom.comp_apply] at h2
      refine Eq.trans ?_ h2
      exact Ideal.Quotient.eq.2 (by rw [← map_sub]; exact hF)
    have hmem : Ideal.Quotient.mk P (ι a) ∈ Algebra.adjoin (holGerms (B (π w)))
        (Set.range fun k => Ideal.Quotient.mk P (ι (coordGerm (π w) k))) := by
      rw [h1, Algebra.adjoin_range_eq_range_aeval]
      exact ⟨F, rfl⟩
    exact ⟨Algebra.adjoin_le (Set.range_subset_iff.2 hcoordAdj) hmem,
      Algebra.adjoin_le (Set.range_subset_iff.2 hcoordInt) hmem⟩

  have hθInt : Ideal.Quotient.mk P (affineGerm w T c) ∈ Icl := by
    obtain ⟨b, hb⟩ := hdiv (affineGerm w T c ^ n)
    let b' : Fin n → Icl := fun j => ⟨Ideal.Quotient.mk P (ι (-b j)), (hR (-b j)).2⟩
    have hmon : (Polynomial.X ^ n + ∑ j : Fin n, Polynomial.C (b' j) * Polynomial.X ^ (j : ℕ)).Monic :=
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
    have hI : IsIntegral Icl (Ideal.Quotient.mk P (affineGerm w T c)) := by
      refine ⟨_, hmon, ?_⟩
      have hS : affineGerm w T c ^ n + ∑ j : Fin n, ι (-b j) * affineGerm w T c ^ (j : ℕ) ∈ P := by
        have e : affineGerm w T c ^ n + ∑ j : Fin n, ι (-b j) * affineGerm w T c ^ (j : ℕ) =
            affineGerm w T c ^ n - ∑ j : Fin n, ι (b j) * affineGerm w T c ^ (j : ℕ) := by
          simp only [map_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
        rw [e]
        exact hb
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hS
      rw [map_add, map_sum, map_pow] at h0
      simp only [map_mul, map_pow] at h0
      rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      exact h0
    exact isIntegral_trans (R := holGerms (B (π w))) (A := Icl) _ hI

  have hall : ∀ ψ : holGerms w, Ideal.Quotient.mk P ψ ∈ Adj ∧ Ideal.Quotient.mk P ψ ∈ Icl := by
    intro ψ
    obtain ⟨a, ha⟩ := hdiv ψ
    have hψ : Ideal.Quotient.mk P ψ = ∑ j : Fin n, Ideal.Quotient.mk P (ι (a j)) * Ideal.Quotient.mk P (affineGerm w T c) ^ (j : ℕ) := by
      rw [Ideal.Quotient.eq.2 ha, map_sum]
      simp only [map_mul, map_pow]
    rw [hψ]
    exact ⟨Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hR (a j)).1
        (Subalgebra.pow_mem _ (haff T c) _),
      Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hR (a j)).2 (Subalgebra.pow_mem _ hθInt _)⟩
  refine ⟨fun φ hφ => hBinj φ hφ, fun ψ => ?_, fun i => ?_⟩
  · have h := (hall ψ).1
    rw [hAdj] at h
    obtain ⟨F, hF⟩ := h
    refine ⟨F, Ideal.Quotient.eq.1 ?_⟩
    rw [hev]
    exact hF.symm
  · obtain ⟨q, hq, h0⟩ := (hall (coordGerm w i)).2
    refine ⟨q, hq, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    rw [Polynomial.hom_eval₂]
    exact h0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
