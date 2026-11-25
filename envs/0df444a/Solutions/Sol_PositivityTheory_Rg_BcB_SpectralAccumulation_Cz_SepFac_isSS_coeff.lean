-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:22.41733+00:00
-- url     : https://prove2.me/submissions/d60a4bb2-0dd6-469f-b12e-de17ffb05090

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_factor_roots
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_factor_deg
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_of_decomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {B : Type} [CommRing B] [Algebra ℂ B]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
theorem _root_.solution (p : ℂ[X]) (hp : p.Separable) (P Q : B[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P * Q = p.map (algebraMap ℂ B)) (k : ℕ) : IsSS (P.coeff k) := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact ⟨∅, Subsingleton.elim _ _⟩
  have hinj : Function.Injective (algebraMap ℂ B) := (algebraMap ℂ B).injective
  have hp0 : p ≠ 0 := hp.ne_zero
  set R := p.roots.toFinset with hR
  have hdegPQ : P.natDegree + Q.natDegree = p.natDegree := by
    rw [← hP.natDegree_mul hQ, hPQ, natDegree_map_eq_of_injective hinj]
  have hcard : R.card = p.natDegree := by
    rw [hR, Multiset.toFinset_card_of_nodup (nodup_roots hp)]
    exact IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ α ∈ R, p.eval α = 0 := fun α hα => by
    rw [hR, Multiset.mem_toFinset, mem_roots hp0] at hα
    exact hα
  have hder : ∀ α ∈ R, p.derivative.eval α ≠ 0 := fun α hα h0 => by
    obtain ⟨u, v, huv⟩ : IsCoprime p (derivative p) := hp
    have := congrArg (eval α) huv
    simp [eval_add, eval_mul, hroot α hα, h0] at this
  have hPQa : ∀ α ∈ R, P.eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    rw [← eval_mul, hPQ, eval_map, eval₂_at_apply, hroot α hα, map_zero]
  have hDa : ∀ α ∈ R, (derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
      P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) = algebraMap ℂ B (p.derivative.eval α) := by
    intro α hα
    rw [← eval_mul, ← eval_mul, ← eval_add, ← derivative_mul, hPQ, derivative_map, eval_map, eval₂_at_apply]
  let e : ℂ → B := fun α =>
    P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹
  have heQ : ∀ α ∈ R, e α * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    linear_combination ((derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  have hfP : ∀ α ∈ R, (1 - e α) * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    have hI : ((derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
        P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α)) *
          algebraMap ℂ B (p.derivative.eval α)⁻¹ = 1 := by
      rw [hDa α hα, ← map_mul, mul_inv_cancel₀ (hder α hα), map_one]
    linear_combination (-P.eval (algebraMap ℂ B α)) * hI +
      ((derivative P).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  let E : Finset ℂ → B := fun I => (∏ α ∈ I, e α) * ∏ α ∈ R \ I, (1 - e α)
  have hsum : ∑ I ∈ R.powerset, E I = 1 := by
    simp only [E]
    rw [← Finset.prod_add]
    simp
  have hmonJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).Monic := fun J =>
    monic_prod_of_monic _ _ fun α _ => monic_X_sub_C _
  have hdegJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).natDegree = J.card := by
    intro J
    rw [natDegree_prod_of_monic _ _ fun α _ => monic_X_sub_C _]
    simp
  have hmapJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))) = (∏ α ∈ J, (X - C α)).map (algebraMap ℂ B) := by
    intro J
    simp [Polynomial.map_prod]
  refine isSS_of_decomp R.powerset E (fun I => (∏ α ∈ R \ I, (X - C α)).coeff k) hsum fun I hI => ?_
  rw [Finset.mem_powerset] at hI
  by_cases hE : E I = 0
  · rw [hE, mul_zero, smul_zero]
  have hEQ : ∀ α ∈ I, E I * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * Q.eval (algebraMap ℂ B α) =
        (e α * Q.eval (algebraMap ℂ B α)) * ((∏ β ∈ I.erase α, e β) * ∏ β ∈ R \ I, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase I e hα]
          ring
      _ = 0 := by rw [heQ α (hI hα), zero_mul]
  have hEP : ∀ α ∈ R \ I, E I * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * P.eval (algebraMap ℂ B α) =
        ((1 - e α) * P.eval (algebraMap ℂ B α)) * ((∏ β ∈ I, e β) * ∏ β ∈ (R \ I).erase α, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase (R \ I) (fun β => 1 - e β) hα]
          ring
      _ = 0 := by rw [hfP α (Finset.mem_sdiff.1 hα).1, zero_mul]
  obtain ⟨R₁, hR₁⟩ := factor_roots (E I) P (R \ I) hEP
  obtain ⟨R₂, hR₂⟩ := factor_roots (E I) Q I hEQ
  obtain ⟨h1, h2⟩ := factor_deg hP (hmonJ _) hR₁
  obtain ⟨h3, -⟩ := factor_deg hQ (hmonJ _) hR₂
  rw [hdegJ] at h1 h2 h3
  have hsd := Finset.card_sdiff_add_card_eq_card hI
  have heq : (R \ I).card = P.natDegree := by
    rcases h1 with h1 | h1
    · rcases h3 with h3 | h3
      · omega
      · exact absurd h3 hE
    · exact absurd h1 hE
  have := h2 heq k
  rw [hmapJ, coeff_map] at this
  rw [mul_comm, this, Algebra.smul_def, mul_comm]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
