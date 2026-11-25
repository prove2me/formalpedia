-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_ext_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:07.651721+00:00
-- url     : https://prove2.me/submissions/1dba2228-2b83-461d-8f40-0d556af6e994

import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_eval_eq_lagrange
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_exists_nodes
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_poly_eq_of_eval_eq_off
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_sepPoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (g D : (σ → ℂ) → ℂ)
    (w : σ → ℂ) (hw : ∀ z, {s : ℂ | D (z + s • w) = 0}.Finite)
    (hD : ∀ z v, D z ≠ 0 → {t : ℂ | D (z + t • v) = 0}.Finite)
    (hL : ∀ z v, {t : ℂ | D (z + t • v) = 0}.Finite → ∃ Q : ℂ[X], Q.natDegree ≤ k ∧
      ∀ t, D (z + t • v) ≠ 0 → g (z + t • v) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ z, D z ≠ 0 → g z = MvPolynomial.eval z F := by

  have hw' := fun y => hL y w (hw y)
  choose Qw hQd hQ using hw'

  have hv' := fun (y v : σ → ℂ) (h : D y ≠ 0) => hL y v (hD y v h)
  choose P hPd hP using hv'
  let G : (σ → ℂ) → ℂ := fun y => (Qw y).eval 0
  have hsep : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t := by
    intro y m
    set z : σ → ℂ := Function.update y m 0
    set e : σ → ℂ := Pi.single m 1
    have hupd : ∀ t, Function.update y m t = z + t • e := by
      intro t; ext i
      by_cases hi : i = m
      · subst hi; simp [z, e]
      · simp [z, e, Function.update_apply, hi, Pi.single_apply]
    let Pc : ℂ → ℂ[X] := fun c => if h : D (z + c • w) = 0 then 0 else P (z + c • w) e h
    let R : Finset ℂ → ℂ[X] := fun S =>
      ∑ c ∈ S, Polynomial.C ((Lagrange.basis S id c).eval 0) * Pc c
    have hRdeg : ∀ S, (R S).natDegree ≤ k := by
      intro S
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun c _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      simp only [Pc]
      split_ifs with h
      · simp
      · exact hPd _ _ h

    have key : ∀ S : Finset ℂ, S.card = k + 1 → (∀ c ∈ S, D (z + c • w) ≠ 0) →
        ∀ t, (∀ c ∈ S, D ((z + t • e) + c • w) ≠ 0) → G (z + t • e) = (R S).eval t := by
      intro S hS hSz t ht
      simp only [G, R]
      rw [bwp_eval_eq_lagrange S (Qw (z + t • e)) k hS (hQd _) 0, Polynomial.eval_finset_sum]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, ← hQ _ c (ht c hc)]
      congr 1
      simp only [Pc, dif_neg (hSz c hc)]
      rw [← hP _ _ (hSz c hc) t (by rw [add_right_comm]; exact ht c hc), add_right_comm]
    have hbad : ∀ S : Finset ℂ, (∀ c ∈ S, D (z + c • w) ≠ 0) →
        {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0}.Finite := by
      intro S hSz
      have : {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0} =
          ⋃ c ∈ S, {t : ℂ | D ((z + c • w) + t • e) = 0} := by
        ext t; simp [add_right_comm]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet (fun c hc => hD _ e (hSz c hc))
    obtain ⟨S0, hS0, hS0z⟩ := bwp_exists_nodes {s | D (z + s • w) = 0} (hw z) k
    refine ⟨R S0, hRdeg S0, fun t0 => ?_⟩
    rw [hupd]
    obtain ⟨S1, hS1, hS1z⟩ := bwp_exists_nodes
      ({s | D (z + s • w) = 0} ∪ {s | D ((z + t0 • e) + s • w) = 0})
      ((hw z).union (hw (z + t0 • e))) k
    have hS1a : ∀ c ∈ S1, D (z + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inl h)
    have hS1b : ∀ c ∈ S1, D ((z + t0 • e) + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inr h)
    have hS0a : ∀ c ∈ S0, D (z + c • w) ≠ 0 := fun c hc h => hS0z c hc h
    have hRR : R S0 = R S1 := by
      refine bwp_poly_eq_of_eval_eq_off _ _ _ ((hbad S0 hS0a).union (hbad S1 hS1a)) (fun t ht => ?_)
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at ht
      rw [← key S0 hS0 hS0a t ht.1, ← key S1 hS1 hS1a t ht.2]
    rw [hRR, key S1 hS1 hS1a t0 hS1b]
  obtain ⟨F, hF⟩ := bwp_sepPoly k G hsep
  refine ⟨F, fun z hz => ?_⟩
  rw [← hF]
  have := hQ z 0 (by simpa using hz)
  simpa [G] using this
end ReciprocityTheory.MultiplicativeHeights
