-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.prod_reindex_option
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:35.577913+00:00
-- url     : https://prove2.me/submissions/abff343c-5054-4186-9b88-3861763be026

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {e rc : ℕ} (J : Finset (Fin e)) (σ : Fin e → Option (Fin rc))
    (hnone : ∀ l, σ l = none ↔ l ∉ J) (σ' : Fin rc → Option (Fin e))
    (hσ' : ∀ k l, σ' k = some l ↔ σ l = some k) (m : Fin rc → ℕ) (w : Fin e → ℂ) :
    ∏ l ∈ J, w l ^ (σ l).elim 0 m = ∏ k, Option.elim (σ' k) 1 (fun i => w i ^ m k) := by
  have hL : ∀ l, w l ^ (σ l).elim 0 m = ∏ k, if σ l = some k then w l ^ m k else 1 := by
    intro l
    cases h : σ l with
    | none => simp
    | some k0 => simp [Finset.prod_ite_eq, Finset.prod_ite_eq']
  have hR : ∀ k, Option.elim (σ' k) 1 (fun i => w i ^ m k) =
      ∏ l ∈ J, if σ l = some k then w l ^ m k else 1 := by
    intro k
    cases h : σ' k with
    | none =>
      simp only [Option.elim]
      refine (Finset.prod_eq_one fun l _ => ?_).symm
      rw [if_neg]
      intro hl
      rw [← hσ', h] at hl
      cases hl
    | some l0 =>
      have hl0 : σ l0 = some k := (hσ' k l0).1 h
      have hJ : l0 ∈ J := by
        by_contra hn
        rw [(hnone l0).2 hn] at hl0
        cases hl0
      simp only [Option.elim]
      rw [Finset.prod_eq_single l0]
      · rw [if_pos hl0]
      · intro l _ hne
        rw [if_neg]
        intro hl
        rw [← hσ', h] at hl
        exact hne (Option.some_injective _ hl).symm
      · intro hn
        exact absurd hJ hn
  rw [Finset.prod_congr rfl fun l _ => hL l, Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => (hR k).symm
end ReciprocityTheory.AnForm.R
