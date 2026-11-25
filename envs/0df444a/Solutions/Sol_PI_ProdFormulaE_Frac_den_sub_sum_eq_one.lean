-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.den_sub_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:58.114807+00:00
-- url     : https://prove2.me/submissions/2fe6da3a-168e-4218-8162-7b917073c947

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Theorems.Thm_PI_ProdFormulaE_Frac_padicNorm_le_one_of_den_pow
import Theorems.Thm_PI_ProdFormulaE_Frac_den_eq_one_of_forall_padicNorm_le_one
import Theorems.Thm_PI_ProdFormulaE_Frac_padicNorm_le_one_of_den_eq_one
import Theorems.Thm_PI_ProdFormulaE_Frac_padicNorm_add_le_one
import Theorems.Thm_PI_ProdFormulaE_Frac_padicNorm_sub_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open PI PI.ProdFormulaE PI.ProdFormulaE.Frac
namespace PI.ProdFormulaE.Frac
theorem _root_.solution {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (I : Finset ι) (hI : ∀ i, i ∉ I → (a i).den = 1)
    (t : ℚ) (ht : ∀ q : ℕ, q.Prime → padicNorm q (t - ∑ i ∈ fib q, a i) ≤ 1) :
    (t - ∑ i ∈ I, a i).den = 1 := by
  classical
  apply den_eq_one_of_forall_padicNorm_le_one
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  have hsum : ∀ s : Finset ι, (∀ i ∈ s, padicNorm q (a i) ≤ 1) →
      padicNorm q (∑ i ∈ s, a i) ≤ 1 :=
    fun s hs => Finset.sum_induction _ (fun x => padicNorm q x ≤ 1)
      (fun x y hx hy => padicNorm_add_le_one hx hy) (by simp) hs
  have h1 : padicNorm q (∑ i ∈ fib q \ I, a i) ≤ 1 :=
    hsum _ (fun i hi => padicNorm_le_one_of_den_eq_one (hI i (Finset.mem_sdiff.1 hi).2))
  have h2 : padicNorm q (∑ i ∈ I \ fib q, a i) ≤ 1 := hsum _ (fun i hi => by
    obtain ⟨n, hn⟩ := ha i
    have hne : ℓ i ≠ q := fun h => (Finset.mem_sdiff.1 hi).2 ((hfib i q).2 h)
    exact padicNorm_le_one_of_den_pow (hℓ i) hne hn)
  have e : t - ∑ i ∈ I, a i =
      (t - ∑ i ∈ fib q, a i) + (∑ i ∈ fib q \ I, a i - ∑ i ∈ I \ fib q, a i) := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]
    ring
  rw [e]
  exact padicNorm_add_le_one (ht q hq) (padicNorm_sub_le_one h1 h2)
end PI.ProdFormulaE.Frac
