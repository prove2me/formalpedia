-- Prove2me | solution 1 for QH.meanSq_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:17.450052+00:00
-- url     : https://prove2.me/submissions/9333a5f6-66c8-4f42-a71e-8399a9bc742b

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMain
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_MeanSqAbs
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_abs_pair_sum_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_abs_sum_jacobi_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_cN_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_cN_primePow
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_meansq_expand
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_meansq_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_pairs_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_pairs_r
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_soutPart_coprime
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_soutPart_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_soutPart_odd
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_soutPart_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_soutPart_squarefree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ (P : Finset ℕ) (m₀ a₀ nstar : ℕ) (Z y η B : ℝ) (κ : ℕ → ℂ), 8 ∣ m₀ → a₀.Coprime m₀ → 0 ≤ y → 0 ≤ η →
      (∀ q ∈ P, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ ⌊Z⌋₊ ^ 2 < q) → (∀ n, ‖κ n‖ ≤ 1) → (∀ p, sP (cN y) ⌊Z⌋₊ p ≤ B) →
      (∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊Z⌋₊ ^ 2 → s ≠ nstar →
        |∑ q ∈ P, (jacobiSym (q : ℤ) s : ℝ)| ≤ η * P.card) →
      ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ ((∑ p ∈ (Icc 1 ⌊Z⌋₊).filter Nat.Prime, sP (cN y) ⌊Z⌋₊ p ^ 2) + RR (cN y) m₀ ⌊Z⌋₊ ^ 2 +
        (2 * B ^ 2 + 2 * B * RR (cN y) m₀ ⌊Z⌋₊) + η * (∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n) ^ 2) * P.card := by
  intro P m₀ a₀ nstar Z y η B κ h8 hcop hy hη hP hκ hB hJ
  set N := ⌊Z⌋₊ with hN
  have hc0 : ∀ n, 0 ≤ cN y n := cN_nonneg y hy
  have hcpp : ∀ n, cN y n ≠ 0 → IsPrimePow n := cN_primePow y
  have hexp := meansq_expand P (Icc 1 N) (cN y) hc0 κ hκ (fun n q => jacobiSym (n : ℤ) q)
  have hpair : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N,
      |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
        |∑ q ∈ P, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
    intro n hn n' hn'
    rw [Finset.mem_Icc] at hn hn'
    refine abs_pair_sum_eq P m₀ a₀ n n' h8 hcop (by omega) (by omega) ?_
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hP q hq
    refine ⟨h1, h2, lt_of_le_of_lt ?_ h3⟩
    rw [pow_two]
    exact Nat.mul_le_mul hn.2 hn'.2
  have hsplit := meansq_split (Icc 1 N) (cN y) hc0 (fun n n' => soutPart m₀ (n * n'))
    (fun n n' => |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|) (P.card : ℝ) η
    (by positivity) hη (max nstar 2)
    (by
      intro n hn n' hn'
      rw [hpair n hn n' hn']
      exact abs_sum_jacobi_le P _)
    (by
      intro n hn n' hn' hr1 hrs
      rw [hpair n hn n' hn']
      rw [Finset.mem_Icc] at hn hn'
      have hpos := soutPart_pos m₀ (n * n')
      have hnn : 0 < n * n' := Nat.mul_pos (by omega) (by omega)
      have hle : soutPart m₀ (n * n') ≤ N ^ 2 := by
        refine (soutPart_le m₀ _ hnn).trans ?_
        rw [pow_two]
        exact Nat.mul_le_mul hn.2 hn'.2
      refine hJ _ (by omega) (soutPart_odd m₀ _ (dvd_trans (by norm_num) h8))
        (soutPart_squarefree m₀ _) (soutPart_coprime m₀ _) hle ?_
      intro h
      apply hrs
      omega)
  beta_reduce at hsplit
  have h1 := pairs_one (cN y) hc0 hcpp m₀ N
  have h2 := pairs_r (cN y) hc0 hcpp m₀ N (max nstar 2) (by omega) B hB
  refine hexp.trans (hsplit.trans ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith
end QH
