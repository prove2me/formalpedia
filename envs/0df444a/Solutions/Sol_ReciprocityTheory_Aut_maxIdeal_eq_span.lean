-- Prove2me | solution 1 for ReciprocityTheory.Aut.maxIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:41.694792+00:00
-- url     : https://prove2.me/submissions/5d580a2d-0336-4020-ab84-070ee25757e2

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Theorems.Thm_ReciprocityTheory_Aut_mem_maxIdeal_iff
import Theorems.Thm_ReciprocityTheory_Aut_val_le_exp_neg_one_of_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace ReciprocityTheory.Aut
theorem _root_.solution {π : v.adicCompletionIntegers F}
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} := by
  have hπ0 : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  apply le_antisymm
  · intro x hx
    rw [mem_maxIdeal_iff] at hx
    have hx1 := val_le_exp_neg_one_of_lt_one v hx
    have hq : Valued.v ((x : v.adicCompletion F) / π) ≤ 1 := by
      rw [map_div₀, hπ]
      exact (div_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm (by rw [← hπ]; exact (map_ne_zero _).mpr hπ0)))).mpr hx1
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨(x : v.adicCompletion F) / π, hq⟩, ?_⟩
    ext
    simp [div_mul_cancel₀ _ hπ0]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show π ∈ maximalIdeal _
    rw [mem_maxIdeal_iff, hπ]
    exact hexp
end ReciprocityTheory.Aut
