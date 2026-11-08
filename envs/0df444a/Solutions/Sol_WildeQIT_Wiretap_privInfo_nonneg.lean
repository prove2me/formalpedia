-- Prove2me | solution 1 for WildeQIT.Wiretap.privInfo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:37:22.103654+00:00
-- url     : https://prove2.me/submissions/c111a87e-7ac8-4db2-be9c-7691e01d0f05

import Definitions.Def_WildeQIT_Wiretap_privInfo

open WildeQIT

namespace Aux_WildeQIT_privInfo_nonneg

theorem mi_zero {β : Type} [Fintype β] (q : FinDist (Fin 1 × β)) : mutualInfo q = 0 := by
  unfold mutualInfo entropy condEntropy
  have h1 : q.fst.prob 0 = 1 := by
    have := q.fst.sum_eq_one
    rwa [Fin.sum_univ_one] at this
  have h2 : ∀ y, q.prob (0, y) * Real.logb 2 (q.prob (0, y) / q.snd.prob y) = 0 := by
    intro y
    have hs : q.snd.prob y = q.prob (0, y) := by
      rw [FinDist.snd_prob, Fin.sum_univ_one]
    rw [hs]
    by_cases h0 : q.prob (0, y) = 0
    · rw [h0, zero_mul]
    · rw [div_self h0, Real.logb_one, mul_zero]
  rw [Fin.sum_univ_one, Fin.sum_univ_one, h1, Real.logb_one, mul_zero,
    Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_const_zero]
  norm_num

end Aux_WildeQIT_privInfo_nonneg

open WildeQIT.Wiretap in
theorem solution {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (N : WiretapChannel α β γ) : 0 ≤ privInfo N := by
  unfold privInfo
  rcases isEmpty_or_nonempty α with hα | hα
  · apply Real.sSup_nonneg
    rintro x ⟨n, p, -⟩
    have := p.sum_eq_one
    simp at this
  · apply Real.sSup_nonneg'
    have hc : (0:ℝ) < (Fintype.card (Fin 1 × α) : ℝ) := by exact_mod_cast Fintype.card_pos
    let p : FinDist (Fin 1 × α) :=
      { prob := fun _ => 1 / (Fintype.card (Fin 1 × α) : ℝ)
        nonneg := fun _ => by positivity
        sum_eq_one := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp }
    refine ⟨0, ⟨1, p, ?_⟩, le_rfl⟩
    rw [Aux_WildeQIT_privInfo_nonneg.mi_zero, Aux_WildeQIT_privInfo_nonneg.mi_zero]
    norm_num
