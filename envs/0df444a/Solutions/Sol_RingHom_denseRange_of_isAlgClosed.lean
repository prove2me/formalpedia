-- Prove2me | solution 1 for RingHom.denseRange_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f1ca6faa-1231-5d6a-9b3e-6191a2aac2b5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_denseRange_of_isAlgClosed

theorem solution {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (σ : F →+* ℂ) :
    DenseRange σ := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : F) (n := 2) two_pos
  have hσζ : σ ζ ^ 2 = Complex.I ^ 2 := by rw [← map_pow, hζ, map_neg, map_one, Complex.I_sq]
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : F, σ ζ' = Complex.I := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hσζ with h | h
    · exact ⟨ζ, h⟩
    · exact ⟨-ζ, by rw [map_neg, h, neg_neg]⟩
  let f : ℚ × ℚ → ℂ := fun pq => Complex.equivRealProdCLM.symm (Prod.map Rat.cast Rat.cast pq)
  have hf : DenseRange f :=
    Complex.equivRealProdCLM.symm.surjective.denseRange.comp
      (Rat.denseRange_cast.prodMap Rat.denseRange_cast) Complex.equivRealProdCLM.symm.continuous
  refine Dense.mono ?_ hf
  rintro _ ⟨⟨p, q⟩, rfl⟩
  refine ⟨p + q * ζ', ?_⟩
  simp only [f, Prod.map_apply, Complex.equivRealProdCLM_symm_apply, Complex.ofReal_ratCast, map_add, map_mul,
    map_ratCast, hζ']

end S_RingHom_denseRange_of_isAlgClosed
end P2MW
export P2MW.S_RingHom_denseRange_of_isAlgClosed (solution)
