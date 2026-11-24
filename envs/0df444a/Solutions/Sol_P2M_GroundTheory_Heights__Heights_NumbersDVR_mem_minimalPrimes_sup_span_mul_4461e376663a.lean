-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_mul_4461e376663a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:26.585271+00:00
-- url     : https://prove2.me/submissions/b8996ee3-022b-49ce-b758-b879e286e3a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution [IsNoetherianRing A] {P W : Ideal A} [P.IsPrime] {x y : A}
    (hy : y ∉ P) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr (W.mul_mem_right y hxW))⟩, ?_⟩
  rintro Q ⟨hQp, hQ⟩ hQW
  have hPQ : P ≤ Q := le_sup_left.trans hQ
  rcases hQp.mem_or_mem (hQ (Ideal.mem_sup_right (Ideal.subset_span rfl))) with hxQ | hyQ
  · exact hW.2 ⟨hQp, sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hQW
  by_contra hWQ
  have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ h.ge)
  have hPQlt : P < Q := lt_of_le_of_ne hPQ (fun h => hy (h ▸ hyQ))
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hQ' : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPQ)
  have hW' : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPW)
  have h0 : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have hcQ : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPQ]
  have hcW : (W.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = W := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPW]
  have hcP : (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) = P := by
    rw [← RingHom.ker_eq_comap_bot, hker]
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne bot_le (fun h => hPQlt.ne
      (hcP.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcQ)))
  have h2 : Q.map (Ideal.Quotient.mk P) < W.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hQW) (fun h => hlt.ne
      (hcQ.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcW)))
  have hb := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have hc := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have hk := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h2le : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal (A ⧸ P)).height + 1 + 1 := by gcongr; positivity
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ 1 := hc.trans hk
  exact absurd h2le (by norm_num)
end GroundTheory.Heights₂.Heights.NumbersDVR
