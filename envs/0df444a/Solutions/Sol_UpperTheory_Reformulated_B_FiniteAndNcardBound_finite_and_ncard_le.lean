-- Prove2me | solution 1 for UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:01.730289+00:00
-- url     : https://prove2.me/submissions/878cc38e-3bcc-4e17-8318-aae3332c4126

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteAndNcardBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open NumberField
namespace UpperTheory.Reformulated.B.FiniteAndNcardBound
theorem _root_.solution :
    ∀ (E : Type) [inst : Field E] [NumberField E],
    ∃ (C : ℝ) (N : ℕ),
      ∀ (R : ℝ),
        (1 : ℝ) ≤ R →
          {r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.Finite ∧
            (↑{r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.ncard :
                ℝ) ≤
              C * R ^ N := by
  intro E _ _
  classical
  let L := LinearMap.toContinuousLinearMap (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap
  let c : ℝ := ‖L‖
  have hc : 0 ≤ c := norm_nonneg _
  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E))
  refine ⟨(2 * c + 3) ^ n, n, fun R hR => ?_⟩
  let M : ℕ := ⌈c * R⌉₊
  have hM : c * R ≤ M := Nat.le_ceil _
  have hM' : (M : ℝ) ≤ c * R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  let f : RingOfIntegers E → (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E) → ℤ) :=
    (RingOfIntegers.basis E).equivFun
  have hf : Function.Injective f := (RingOfIntegers.basis E).equivFun.injective
  let T : Finset (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E) → ℤ) :=
    Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  have hT : T.card = (2 * M + 1) ^ n := by
    have h1 : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]; omega
    simp only [T, n, Fintype.card_piFinset, h1, Finset.prod_const, Finset.card_univ]
  have hmaps : ∀ r ∈ {r : RingOfIntegers E | ∀ (w : InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R},
      f r ∈ (T : Set _) := by
    intro r hr
    have h1 : ‖canonicalEmbedding E (r : E)‖ ≤ R := by
      rw [canonicalEmbedding.norm_le_iff]
      intro φ
      have := hr (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h2 : ‖L (canonicalEmbedding E (r : E))‖ ≤ M :=
      (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left h1 hc).trans hM)
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h3 := (norm_le_pi_norm _ i).trans h2
    have h4 : L (canonicalEmbedding E (r : E)) i = ((f r i : ℤ) : ℂ) := by
      change (canonicalEmbedding.latticeBasis E).repr (canonicalEmbedding E (r : E)) i = _
      rw [canonicalEmbedding.integralBasis_repr_apply]
      have := integralBasis_repr_apply E r i
      rw [RingOfIntegers.coe_eq_algebraMap, this]
      simp [f]
    rw [h4, Complex.norm_intCast] at h3
    have h5 : |f r i| ≤ (M : ℤ) := by exact_mod_cast h3
    exact abs_le.mp h5
  refine ⟨Set.Finite.of_finite_image (T.finite_toSet.subset ?_) hf.injOn, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact hmaps r hr
  · have h := Set.ncard_le_ncard_of_injOn f hmaps hf.injOn T.finite_toSet
    rw [Set.ncard_coe_finset, hT] at h
    calc _ ≤ (((2 * M + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 * (M : ℝ) + 1) ^ n := by push_cast; rfl
      _ ≤ ((2 * c + 3) * R) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith
      _ = _ := mul_pow _ _ _
end UpperTheory.Reformulated.B.FiniteAndNcardBound
