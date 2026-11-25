-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage.average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:49.56539+00:00
-- url     : https://prove2.me/submissions/72975bb1-cf40-483a-826f-65b57cc5500d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
  ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) (L : ℕ∞) (D : K₁)
    (t : HeightOneSpectrum (𝓞 K₁) → ℝ) (ρ : ℕ) (B : ℝ)
    (h : ∀ w : HeightOneSpectrum (𝓞 K₁), LiesOver w la → ∃ n : ℕ,
      (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) * L = n ∧
      (n : ℝ) ≤ (ordAt w D : ℝ) + t w + ρ * ((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * B)) :
    ∃ ℓ : ℕ, L = ℓ ∧ (ℓ : ℝ) ≤ (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + t w.1)) /
        (Module.finrank K K₁ : ℝ) + ρ * B := by
  classical
  let S := la.asIdeal.primesOver (𝓞 K₁)
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K₁)) :=
    FaithfulSMul.algebraMap_injective _ _
  let E : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la} ≃ S :=
    { toFun := fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨w.2.symm⟩⟩
      invFun := fun q => ⟨⟨q.1, q.2.1, fun h0 => la.ne_bot (by
          have h1 : la.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 K₁)) := q.2.2.over
          rw [h1, h0]
          exact Ideal.comap_bot_of_injective _ hinj)⟩, q.2.2.over.symm⟩
      left_inv := fun w => rfl
      right_inv := fun q => rfl }
  have hsumN : ∑ q : S, q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K K₁ := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 K₁) K₁]
  have hn : 0 < Module.finrank K K₁ := Module.finrank_pos
  have hne : Nonempty S := by
    by_contra hS
    rw [not_nonempty_iff] at hS
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsumN
    omega
  obtain ⟨q0⟩ := hne
  obtain ⟨n0, hn0, -⟩ := h (E.symm q0).1 (E.symm q0).2
  have he0 : 0 < (E.symm q0).1.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_pos _ _
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ : ℕ, L = ℓ := by
    induction L using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.mul_top (by exact_mod_cast he0.ne')] at hn0
      exact ENat.top_ne_natCast n0 hn0
    | coe ℓ => exact ⟨ℓ, rfl⟩
  refine ⟨ℓ, rfl, ?_⟩
  have hq : ∀ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ ≤ (ordAt (E.symm q).1 D : ℝ) +
      t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B) := by
    intro q
    obtain ⟨n, hn1, hn2⟩ := h (E.symm q).1 (E.symm q).2
    have h1 : ((q.1.ramificationIdx (𝓞 K) * ℓ : ℕ) : ℕ∞) = n := by push_cast; exact hn1
    have h2 : q.1.ramificationIdx (𝓞 K) * ℓ = n := by exact_mod_cast h1
    have h3 : (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ = n := by exact_mod_cast h2
    rw [h3]
    exact hn2
  have hsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) ≤
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1 +
        ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)) :=
    Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hq q) (Nat.cast_nonneg _)
  have hN : ∑ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * (q.1.inertiaDeg (𝓞 K) : ℝ) =
      Module.finrank K K₁ := by exact_mod_cast hsumN
  have hfs : (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
      (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + t w.1)) =
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1) := by
    rw [← finsum_comp_equiv E.symm, finsum_eq_sum_of_fintype]
    rfl
  have hLsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) =
      ℓ * Module.finrank K K₁ := by
    rw [← hN, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hRsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) +
      t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)) =
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1) +
        ρ * B * Module.finrank K K₁ := by
    rw [← hN, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hLsum, hRsum] at hsum
  have hnpos : (0 : ℝ) < Module.finrank K K₁ := by exact_mod_cast hn
  rw [hfs, div_add' _ _ _ hnpos.ne', le_div_iff₀ hnpos]
  linarith
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
