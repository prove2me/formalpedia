-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.pos_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:47.196367+00:00
-- url     : https://prove2.me/submissions/62960a3c-2696-4b65-893c-68c6f2e70816

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_herm_swap
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_gram_entry
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_form_eq
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mulVec_map_injective
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_coord_injective
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_sylvester_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (τ : E →+* ℂ) {p q : ℕ} (hsig : Formalism.UG.HasSignature (S.gram.map τ) p q) {r : ℕ} (hq : q ≤ r + 1)
    (e : Fin r → S.V) (he : LinearIndependent E e) (hee : ∀ a b, S.hT (e a) (e b) = 0)
    (z : S.V) (hez : ∀ a, S.hT (e a) z = 0) (hzz : (τ (S.hT z z)).re < 0)
    (y : S.V) (hey : ∀ a, S.hT (e a) y = 0) (hzy : S.hT z y = 0)
    (hyX : y ∉ Submodule.span E (Set.range e)) : 0 < (τ (S.hT y y)).re := by
  by_contra hle'
  have hle := not_lt.mp hle'
  have hzz0 : S.hT z z ≠ 0 := by
    intro h; rw [h, map_zero] at hzz; simp at hzz
  have hze : ∀ a, S.hT z (e a) = 0 := fun a => by rw [herm_swap, hez, star_zero]
  have hye : ∀ a, S.hT y (e a) = 0 := fun a => by rw [herm_swap, hey, star_zero]
  have hyz : S.hT y z = 0 := by rw [herm_swap, hzy, star_zero]

  have hXz : ∀ x ∈ Submodule.span E (Set.range e), S.hT z x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hze a
    | zero => simp
    | add x y _ _ h1 h2 => simp [map_add, h1, h2]
    | smul c x _ h => simp [h]
  let u : Fin r ⊕ Fin 2 → S.V := Sum.elim e ![z, y]
  have hpair : LinearIndependent E ![z, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (S.hT z) hst
    simp [map_add, hzy] at h1
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hzz0
    subst hs
    refine ⟨rfl, ?_⟩
    simp at hst
    rcases hst with h | h
    · exact h
    · exact absurd (h ▸ Submodule.zero_mem _) hyX
  have hdisj : Disjoint (Submodule.span E (Set.range e)) (Submodule.span E (Set.range ![z, y])) := by
    rw [Submodule.disjoint_def]
    intro w hw1 hw2
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair] at hw2
    obtain ⟨s, t, rfl⟩ := hw2
    have h1 := hXz _ hw1
    simp [map_add, hzy] at h1
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hzz0
    subst hs
    simp only [zero_smul, zero_add] at hw1 ⊢
    by_cases ht : t = 0
    · simp [ht]
    · exfalso; apply hyX
      have := Submodule.smul_mem _ t⁻¹ hw1
      rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  have hind : LinearIndependent E u := he.sum_type hpair hdisj
  have hB : Function.Injective (coordC S τ u).mulVec :=
    mulVec_map_injective τ _ (coord_injective S u hind)
  have hneg : ∀ v : Fin r ⊕ Fin 2 → ℂ,
      (star (coordC S τ u *ᵥ v) ⬝ᵥ (S.gram.map τ *ᵥ (coordC S τ u *ᵥ v))).re ≤ 0 := by
    intro v
    rw [form_eq]
    have hM : ∀ a b, ((coordC S τ u)ᴴ * S.gram.map τ * coordC S τ u) a b = τ (S.hT (u a) (u b)) :=
      gram_entry S hstar τ u
    simp only [dotProduct, Matrix.mulVec, hM, Fintype.sum_sum_type, Fin.sum_univ_two, u,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      hee, hez, hey, hze, hye, hzy, hyz, map_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
      add_zero]
    have hn : ∀ w : ℂ, ∀ c : ℂ, (star w * (c * w)).re = Complex.normSq w * c.re := by
      intro w c
      rw [Complex.star_def, mul_comm c w, ← mul_assoc, mul_comm (starRingEnd ℂ w) w, Complex.mul_conj]
      rw [Complex.re_ofReal_mul]
    rw [Pi.star_apply, Pi.star_apply, Complex.add_re, hn, hn]
    have := Complex.normSq_nonneg (v (Sum.inr 0))
    have := Complex.normSq_nonneg (v (Sum.inr 1))
    nlinarith
  have hc := sylvester_le _ hsig _ hB hneg
  simp at hc
  omega
end PI.AutLzFinite.SlopeTestRemainingChoices
