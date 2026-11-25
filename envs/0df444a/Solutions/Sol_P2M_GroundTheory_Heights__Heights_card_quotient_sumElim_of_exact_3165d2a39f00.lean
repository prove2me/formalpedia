-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_card_quotient_sumElim_of_exact_3165d2a39f00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:48.74586+00:00
-- url     : https://prove2.me/submissions/5eba2c6c-2c19-4ec2-8b06-3141e736a4db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {A B C : Type*} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
  [AddCommGroup C] [Module (𝓞 K) C] {i : A →ₗ[𝓞 K] B} {p : B →ₗ[𝓞 K] C}
variable {m n : Type*} [Fintype m] [Fintype n]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) {s' : m → A} {s'' : n → C} {u : n → B} (hu : ∀ j, p (u j) = s'' j)
    (hs'' : LinearIndependent (𝓞 K) s'') :
    Nat.card (B ⧸ Submodule.span (𝓞 K) (Set.range (Sum.elim (fun k ↦ i (s' k)) u))) =
      Nat.card (A ⧸ Submodule.span (𝓞 K) (Set.range s')) *
        Nat.card (C ⧸ Submodule.span (𝓞 K) (Set.range s'')) := by
  set w := Sum.elim (fun k ↦ i (s' k)) u
  set N := Submodule.span (𝓞 K) (Set.range w)
  set S := N ⊔ LinearMap.range i
  rw [← Submodule.card_quotient_mul_card_quotient S N le_sup_left]
  congr 1
  · have hS : S.map N.mkQ = LinearMap.range (N.mkQ ∘ₗ i) := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, LinearMap.range_comp]
    have hker : LinearMap.ker (N.mkQ ∘ₗ i) = Submodule.span (𝓞 K) (Set.range s') := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        rw [Fintype.sum_sum_type] at hg
        simp only [w, Sum.elim_inl, Sum.elim_inr] at hg
        have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
          have := congrArg p hg
          simpa [map_add, map_sum, map_smul, hex.apply_apply_eq_zero, hu] using this
        have hr := (Fintype.linearIndependent_iff.mp hs'') _ h2
        simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
        have : i (∑ k, g (Sum.inl k) • s' k) = i x := by
          rw [← hg, map_sum]
          simp [map_smul]
        rw [← hi this]
        exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · intro hx
        have : i x ∈ (Submodule.span (𝓞 K) (Set.range s')).map i :=
          Submodule.mem_map_of_mem hx
        rw [Submodule.map_span] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨Sum.inl k, rfl⟩
    rw [hS, ← hker]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
  · set φ := (Submodule.span (𝓞 K) (Set.range s'')).mkQ ∘ₗ p
    have hφ : Function.Surjective φ := (Submodule.mkQ_surjective _).comp hp
    have hker : LinearMap.ker φ = S := by
      apply le_antisymm
      · intro x hx
        simp only [φ, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        have hy : x - ∑ j, b j • u j ∈ LinearMap.range i := by
          rw [← hex.linearMap_ker_eq, LinearMap.mem_ker, map_sub, map_sum]
          simp only [map_smul, hu, hb, sub_self]
        have hN : ∑ j, b j • u j ∈ N :=
          Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        have := Submodule.add_mem_sup hN hy
        rwa [add_sub_cancel] at this
      · refine sup_le ?_ ?_
        · rw [Submodule.span_le]
          rintro _ ⟨k, rfl⟩
          rcases k with k | j
          · simp [φ, w, hex.apply_apply_eq_zero]
          · simp only [φ, w, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp,
              Function.comp_apply, Sum.elim_inr, hu, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span ⟨j, rfl⟩
        · rintro _ ⟨y, rfl⟩
          simp [φ, hex.apply_apply_eq_zero]
    rw [← hker]
    exact Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv
end GroundTheory.Heights₂.Heights
