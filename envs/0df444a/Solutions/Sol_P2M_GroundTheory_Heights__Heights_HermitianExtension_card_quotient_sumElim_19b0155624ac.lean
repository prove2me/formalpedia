-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_card_quotient_sumElim_19b0155624ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:46.231529+00:00
-- url     : https://prove2.me/submissions/146e5a2b-cc63-4375-b963-959f838c1f73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n]
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs'' : LinearIndependent (𝓞 K) s'') :
    Nat.card (E.carrier ⧸ Submodule.span (𝓞 K) (Set.range (Sum.elim (fun i ↦ X.incl (s' i)) u))) =
      Nat.card (E'.carrier ⧸ Submodule.span (𝓞 K) (Set.range s')) *
        Nat.card (E''.carrier ⧸ Submodule.span (𝓞 K) (Set.range s'')) := by
  set w := Sum.elim (fun i ↦ X.incl (s' i)) u
  set N := Submodule.span (𝓞 K) (Set.range w)
  set S := N ⊔ LinearMap.range X.incl
  rw [← Submodule.card_quotient_mul_card_quotient S N le_sup_left]
  congr 1
  · have hS : S.map N.mkQ = LinearMap.range (N.mkQ ∘ₗ X.incl) := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, LinearMap.range_comp]
    have hker : LinearMap.ker (N.mkQ ∘ₗ X.incl) = Submodule.span (𝓞 K) (Set.range s') := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        rw [Fintype.sum_sum_type] at hg
        simp only [w, Sum.elim_inl, Sum.elim_inr] at hg
        have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
          have := congrArg X.proj hg
          simpa [map_add, map_sum, map_smul, proj_incl, hu] using this
        have hr := (Fintype.linearIndependent_iff.mp hs'') _ h2
        simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
        have : X.incl (∑ i, g (Sum.inl i) • s' i) = X.incl x := by
          rw [← hg, map_sum]
          simp [map_smul]
        rw [← X.incl_injective this]
        exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hx
        have : X.incl x ∈ (Submodule.span (𝓞 K) (Set.range s')).map X.incl :=
          Submodule.mem_map_of_mem hx
        rw [Submodule.map_span] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
    rw [hS, ← hker]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
  · set φ := (Submodule.span (𝓞 K) (Set.range s'')).mkQ ∘ₗ X.proj
    have hφ : Function.Surjective φ := (Submodule.mkQ_surjective _).comp X.proj_surjective
    have hker : LinearMap.ker φ = S := by
      apply le_antisymm
      · intro x hx
        simp only [φ, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        have hy : x - ∑ j, b j • u j ∈ LinearMap.range X.incl := by
          rw [← X.exact.linearMap_ker_eq, LinearMap.mem_ker, map_sub, map_sum]
          simp only [map_smul, hu, hb, sub_self]
        have hN : ∑ j, b j • u j ∈ N :=
          Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        have := Submodule.add_mem_sup hN hy
        rwa [add_sub_cancel] at this
      · refine sup_le ?_ ?_
        · rw [Submodule.span_le]
          rintro _ ⟨k, rfl⟩
          rcases k with i | j
          · simp [φ, w, proj_incl]
          · simp only [φ, w, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp,
              Function.comp_apply, Sum.elim_inr, hu, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span ⟨j, rfl⟩
        · rintro _ ⟨y, rfl⟩
          simp [φ, proj_incl]
    rw [← hker]
    exact Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv
end GroundTheory.Heights₂.Heights.HermitianExtension
