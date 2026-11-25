-- Prove2me | solution 1 for PI.LocFramePrimWork.dualFunctionalsExist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:08.031176+00:00
-- url     : https://prove2.me/submissions/28b04694-539c-4faf-b802-c954c2737f17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DualFunctionalsExist
import Theorems.Thm_PI_LocFramePrimWork_Dual_coe_injective
import Theorems.Thm_PI_LocFramePrimWork_Dual_smul_coe
import Theorems.Thm_PI_LocFramePrimWork_Dual_retract
import Theorems.Thm_PI_LocFramePrimWork_Dual_den
import Theorems.Thm_PI_LocFramePrimWork_Dual_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution : Dual := by
  intro F E _ _ _ _ _ n r Λ Lb e f z hΛfg hΛ hind hLb hz hprim
  classical
  have hLbΛ : Lb ≤ Λ := by
    rw [hΛ]
    exact le_sup_right.trans le_sup_left
  have hfg : Lb.FG := Submodule.FG.of_le hΛfg hLbΛ
  obtain ⟨ψ, hψ⟩ := Dual_retract Lb hfg z hz hprim
  obtain ⟨S, hS⟩ := hfg
  have hSLb : ∀ s ∈ S, s ∈ Lb := fun s hs => hS ▸ Submodule.subset_span hs
  obtain ⟨B, hBS, hBspan, hBind⟩ := exists_linearIndependent E (S : Set (Fin n → E))
  have hBLb : ∀ t ∈ B, t ∈ Lb := fun t ht => hSLb t (hBS ht)
  have : Fintype B := (S.finite_toSet.subset hBS).fintype
  have hrange : Set.range (Fin.append e f) ⊆ Set.range e ∪ Set.range f := by
    rintro _ ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left a => exact Or.inl ⟨a, (Fin.append_left e f a).symm⟩
    | right a => exact Or.inr ⟨a, (Fin.append_right e f a).symm⟩
  have hdisj : Disjoint (Submodule.span E (Set.range (Fin.append e f)))
      (Submodule.span E (Set.range ((↑) : B → Fin n → E))) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    rw [Subtype.range_coe] at hx2
    obtain ⟨d, hd, o, hdo⟩ := Dual_den (fun t : B => (t : Fin n → E)) x (by rwa [Subtype.range_coe])
    have hdx : (d : E) • x ∈ Lb := by
      rw [hdo]
      refine Submodule.sum_mem _ fun t _ => ?_
      rw [← Dual_smul_coe]
      exact Lb.smul_mem _ (hBLb t t.2)
    have h0 := hLb _ hdx (Submodule.span_mono hrange (Submodule.smul_mem _ _ hx1))
    have hdE : (d : E) ≠ 0 := fun h => hd (Dual_coe_injective (by rw [h]; rfl))
    exact (smul_eq_zero.1 h0).resolve_left hdE
  have hfam := hind.sum_type hBind hdisj
  have key : ∀ (χ : (Fin n → E) →ₗ[E] E) (ρ : Lb →ₗ[𝓞 E] 𝓞 E),
      (∀ t : B, χ t = (ρ ⟨t, hBLb t t.2⟩ : E)) → ∀ l (hl : l ∈ Lb), χ l = (ρ ⟨l, hl⟩ : E) := by
    intro χ ρ hχ
    have hgen : ∀ s (hs : s ∈ S), χ s = (ρ ⟨s, hSLb s hs⟩ : E) := by
      intro s hs
      have hsB : s ∈ Submodule.span E (Set.range ((↑) : B → Fin n → E)) := by
        rw [Subtype.range_coe, hBspan]
        exact Submodule.subset_span hs
      obtain ⟨d, hd, o, hdo⟩ := Dual_den (fun t : B => (t : Fin n → E)) s hsB
      have hdE : (d : E) ≠ 0 := fun h => hd (Dual_coe_injective (by rw [h]; rfl))
      have hsum : (d • (⟨s, hSLb s hs⟩ : Lb)) = ∑ t : B, o t • (⟨t, hBLb t t.2⟩ : Lb) := by
        apply Subtype.ext
        rw [Submodule.coe_smul, Dual_smul_coe, hdo, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Submodule.coe_smul, Dual_smul_coe]
      have h1 : (d : E) * χ s = (d : E) * (ρ ⟨s, hSLb s hs⟩ : E) := by
        have hL : (d : E) * χ s = ∑ t : B, (o t : E) * (ρ ⟨t, hBLb t t.2⟩ : E) := by
          rw [← smul_eq_mul, ← map_smul, hdo, map_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_smul, smul_eq_mul, hχ t]
        have hR : ρ (d • (⟨s, hSLb s hs⟩ : Lb)) = ∑ t : B, o t * ρ ⟨t, hBLb t t.2⟩ := by
          rw [hsum, map_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_smul, smul_eq_mul]
        rw [map_smul, smul_eq_mul] at hR
        rw [hL]
        have h3 := congrArg (algebraMap (𝓞 E) E) hR
        simp only [map_mul, map_sum] at h3
        exact h3.symm
      exact mul_left_cancel₀ hdE h1
    have key' : ∀ l, l ∈ Submodule.span (𝓞 E) (S : Set (Fin n → E)) → ∀ hl : l ∈ Lb,
        χ l = (ρ ⟨l, hl⟩ : E) := by
      intro l hl'
      induction hl' using Submodule.span_induction with
      | mem x hx => intro hl; exact hgen x hx
      | zero =>
        intro hl
        have h0 : (⟨0, hl⟩ : Lb) = 0 := rfl
        rw [h0, map_zero, map_zero]
        rfl
      | add x y hx hy ihx ihy =>
        intro hl
        have hx' : x ∈ Lb := hS ▸ hx
        have hy' : y ∈ Lb := hS ▸ hy
        have h0 : (⟨x + y, hl⟩ : Lb) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
        rw [map_add, ihx hx', ihy hy', h0, map_add]
        exact (map_add (algebraMap (𝓞 E) E) _ _).symm
      | smul a x hx ihx =>
        intro hl
        have hx' : x ∈ Lb := hS ▸ hx
        have h0 : (⟨a • x, hl⟩ : Lb) = a • ⟨x, hx'⟩ := rfl
        rw [h0, LinearMap.map_smul ρ, Dual_smul_coe, LinearMap.map_smul χ, ihx hx', smul_eq_mul, smul_eq_mul]
        exact (map_mul (algebraMap (𝓞 E) E) _ _).symm
    intro l hl
    exact key' l (hS.symm ▸ hl) hl
  obtain ⟨φz, hφz⟩ := Dual_ext _ hfam (Sum.elim (fun _ => 0) fun t : B => (ψ ⟨t, hBLb t t.2⟩ : E))
  have hφ : ∀ a : Fin r, ∃ φ : (Fin n → E) →ₗ[E] E, ∀ k, φ (Sum.elim (Fin.append e f)
      ((↑) : B → Fin n → E) k) =
      Sum.elim (Fin.append (fun b : Fin r => if a = b then (1 : E) else 0) fun _ => 0) (fun _ => 0) k :=
    fun a => Dual_ext _ hfam _
  choose φ hφ using hφ
  refine ⟨φ, φz, fun a b => ?_, fun a b => ?_, fun a l hl => ?_, fun a => ?_, fun a => ?_, ?_, fun l hl => ?_⟩
  · have := hφ a (Sum.inl (Fin.castAdd r b))
    simpa only [Sum.elim_inl, Fin.append_left] using this
  · have := hφ a (Sum.inl (Fin.natAdd r b))
    simpa only [Sum.elim_inl, Fin.append_right] using this
  · have := key (φ a) 0 (fun t => by
      have h := hφ a (Sum.inr t)
      simp only [Sum.elim_inr] at h
      rw [h]
      rfl) l hl
    rw [this]
    rfl
  · have := hφz (Sum.inl (Fin.castAdd r a))
    simpa only [Sum.elim_inl, Fin.append_left] using this
  · have := hφz (Sum.inl (Fin.natAdd r a))
    simpa only [Sum.elim_inl, Fin.append_right] using this
  · rw [key φz ψ (fun t => by simpa only [Sum.elim_inr] using hφz (Sum.inr t)) z hz, hψ]
    rfl
  · exact ⟨ψ ⟨l, hl⟩, key φz ψ (fun t => by simpa only [Sum.elim_inr] using hφz (Sum.inr t)) l hl⟩
end PI.LocFramePrimWork
