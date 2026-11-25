-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:08.903605+00:00
-- url     : https://prove2.me/submissions/08e88de0-9213-4b13-8b5d-5ae4d4a6911c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_UJClassFinOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Lam_emb_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_emb_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_sfin_of_Lam_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (hR : RatDense) (hC : ClassFinite) : UJClassFin := by
  unfold UJClassFin
  intro F E _ _ _ _ _ _ σ M J L h1 h2 h3 h4 h5
  have hRL := hR F E σ M J L h4 h5
  obtain ⟨S, hSf, hS⟩ := hC F E σ M J L h1 h2 h3 h4 h5

  let rel : HA (AF F) σ J → HA (AF F) σ J → Prop := fun x y =>
    ∃ γ ∈ GamG σ J, ∃ k ∈ SFin σ J L, x = γ * y * k
  have hrefl : ∀ x, rel x x := fun x => ⟨1, one_mem _, 1, one_mem _, by simp⟩
  have hsymm : ∀ {x y}, rel x y → rel y x := by
    rintro x y ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨γ⁻¹, inv_mem hγ, k⁻¹, inv_mem hk, by group⟩
  have htrans : ∀ {x y z}, rel x y → rel y z → rel x z := by
    rintro x y z ⟨γ, hγ, k, hk, rfl⟩ ⟨γ', hγ', k', hk', rfl⟩
    exact ⟨γ * γ', mul_mem hγ hγ', k' * k, mul_mem hk' hk, by group⟩
  let st : Setoid (HA (AF F) σ J) := ⟨rel, ⟨hrefl, hsymm, htrans⟩⟩
  choose f hfS g hg using hS

  have key : ∀ x y, f x = f y → rel y x := by
    intro x y hxy
    have hL : abelian₂ σ J L (emb σ J (g y * (g x)⁻¹) * x) = abelian₂ σ J L y := by
      rw [Lam_emb_mul (σ := σ) (J := J) L, hg x, hg y, Set.image_image, hxy]
      congr 1
      funext v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel_right]
    have hk := sfin_of_Lam_eq (σ := σ) (J := J) L hRL _ _ hL
    exact ⟨emb σ J (g y * (g x)⁻¹), emb_mem (σ := σ) (J := J) _, _, hk,
      (mul_inv_cancel_left _ _).symm⟩
  have hQ : Finite (Quotient st) := by
    have hfin : (Set.range f).Finite := hSf.subset (by rintro _ ⟨x, rfl⟩; exact hfS x)
    have : Finite (Set.range f) := hfin.to_subtype
    refine Finite.of_surjective (fun s : Set.range f => Quotient.mk st s.2.choose) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      refine ⟨⟨f x, x, rfl⟩, ?_⟩
      exact Quotient.sound (s := st) (key _ _ (Exists.choose_spec (⟨x, rfl⟩ : f x ∈ Set.range f)).symm)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient st)
  refine ⟨n, fun i => (e.symm i).out, ?_, ?_⟩
  · intro x
    have hq : rel (Quotient.mk st x).out x := Quotient.exact (Quotient.out_eq (Quotient.mk st x))
    obtain ⟨γ, hγ, k, hk, hx⟩ := hsymm hq
    refine ⟨e (Quotient.mk st x), ⟨γ, hγ⟩, ⟨k, hk⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hx
  · intro i j γ γ' k k' hEq
    simp only at hEq
    have hr : rel (e.symm i).out (e.symm j).out := by
      refine ⟨(γ : HA (AF F) σ J)⁻¹ * γ', mul_mem (inv_mem γ.2) γ'.2, (k' : HA (AF F) σ J) * (k : HA (AF F) σ J)⁻¹,
        mul_mem k'.2 (inv_mem k.2), ?_⟩
      have h0 : (e.symm i).out = (γ : HA (AF F) σ J)⁻¹ * (γ * (e.symm i).out * k) * (k : HA (AF F) σ J)⁻¹ := by
        group
      rw [h0, hEq]
      group
    have := Quotient.sound (s := st) hr
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact e.symm.injective this
end PI.UnitaryGroupMassFormula.UJClassFin
