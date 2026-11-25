-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_ChainHighest_aux__53c00536da70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:18.270904+00:00
-- url     : https://prove2.me/submissions/ba1dd4f2-b767-454c-a993-b4da714d600e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsCocycleOfMapToDegreeOneTerm
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainHighest_kRel_map
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainHighest_fdual_single
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainHighest
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)
namespace GlobalTheory.CompanionTheory.ChainHighest
theorem _root_.solution : FRel → GFacts → GamDom → KHWExists → HWMap → PRV := by
  intro hF hG hγ hK hM n ε lam V _ _ E v S hlam hE hEu hv hS hSt hvS
  obtain ⟨γ, hγ1, hγ2⟩ := hγ n ε lam hlam
  obtain ⟨U, _, _, _, EU, u, hU, hUu, hu0, hu⟩ := hK n ε γ hγ2
  obtain ⟨g, hg, hgs, hgc, hgd, hgl⟩ := hG n ε
  let T : Type := PiLp 2 (fun _ : Finset (NC ε) => U)
  let e : Ch ε U ≃ₗ[ℂ] T := (WithLp.linearEquiv 2 ℂ (Finset (NC ε) → U)).symm
  have he : ∀ (x : Ch ε U) A, (e x).ofLp A = x A := fun _ _ => rfl
  let ET : Fin n → Fin n → Module.End ℂ T := fun a b => e.conjRingEquiv.toRingHom (Fdual ε EU a b)
  have hET : ∀ a b x, ET a b (e x) = e (Fdual ε EU a b x) := by
    intro a b x
    rfl
  have hTrel : KRel ε ET := kRel_map ε _ _ (hF n ε U EU hU).2
  have hTu : KUnit ε ET := by
    intro a b hab x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hET, hET, PiLp.inner_apply, PiLp.inner_apply]
    simp only [he, Fdual, LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg, inner_sub_left,
      inner_sub_right, Finset.sum_sub_distrib, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    congr 1
    · exact Finset.sum_congr rfl fun A _ => hUu a b hab _ _
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      rw [hgs b a B A]
  have ht0 : e (Pi.single (A1 ε) u) ≠ 0 := by
    intro h
    have := he (Pi.single (A1 ε) u) (A1 ε)
    rw [h] at this
    apply hu0
    simpa using this.symm
  have ht : KHighest ε ET (lowK ε lam) (e (Pi.single (A1 ε) u)) := by
    constructor
    · intro a
      rw [hET, ← map_smul]
      congr 1
      funext B
      rw [fdual_single EU g (hg U), hu.1 a, hgd]
      by_cases h : B = A1 ε
      · subst h
        have h1 := hγ1 a
        simp only [gam, Pi.add_apply] at h1
        simp only [Pi.single_eq_same, if_true, Pi.smul_apply, ← sub_smul, ← h1]
        congr 1
        push_cast
        ring
      · simp [h]
    · intro a b hab hε
      rw [hET, map_eq_zero_iff _ e.injective]
      funext B
      rw [fdual_single EU g (hg U), hu.2 a b hab hε, hgl b a B hab]
      simp
  obtain ⟨φ, hφ1, hφ2⟩ := hM n ε T V ET E (lowK ε lam) _ v S hTrel hTu hE hEu ht0 ht hv hS hSt hvS
  let c : Ch ε V := fun A => if A.card = (A1 ε).card then φ (e (Pi.single A u)) else 0
  have key : ∀ a b, ε a = ε b → ∀ A, Fop ε E a b c A =
      if A.card = (A1 ε).card then φ (e (Pi.single A (EU a b u))) else 0 := by
    intro a b hab A
    unfold Fop
    rw [LinearMap.add_apply, Pi.add_apply, lift_apply, hg]
    by_cases hA : A.card = (A1 ε).card
    · have h1 : Fdual ε EU a b (Pi.single A u) =
          Pi.single A (EU a b u) - ∑ B, (g a b A B : ℂ) • (Pi.single B u : Ch ε U) := by
        funext B
        rw [fdual_single EU g (hg U), Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single B, hgs b a B A]
        · simp
        · intro C _ hC; simp [hC.symm]
        · simp
      have h2 : ∀ B, (g a b A B : ℂ) • c B = (g a b A B : ℂ) • φ (e (Pi.single B u)) := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_true]
      simp only [h2]
      simp only [c, hA, if_true]
      rw [← hφ2 a b hab, hET, h1]
      simp only [map_sub, map_sum, map_smul]
      abel
    · have h2 : ∀ B, (g a b A B : ℂ) • c B = 0 := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_false, smul_zero]
      simp only [h2]
      simp [c, hA]
  refine ⟨c, fun A hA => by simp [c, hA], ⟨fun a => ?_, fun a b hab hε => ?_⟩, by simp [c, hφ1]⟩
  · funext A
    rw [key a a rfl, hu.1 a, Pi.smul_apply, hγ1 a]
    by_cases hA : A.card = (A1 ε).card
    · simp only [c, hA, if_true]
      rw [Pi.single_smul, map_smul, map_smul]
    · simp [c, hA]
  · funext A
    rw [key a b hε, hu.2 a b hab hε]
    simp
end GlobalTheory.CompanionTheory.ChainHighest
