-- Prove2me | solution 1 for PI.EmbPermWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:38.218988+00:00
-- url     : https://prove2.me/submissions/a751ece0-1cd8-4306-a0d6-45fdc0d3f3ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_EmbPerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingPermutations_CjEq
import Theorems.Thm_PI_EmbPermWork_cj_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EmbPermWork
namespace PI.EmbPermWork
theorem _root_.solution : PI.EmbPerm := by
  intro E _ _ K φ₀ S _ emb hinj hagree hcard M ρ hK hM
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have _ : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  let f : S → (E →ₐ[K] ℂ) := fun s =>
    { (emb s) with commutes' := fun a => hagree s a }
  have hf : Function.Injective f := by
    intro s t h
    apply hinj
    ext x
    exact congrArg (fun g : E →ₐ[K] ℂ => g x) h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    rw [hcard, AlgHom.card]

  let g : S → (E →+* ℂ) := fun s =>
    (ρ : M →+* ℂ).comp ((emb s).codRestrict M (hM s))
  have hg : ∀ s x, g s x = PI.EmbPermDefs.cj M ρ (emb s x) := by
    intro s x
    rw [cj_eq M ρ _ (hM s x)]
    rfl
  have hgK : ∀ s (a : K), g s (a : E) = φ₀ (a : E) := by
    intro s a
    rw [hg, hagree s a]
    exact (hK a).2
  let G : S → (E →ₐ[K] ℂ) := fun s =>
    { (g s) with commutes' := fun a => hgK s a }
  have hex : ∀ s, ∃ t, f t = G s := fun s => hbij.2 (G s)
  choose p hp using hex
  have hpx : ∀ s x, emb (p s) x = PI.EmbPermDefs.cj M ρ (emb s x) := by
    intro s x
    rw [← hg]
    exact congrArg (fun h : E →ₐ[K] ℂ => h x) (hp s)
  have hpinj : Function.Injective p := by
    intro s t hst
    apply hinj
    ext x
    have h1 : g s x = g t x := by rw [hg, hg, ← hpx, ← hpx, hst]
    have h2 : ((emb s).codRestrict M (hM s)) x = ((emb t).codRestrict M (hM t)) x :=
      (ρ : M →+* ℂ).injective h1
    exact congrArg Subtype.val h2
  have hpbij : Function.Bijective p := Finite.injective_iff_bijective.mp hpinj
  exact ⟨Equiv.ofBijective p hpbij, fun s x => (hpx s x).symm⟩
end PI.EmbPermWork
