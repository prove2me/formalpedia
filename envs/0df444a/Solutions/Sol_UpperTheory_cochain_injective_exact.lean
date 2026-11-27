-- Prove2me | solution 1 for UpperTheory.cochain_injective_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:30.138446+00:00
-- url     : https://prove2.me/submissions/c5936985-6a7e-4d04-81ac-92112e7003c1

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CochainInjectiveExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory in
private lemma exists_lift {k : Type} [CommRing k] {K L M : CochainComplex (ModuleCat.{0} k) ℕ}
    (u : K ⟶ M) (ι : L ⟶ M) (hι : ∀ m : ℕ, Function.Injective (ι.f m).hom)
    (h : ∀ (m : ℕ) (x : K.X m), ∃ y, (ι.f m).hom y = (u.f m).hom x) :
    ∃ φ : K ⟶ L, ∀ (m : ℕ) (x : K.X m), (ι.f m).hom ((φ.f m).hom x) = (u.f m).hom x := by
  let p : ∀ m : ℕ, K.X m ⟶ L.X m := fun m =>
    ModuleCat.ofHom ((u.f m).hom.codRestrictOfInjective (ι.f m).hom (hι m) (h m))
  have hp : ∀ m : ℕ, p m ≫ ι.f m = u.f m := fun m =>
    ModuleCat.hom_ext (LinearMap.codRestrictOfInjective_comp _ _ _ _)
  refine ⟨{ f := p, comm' := fun i j _ => ?_ }, fun m x => congr($(hp m).hom x)⟩
  haveI : Mono (ι.f j) := (ModuleCat.mono_iff_injective _).2 (hι j)
  rw [← cancel_mono (ι.f j), Category.assoc, Category.assoc, hp, ← ι.comm, ← Category.assoc, hp,
    u.comm]
open CategoryTheory in
private lemma exists_map {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    {A B : Rep.{0, 0, 0} k G} (f : A ⟶ B) {KA KB : CochainComplex (ModuleCat.{0} k) ℕ}
    (ιA : KA ⟶ groupCohomology.inhomogeneousCochains A)
    (ιB : KB ⟶ groupCohomology.inhomogeneousCochains B)
    (iB : ∀ m : ℕ, Function.Injective (ιB.f m).hom)
    (hA : ∀ (m : ℕ) (x : (Fin m → G) → A.V), (∃ y, (ιA.f m).hom y = x) ↔ IsLocallyConstant x)
    (hB : ∀ (m : ℕ) (x : (Fin m → G) → B.V), (∃ y, (ιB.f m).hom y = x) ↔ IsLocallyConstant x) :
    ∃ φ : KA ⟶ KB, ∀ (m : ℕ) (x : KA.X m) (t : Fin m → G),
      ((ιB.f m).hom ((φ.f m).hom x) : (Fin m → G) → B.V) t =
        f.hom (((ιA.f m).hom x : (Fin m → G) → A.V) t) := by
  obtain ⟨φ, hφ⟩ := exists_lift (ιA ≫ groupCohomology.cochainsMap (MonoidHom.id G) f) ιB iB
    fun m x => (hB m _).2 (((hA m _).1 ⟨x, rfl⟩).comp f.hom)
  exact ⟨φ, fun m x t => congr_fun (hφ m x) t⟩
end

set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] (A B C : Rep.{0, 0, 0} k G)
        (f : A ⟶ B) (g : B ⟶ C) (KA KB KC : CochainComplex (ModuleCat.{0} k) ℕ)
        (ιA : KA ⟶ groupCohomology.inhomogeneousCochains A)
        (ιB : KB ⟶ groupCohomology.inhomogeneousCochains B)
        (ιC : KC ⟶ groupCohomology.inhomogeneousCochains C),
        Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
        (∀ m : ℕ, Function.Injective (ιA.f m).hom) → (∀ m : ℕ, Function.Injective (ιB.f m).hom) →
        (∀ m : ℕ, Function.Injective (ιC.f m).hom) →
        (∀ (m : ℕ) (x : (Fin m → G) → A.V), (∃ y, (ιA.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → B.V), (∃ y, (ιB.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → C.V), (∃ y, (ιC.f m).hom y = x) ↔ IsLocallyConstant x) →
        ∃ (φ : KA ⟶ KB) (ψ : KB ⟶ KC) (w : CategoryTheory.CategoryStruct.comp φ ψ = 0),
          (CategoryTheory.ShortComplex.mk φ ψ w).ShortExact := by
  intro k G _ _ _ A B C f g KA KB KC ιA ιB ιC hf hfg hg iA iB iC hA hB hC
  obtain ⟨φ, hφ⟩ := exists_map f ιA ιB iB hA hB
  obtain ⟨ψ, hψ⟩ := exists_map g ιB ιC iC hB hC
  have w : CategoryTheory.CategoryStruct.comp φ ψ = 0 := by
    ext m : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => iC m ?_)
    change (ιC.f m).hom ((ψ.f m).hom ((φ.f m).hom x)) = (ιC.f m).hom 0
    rw [map_zero]
    funext t
    rw [hψ, hφ]
    exact hfg.apply_apply_eq_zero _
  refine ⟨φ, ψ, w, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun m => ?_⟩
  have hm : CategoryTheory.Mono (φ.f m) := by
    refine (ModuleCat.mono_iff_injective _).2 fun a b hab => iA m (funext fun t => hf ?_)
    have hab' : (φ.f m).hom a = (φ.f m).hom b := hab
    rw [← hφ, ← hφ, hab']
  have he : CategoryTheory.Epi (ψ.f m) := by
    refine (ModuleCat.epi_iff_surjective _).2 fun c => ?_
    obtain ⟨b, hb⟩ := (hB m _).2 (((hC m _).1 ⟨c, rfl⟩).comp (Function.surjInv hg))
    refine ⟨b, iC m (funext fun t => ?_)⟩
    refine (hψ m b t).trans ?_
    rw [hb]
    exact Function.surjInv_eq hg _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  refine (CategoryTheory.ShortComplex.moduleCat_exact_iff _).2 fun (b : KB.X m) hb => ?_
  have hb0 : (ψ.f m).hom b = 0 := hb
  have hb' : ∀ t : Fin m → G, ∃ a, f.hom a = ((ιB.f m).hom b : (Fin m → G) → B.V) t := fun t => by
    refine (hfg _).1 ?_
    rw [← hψ, hb0, map_zero]
    rfl
  choose a ha using hb'
  have hla : IsLocallyConstant a := by
    refine IsLocallyConstant.desc a f.hom ?_ hf
    have e : f.hom ∘ a = (ιB.f m).hom b := funext ha
    rw [e]
    exact (hB m _).1 ⟨b, rfl⟩
  obtain ⟨y, hy⟩ := (hA m a).2 hla
  refine ⟨y, iB m (funext fun t => ?_)⟩
  refine (hφ m y t).trans ?_
  rw [hy]
  exact ha t
end UpperTheory
