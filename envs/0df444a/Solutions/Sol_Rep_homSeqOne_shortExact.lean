-- Prove2me | solution 1 for Rep.homSeqOne_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4ffd7d56-d9df-50ed-bd61-54ba96265748

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_homSeqOne_shortExact

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open CategoryTheory

namespace Rep p2m_export "Rep" "free of epi_iff_surjective mono_iff_injective id_apply freeCover relationModule relationModuleInt relationModuleInt.ι preHom preHom_hom_apply preι homSeq₁" end Rep
p2m_open_scoped "Rep" in

theorem Rep.shortExact_of_hom₃ {k G : Type} [CommRing k] [Group G] {S : ShortComplex (Rep k G)}
    (hf : Function.Injective S.f.hom) (hg : Function.Surjective S.g.hom)
    (hfg : ∀ y : S.X₂, S.g.hom y = 0 ↔ y ∈ Set.range S.f.hom) : S.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  exact hfg y

p2m_open_scoped "Rep" in

theorem Rep.preHom_hom_apply_apply {k G : Type} [CommRing k] [Group G] {A A' : Rep k G} (f : A ⟶ A') (E : Rep k G)
    (x : (ihom A').obj E) (a : A) :
    (show A →ₗ[k] E from (Rep.preHom f E).hom x) a = (show A' →ₗ[k] E from x) (f.hom a) := rfl

p2m_open_scoped "Rep" in

theorem Rep.exists_preHom_freeCover_eq {k G : Type} [CommRing k] [Group G] (B E : Rep k G)
    (y : (ihom (Rep.free k G B)).obj E) (hy : ∀ r : Rep.relationModule B, (show Rep.free k G B →ₗ[k] E from y) (r : Rep.free k G B) = 0) :
    ∃ x : (ihom B).obj E, (Rep.preHom (Rep.freeCover B) E).hom x = y := by
  let ε : Rep.free k G B →ₗ[k] B := (Rep.freeCover B).hom.toLinearMap
  let y' : Rep.free k G B →ₗ[k] E := (show Rep.free k G B →ₗ[k] E from y)
  have hsurj : Function.Surjective ε := by
    intro b
    refine ⟨Finsupp.single b (MonoidAlgebra.single 1 1), ?_⟩
    simp [ε, Rep.freeCover]
  have hker : ∀ f : Rep.free k G B, ε f = 0 → y' f = 0 := fun f hf => hy ⟨f, hf⟩
  choose s hs using hsurj
  have key : ∀ f f' : Rep.free k G B, ε f = ε f' → y' f = y' f' := fun f f' h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hker _ (by rw [map_sub, h, sub_self])
  let x : B →ₗ[k] E :=
    { toFun := fun b => y' (s b)
      map_add' := fun b b' => by
        rw [← map_add]
        exact key _ _ (by rw [map_add, hs, hs, hs])
      map_smul' := fun c b => by
        rw [RingHom.id_apply, ← map_smul]
        exact key _ _ (by rw [map_smul, hs, hs]) }
  refine ⟨(show (ihom B).obj E from x), ?_⟩
  rw [Rep.preHom_hom_apply]
  apply LinearMap.ext
  intro f
  exact key _ _ (hs (ε f))

p2m_open_scoped "Rep" in

theorem Rep.preHom_freeCover_injective {k G : Type} [CommRing k] [Group G] (B E : Rep k G) :
    Function.Injective (Rep.preHom (Rep.freeCover B) E).hom := by
  intro x x' h
  rw [Rep.preHom_hom_apply, Rep.preHom_hom_apply] at h
  have hsurj : Function.Surjective (Rep.freeCover B).hom.toLinearMap := by
    intro b
    refine ⟨Finsupp.single b (MonoidAlgebra.single 1 1), ?_⟩
    simp [Rep.freeCover]
  apply LinearMap.ext
  intro b
  obtain ⟨f, rfl⟩ := hsurj b
  exact LinearMap.congr_fun h f

theorem solution {G : Type} [Group G] (B E : Rep ℤ G) : (Rep.homSeq₁ B E).ShortExact := by
  refine Rep.shortExact_of_hom₃ (Rep.preHom_freeCover_injective B E) ?_ ?_
  · intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  · intro y
    constructor
    · intro hy0
      have hval : (Rep.preι B E).hom y = 0 := congrArg Subtype.val hy0
      obtain ⟨x, hx⟩ := Rep.exists_preHom_freeCover_eq B E y (fun r => by
        erw [← Rep.preHom_hom_apply_apply (Rep.relationModuleInt.ι B) E y (show Rep.relationModuleInt B from r), hval]
        rfl)
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      exact congrArg (fun φ : (ihom B).obj E ⟶ _ => φ.hom x) (Rep.homSeq₁ B E).zero

end S_Rep_homSeqOne_shortExact
end P2MW
export P2MW.S_Rep_homSeqOne_shortExact (solution)
