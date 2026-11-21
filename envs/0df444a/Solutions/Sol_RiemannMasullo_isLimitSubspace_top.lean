-- Prove2me | solution 1 for RiemannMasullo.isLimitSubspace_top
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:40:53.906722+00:00
-- url     : https://prove2.me/submissions/3c8ff180-fe7e-4725-8bce-7aaf3df2907d

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L382-L416
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

theorem solution [T2Space E] (hX : ∀ k, IsFrechetTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i) :
    IsLimitSubspace i ⊤ := by
  refine ⟨by simpa only [Submodule.top_coe] using isClosed_univ, ?_⟩
  let F : Submodule ℂ E := ⊤
  let inclusion (k : ℕ) : F.comap (i k).toLinearMap →ₗ[ℂ] F :=
    (i k).toLinearMap.restrict (fun _ hx ↦ hx)
  let p : SeminormFamily ℂ E {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} :=
    Subtype.val
  let q : SeminormFamily ℂ F {q : Seminorm ℂ F // ∀ k, Continuous (q ∘ inclusion k)} :=
    Subtype.val
  have hp : WithSeminorms p := ⟨h.topology_eq⟩
  have hsub : WithSeminorms (p.comp F.subtype) := F.subtype.withSeminorms_induced hp
  -- Each generating seminorm in either family is a member of the other family.
  have hq : WithSeminorms q := by
    apply hsub.congr
    · intro s
      let lift : E →ₗ[ℂ] F := LinearMap.codRestrict F LinearMap.id (fun _ ↦ Submodule.mem_top)
      have hs : ∀ k, Continuous (s.val.comp lift ∘ i k) := by
        intro k
        have hlift : Continuous (fun x : X k ↦
            (⟨x, Submodule.mem_top⟩ : F.comap (i k).toLinearMap)) :=
          continuous_id.subtype_mk _
        exact (s.property k).comp hlift
      refine ⟨{⟨s.val.comp lift, hs⟩}, 1, ?_⟩
      rw [Finset.sup_singleton, one_smul]
      exact le_rfl
    · intro a
      have ha : ∀ k, Continuous ((p.comp F.subtype) a ∘ inclusion k) := by
        intro k
        exact (a.property k).comp continuous_subtype_val
      refine ⟨{⟨(p.comp F.subtype) a, ha⟩}, 1, ?_⟩
      rw [Finset.sup_singleton, one_smul]
      exact le_rfl
  exact hq.topology_eq_withSeminorms
