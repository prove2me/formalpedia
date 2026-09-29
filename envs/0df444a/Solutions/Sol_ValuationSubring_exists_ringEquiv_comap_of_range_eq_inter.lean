-- Prove2me | solution 1 for ValuationSubring.exists_ringEquiv_comap_of_range_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1099344c-4008-592f-8e6e-c0e9245a6046

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter

set_option autoImplicit false

theorem solution
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (k₀ : IntermediateField F L) (A : ValuationSubring L)
    (A₀ : Type*) [CommRing A₀] (ι : A₀ →+* ↥A) (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : L)) = (A : Set L) ∩ (k₀ : Set L)) :
    ∃ e : A₀ ≃+* ↥(A.comap (algebraMap ↥k₀ L)),
      ∀ a : A₀, algebraMap ↥k₀ L ((e a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) = ((ι a : ↥A) : L) := by
  classical
  have hk : ∀ a : A₀, ((ι a : ↥A) : L) ∈ (k₀ : Set L) := fun a =>
    (hιK₀ ▸ (Set.mem_range_self a : ((ι a : ↥A) : L) ∈ Set.range (fun a : A₀ => ((ι a : ↥A) : L)))).2
  have hA : ∀ a : A₀, ((ι a : ↥A) : L) ∈ A := fun a => (ι a).2
  let f : A₀ →+* ↥(A.comap (algebraMap ↥k₀ L)) :=
    { toFun := fun a => ⟨⟨((ι a : ↥A) : L), hk a⟩, show algebraMap ↥k₀ L ⟨((ι a : ↥A) : L), hk a⟩ ∈ A from hA a⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp }
  have hf : ∀ a : A₀, (((f a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) : L) = ((ι a : ↥A) : L) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro a b h
    apply hι
    apply Subtype.ext
    have h' : (((f a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) : L) = (((f b : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) : L) :=
      congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ L)) => ((z : ↥k₀) : L)) h
    rwa [hf, hf] at h'
  have hsurj : Function.Surjective f := by
    intro x
    have hx : ((x : ↥k₀) : L) ∈ (A : Set L) ∩ (k₀ : Set L) := ⟨x.2, (x : ↥k₀).2⟩
    rw [← hιK₀] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    exact ha
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a => hf a⟩

end S_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter
end P2MW
export P2MW.S_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter (solution)
