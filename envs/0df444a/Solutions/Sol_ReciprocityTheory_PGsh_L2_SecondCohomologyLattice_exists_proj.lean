-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:30.091026+00:00
-- url     : https://prove2.me/submissions/0cf30703-5f89-45f9-a08f-ddf52490ace4

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_Lemmata_MiscLemmasL_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_exists_smul_mem_of_mem_span
import Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_free_of_finite_torsionFree
import Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_algebraMap_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
open Module
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
theorem _root_.solution [IsDomain R] [ValuationRing R] [IsFractionRing R C]
    {X : Type} [Fintype X] (A : Submodule R (X → C)) (hfg : A.FG)
    (hsp : Submodule.span C (A : Set (X → C)) = ⊤) (W : Submodule C (X → C)) :
    ∃ E : (X → C) →ₗ[C] (X → C), (∀ f ∈ A, E f ∈ A ∧ E f ∈ W) ∧ ∀ f ∈ W, E f = f := by
  classical
  let P : Submodule R A := (W.restrictScalars R).comap A.subtype
  have : Module.Finite R A := Module.Finite.iff_fg.2 hfg
  have : Module.Free R (A ⧸ P) := free_of_finite_torsionFree _ (by
    intro r x hr hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective P x
    rw [← map_smul, ← LinearMap.mem_ker, Submodule.ker_mkQ] at hx
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    have hx' : ((r • a : A) : X → C) ∈ W := hx
    show (a : X → C) ∈ W
    have : (a : X → C) = (algebraMap R C r)⁻¹ • ((r • a : A) : X → C) := by
      rw [Submodule.coe_smul, ← algebraMap_smul C r (a : X → C), smul_smul,
        inv_mul_cancel₀ (algebraMap_ne_zero hr), one_smul]
    rw [this]; exact W.smul_mem _ hx')
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id
    (Submodule.mkQ_surjective P)
  have hs' : ∀ y, P.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  let S : Submodule R (X → C) := LinearMap.range (A.subtype ∘ₗ s)
  let W' : Submodule C (X → C) := Submodule.span C (S : Set (X → C))
  have hdec : ∀ a : A, ((a - s (P.mkQ a) : A) : X → C) ∈ W := by
    intro a
    have h2 : P.mkQ (a - s (P.mkQ a)) = 0 := by rw [map_sub, hs', sub_self]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at h2
    exact h2
  have hSW' : ∀ a : A, ((s (P.mkQ a) : A) : X → C) ∈ W' :=
    fun a => Submodule.subset_span ⟨P.mkQ a, rfl⟩
  have hcompl : IsCompl W W' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxW hxW'
      obtain ⟨r, hr, hrx⟩ := exists_smul_mem_of_mem_span S hxW'
      obtain ⟨y, hy⟩ := hrx
      have hyW : ((s y : A) : X → C) ∈ W := by
        have : ((s y : A) : X → C) = r • x := hy
        rw [this, ← algebraMap_smul C r x]; exact W.smul_mem _ hxW
      have hy0 : y = 0 := by
        rw [← hs' y, ← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hyW
      have : r • x = 0 := by rw [← hy]; simp [hy0]
      rw [← algebraMap_smul C r x] at this
      exact (smul_eq_zero.1 this).resolve_left (algebraMap_ne_zero hr)
    · rw [codisjoint_iff, eq_top_iff, ← hsp, Submodule.span_le]
      intro f hf
      have : f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) + ((s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
        simp
      rw [this]
      exact Submodule.add_mem_sup (hdec _) (hSW' _)
  have hc : IsCompl (LinearMap.range W.subtype) W' := by rw [Submodule.range_subtype]; exact hcompl
  let E : (X → C) →ₗ[C] (X → C) :=
    W.subtype ∘ₗ LinearMap.linearProjOfIsCompl W' W.subtype W.injective_subtype hc
  have hEW : ∀ f ∈ W, E f = f := by
    intro f hf
    have : E (W.subtype ⟨f, hf⟩) = W.subtype ⟨f, hf⟩ := by
      simp only [E, LinearMap.comp_apply, LinearMap.linearProjOfIsCompl_apply_left]
    simpa using this
  have hEW' : ∀ f ∈ W', E f = 0 := by
    intro f hf
    simp only [E, LinearMap.comp_apply,
      LinearMap.linearProjOfIsCompl_apply_right' W' W.subtype W.injective_subtype hc f hf, map_zero]
  refine ⟨E, ?_, hEW⟩
  intro f hf
  have hsplit : f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) + ((s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
    simp
  have : E f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
    conv_lhs => rw [hsplit]
    rw [map_add, hEW _ (hdec _), hEW' _ (hSW' _), add_zero]
  rw [this]
  exact ⟨Subtype.prop _, hdec _⟩
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
