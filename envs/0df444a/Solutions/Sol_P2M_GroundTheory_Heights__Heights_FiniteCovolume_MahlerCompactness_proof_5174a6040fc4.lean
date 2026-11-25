-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_MahlerCompactness_proof_5174a6040fc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:13:50.843804+00:00
-- url     : https://prove2.me/submissions/962c563d-bf19-44b7-9d2f-5924c180ddb7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StGramDetermines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMahlerCompactness
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_archEmbed_mul_8e0f0497cff9
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace MahlerCompactness
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (hB : BoundedGenerators.Statement h v) (hCS : LenCauchySchwarz.Statement h v)
    (hG : GramDetermines.Statement h) (hK : BoundedInverseCompact.Statement h v) :
    MahlerCompactness.Statement h v := by
  intro M D t ht
  obtain ⟨n, C, hC⟩ := hB M D t ht

  let P : Set (AddSubgroup W × (Fin n → W)) := {p | IsDIntegral h D p.1 ∧
    AddSubgroup.closure (Set.range p.2) = p.1 ∧
      ∃ g : archUnitary h v, ∀ a, M.len (invApply g (vecAt v (p.2 a))) ≤ C}
  let gr : (Fin n → W) → Matrix (Fin n) (Fin n) E := fun e a b => h.toSesq (e a) (e b)
  let T : Set (Matrix (Fin n) (Fin n) E) := (fun p => gr p.2) '' P
  have hT : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C * C})
      fun _ => Set.Finite.pi fun _ => Embeddings.finite_of_norm_le E ℂ (C * C)).subset ?_
    rintro _ ⟨p, ⟨hD, hcl, g, hg⟩, rfl⟩
    intro a _ b _
    have hmem : ∀ c, p.2 c ∈ p.1 := fun c => hcl ▸ AddSubgroup.subset_closure ⟨c, rfl⟩
    refine Set.mem_ofPred.2 ⟨(mem_integralClosure_iff ℤ E).1 (hD.integral _ (hmem a) _ (hmem b)), fun φ => ?_⟩
    have h1 := hCS M g (p.2 a) (p.2 b) (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1.trans (mul_le_mul (hg a) (hg b) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hg a)))
  have hrep : ∀ H ∈ T, ∃ p ∈ P, gr p.2 = H := fun H ⟨p, hp, hH⟩ => ⟨p, hp, hH⟩
  choose! rep hrepP hrepG using hrep
  let Kset : (Fin n → W) → Set (archUnitary h v) :=
    fun e => {g | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  refine ⟨(fun H => (rep H).1) '' T, hT.image _, ⋃ H ∈ T, Kset (rep H).2,
    hT.isCompact_biUnion fun H hH => hK M n (rep H).2 ?_ C, ?_⟩
  · obtain ⟨hD, hcl, -⟩ := hrepP H hH
    have hsp := hD.isLattice.span_eq_top
    rw [← hcl] at hsp
    rw [eq_top_iff, ← hsp]
    refine Submodule.span_le.2 fun x hx => ?_
    exact (AddSubgroup.closure_le (Submodule.span E (Set.range (rep H).2)).toAddSubgroup).2
      Submodule.subset_span hx
  · intro La g hLa hmin
    obtain ⟨e, he, heC⟩ := hC La g hLa hmin
    have hH : gr e ∈ T := ⟨(La, e), ⟨hLa, he, g, heC⟩, rfl⟩
    obtain ⟨hD', hcl', -⟩ := hrepP _ hH
    have hgr := hrepG _ hH
    obtain ⟨γ, hγ⟩ := hG n e (rep (gr e)).2 (he ▸ hLa.isLattice) (hcl' ▸ hD'.isLattice)
      fun a b => (congrFun (congrFun hgr a) b).symm
    refine ⟨γ, ⟨gr e, hH, ?_⟩, Set.mem_biUnion hH fun a => ?_⟩
    · show (rep (gr e)).1 = γ • La
      rw [← hcl', ← he, Subgroup.smul_def, AddSubgroup.pointwise_smul_def]
      erw [AddMonoidHom.map_closure]
      rw [← Set.range_comp]
      exact congrArg (fun s => AddSubgroup.closure (Set.range s)) (funext fun a => (hγ a).symm)
    · show M.len (invApply (archEmbed h v γ * g) (vecAt v ((rep (gr e)).2 a))) ≤ C
      rw [← hγ a, invApply_archEmbed_mul]
      exact heC a
end MahlerCompactness
end GroundTheory.Heights₂.Heights.FiniteCovolume
