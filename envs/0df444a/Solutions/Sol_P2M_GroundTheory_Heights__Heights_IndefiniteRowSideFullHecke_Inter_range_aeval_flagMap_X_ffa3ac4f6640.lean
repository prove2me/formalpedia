-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_range_aeval_flagMap_X_ffa3ac4f6640
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:19.426361+00:00
-- url     : https://prove2.me/submissions/a091d704-a4ea-4c81-a43c-30fd24e0fa49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTrdegAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagConeTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range =
      Algebra.adjoin ℤ
        (Set.range (fun d : MRing ι ⧸ P => algebraMap (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))
            (algebraMap (MRing ι ⧸ P) (FnField P) d)) ∪
          Set.range fun q : Σ j, PluckerBlocks N1 n j => flagMinor (genMat (FnField P) n * B.map C) q.1 q.2) := by
  rw [← Algebra.adjoin_range_eq_range_aeval]
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k | j, i⟩, rfl⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨Ideal.Quotient.mk P (X ⟨k, i⟩), by simp [flagMap, genPt, algebraMap_eq]⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨⟨j, i⟩, by simp [flagMap]⟩)
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨d, rfl⟩ | ⟨⟨j, S⟩, rfl⟩)
    · obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
      have e := @aeval_comp_X _ _ _ _ _ inferInstance (Ideal.Quotient.mk P)
        ((algebraMap (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))).comp
          (algebraMap (MRing ι ⧸ P) (FnField P))) f
      have hm : aeval (fun p => flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p))) f ∈
          Algebra.adjoin ℤ (Set.range fun p => flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p))) := by
        rw [Algebra.adjoin_range_eq_range_aeval]
        exact ⟨f, rfl⟩
      simp_rw [flagMap_X_inl] at hm
      refine Algebra.adjoin_mono ?_ (e ▸ hm)
      · rintro _ ⟨p, rfl⟩
        exact ⟨_, flagMap_X_inl P B p⟩
    · exact Algebra.subset_adjoin ⟨⟨Sum.inr j, S⟩, by simp [flagMap]⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
