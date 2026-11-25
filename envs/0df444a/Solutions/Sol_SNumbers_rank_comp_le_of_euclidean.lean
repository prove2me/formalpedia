-- Prove2me | solution 1 for SNumbers.rank_comp_le_of_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:00:44.027688+00:00
-- url     : https://prove2.me/submissions/43996074-1cde-43f8-a5bb-fd23ae4cf165

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference

set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {k : ℕ} (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Y)
    (G : X →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    (F.comp G).rank ≤ (k : Cardinal) := by
  have hdom : Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = (k : Cardinal) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  calc (F.comp G).rank
      ≤ F.rank := LinearMap.rank_comp_le_left _ _
    _ ≤ Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin k)) := LinearMap.rank_le_domain _
    _ = (k : Cardinal) := hdom
end SNumbers
