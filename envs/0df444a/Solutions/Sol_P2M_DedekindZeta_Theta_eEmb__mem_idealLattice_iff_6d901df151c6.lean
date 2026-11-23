-- Prove2me | solution 1 for P2M_DedekindZeta_Theta_eEmb__mem_idealLattice_iff_6d901df151c6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:32.496028+00:00
-- url     : https://prove2.me/submissions/7d3e3d17-248f-4033-b49c-1115d8ef9328

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (η : mixedSpace K) :
    eEmbℝ K η ∈ idealLattice K I ↔
      ∃ b ∈ (I : Submodule (𝓞 K) K), mixedEmbedding K b = η := by
  rw [mem_idealLattice_iff]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  rw [← eEmbℝ_mixedEmbedding, (eEmbℝ K).injective.eq_iff]
end DedekindZeta.Theta
