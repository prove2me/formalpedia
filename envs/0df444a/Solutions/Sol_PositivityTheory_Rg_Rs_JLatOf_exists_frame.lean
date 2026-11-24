-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:25.205816+00:00
-- url     : https://prove2.me/submissions/7d6cc590-53c6-489d-8762-af4ad3d9449b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_Formalism_UG_P_GL_smul_standard_tuple
import Theorems.Thm_Formalism_UG_P_tjcosets_exists_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution [Finite k] (N j m : ℕ) (h : m + j = N) (u : Fin m → Fin N → k) (hu : LinearIndependent k u) :
    ∃ g : GL (Fin N) k, ∀ i : Fin m, (g : Matrix (Fin N) (Fin N) k) *ᵥ ej N j m h i = u i := by
  subst h
  have hm : m + j - j = m := by omega
  let w : Formalism.UG.P.TjcosetsFr (m + j - j) (m + j) k := fun i => u (Fin.cast hm i)
  have hw : LinearIndependent k w := hu.comp _ (Fin.cast_injective hm)
  obtain ⟨g, hg⟩ := Formalism.UG.P.tjcosets_exists_smul (m + j) j w hw
  refine ⟨g, fun i => ?_⟩
  have h1 := congrFun hg (Fin.cast hm.symm i)
  rw [Formalism.UG.P.GL_smul_standard_tuple] at h1
  have h2 : w (Fin.cast hm.symm i) = u i := by
    simp only [w]
    congr 1
  rw [← h2, ← h1]
  ext a
  (simp [ej, Matrix.mulVec, dotProduct, Pi.single_apply]) <;> rfl
end PositivityTheory.Rg.Rs.JLatOf
