-- Prove2me | solution 1 for P2M_DedekindZeta_Theta_inner_eEmb__eq_traceForm_conjMixed_b285258bd3d8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:11:05.14602+00:00
-- url     : https://prove2.me/submissions/546768cd-b1f8-4c15-96c4-a3b449827ceb

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_P2M_DedekindZeta_Theta_inner_eEmb__991a1bff15f2

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (ξ : mixedSpace K) (a : K) :
    (inner ℝ (eEmbℝ K ξ) (eEmb K a) : ℝ) = traceForm K (conjMixed K ξ) a := by
  rw [inner_eEmbℝ, traceForm]
  simp only [conjMixed_fst, conjMixed_snd]
end DedekindZeta.Theta
