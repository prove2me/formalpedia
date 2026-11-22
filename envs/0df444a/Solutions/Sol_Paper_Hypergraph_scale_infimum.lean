-- Prove2me | solution 1 for Paper.Hypergraph.scale_infimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:29.428464+00:00
-- url     : https://prove2.me/submissions/67ed35db-137a-4637-9950-d9e24e2cecb6

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_width_scale_mono

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {A : Set ℝ} (hne : A.Nonempty) (hA : ∀ r ∈ A, 0 ≤ r)
    {c : ℝ} (hc : 0 ≤ c) :
    c * (sInf A + 1) * Real.log (2 + sInf A) =
      sInf ((fun r => c * (r + 1) * Real.log (2 + r)) '' A) := by
  have hinf : 0 ≤ sInf A := le_csInf hne hA
  have hlog : ContinuousAt (fun r : ℝ => Real.log (2 + r)) (sInf A) :=
    (continuousAt_const.add continuousAt_id).log (by change 2 + sInf A ≠ 0; linarith)
  have hcont : ContinuousAt (fun r : ℝ => c * (r + 1) * Real.log (2 + r)) (sInf A) :=
    (continuousAt_const.mul (continuousAt_id.add continuousAt_const)).mul hlog
  apply MonotoneOn.map_csInf_of_continuousWithinAt hcont.continuousWithinAt ?_ hne ⟨0, hA⟩
  intro a ha b hb hab
  convert mul_le_mul_of_nonneg_left (width_scale_mono (hA a ha) hab) hc using 1 <;> ring
end Paper.Hypergraph
