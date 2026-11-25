-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.swap4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:45.758726+00:00
-- url     : https://prove2.me/submissions/b5c0c12c-c755-425a-8cd6-e8f43c05204b

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution {α : Type*} [AddCommMonoid α] (s t : Finset ℕ)
    (f : (n : ℕ) → (Fin n → Fin d) → (n' : ℕ) → (Fin n' → Fin d) → α) :
    ∑ n ∈ s, ∑ w : Fin n → Fin d, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, f n w n' w' =
      ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ n ∈ s, ∑ w : Fin n → Fin d, f n w n' w' := by
  calc ∑ n ∈ s, ∑ w : Fin n → Fin d, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, f n w n' w'
      = ∑ n ∈ s, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ w : Fin n → Fin d, f n w n' w' := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun n' _ => Finset.sum_comm)
    _ = ∑ n' ∈ t, ∑ n ∈ s, ∑ w' : Fin n' → Fin d, ∑ w : Fin n → Fin d, f n w n' w' := Finset.sum_comm
    _ = ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ n ∈ s, ∑ w : Fin n → Fin d, f n w n' w' :=
        Finset.sum_congr rfl (fun n' _ => Finset.sum_comm)
end ZetaZeros.D.EllReg.WF
