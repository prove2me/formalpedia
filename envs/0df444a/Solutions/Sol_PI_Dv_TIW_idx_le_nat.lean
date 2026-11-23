-- Prove2me | solution 1 for PI.Dv.TIW.idx_le_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:23.830854+00:00
-- url     : https://prove2.me/submissions/17b7c5f0-d13a-4c2d-a3b4-5393ee8570f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (n : ℕ) (hn : 0 < n)
    (hle : N ≤ M) (hsm : ∀ x ∈ M, ((n : ℕ) : 𝓞 K) • x ∈ N) :
    idxAt w M N ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((n : ℕ) : K) :=
  (hI K V w M N hM hN h1).2.2.2.2.2 n hn hle hsm
end PI.Dv.TIW
