-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__four_wf0_f09ec81eba5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:07:06.984748+00:00
-- url     : https://prove2.me/submissions/8c93133c-149c-4b1d-a530-e422f1b1e0ad

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_QuadraticExampleRankThreePackage
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__line_indep_7b4cd6eaa39e
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_isCMSub_cmMax
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_isHermAt_of_ratHerm
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__one_posDef_f9e7b90361ac
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__one_quot_de26657ef017


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.L2.Indef.Examples₂.four
open scoped Classical
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (b : Fin 2 → Fin 2 → K) (kap : ℝ) (l : Fin 2 → Fin 2 → ℝ)
namespace Formalism.L2.Indef.Examples₂.four
theorem _root_.solution (hv0 : IsConjAt v0) : (df0 K v0).WF where
  cm := ConjugateWeightGram.isCMSub_cmMax
  conj := hv0
  HV_rat := fun _ => (std_ratHerm K (cmMax K) 2).1
  HV_pos := fun _ v => one_posDef K 2 v
  Mt_lat := fun _ => sl_lattice K 2
  Pq_surj := fun _ x => ⟨x, by simp⟩
  XQ_quot := fun _ => one_quot K 2
  Lam_lat := fun _ => by
    show Submodule.IsLattice K (matLat (1 : Matrix (Fin 2) (Fin 2) K) (sl K 2))
    rw [matLat_one]; exact sl_lattice K 2
  Qp_indep := line_indep 2
  Qp_top := line_top 2
  XT_herm := fun _ _ => ConjugateWeightGram.isHermAt_of_ratHerm (std_ratHerm K (cmMax K) 2) v0
  Tl_lat := fun _ _ => sl_lattice K 2
  Zp_indep := fun _ => line_indep 2
end Formalism.L2.Indef.Examples₂.four
