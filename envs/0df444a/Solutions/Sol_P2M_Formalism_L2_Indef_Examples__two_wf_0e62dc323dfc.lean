-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__two_wf_0e62dc323dfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:46.187933+00:00
-- url     : https://prove2.me/submissions/4d4fd093-90dc-4b69-85df-5d5730362aa1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__one_posDef_f9e7b90361ac
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__one_quot_de26657ef017
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__indep_unit_5db93c2a0b31
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_isCMSub_cmMax
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_isHermAt_of_ratHerm


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
open Formalism.L2.Indef.Examples₂.two
open scoped Classical
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (a : K) (kap l : InfinitePlace K → ℝ)
namespace Formalism.L2.Indef.Examples₂.two
theorem _root_.solution (hv0 : IsConjAt v0) : (df K v0).WF where
  cm := ConjugateWeightGram.isCMSub_cmMax
  conj := hv0
  HV_rat := fun _ => (std_ratHerm K (cmMax K) 1).1
  HV_pos := fun _ v => one_posDef K 1 v
  Mt_lat := fun _ => sl_lattice K 1
  Pq_surj := fun _ x => ⟨x, by simp⟩
  XQ_quot := fun _ => one_quot K 1
  Lam_lat := fun _ => by
    show Submodule.IsLattice K (matLat (1 : Matrix (Fin 1) (Fin 1) K) (sl K 1))
    rw [matLat_one]; exact sl_lattice K 1
  Qp_indep := indep_unit K _
  Qp_top := by simp
  XT_herm := fun _ _ => ConjugateWeightGram.isHermAt_of_ratHerm (std_ratHerm K (cmMax K) 1) v0
  Tl_lat := fun _ _ => sl_lattice K 1
  Zp_indep := fun _ => indep_unit K _
end Formalism.L2.Indef.Examples₂.two
