-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GreenFromLelong_proof_0fe43a25b4c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:34.778504+00:00
-- url     : https://prove2.me/submissions/fe924fc1-79dd-4bdd-8697-c3261645653c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonotoneDoubleLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormSectionAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGreenFromLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivCyclePrime_proof_a79e8cf92f7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProperSymm_proof_b0183563c887
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_iterLim_eq_of_monotone_e11b6f1f0d13


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace GreenFromLelong
theorem _root_.solution (hS : FormIntSymm.Statement) (hP : FormIntPos.Statement)
    (hL : FormIntLelong.Statement) (hD : RegConeLimit.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) : GreenFromLelong.Statement := by
  intro _ _ _ _ _ _ n e h W u u' hW hg hu hu' hadm
  obtain ⟨g, hgc⟩ := hg

  have comps : ∀ v v' : Fin n → ℂ, linForm v ∉ W →
      (∀ W' ∈ (divCycle W v).support, linForm v' ∉ W') →
      Tendsto (fun δ => cycleIntegral h (divCycle W v) e (fsLogReg h v' δ)) (𝓝[>] 0)
        (𝓝 (cycleIntegral h (divCycle W v) e (fsLog h v'))) := by
    intro v v' hv hv'
    obtain ⟨c, -, gW, hgW, -⟩ := hCh ℂ n (e + 1) W g v hW hgc hv
    unfold cycleIntegral
    refine tendsto_finsetSum _ fun W' hW' => ?_
    exact (hD n e h W' v' (DivCyclePrime.proof n W v hW W' hW') ⟨gW W', hgW W' hW'⟩
      (hv' W' hW')).const_mul _
  have hadm' : ∀ W' ∈ (divCycle W u').support, linForm u ∉ W' :=
    ProperSymm.proof n W u u' hW hu hu' hadm
  have hg2 : ∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g := ⟨g, hgc⟩
  have hg1 : ∃ g : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ, IsChowForm W (e + 1 + 1) g := ⟨g, hgc⟩
  refine (iterLim_eq_of_monotone
    (T := fun ε δ => formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) +
      coneIntegral h W (e + 1) (fsLogReg h u δ) + coneIntegral h W (e + 1) (fsLogReg h u' ε))
    (A := fun δ => cycleIntegral h (divCycle W u') e (fsLogReg h u δ) +
      coneIntegral h W (e + 1) (fsLog h u'))
    (B := fun ε => cycleIntegral h (divCycle W u) e (fsLogReg h u' ε) +
      coneIntegral h W (e + 1) (fsLog h u)) ?_ ?_ ?_ ?_ ?_ ?_).symm
  ·
    intro δ hδ ε hε ε' hεε'
    have h1 := hP n e h W u' u δ ε ε' hW hg2 hδ hε hεε'
    rw [← hS n e h W u u' ε δ hW hg2 hε hδ, ← hS n e h W u u' ε' δ hW hg2 (hε.trans_le hεε') hδ] at h1
    linarith
  · intro ε hε δ hδ δ' hδδ'
    have h1 := hP n e h W u u' ε δ δ' hW hg2 hε hδ hδδ'
    linarith
  · intro δ hδ
    have := ((hL n e h W u u' δ hW hg2 hu' hδ).add_const
      (coneIntegral h W (e + 1) (fsLogReg h u δ))).add (hD n (e + 1) h W u' hW hg1 hu')
    convert this using 2
    ring
  · intro ε hε
    have := ((hL n e h W u' u ε hW hg2 hu hε).add (hD n (e + 1) h W u hW hg1 hu)).add_const
      (coneIntegral h W (e + 1) (fsLogReg h u' ε))
    refine Tendsto.congr' ?_ (by convert this using 2; ring)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [hS n e h W u u' ε δ hW hg2 hε hδ]
  · exact (comps u' u hu' hadm').add_const _
  · exact (comps u u' hu hadm).add_const _
end GreenFromLelong
end GroundTheory.Heights₂.Heights
