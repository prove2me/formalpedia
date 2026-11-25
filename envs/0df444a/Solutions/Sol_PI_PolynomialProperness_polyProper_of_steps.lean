-- Prove2me | solution 1 for PI.PolynomialProperness.polyProper_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:10.413829+00:00
-- url     : https://prove2.me/submissions/3c862571-c13a-42b8-b4c3-27c399c1aee4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul
import Theorems.Thm_PI_PolynomialProperness_bound_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper := by
  refine ⟨5, fun k r z z' γ hstd hpos hmono => ?_⟩
  obtain ⟨CA, hA1, hA2⟩ := hA k r z z' γ hmono
  obtain ⟨Cc, hCc⟩ := hC k r z z' γ hstd hpos
  obtain ⟨Cf, hCf⟩ := hF k r z
  obtain ⟨Cf', hCf'⟩ := hF k r z'
  have hγ : γ ∈ B.GV k r := hpos.1
  obtain ⟨hmul, hinv⟩ := hG k r
  refine ⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_, ?_⟩
  · intro σ hσ s' hs'
    obtain ⟨hσG, v, hv, hvL, hσf⟩ := hSg k r z z' γ hstd σ hσ
    obtain ⟨hs'G, u', hu, hsf⟩ := hS k r z' hstd.2.2 s' hs'
    have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf
    obtain ⟨hbv, hbu⟩ := hA1 v hv hvL u' hu _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu
  · intro s hs σ' hσ'
    obtain ⟨hsG, u, hu, hsf⟩ := hS k r z hstd.2.1 s hs
    obtain ⟨hσG, v', hv', hPv, hσf⟩ := hSg' k r z z' γ hstd σ' hσ'
    have hg : s⁻¹ * γ * σ' ∈ B.GV k r := hmul _ (hmul _ (hinv s hsG).2.1 _ hγ) _ hσG
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ s σ' u v' hsG hσG hsf hσf
    obtain ⟨hbu, hbv⟩ := hA2 u hu v' hv' hPv _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc s σ' u v' hsG hσG hu hv' hsf hσf hbu hbv
end PI.PolynomialProperness
