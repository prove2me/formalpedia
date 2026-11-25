-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_le_comap_5dabf6160a8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:04.740061+00:00
-- url     : https://prove2.me/submissions/30f93803-19c0-4945-a900-8e29907816ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_eq_217fcd3dcb1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_e65327d6784a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_baseToBn_toBase_2f2e4d6deddf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)} {j : Fin n}
  {v : HeightOneSpectrum (𝓞 K)} {W : Ideal (MvPolynomial (Fin n) (𝓞 K))}
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    Q e I j W ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)).comap (Φ hj) := by
  rw [Q_eq, Ideal.map_le_iff_le_comap, Ideal.comap_comap, Wb, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro w hw
  rw [Ideal.mem_comap]
  change Φ hj (C (toBase I j w)) ∈ _
  rw [Φ_C, baseToBn_toBase, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔫) 𝔫, ← h𝔫]
  exact Ideal.mem_map_of_mem _ hw
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
