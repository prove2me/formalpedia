-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_C_mul_X__435eef58e544
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:22.003495+00:00
-- url     : https://prove2.me/submissions/542c62f2-c3b3-4281-be49-1f5352389983

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_eq_eval__d8b4e12d492f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_aeval_C_mul_X_e703e1c7feb0


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointNagata
variable {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointNagata
theorem _root_.solution {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (Polynomial S)] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : IsMultiHomog f (fun _ => d)) :
    (aeval (fun p => Polynomial.C (r p) * Polynomial.X) f : Polynomial S) =
      Polynomial.C (aeval r f) * Polynomial.X ^ d := by
  rw [aeval_eq_eval₂, aeval_eq_eval₂, VerticalPointMultiplicityChart.aeval_C_mul_X r f d hf]
end GroundTheory.Heights₂.Heights.VerticalPointNagata
