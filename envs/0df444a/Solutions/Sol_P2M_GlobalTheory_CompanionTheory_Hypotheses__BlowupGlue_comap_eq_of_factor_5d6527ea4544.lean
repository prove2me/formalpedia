-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_comap_eq_of_factor_5d6527ea4544
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:47:49.27311+00:00
-- url     : https://prove2.me/submissions/74d94276-2ada-4c11-ad43-70a5a143c5d1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
namespace GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
theorem _root_.solution {T X : Scheme.{0}} {Z Z' : X.IdealSheafData} {O : X.Opens}
    (h : Z'.comap O.ι = Z.comap O.ι) (a : T ⟶ X) (b : T ⟶ O) (hab : b ≫ O.ι = a) : Z'.comap a = Z.comap a := by
  subst hab
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h]
end GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
