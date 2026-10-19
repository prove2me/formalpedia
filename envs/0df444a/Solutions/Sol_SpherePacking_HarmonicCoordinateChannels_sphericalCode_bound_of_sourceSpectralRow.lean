-- Prove2me | solution 1 for SpherePacking.HarmonicCoordinateChannels.sphericalCode_bound_of_sourceSpectralRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/8b667176-8e6a-4ec2-b15c-e2a06fe45072

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finiteGramCertificate_sphericalCode_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open SpherePacking.HarmonicCoordinateChannels
namespace SpherePacking.HarmonicCoordinateChannels
theorem _root_.solution
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (source : SourceSpectralRowData n k L
      (HarmonicCertificateAssembly.harmonicWeightedFibre
        n k L hn hkl degreeFibre))
    {s : ℝ} (hs : s ≤ 1)
    (hgap : s < Jacobi.topEigenvalue n k L)
    (C : SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) / (Jacobi.topEigenvalue n k L - s)) *
        ((truncatedHarmonicDimension n k L : ℝ) /
          (Gegenbauer.fibreDimension n k : ℝ)) :=
  finiteGramCertificate_sphericalCode_bound hn hkl
    (assembleFiniteGramCertificateOfSourceRow
      n k L hn hkl degreeFibre source)
    hs hgap C
end SpherePacking.HarmonicCoordinateChannels
