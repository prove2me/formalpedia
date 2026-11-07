-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_jointTriangleHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:18.691842+00:00
-- url     : https://prove2.me/submissions/dfdec58b-8ad0-4590-8873-0deec2c2a3f0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_triangleHit_of_continuous

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution : IsClosed
    {d : TriangleHitData | d.2.2.2 ∈ triangleHit d.1 d.2.1 d.2.2.1} :=
  isClosed_triangleHit_of_continuous (fun d : TriangleHitData => d.1)
    (fun d => d.2.2.2) (fun d => d.2.1) (fun d => d.2.2.1)
    continuous_fst continuous_snd.snd.snd continuous_snd.fst continuous_snd.snd.fst
end QEC.Coding.ProbabilisticConstruction.SphericalCap
