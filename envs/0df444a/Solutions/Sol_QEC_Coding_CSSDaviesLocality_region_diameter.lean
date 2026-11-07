-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.region_diameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:34:22.214497+00:00
-- url     : https://prove2.me/submissions/8af89ce9-0fe2-44a3-bc09-2e8320263b4d

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_region_dist_center

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
variable (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
include horth
omit horth
namespace QEC.Coding.CSSDaviesLocality
theorem _root_.solution (J : ι → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ j, ∀ x ∈ rowSupport P Q j, ∀ y ∈ rowSupport P Q j, dist (J x) (J y) ≤ r)
    (q x y : ι) (hx : x ∈ region P Q q) (hy : y ∈ region P Q q) : dist (J x) (J y) ≤ 2*r := by
  have h1 := region_dist_center P Q J r hr hs q x hx
  have h2 := region_dist_center P Q J r hr hs q y hy
  have ht := dist_triangle (J x) (J q) (J y)
  rw [dist_comm (J x) (J q)] at ht
  linarith
end QEC.Coding.CSSDaviesLocality
