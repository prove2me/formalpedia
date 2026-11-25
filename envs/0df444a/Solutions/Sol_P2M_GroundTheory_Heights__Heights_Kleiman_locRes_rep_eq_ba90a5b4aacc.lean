-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locRes_rep_eq_ba90a5b4aacc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:54.516821+00:00
-- url     : https://prove2.me/submissions/37959462-7535-4acf-a862-d316ce9dc20e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {n : ℕ} {z : Ω} {J : Finset (Fin (N + 1))} {a b : Fin (N + 1)}
    (ha : a ∈ J) (hb : b ∈ J) (ga sa gb sb : Poly S N) (ea eb : ℕ)
    (hsa : sa ∈ monos ({a} : Finset (Fin (N + 1)))) (hsb : sb ∈ monos ({b} : Finset (Fin (N + 1))))
    (hsae : sa.IsHomogeneous ea) (hsbe : sb.IsHomogeneous eb)
    (hga : ga.IsHomogeneous (ea + n)) (hgb : gb.IsHomogeneous (eb + n))
    (hza : aeval y ga = z * aeval y sa) (hzb : aeval y gb = z * aeval y sb) :
    locRes (Finset.singleton_subset_iff.mpr ha)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) ga) ⟨sa, hsa⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {a}) =
      locRes (Finset.singleton_subset_iff.mpr hb)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) gb) ⟨sb, hsb⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {b}) := by
  rw [locRes_mk, locRes_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def]
  change Ideal.Quotient.mk _ (sb * ga) = Ideal.Quotient.mk _ (sa * gb)
  rw [Ideal.Quotient.eq]
  have h1 : (sb * ga).IsHomogeneous (eb + (ea + n)) := hsbe.mul hga
  have h2 : (sa * gb).IsHomogeneous (eb + (ea + n)) := by
    have := hsae.mul hgb
    rwa [show ea + (eb + n) = eb + (ea + n) by omega] at this
  rw [mem_primeOf_of_isHomogeneous y (h1.sub h2), map_sub, map_mul, map_mul, hza, hzb]
  ring
end GroundTheory.Heights₂.Heights.Kleiman
