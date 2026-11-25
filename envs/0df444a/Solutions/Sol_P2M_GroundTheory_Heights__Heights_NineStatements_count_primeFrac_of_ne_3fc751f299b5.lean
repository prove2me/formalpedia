-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_count_primeFrac_of_ne_3fc751f299b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:21.395085+00:00
-- url     : https://prove2.me/submissions/d6026129-67b6-4254-9c8e-06667f3726e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_natCast_notMem_of_ne_7acf22c28962
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_primeSpan_ne_bot_2babad6d564f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (𝔓 : HeightOneSpectrum (𝓞 L)) (h : (p : 𝓞 L) ∈ 𝔓.asIdeal) :
    FractionalIdeal.count L 𝔓 (primeFrac L q) = 0 := by
  classical
  have hJ := primeSpan_ne_bot (L := L) hq
  rw [primeFrac, FractionalIdeal.count_coe L 𝔓 hJ, Nat.cast_eq_zero]
  by_contra hc
  have hd := (Associates.count_ne_zero_iff_dvd hJ 𝔓.irreducible).mp hc
  exact natCast_notMem_of_ne hp hq hpq 𝔓 h
    ((Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (Set.mem_singleton _)))
end GroundTheory.Heights₂.Heights.NineStatements
