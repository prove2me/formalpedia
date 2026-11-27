-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_glue_loc_988e0dd258a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:18.963064+00:00
-- url     : https://prove2.me/submissions/b0406d13-94be-4066-bcf9-35137e9b3156

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZColB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_not_le_of_prod_10e9f6327452

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (A : HeightOneSpectrum R → Submodule R V)
    (hsat : ∀ w (s : R), s ∉ w.asIdeal → ∀ x, s • x ∈ A w → x ∈ A w)
    (hfin : ∀ x : V, {w | x ∉ A w}.Finite)
    (habs : ∀ w (x : V), ∃ m : ℕ, ∀ a ∈ w.asIdeal ^ m, a • x ∈ A w)
    (w : HeightOneSpectrum R) (x : V) :
    (∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ glue A) ↔ x ∈ A w := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w s hs x ((Submodule.mem_iInf _).mp hx w)
  · intro hx
    classical
    choose m hm using fun v => habs v x
    have hw : w ∉ (hfin x).toFinset := by simpa using hx
    obtain ⟨s, hsI, hsw⟩ := SetLike.not_le_iff_exists.mp (not_le_of_prod m w hw)
    refine ⟨s, hsw, (Submodule.mem_iInf _).mpr fun v => ?_⟩
    by_cases hv : x ∈ A v
    · exact (A v).smul_mem s hv
    · exact hm v s (Ideal.prod_le_inf.trans (Finset.inf_le ((hfin x).mem_toFinset.mpr hv)) hsI)
end Formalism.BasicNotions.Examples₂.NZ
