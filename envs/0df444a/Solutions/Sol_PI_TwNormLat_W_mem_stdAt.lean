-- Prove2me | solution 1 for PI.TwNormLat.W.mem_stdAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:19.487212+00:00
-- url     : https://prove2.me/submissions/3a4ecbb5-104a-4e60-8709-df44d22b002c

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution {n : ℕ} (v : Sp E n) : v ∈ stdAt E n P ↔ ∀ l, IntAt P (v l) := by
  change (∃ s ∈ P.asIdeal.primeCompl, s • v ∈ stdLat E n) ↔ _
  constructor
  · rintro ⟨s, hs, hv⟩ l
    have hl : (s • v) l ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_pi.mp hv l (Set.mem_univ l)
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hl
    refine ⟨r, s, hs, ?_⟩
    rw [hr, Pi.smul_apply, Algebra.smul_def]
  · intro h
    choose r s hs hrs using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ (fun l _ => hs l), ?_⟩
    refine Submodule.mem_pi.mpr fun l _ => ?_
    refine Submodule.mem_one.mpr ⟨(∏ l' ∈ Finset.univ.erase l, s l') * r l, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l),
      map_mul, map_mul, ← hrs l]
    ring
end PI.TwNormLat.W
