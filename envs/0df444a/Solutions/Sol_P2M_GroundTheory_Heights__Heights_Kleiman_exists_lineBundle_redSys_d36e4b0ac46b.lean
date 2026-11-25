-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_redSys_d36e4b0ac46b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:10.416616+00:00
-- url     : https://prove2.me/submissions/994db967-a621-4b88-b10f-2f3dfa2caafd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_ebff74c5b356
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_one_d19ae30e21d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_span_iff_exists_isUnit_1ef95d12e374


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}
include hsp
variable {g : Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg0 : g ≠ 0)
    (hg : RedGood hxy Nb.toSubSystem g) (hgsec : ∀ I : Chart x, g ∈ Nb.sub I) :
    ∃ Q' : LineBundle k y, Q'.toSubSystem = redSys hxy Nb.toSubSystem g := by
  refine ⟨LineBundle.mk (SubFamily.mk (redSys hxy Nb.toSubSystem g) ?_) ?_ ?_, rfl⟩
  · intro I J hIJ z
    rw [redSys_sub_eq hsp hxy hV hg, redSys_sub_eq hsp hxy hV hg]
    exact res_mem_span_iff_exists_isUnit hIJ z
  · intro I
    rw [redSys_sub_eq hsp hxy hV hg]
    exact Submodule.fg_span (Set.finite_range _)
  · intro I
    obtain ⟨M, hM⟩ := Nb.invertible (liftChart hxy I)
    refine ⟨Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * g)) '' M), ?_⟩
    have hA : ∀ {q m : Ω}, q ∈ Nb.sub (liftChart hxy I) → m ∈ M →
        q * m ∈ chartRing k x (liftChart hxy I) :=
      fun hq hm => mul_mem_chartRing_of_mul_eq_one hM hq hm
    have hmg : ∀ {m : Ω}, m ∈ M → m * g ∈ locAt k x y := fun hm =>
      (chartRing_sub_locAt hsp hxy I (by rw [mul_comm]; exact hA (hgsec _) hm)).1
    have hsplit : ∀ q m : Ω, q * m = q / g * (m * g) := fun q m => by field_simp
    apply le_antisymm
    · change Submodule.span _ _ * Submodule.span _ _ ≤ 1
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
      show redAt k x y (q / g) * redAt k x y (m * g) ∈ (1 : Submodule (chartRing k y I) K')
      rw [← (locAt_mul hsp (hg I q hq) (hmg hm)).2, ← hsplit]
      exact Submodule.mem_one.mpr ⟨⟨_, (chartRing_sub_locAt hsp hxy I (hA hq hm)).2⟩, rfl⟩
    · rw [Submodule.one_le]
      have h1 : (1 : Ω) ∈ Nb.sub (liftChart hxy I) * M := by
        rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z ∈
          (redSys hxy Nb.toSubSystem g).sub I *
            Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * g)) '' M)) h1
        (fun q hq m hm => ⟨(chartRing_sub_locAt hsp hxy I (hA hq hm)).1, by
          rw [hsplit, (locAt_mul hsp (hg I q hq) (hmg hm)).2]
          exact Submodule.mul_mem_mul (Submodule.subset_span ⟨q, hq, rfl⟩)
            (Submodule.subset_span ⟨m, hm, rfl⟩)⟩)
        (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
          rw [(locAt_add hsp hu.1 hv.1).2]; exact Submodule.add_mem _ hu.2 hv.2⟩)
      rw [(locAt_one hsp).2] at this
      exact this.2
end GroundTheory.Heights₂.Heights.Kleiman
