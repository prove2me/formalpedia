-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_mem_twist_of_eq_zero_e2a97b30400f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:29:27.634015+00:00
-- url     : https://prove2.me/submissions/ec48ad40-e338-4d9b-a960-191d4f7559df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_sub_ne_bot_cb59329d6f45
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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
theorem _root_.solution (Q : LineBundle S x) (Q' : LineBundle S y) {r : Ω → K'}
    {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y = pp)
    (h : RestrictData Q.toSubSystem hxy Q'.toSubSystem r) (J : Chart y) {z : Ω}
    (hz : z ∈ Q.toSubSystem.sub (liftChart hxy J)) (hr : r z = 0) :
    z ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
  obtain ⟨w₀, hw₀, hrw₀⟩ : ∃ w ∈ Q.toSubSystem.sub (liftChart hxy J), r w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply sub_ne_bot Q' J
    rw [← h.span J, Submodule.span_eq_bot]
    rintro _ ⟨w, hw, rfl⟩
    exact hcon w hw
  obtain ⟨Q'', hQ''⟩ := Q.invertible (liftChart hxy J)
  have hmulA : ∀ u ∈ Q.toSubSystem.sub (liftChart hxy J), ∀ v ∈ Q'',
      u * v ∈ chartRing S x (liftChart hxy J) := by
    intro u hu v hv
    have : u * v ∈ Q.toSubSystem.sub (liftChart hxy J) * Q'' := Submodule.mul_mem_mul hu hv
    change u * v ∈ Q.sub (liftChart hxy J) * Q'' at this
    rw [hQ''] at this
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp this
    rw [← hb]; exact b.2
  have hkey : ∀ v ∈ Q'', z * v ∈ idealMod (x := x) pp (liftChart hxy J) := by
    intro v hv
    obtain ⟨f, s, e, hs, hf, hse, ha⟩ := hmulA z hz v hv
    obtain ⟨g, t, e', ht, hg, hte, hb⟩ := hmulA w₀ hw₀ v hv
    have h1 := h.smul J w₀ hw₀ f s e hs hf hse
    have h2 := h.smul J z hz g t e' ht hg hte
    have heq : aeval x f / aeval x s * w₀ = aeval x g / aeval x t * z := by
      rw [← ha, ← hb]; ring
    rw [heq, h2, hr, mul_zero] at h1
    have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos J hs
    have hfy : aeval y f = 0 :=
      (div_eq_zero_iff.mp ((mul_eq_zero.mp h1.symm).resolve_right hrw₀)).resolve_right hs0
    have hfp : f ∈ pp := by
      rw [← hpp]; exact (mem_primeOf_of_isHomogeneous y hf).mpr hfy
    rw [ha]
    exact Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩
  have hall : ∀ m ∈ Q.sub (liftChart hxy J) * Q'',
      z * m ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
    intro m hm
    induction hm using Submodule.mul_induction_on' with
    | mem_mul_mem q hq v hv =>
      refine Submodule.subset_span ⟨z * v, hkey v hv, q, hq, ?_⟩
      rw [smul_eq_mul]; ring
    | add m _ m' _ hm hm' => rw [mul_add]; exact add_mem hm hm'
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy J) * Q'' := by
    rw [hQ'']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  simpa using hall 1 h1
end GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
