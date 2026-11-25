-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_restrictData_comp_e303461df737
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:43.727974+00:00
-- url     : https://prove2.me/submissions/3e8d8016-b8f1-4c53-9b9c-15db2580cc77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict

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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {K' K'' : Type w}
  [Field K'] [Algebra S K'] [Field K''] [Algebra S K''] {N : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {z : Fin (N + 1) → K''}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
theorem _root_.solution {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {hyz : ∀ i, z i ≠ 0 → y i ≠ 0}
    {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {Q'' : SubSystem S z K''} {r : Ω → K'}
    {r' : K' → K''} (h1 : RestrictData Q hxy Q' r) (h2 : RestrictData Q' hyz Q'' r') :
    RestrictData Q (fun i hi => hxy i (hyz i hi)) Q'' (r' ∘ r) where
  mem I q hq := h2.mem I _ (h1.mem (liftChart hyz I) q hq)
  add I q hq q' hq' := by
    simp only [Function.comp_apply]
    rw [h1.add (liftChart hyz I) q hq q' hq',
      h2.add I _ (h1.mem (liftChart hyz I) q hq) _ (h1.mem (liftChart hyz I) q' hq')]
  smul I q hq f s e hs hf hse := by
    simp only [Function.comp_apply]
    rw [h1.smul (liftChart hyz I) q hq f s e hs hf hse,
      h2.smul I (r q) (h1.mem (liftChart hyz I) q hq) f s e hs hf hse]
  span I := by
    rw [← h2.span I]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨r q, h1.mem (liftChart hyz I) q hq, rfl⟩
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨q', hq', rfl⟩
      have hle := (h1.span (liftChart hyz I)).le
      have hq'' : q' ∈ Submodule.span (chartRing S y (liftChart hyz I))
          (r '' Q.sub (liftChart hxy (liftChart hyz I))) := by
        rw [h1.span (liftChart hyz I)]
        exact hq'
      have h0 : r' 0 = 0 := by
        have := h2.add I 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
        rw [add_zero] at this
        simpa using this
      refine Submodule.span_induction (p := fun q' _ => r' q' ∈ Submodule.span (chartRing S z I)
        ((r' ∘ r) '' Q.sub (liftChart (fun i hi => hxy i (hyz i hi)) I))) ?_ ?_ ?_ ?_ hq''
      · rintro _ ⟨q, hq, rfl⟩
        exact Submodule.subset_span ⟨q, hq, rfl⟩
      · rw [h0]
        exact Submodule.zero_mem _
      · intro a b ha hb iha ihb
        rw [h2.add I a (hle ha) b (hle hb)]
        exact Submodule.add_mem _ iha ihb
      · intro c a ha iha
        obtain ⟨f, s, e, hs, hf, hse, hc⟩ := c.2
        have key : r' (c • a) =
            (⟨aeval z f / aeval z s, f, s, e, hs, hf, hse, rfl⟩ : chartRing S z I) • r' a := by
          rw [Subalgebra.smul_def, smul_eq_mul, hc, h2.smul I a (hle ha) f s e hs hf hse]
          rfl
        rw [key]
        exact Submodule.smul_mem _ _ iha
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
