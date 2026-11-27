-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:33:57.259801+00:00
-- url     : https://prove2.me/submissions/4ba77f96-41e4-4fc5-817d-7782c6247bb0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Parity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.ChartRestriction.G.FD in
private theorem UpperTheory.Reformulated.B.Ue6.herm_smul_right {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Ue6
theorem _root_.solution :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (w0 : NumberField.RingOfIntegers E),
      ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E) = (1 : E) - (↑w0 : E) →
        ∀ u ∈ X.Λ,
          ∀ v ∈ X.Λ,
            ∃ (k : ℤ),
              (Algebra.trace ℚ E : E → ℚ)
                    (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u (((↑w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E)) • v)) -
                  (Algebra.trace ℚ E : E → ℚ) (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) =
                (2 : ℚ) * (↑k : ℚ) := by
  intro E _ _ _ r X w0 hw u hu v hv
  have hwv : (w0 : E) • v ∈ X.Λ := X.Λ.smul_mem w0 hv
  obtain ⟨a, ha⟩ := X.EF_int u hu _ hwv
  obtain ⟨b, hb⟩ := X.EF_int u hu v hv
  have hc : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) = 1 - 2 * (w0 : E) := by
    have h1 : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - (1 - (w0 : E))) =
        ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) - (1 - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_sub, map_one]
    rw [hw, h1, hw]
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.EFf at ha hb
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hw] at ha
  refine ⟨b - a, ?_⟩
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hc, Int.cast_sub, ← ha, ← hb, ← map_sub, ← map_sub,
    two_mul ((Algebra.trace ℚ E) _), ← map_add]
  congr 1
  ring
end UpperTheory.Reformulated.B.Ue6
