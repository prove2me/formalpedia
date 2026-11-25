-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.row_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:36.61651+00:00
-- url     : https://prove2.me/submissions/e892180d-8934-4aad-9462-9bd290e758c0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_lt
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_inj
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_apply_sum__9640259db90f
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_atN_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {N' n c k₀ : ℕ} (hk : k₀ ≤ n) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E N' (n + c))
    (s p : ℕ) (hp : p < n + c) :
    atN ((g.toLinearMap ∘ₗ y) (eN E N' s)) (fIdx k₀ c n p) =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        atN (y (eN E N' s)) (fIdx k₀ c n p'') := by
  have himg : (Finset.range (n + c)).image (fIdx k₀ c n) = Finset.range (n + c) := by
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      obtain ⟨p'', hp'', rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (fIdx_lt hk (Finset.mem_range.mp hp''))
    · rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      exact fIdx_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hk hab
  have hsum : ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        atN (y (eN E N' s)) (fIdx k₀ c n p'') =
      ∑ m ∈ Finset.range (n + c), atN (g (eN E (n + c) m)) (fIdx k₀ c n p) * atN (y (eN E N' s)) m := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a ha b hb hab => fIdx_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hk hab)]
  have hA : ∀ {M : ℕ} (v : Fin M → E) (m : Fin M), atN v m.1 = v m := fun v m => by
    rw [atN_of_lt v m.isLt]
  have hB : ∀ (v : Fin (n + c) → E), atN v (fIdx k₀ c n p) = v ⟨_, fIdx_lt hk hp⟩ := fun v => atN_of_lt v _
  rw [hsum, Finset.sum_range (fun m => atN (g (eN E (n + c) m)) (fIdx k₀ c n p) * atN (y (eN E N' s)) m)]
  simp only [hA, hB, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [apply_sum' g]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mul_comm]
end PI.TwistedEisensteinNonvanishing.W
