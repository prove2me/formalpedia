-- Prove2me | solution 1 for PI.FT.frame_formulas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:02.17102+00:00
-- url     : https://prove2.me/submissions/8879a766-906c-443a-b73a-0bfeb68f29e7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
import Theorems.Thm_PI_FT_Lm_mul
import Theorems.Thm_PI_FT_Xc_q_add_B_R
import Theorems.Thm_PI_FT_formulaA
import Theorems.Thm_PI_FT_formulaB
import Theorems.Thm_PI_FT_stab_mul_Xc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
local notation "ι" => inclR (F := F) (E := E) (AF F)
namespace PI.FT
theorem _root_.solution {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    {J' : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {β : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hH : FrameHyp F E σ M J J' x β B)
    (e : Hstab (AF F) σ J x ≃* HA (AF F) σ J')
    (he : ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) :
    (∀ g : Hstab (AF F) σ J x,
      mt (e g) = (Lm σ J J' B).map ι * mt (g : HA (AF F) σ J) * B.map ι) ∧
    (∀ g : Hstab (AF F) σ J x,
      mt (g : HA (AF F) σ J) = (Xc x).map ι * (qm σ J x (algebraMap F E β)).map ι +
        B.map ι * mt (e g) * (Rm σ J J' B x (algebraMap F E β)).map ι) := by
  obtain ⟨-, hβ, hx, hxB, hJ', -, hd⟩ := hH
  have hb : algebraMap F E β ≠ 0 := fun h =>
    hβ ((algebraMap F E).injective (h.trans (map_zero _).symm))
  have hLB := Lm_mul σ hJ' hd
  have hdec := Xc_q_add_B_R σ hb hx hxB hLB
  exact ⟨fun g => formulaA σ (AF F) hLB _ _ (he g),
    fun g => formulaB σ (AF F) hdec _ _ (stab_mul_Xc σ (AF F) g) (he g)⟩
end PI.FT
