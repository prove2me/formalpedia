-- Prove2me | solution 1 for PI.ScRefExists.GWG.globW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:52:23.94808+00:00
-- url     : https://prove2.me/submissions/901359a3-a569-4077-a79d-5d85a79f9e6a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
import Theorems.Thm_PI_ScRefExists_GWG_hyp_dvd
import Theorems.Thm_PI_ScRefExists_GWG_concl_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
namespace PI.ScRefExists.GWG
theorem _root_.solution (h1 : GWpp) (h2 : GWcrt) : GlobW := by
  have key : ∀ (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ)
      (g : ℕ), Hyp I g r k θ e f M → Concl I g r k θ e f M := by
    intro I r k θ e f M g
    induction g using Nat.recOnPosPrimePosCoprime with
    | prime_pow p n hp hn => exact h1 I p n r k θ e f M hp hn
    | zero => intro h; exact absurd h.1 (by norm_num)
    | one => intro _; exact concl_one I r k θ e f M
    | coprime a b ha hb hab iha ihb =>
      intro h
      exact h2 I a b r k θ e f M hab h (iha (hyp_dvd h (Dvd.intro b rfl) (by omega)))
        (ihb (hyp_dvd h (Dvd.intro_left a rfl) (by omega)))
  intro I g r k θ e f M hg hS hT hn he hf hef hM hL
  exact key I r k θ e f M g ⟨hg, hS, hT, hn, he, hf, hef, hM, hL⟩
end PI.ScRefExists.GWG
